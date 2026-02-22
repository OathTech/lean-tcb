# lean-tcb

> **Status: Experimental** — This project is in early development and has
> been primarily developed with AI assistance (Claude Code). While it has
> a test suite, it has not been independently audited. Use at your own
> risk and verify results manually for high-assurance applications.

[Trusted computing base](https://en.wikipedia.org/wiki/Trusted_computing_base) analyzer for Lean 4.

## Why?

Lean's kernel checks that proofs are correct — but it can't check that your
*definitions* mean what you think they mean. If your definition of `prime`
accidentally allows 1, your "proof" that 2 is prime is technically valid but
meaningless.

`lean-tcb` answers the question: **which declarations must a human review
to trust that a theorem says what it claims?** It computes the transitive
closure of trust-relevant dependencies, separating the definitions that give
a theorem its meaning from the proof infrastructure that the kernel verifies.

This is useful for:
- **Auditing formal proofs** — know exactly which definitions to review
  instead of reading the entire codebase
- **Tracking specification drift** — catch when refactoring changes what
  a theorem depends on
- **Understanding proof architecture** — see why a particular definition
  ended up in your trust boundary

## Installation

Add `lean-tcb` as a dependency in your lakefile.

`lakefile.lean`:
```lean
require «lean-tcb» from git
  "https://github.com/OathTech/lean-tcb" @ "main"
```

`lakefile.toml`:
```toml
[[require]]
name = "lean-tcb"
git = "https://github.com/OathTech/lean-tcb"
rev = "main"
```

Then run `lake update lean-tcb`. In your Lean files:

```lean
import LeanTcb
```

Requires Lean 4.27.0 (forward compatibility with later versions is
best-effort).

## Quick start

```lean
import LeanTcb

def myDvd (a b : Nat) : Prop := ∃ k, b = a * k

def myPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬ ∃ d, 2 ≤ d ∧ d < n ∧ myDvd d n

theorem two_is_prime : myPrime 2 := by
  constructor <;> omega

#tcb two_is_prime
```

Hover over `#tcb` in the infoview to see:

```
═══ TCB Analysis ═══

Entry points: two_is_prime

── Must Review (3 declarations) ──
  • myDvd          def
  • myPrime        def
  • two_is_prime   theorem

── Axioms ──
  none

── Summary ──
  Must review:    3 declarations (75% of project)
  Not in TCB:     1 declaration
  Depends on:     36 library dependencies

Tip: #tcb_tree for dependency graph · #tcb_why <entry> <name> to trace a path
```

**Must Review** lists the declarations whose definitions a human must read
to trust the theorem — here, `myPrime` and `myDvd` define what "prime" and
"divides" mean. **Axioms** shows any axioms in the trust path (e.g.,
`Classical.choice`). **Summary** gives counts: how much of your project is
in the TCB, how many library dependencies, and the percentage of
human-written code that needs review.

Once you know your TCB, you can lock it down with [`@[tcb]`
annotations](#tcb-annotations) — the tool will warn if the TCB
drifts from your expectations.

Use `#tcb!` for verbose output that includes the full list of library
dependencies (Nat, And, Exists, etc.).

You can analyze multiple entry points at once: `#tcb theorem1 theorem2`.

## Dependency tree

`#tcb_tree` renders the full dependency graph as an indented tree:

```lean
#tcb_tree two_is_prime
```

```
═══ TCB Dependency Tree ═══

two_is_prime [theorem]
├── myPrime [def] ← referenced in type
│   ├── myDvd [def] ← referenced in body
│   │   └── [6 library dependencies]
│   └── [7 library dependencies]
└── [3 library dependencies]

Tip: #tcb_why <entry> <name> to trace why a name is included
```

Library dependencies and auto-generated declarations (recursors, casesOn,
match helpers) are collapsed by default. Use `#tcb_tree!` to expand library
dependencies. Each edge is labeled with why the dependency exists —
"referenced in type" vs "referenced in body" for expression references, and
structural reasons like "mutual block companion" or "parent inductive
(recursor)" where applicable. Already-rendered nodes show `(see above)` to
handle diamond dependencies.

## Path query

`#tcb_why` explains why a specific declaration is in the TCB:

```lean
#tcb_why two_is_prime myDvd
```

```
═══ TCB Path: two_is_prime → myDvd ═══

  ● two_is_prime [theorem]
  → myPrime [def] ← referenced in type
  → myDvd [def] ← referenced in body

Tip: #tcb_tree for the full dependency graph
```

If the target is not in the TCB, the tool says so — useful for confirming
that helper lemmas are correctly excluded.

## Warnings

The tool detects and warns about soundness-relevant issues in the TCB:

- **sorry** — proofs that are incomplete (`depends on sorry`)
- **native_decide** — proofs that trust the Lean compiler
- **unsafe** — declarations with weaker kernel guarantees

These warnings appear both inline (as Lean warnings) and in the `#tcb`
output.

## How it works

Starting from a theorem's type, `lean-tcb` traverses trust-relevant
dependencies. What counts as "trusted" depends on the declaration kind:

| Declaration kind | What's in the TCB      |
|------------------|------------------------|
| `theorem`        | type only (proof is kernel-checked) |
| `def` / `abbrev` | type + body (body defines meaning) |
| `axiom`          | type only              |
| `opaque`         | type only              |
| `inductive`      | type + constructor types |

The key insight: for a `def`, the body *is* the specification — it defines
what the name means. For a `theorem`, only the statement matters — the proof
is kernel-checked. This is why helper lemmas used in proofs are excluded
from the TCB while definitions are included.

The traversal also follows structural links: constructors pull in their
parent inductive, recursors pull in parent inductives, and mutual blocks
include all companions together.

## `@[tcb]` annotations

You can mark declarations you *expect* to be in the TCB:

```lean
set_option tcb.checkAnnotations true

@[tcb] def myDvd (a b : Nat) : Prop := ∃ k, b = a * k
@[tcb] def myPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬ ∃ d, 2 ≤ d ∧ d < n ∧ myDvd d n

#tcb two_is_prime  -- checks annotations as part of output
```

With annotations enabled, `#tcb` cross-checks the TCB against your
`@[tcb]` tags and warns about:
- **Unannotated TCB members** — a definition is in the TCB but you forgot
  to tag it (an unexpected trust dependency crept in)
- **Stale annotations** — a `@[tcb]` tag on a declaration that isn't in
  the TCB for the given entry points

To enable project-wide, add to your `lakefile.lean`:

```lean
leanOptions := #[⟨`tcb.checkAnnotations, true⟩]
```

Annotating an `inductive` or `def` covers auto-generated companions
(constructors, recursors, `.casesOn`, `.match_1`, etc.).

## Command reference

| Command | Description |
|---------|-------------|
| `#tcb name₁ name₂ ...` | Analyze the TCB for given entry points |
| `#tcb! name₁ ...` | Same, with full library dependency listing |
| `#tcb_tree name₁ ...` | Render dependency tree (library collapsed) |
| `#tcb_tree! name₁ ...` | Render dependency tree (library expanded) |
| `#tcb_why entry target` | Show why `target` is in the TCB of `entry` |

All commands automatically warn about **soundness issues**
(`sorry`, `native_decide`, `unsafe`) in project-local TCB
members. Enable `set_option tcb.checkAnnotations true` to
also cross-check `@[tcb]` annotations (see above).

## Limitations

- **The TCB may be larger than strictly necessary.** `def` bodies can
  contain proof sub-terms (e.g., decidability witnesses) that get included.
  This is by design — the tool never misses a real dependency.
- **`sorry` is detected via warnings, not traversal.** Since theorem
  proofs are intentionally skipped, `sorry` won't appear in the TCB.
  Instead, `#tcb` uses `Lean.collectAxioms` to warn about `sorry` and
  `native_decide` in project-local declarations separately.
- **Type class instances may be inlined.** Lean can inline instances or
  coercions at elaboration time. When this happens, the instance's *body*
  is captured in the TCB but its *name* may not appear. This is sound
  but can be surprising — if you expect `MyInstance` in the TCB and don't
  see it, its logic is still being checked.

## Development

Run the test suite:

```bash
lake build LeanTcbTest
```

Tests execute at elaboration time — if a test fails, the build reports
the error with file and line number.

