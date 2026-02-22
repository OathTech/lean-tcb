# lean-tcb

> **Status: Experimental** — This project is in early development and has
> been primarily developed with AI assistance (Claude Code). While it has
> a test suite, it has not been independently audited. Use at your own
> risk and verify results manually for high-assurance applications.

Trusted Computing Base analyzer for Lean 4.

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

Then run `lake update lean-tcb`.

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
  Not in TCB:     1 declarations
  Depends on:     36 library declarations
```

The tool found that `two_is_prime`'s meaning depends on `myPrime` and `myDvd`
(which define what "prime" and "divides" mean), but not on any helper lemmas
used only in the proof. A reviewer needs to check these two definitions to
trust the theorem statement.

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
├── myPrime [def] ← referenced in type/body
│   ├── myDvd [def] ← referenced in type/body
│   │   └── [6 library dependencies]
│   └── [7 library dependencies]
└── [3 library dependencies]
```

Library dependencies are collapsed by default. Use `#tcb_tree!` to expand
them. Each edge is labeled with why the dependency exists — structural
reasons like "mutual block companion" or "recursor enqueued parent inductive"
are shown where applicable. Already-rendered nodes show `(see above)` to
handle diamond dependencies.

## Path query

`#tcb_why` explains why a specific declaration is in the TCB:

```lean
#tcb_why two_is_prime myDvd
```

```
═══ TCB Path: two_is_prime → myDvd ═══

  ● two_is_prime [theorem]
  → myPrime [def] ← referenced in type/body
  → myDvd [def] ← referenced in type/body
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

Starting from a theorem's type, `lean-tcb` does a worklist traversal of
trust-relevant dependencies:

| Declaration kind | What's trusted         |
|------------------|------------------------|
| `theorem`        | type only (proof is kernel-checked) |
| `def` / `abbrev` | type + value (body defines meaning) |
| `axiom`          | type only              |
| `opaque`         | type only              |
| `inductive`      | type + constructor types |

The key insight: for a `def`, the body *is* the specification — it defines
what the name means. For a `theorem`, only the type matters — the proof is
kernel-checked and doesn't affect meaning. This is why helper lemmas used
in proofs are excluded from the TCB while definitions are included.

The traversal also handles:
- **Constructor → parent inductive** linkage
- **Recursor → parent inductive** linkage
- **Mutual blocks** — all companions are included together
- **`Expr.proj`** — structure projection type names (missed by `foldConsts`)

The result partitions the environment into the **TCB** (must review) and
everything else (kernel-verified, no trust needed).

## `@[tcb]` annotations

You can mark declarations you *expect* to be in the TCB:

```lean
set_option tcb.checkAnnotations true

@[tcb] def myDvd (a b : Nat) : Prop := ∃ k, b = a * k
@[tcb] def myPrime (n : Nat) : Prop := ...
```

Enable `set_option tcb.checkAnnotations true` to have `#tcb` cross-check
the computed TCB against your annotations. It warns about:
- Declarations in the TCB that you forgot to annotate
- Stale `@[tcb]` annotations on declarations no longer in the TCB

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

## Limitations

- **Over-approximation by design.** Walking `def` bodies collects all
  referenced constants, including proof sub-terms like decidability
  witnesses. This means the TCB may be larger than strictly necessary,
  but it never misses a real dependency.
- **Theorem proofs are skipped.** This means `sorry` is not detected
  through traversal (use `#tcb` warnings for that). By design: the tool
  answers "what must a human trust?" not "is the proof complete?"
- **sorry/native_decide detection.** These warnings are generated by
  `Lean.collectAxioms`, which traverses proof bodies — a separate
  mechanism from the TCB traversal. Detection covers all project-local
  declarations in the TCB.
- **Elaborator inlining.** Lean may inline type class instances or
  coercions at elaboration time. The tool sees the inlined expression,
  so instance *names* may not appear in the TCB even though their
  *bodies* are captured. This is sound but can be surprising.

## Development

Run the test suite:

```bash
lake build LeanTcbTest
```

Tests execute at elaboration time — if a test fails, the build reports
the error with file and line number.

## Requirements

- Lean 4.27.0 (forward compatibility with later versions is best-effort)
