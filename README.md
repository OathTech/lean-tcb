# lean-tcb

> **Status: Experimental** — This project is in early development and has
> been primarily developed with AI assistance (Claude Code). While it has
> a test suite, it has not been independently audited. Use at your own
> risk and verify results manually for high-assurance applications.

Trusted Computing Base analyzer for Lean 4.

When you prove a theorem in Lean, the kernel checks the proof — but the
*statement* still depends on definitions you wrote.  `lean-tcb` computes
exactly which declarations must be trusted for a given theorem to mean
what you think it means.

## Installation

Add `lean-tcb` as a dependency in your `lakefile.lean`:

```lean
require «lean-tcb» from git
  "https://github.com/OathTech/lean-tcb" @ "main"
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

Hover over `#tcb` in the infoview to see the analysis:

- **Must Review** — your declarations that the theorem's meaning depends on
- **Axioms** — which axioms are in scope (standard vs non-standard)
- **Summary** — how much of your project is in the TCB vs not

Use `#tcb!` for verbose output that includes library dependencies.

### Dependency tree

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

Library dependencies are collapsed by default. Use `#tcb_tree!` to expand them.

Structural reasons like "mutual block companion", "recursor enqueued parent
inductive", and "constructor enqueued parent inductive" are shown instead of
generic "referenced in type/body" where applicable. Already-rendered nodes
show `(see above)` with the edge reason preserved.

### Path query

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

The result partitions the environment into a **spec set** (must review) and
everything else (kernel-verified, no trust needed). Helper lemmas used only
in proofs are excluded from the TCB.

## `@[tcb]` annotations

You can mark declarations you *expect* to be in the TCB:

```lean
@[tcb] def myDvd (a b : Nat) : Prop := ∃ k, b = a * k
@[tcb] def myPrime (n : Nat) : Prop := ...
```

When `#tcb` runs, it cross-checks the computed TCB against your annotations
and warns about:
- Declarations in the TCB that you forgot to annotate
- Stale `@[tcb]` annotations on declarations no longer in the TCB

Annotating an `inductive` or `def` covers auto-generated companions
(constructors, recursors, `.casesOn`, `.match_1`, etc.).

## Requirements

- Lean 4.27.0+
