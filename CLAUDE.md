# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Test Commands

```bash
lake build              # Build the library (default target: LeanTcb)
lake build LeanTcbTest  # Build and run all tests (tests execute at build time)
lake clean              # Clean build artifacts
```

There is no way to run a single test file independently. Tests are Lean files that execute assertions during elaboration — if a test fails, `lake build LeanTcbTest` will report the error with file and line number.

## Architecture

**lean-tcb** is a Lean 4 metaprogramming library that computes which declarations a theorem's *meaning* depends on (the "trusted computing base"). It works by traversing the `Environment` at elaboration time.

### Core semantic model

The key insight: for `def`s, the body IS the specification (it defines meaning). For `theorem`s, only the type matters — the proof is kernel-checked. This determines what gets walked during traversal:

- `def`/`abbrev`: type + value (both trusted)
- `theorem`/`opaque`: type only (proof/body not trusted)
- `axiom`: type only
- `inductive`: type + constructor types

### Module pipeline

1. **Types.lean** — `TcbResult` (flat spec set), `TcbGraphResult` (spec set + `parentMap` provenance + `depsMap` forward adjacency), `DepReason` (why a dependency was enqueued)
2. **Classify.lean** — `trustRelevantExprs` returns which `Expr`s to walk per declaration kind; `collectConstants` extracts names via `Expr.foldConsts` and `collectProjTypeNames` for `Expr.proj`
3. **Core.lean** — `computeTcb` / `computeTcbGraph`: partial worklist traversal. Handles constructors (enqueue parent inductive), recursors (enqueue all parent inductives), and mutual blocks (enqueue all companions). The graph variant records `parentMap` (discovery tree) and `depsMap` (all edges with reasons)
4. **Attr.lean** — `@[tcb]` tag attribute via `registerTagAttribute`; `isTcbAnnotated` walks parent names for coverage; `checkAnnotations` cross-checks computed vs declared TCB
5. **Format.lean** — `formatResult` categorizes into axioms/userSpec/librarySpec using `env.getModuleIdxFor?` (returns `none` for current-module declarations); `renderResult` produces the infoview string
6. **Path.lean** — `findPath` walks `parentMap` backwards from target to entry point; `renderPath` formats the chain for `#tcb_why`
7. **Tree.lean** — `renderTree` renders `TcbGraphResult` as an indented tree (like Unix `tree`). Supports DAG dedup (`(see above)`), library collapsing, auto-generated collapsing, and prefers structural dependency reasons (`recParent`, `mutualCompanion`) over generic `exprRefType`/`exprRefBody` in labels
8. **Command.lean** — `#tcb`/`#tcb!`, `#tcb_tree`/`#tcb_tree!`, `#tcb_why` syntax and elaborators; resolves names, runs pipeline, emits warnings for annotation mismatches

### Test infrastructure

Tests use custom command elaborators (`elab "#test_foo" : command => do ...`) because `#eval` cannot access `Environment` (no `MonadEnv IO` instance). Each test file defines fixtures, runs assertions via `throwError`, and includes `#tcb` smoke tests for visual verification in the infoview. Tests are in `test/LeanTcbTest/`.

## Lean Conventions

- `autoImplicit` is set to `false` project-wide (in lakefile.lean) — all type variables must be explicitly bound
- All source files have copyright headers and module docstrings (`/-! ... -/`)
- Module docstrings must come *after* imports (Lean requires imports first)
- Keep lines under 100 characters
- Apache 2.0 license
- `String.containsSubstr` doesn't exist in this Lean version; use `(s.splitOn needle).length > 1`

## Known Limitations

- Walking `def` bodies over-approximates: `foldConsts` collects proof sub-terms (e.g., decidability witnesses). This is the safe direction — never misses a real dependency.
- Skipping theorem proofs means `sorryAx` won't be detected through traversal. This is by design: the tool answers "what must a human trust?" not "is the proof complete?"
