# TODO — lean-tcb backlog

Items identified during the 2026-02-21 release readiness audit
that are deferred to future work.

## Detection / Correctness

- [ ] **`isProjectLocal` fallback when package info unavailable (H3)**
  When `getModulePackage?` returns `none` (non-Lake builds), all
  imported declarations are classified as "library." Correct safe
  direction but could confuse users in unusual build setups.
  Consider a fallback heuristic or clearer warning.

- [ ] **`isTcbAnnotated` `.num` branch untested (M8)**
  Auto-generated declarations with numeric suffixes (like `match_1`)
  exercise the `.num parent _` branch in `Attr.lean:36`. No test
  covers this. Add a test with a fixture that generates numeric
  name components.

- [ ] **Percentage denominator includes auto-generated declarations (M4)**
  "X% of project" counts ALL project-local constants (`.match_1`,
  `.rec`, `.casesOn`) in the denominator. Consider filtering to
  only "human-written" declarations, or document as a known
  limitation.

- [ ] **DAG dedup across multiple tree entry points (M6)**
  `renderTree` resets `seen = {}` for each entry point, so shared
  dependencies render fully under both trees. Consider sharing the
  `seen` set or documenting the current behavior.

## UX / Output

- [ ] **Confusing output when analyzing library entry points (L9)**
  `#tcb Nat.add` produces empty "Must Review" with no explanation
  that the entry point is library-level. Consider a hint message.

## Performance

- [ ] **`.toList` allocations throughout codebase (L6)**
  Multiple places use `specSet.toList` / `depsMap.toList` where
  direct iteration would avoid intermediate allocation. Minor for
  typical TCBs but could matter for large projects.

- [ ] **`collectProjTypeNames` lacks pointer-based dedup (L7)**
  Unlike `foldConsts` (which uses `PtrSet`), the proj traversal
  has no sharing cache. Could cause exponential traversal on
  heavily-shared expressions. Performance only, not correctness.

## Infrastructure

- [ ] **Add GitHub Actions CI (L8)**
  A workflow running `lake build` and `lake build LeanTcbTest`
  on push/PR would catch regressions.

## API Stability

- [ ] **`standardAxioms` hardcodes three axiom names (L4)**
  `propext`, `Classical.choice`, `Quot.sound` are hardcoded in
  `Format.lean`. Revisit on Lean version bumps.

- [ ] **Attribute name `tcb` could collide (L5)**
  A more namespaced name like `lean_tcb` would be safer, but
  renaming is a breaking change. Defer until a collision actually
  occurs.

## Documentation

- [ ] **`docs/2026-02-21-design.md` review (L11)**
  Internal design document is tracked in git. Decide whether to
  keep, move to a wiki, or remove before 1.0.
