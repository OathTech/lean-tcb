/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

open Lean Elab Command LeanTcb

set_option tcb.checkAnnotations true

/-!
# Tests for `@[tcb]` annotation checking

Tests that the annotation cross-check correctly identifies:
- Unannotated TCB members (in spec but no `@[tcb]`)
- Unnecessary annotations (`@[tcb]` but not in spec)
- Correct annotations (everything matches)
- Parent coverage (annotating an inductive covers its constructors)
-/

-- ═══════════════════════════════════════════════
-- Fixtures
-- ═══════════════════════════════════════════════

@[tcb] def annDvd (a b : Nat) : Prop := ∃ k, b = a * k

@[tcb] def annPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬ ∃ d, 2 ≤ d ∧ d < n ∧ annDvd d n

-- Deliberately NOT annotated — should trigger a warning
def annHelper (n : Nat) : Nat := n + 1

-- A theorem whose type mentions annHelper (so annHelper is in TCB)
@[tcb] theorem annThm : annHelper 0 = 1 := rfl

-- A helper lemma only used in proofs
theorem annProofHelper : annDvd 1 1 := ⟨1, by omega⟩

-- Annotated but NOT reachable from any entry point we'll test
@[tcb] def annUnused (n : Nat) : Nat := n * 2

-- An annotated inductive — should cover its constructors
@[tcb] inductive AnnColor where
  | red | green | blue

@[tcb] def annColorName : AnnColor → String
  | .red => "red"
  | .green => "green"
  | .blue => "blue"

@[tcb] theorem annColorThm : annColorName AnnColor.red = "red" := rfl

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_ann_unannotated" : command => do
  let env ← getEnv
  match computeTcb env #[`annThm] with
  | .ok result =>
    let allUserDecls := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let userSpecNames := fr.userSpec.map (·.1)
    let ac := checkAnnotations env userSpecNames allUserDecls
    unless ac.hasAnnotations do
      throwError "Should detect annotations"
    -- annHelper is in TCB (used in annThm's type) but not annotated
    unless ac.unannotated.any (· == `annHelper) do
      throwError "annHelper should be flagged as unannotated"
    -- annThm is annotated and in TCB — should NOT be unannotated
    if ac.unannotated.any (· == `annThm) then
      throwError "annThm should not be unannotated"
    logInfo "✓ unannotated detection: PASS"
  | .error msg => throwError msg

#test_ann_unannotated

elab "#test_ann_unnecessary" : command => do
  let env ← getEnv
  -- annPrime's TCB: only annThm's entry point won't include annUnused or annPrime
  match computeTcb env #[`annThm] with
  | .ok result =>
    let allUserDecls := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let userSpecNames := fr.userSpec.map (·.1)
    let ac := checkAnnotations env userSpecNames allUserDecls
    -- annUnused is annotated but not in TCB for this entry point
    unless ac.unnecessary.any (· == `annUnused) do
      throwError "annUnused should be flagged as unnecessary"
    -- annPrime is annotated but not reachable from annThm
    unless ac.unnecessary.any (· == `annPrime) do
      throwError "annPrime should be flagged as unnecessary"
    logInfo "✓ unnecessary annotation detection: PASS"
  | .error msg => throwError msg

#test_ann_unnecessary

elab "#test_ann_inductive_coverage" : command => do
  let env ← getEnv
  match computeTcb env #[`annColorThm] with
  | .ok result =>
    let allUserDecls := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let userSpecNames := fr.userSpec.map (·.1)
    let ac := checkAnnotations env userSpecNames allUserDecls
    -- AnnColor.red, AnnColor.green etc. should be covered by @[tcb] on AnnColor
    for ctor in #[`AnnColor.red, `AnnColor.green, `AnnColor.blue] do
      if ac.unannotated.any (· == ctor) then
        throwError s!"{ctor} should be covered by @[tcb] on AnnColor"
    -- Auto-generated like AnnColor.rec, AnnColor.casesOn should also be covered
    for aux in #[`AnnColor.rec, `AnnColor.casesOn] do
      if ac.unannotated.any (· == aux) then
        throwError s!"{aux} should be covered by @[tcb] on AnnColor"
    logInfo "✓ inductive parent coverage: PASS"
  | .error msg => throwError msg

#test_ann_inductive_coverage

-- M8: .num branch in isTcbAnnotated
elab "#test_num_branch_coverage" : command => do
  let env ← getEnv
  -- Construct a synthetic .num name under @[tcb] annDvd
  let numName := Name.num `annDvd 42
  unless isTcbAnnotated env numName do
    throwError "isTcbAnnotated should cover .num children \
      of @[tcb] names"
  -- Negative: .num under non-annotated name
  if isTcbAnnotated env (Name.num `annHelper 1) then
    throwError "should NOT cover .num under non-annotated"
  logInfo "✓ .num branch coverage: PASS"

#test_num_branch_coverage

-- ═══════════════════════════════════════════════
-- Additional fixtures
-- ═══════════════════════════════════════════════

-- Mid-hierarchy annotation: annotate a def, check
-- its auto-generated children are covered
@[tcb] def annMidLevel (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => k

-- ═══════════════════════════════════════════════
-- Additional tests
-- ═══════════════════════════════════════════════

elab "#test_ann_mid_hierarchy_coverage" : command => do
  let env ← getEnv
  match computeTcb env #[`annMidLevel] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let userSpecNames := fr.userSpec.map (·.1)
    let ac := checkAnnotations env userSpecNames
      allUserDecls
    -- Auto-generated children (annMidLevel.*) in the
    -- TCB should be covered by @[tcb] on annMidLevel
    for name in userSpecNames do
      if name.getPrefix == `annMidLevel then
        if ac.unannotated.any (· == name) then
          throwError s!"{name} should be covered by \
            @[tcb] on annMidLevel"
    logInfo "✓ mid-hierarchy annotation coverage: PASS"
  | .error msg => throwError msg

#test_ann_mid_hierarchy_coverage

-- ═══════════════════════════════════════════════
-- Smoke tests — visual check in infoview
-- ═══════════════════════════════════════════════

-- This should show warnings for annHelper (unannotated) and annUnused/annPrime (unnecessary)
#tcb annThm

-- This should show clean annotations (everything matched)
#tcb annColorThm

-- Mid-hierarchy annotation
#tcb annMidLevel
