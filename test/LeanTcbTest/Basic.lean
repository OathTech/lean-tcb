/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Basic TCB tests

Tests for core reachability, def body walking, multiple entry points,
unknown entry point handling, and user vs library classification.
-/

open Lean Elab Command LeanTcb

-- ═══════════════════════════════════════════════
-- Test fixtures: a small development to classify
-- ═══════════════════════════════════════════════

def myPred (n : Nat) : Prop := n > 0

theorem myPred_succ (n : Nat) : myPred (n + 1) := by
  unfold myPred
  omega

def myDouble (n : Nat) : Nat := n + n

theorem myDouble_pos (n : Nat) (h : myPred n) : myPred (myDouble n) := by
  unfold myPred at *
  unfold myDouble
  omega

-- Helper lemma used only in proofs — should be proof infrastructure
theorem helper_lemma (a b : Nat) : a + b = b + a := Nat.add_comm a b

-- ═══════════════════════════════════════════════
-- Tests via command elaboration
-- ═══════════════════════════════════════════════

elab "#test_basic_reachability" : command => do
  let env ← getEnv
  match computeTcb env #[`myPred_succ] with
  | .ok result =>
    -- myPred_succ itself must be in spec
    unless result.specSet.contains `myPred_succ do
      throwError "myPred_succ should be in spec"
    -- myPred (used in the type) must be in spec
    unless result.specSet.contains `myPred do
      throwError "myPred should be in spec"
    -- myDouble should NOT be in spec (not reachable from myPred_succ)
    if result.specSet.contains `myDouble then
      throwError "myDouble should NOT be in spec"
    -- helper_lemma should NOT be in spec
    if result.specSet.contains `helper_lemma then
      throwError "helper_lemma should NOT be in spec"
    logInfo "✓ basic reachability: PASS"
  | .error msg => throwError msg

#test_basic_reachability

elab "#test_def_body_walking" : command => do
  let env ← getEnv
  match computeTcb env #[`myDouble_pos] with
  | .ok result =>
    unless result.specSet.contains `myDouble_pos do
      throwError "myDouble_pos should be in spec"
    unless result.specSet.contains `myPred do
      throwError "myPred should be in spec"
    unless result.specSet.contains `myDouble do
      throwError "myDouble should be in spec"
    logInfo "✓ def body walking: PASS"
  | .error msg => throwError msg

#test_def_body_walking

elab "#test_multiple_entry_points" : command => do
  let env ← getEnv
  match computeTcb env #[`myPred_succ, `myDouble_pos] with
  | .ok result =>
    unless result.specSet.contains `myPred_succ do
      throwError "myPred_succ should be in spec"
    unless result.specSet.contains `myDouble_pos do
      throwError "myDouble_pos should be in spec"
    unless result.specSet.contains `myPred do
      throwError "myPred should be in spec"
    unless result.specSet.contains `myDouble do
      throwError "myDouble should be in spec"
    logInfo "✓ multiple entry points: PASS"
  | .error msg => throwError msg

#test_multiple_entry_points

elab "#test_unknown_entry_point" : command => do
  let env ← getEnv
  match computeTcb env #[`nonexistent_name_xyz] with
  | .ok _ => throwError "Should have failed for unknown name"
  | .error msg =>
    unless (msg.splitOn "not found").length > 1 do
      throwError s!"Expected 'not found' in error, got: {msg}"
    logInfo "✓ unknown entry point: PASS"

#test_unknown_entry_point

elab "#test_user_vs_library" : command => do
  let env ← getEnv
  match computeTcb env #[`myDouble_pos] with
  | .ok result =>
    let allUserDecls := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    -- myDouble and myPred should be in userSpec (defined in this module)
    unless fr.userSpec.any (·.1 == `myDouble) do
      throwError "myDouble should be in userSpec"
    unless fr.userSpec.any (·.1 == `myPred) do
      throwError "myPred should be in userSpec"
    -- Nat should be in librarySpec (imported)
    unless fr.librarySpec.contains `Nat do
      throwError "Nat should be in librarySpec"
    logInfo "✓ user vs library classification: PASS"
  | .error msg => throwError msg

#test_user_vs_library

-- ═══════════════════════════════════════════════
-- Smoke test: #tcb command (visual check in infoview)
-- ═══════════════════════════════════════════════

#tcb myDouble_pos
