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

-- computeTcbGraph error path for unknown entry point
elab "#test_graph_unknown_entry_point" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`nonexistent_graph_xyz] with
  | .ok _ =>
    throwError "Should have failed for unknown name"
  | .error msg =>
    unless (msg.splitOn "not found").length > 1 do
      throwError s!"Expected 'not found' in error, \
        got: {msg}"
    logInfo "✓ graph unknown entry point: PASS"

#test_graph_unknown_entry_point

-- Entry points formatted as comma-separated list
elab "#test_entry_point_format" : command => do
  let env ← getEnv
  match computeTcb env #[`myPred, `myDouble] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let output := renderResult fr
    -- Should NOT contain #[ (old array format)
    if (output.splitOn "#[").length > 1 then
      throwError "Entry points should not use #[] format"
    -- Should contain comma separator
    unless (output.splitOn ", ").length > 1 do
      throwError "Expected comma-separated entry points"
    logInfo "✓ entry point format: PASS"
  | .error msg => throwError msg

#test_entry_point_format

-- Package info should be available in normal Lake builds
elab "#test_package_info_available" : command => do
  let env ← getEnv
  unless env.getModulePackage?.isSome do
    throwError "getModulePackage? should be some in Lake"
  logInfo "✓ package info available: PASS"

#test_package_info_available

-- Verbose output includes full library dependency listing
elab "#test_verbose_library_listing" : command => do
  let env ← getEnv
  match computeTcb env #[`myDouble_pos] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    -- Verbose should include "Library Dependencies" section
    let verbose := renderResult fr true
    unless (verbose.splitOn "Library Dependencies").length
        > 1 do
      throwError "verbose output should include Library \
        Dependencies section"
    -- Non-verbose should NOT include it
    let brief := renderResult fr false
    if (brief.splitOn "Library Dependencies").length
        > 1 then
      throwError "non-verbose output should not include \
        Library Dependencies section"
    logInfo "✓ verbose library listing: PASS"
  | .error msg => throwError msg

#test_verbose_library_listing

-- Graph parentMap/specSet consistency invariants
elab "#test_graph_invariants" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`myDouble_pos] with
  | .ok graph =>
    let entrySet := graph.entryPoints.foldl
      (fun acc n => acc.insert n) ({} : Lean.NameSet)
    -- Every non-entry in specSet has a parentMap entry
    for name in graph.specSet do
      unless entrySet.contains name do
        unless graph.parentMap.contains name do
          throwError s!"{name} in specSet but not in \
            parentMap and not an entry point"
    -- Every parentMap key is in specSet
    for (name, _) in graph.parentMap do
      unless graph.specSet.contains name do
        throwError s!"{name} in parentMap but not in \
          specSet"
    logInfo "✓ graph invariants: PASS"
  | .error msg => throwError msg

#test_graph_invariants

-- Graph depsMap is populated for non-leaf nodes
elab "#test_graph_depsmap_populated" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`myDouble_pos] with
  | .ok graph =>
    -- At least some nodes should have depsMap entries
    let mut hasDeps := false
    for (_, arr) in graph.depsMap do
      if arr.size > 0 then
        hasDeps := true
    unless hasDeps do
      throwError "depsMap should have non-empty entries"
    logInfo "✓ graph depsMap populated: PASS"
  | .error msg => throwError msg

#test_graph_depsmap_populated
