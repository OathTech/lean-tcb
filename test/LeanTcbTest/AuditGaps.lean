/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Audit gap tests

Tests that close specific coverage gaps identified during the
2026-02-21 release readiness audit. Covers: theorem proof body
exclusion, opaque body exclusion, `computeTcbGraph` error path,
`Expr.proj` in binder positions, mutual partial companions,
entry point formatting, library grammar, annotation hierarchy,
and missing-names warning rendering.
-/

open Lean Elab Command LeanTcb

set_option tcb.checkAnnotations true

-- ═══════════════════════════════════════════════
-- Fixtures
-- ═══════════════════════════════════════════════

-- For theorem proof exclusion test
def secretDef : Nat := 42

theorem proofUsesSecret : True :=
  (fun _ => trivial) secretDef

-- For opaque body exclusion test
def opaqueHelper : Nat := 99

opaque opaqueWithBody : Nat := opaqueHelper + 1

-- For proj-in-let test
structure LetProjStruct where
  val : Nat

def projInLet (s : LetProjStruct) : Nat :=
  let v := s.val
  v + 1

-- For mutual partial companions test
mutual
  partial def mpEven : Nat → Bool
    | 0 => true
    | n + 1 => mpOdd n
  partial def mpOdd : Nat → Bool
    | 0 => false
    | n + 1 => mpEven n
end

-- For annotation hierarchy test
inductive AuditColor where | red | green

@[tcb] inductive AuditColor2 where | x | y

def useAuditColor : AuditColor → Nat
  | .red => 0 | .green => 1

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

-- Theorem proof body should NOT be walked
elab "#test_theorem_proof_exclusion" : command => do
  let env ← getEnv
  match computeTcb env #[`proofUsesSecret] with
  | .ok result =>
    if result.specSet.contains `secretDef then
      throwError "secretDef should NOT be in TCB \
        (only referenced in proof body)"
    logInfo "✓ theorem proof body excluded: PASS"
  | .error msg => throwError msg

#test_theorem_proof_exclusion

-- Opaque body should NOT be walked
elab "#test_opaque_body_excluded" : command => do
  let env ← getEnv
  match computeTcb env #[`opaqueWithBody] with
  | .ok result =>
    unless result.specSet.contains `opaqueWithBody do
      throwError "opaqueWithBody should be in spec"
    if result.specSet.contains `opaqueHelper then
      throwError "opaqueHelper should NOT be in spec \
        (opaque body not walked)"
    logInfo "✓ opaque body exclusion: PASS"
  | .error msg => throwError msg

#test_opaque_body_excluded

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

-- Expr.proj inside let-binding
elab "#test_proj_in_let" : command => do
  let env ← getEnv
  match computeTcb env #[`projInLet] with
  | .ok result =>
    unless result.specSet.contains `LetProjStruct do
      throwError "LetProjStruct should be in spec \
        (proj in let-binding)"
    logInfo "✓ proj in let-binding: PASS"
  | .error msg => throwError msg

#test_proj_in_let

-- Mutual partial def companions (opaqueInfo branch)
elab "#test_mutual_partial_companions" : command => do
  let env ← getEnv
  match computeTcb env #[`mpEven] with
  | .ok result =>
    unless result.specSet.contains `mpEven do
      throwError "mpEven should be in spec"
    unless result.specSet.contains `mpOdd do
      throwError "mpOdd should be in spec \
        (mutual companion via opaqueInfo)"
    logInfo "✓ mutual partial companions: PASS"
  | .error msg => throwError msg

#test_mutual_partial_companions

-- Entry points formatted as comma-separated list
elab "#test_entry_point_format" : command => do
  let env ← getEnv
  match computeTcb env #[`secretDef, `opaqueHelper] with
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

-- Singular "library dependency" grammar
elab "#test_library_singular_grammar" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`secretDef] with
  | .ok graph =>
    let output := renderTree env graph
    -- Should never have "1 library dependencies" (plural)
    if (output.splitOn "1 library dependencies").length
        > 1 then
      throwError "Should use singular 'dependency'"
    logInfo "✓ library grammar: PASS"
  | .error msg => throwError msg

#test_library_singular_grammar

-- @[tcb] on unused inductive should be unnecessary
elab "#test_annotation_unnecessary" : command => do
  let env ← getEnv
  match computeTcb env #[`useAuditColor] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let userSpecNames :=
      (formatResult env result allUserDecls).userSpec.map
        (·.1)
    let ac :=
      checkAnnotations env userSpecNames allUserDecls
    -- AuditColor2 is annotated but not in the TCB
    unless ac.unnecessary.contains `AuditColor2 do
      throwError "AuditColor2 should be unnecessary"
    logInfo "✓ annotation unnecessary: PASS"
  | .error msg => throwError msg

#test_annotation_unnecessary

-- Test missing-names warning rendering with synthetic result
-- (warnings are now added by emitSoundnessWarnings, so we
-- manually add them here to test the rendering path)
elab "#test_missing_names_warning_rendered" : command => do
  let env ← getEnv
  let fakeResult : TcbResult := {
    entryPoints := #[`secretDef]
    specSet :=
      ({} : Lean.NameSet).insert `secretDef
    missingNames :=
      ({} : Lean.NameSet).insert `fakeMissing
  }
  let allUserDecls : Array Name := #[`secretDef]
  let mut fr := formatResult env fakeResult allUserDecls
  -- Simulate what emitSoundnessWarnings would add
  fr := { fr with warnings := #[
    "'fakeMissing' was referenced but not found — \
      transitive dependencies unknown"
  ] }
  unless fr.warnings.size > 0 do
    throwError "Expected warnings for missing names"
  let output := renderResult fr
  unless (output.splitOn "fakeMissing").length > 1 do
    throwError "Expected fakeMissing in rendered output"
  unless (output.splitOn "Warnings").length > 1 do
    throwError "Expected Warnings section"
  logInfo "✓ missing names warning rendered: PASS"

#test_missing_names_warning_rendered

-- Annotation warnings include corrective action hints
elab "#test_annotation_action_hints" : command => do
  let env ← getEnv
  match computeTcb env #[`useAuditColor] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let userSpecNames := fr.userSpec.map (·.1)
    let ac :=
      checkAnnotations env userSpecNames allUserDecls
    let output := renderResult fr false (some ac)
    -- Check for corrective action hints
    if ac.unannotated.size > 0 then
      unless (output.splitOn "consider adding").length
          > 1 do
        throwError "Expected 'consider adding @[tcb]' hint"
    if ac.unnecessary.size > 0 then
      unless (output.splitOn "for these entry points").length
          > 1 do
        throwError "Expected 'for these entry points' caveat"
    logInfo "✓ annotation action hints: PASS"
  | .error msg => throwError msg

#test_annotation_action_hints

-- Package info should be available in normal Lake builds
elab "#test_package_info_available" : command => do
  let env ← getEnv
  unless env.getModulePackage?.isSome do
    throwError "getModulePackage? should be some in Lake"
  logInfo "✓ package info available: PASS"

#test_package_info_available

-- Library entry point should show hint
elab "#test_library_entry_point_hint" : command => do
  let env ← getEnv
  match computeTcb env #[`Nat.add] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let output := renderResult fr
    unless (output.splitOn
        "library declarations").length > 1 do
      throwError s!"expected library hint in output: \
        {output}"
    logInfo "✓ library entry point hint: PASS"
  | .error msg => throwError msg

#test_library_entry_point_hint

-- Auto-generated declarations should not inflate percentage
elab "#test_auto_generated_filtering" : command => do
  let env ← getEnv
  -- useAuditColor references AuditColor which generates
  -- .rec, .casesOn, etc. The percentage should use filtered
  -- counts that exclude these auto-generated companions.
  match computeTcb env #[`useAuditColor] with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    -- humanSpecCount should be less than or equal to
    -- the full userSpec count (auto-generated filtered out)
    unless fr.humanSpecCount ≤ fr.userSpec.size do
      throwError "humanSpecCount should not exceed \
        userSpec.size"
    -- humanNotInTcb should be less than or equal to
    -- userNotInTcb (auto-generated filtered out)
    unless fr.humanNotInTcb ≤ fr.userNotInTcb do
      throwError "humanNotInTcb should not exceed \
        userNotInTcb"
    logInfo "✓ auto-generated filtering: PASS"
  | .error msg => throwError msg

#test_auto_generated_filtering

-- ═══════════════════════════════════════════════
-- Smoke tests
-- ═══════════════════════════════════════════════

#tcb proofUsesSecret
#tcb opaqueWithBody
#tcb projInLet
#tcb mpEven
#tcb useAuditColor
#tcb_tree projInLet
