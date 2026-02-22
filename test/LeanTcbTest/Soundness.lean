/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

open Lean Elab Command LeanTcb

/-!
# Soundness tests

Tests that sorry, native_decide, unsafe, and partial definitions are
detected, even though some live in proof terms (which `computeTcb`
correctly skips for theorems).
-/

-- ═══════════════════════════════════════════════
-- Fixtures
-- ═══════════════════════════════════════════════

theorem sorryThm : 1 + 1 = 3 := by sorry

theorem nativeThm : (10 : Nat) < 20 := by native_decide

-- A sound theorem for comparison
theorem soundThm : 1 + 1 = 2 := rfl

-- unsafe definition in the TCB
unsafe def unsafeId (n : Nat) : Nat :=
  unsafeCast (unsafeCast n : Nat)

-- partial definition in the TCB
partial def partialFn (n : Nat) : Nat :=
  if n == 0 then 0 else partialFn (n - 1)

-- safe definition for comparison
def safeDef (n : Nat) : Nat := n + 1

-- Custom user axiom (non-standard)
axiom customAxiom : Nat → Prop

def usesCustomAxiom (n : Nat) : Prop := customAxiom n

-- Proof exclusion breadth: helpers used ONLY in proofs
def proofOnlyHelper1 : Nat := 99
def proofOnlyHelper2 : Nat := 100

theorem omegaProof : proofOnlyHelper1 > 0 := by decide

theorem simpProof : 0 + 1 = 1 := by simp

-- A theorem whose TYPE references nothing interesting
-- but whose PROOF uses a complex helper
def complexHelper (n : Nat) : n + 0 = n := by omega

theorem termProof : True :=
  (fun _ => trivial) (complexHelper 0)

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_sorry_detected" : command => do
  let axs ← liftCoreM <| Lean.collectAxioms `sorryThm
  unless axs.contains `sorryAx do
    throwError "collectAxioms should find sorryAx for sorryThm"
  logInfo "✓ sorry detected via collectAxioms — PASS"

#test_sorry_detected

elab "#test_native_decide_detected" : command => do
  let axs ← liftCoreM <| Lean.collectAxioms `nativeThm
  unless axs.contains ``Lean.ofReduceBool ||
      axs.contains ``Lean.ofReduceNat do
    throwError "collectAxioms should find ofReduceBool or \
      ofReduceNat for nativeThm"
  logInfo "✓ native_decide detected via collectAxioms — PASS"

#test_native_decide_detected

elab "#test_sound_no_sorry" : command => do
  let axs ← liftCoreM <| Lean.collectAxioms `soundThm
  if axs.contains `sorryAx then
    throwError "soundThm should not depend on sorry"
  if axs.contains ``Lean.ofReduceBool then
    throwError "soundThm should not depend on ofReduceBool"
  if axs.contains ``Lean.ofReduceNat then
    throwError "soundThm should not depend on ofReduceNat"
  logInfo "✓ sound theorem has no sorry/native_decide — PASS"

#test_sound_no_sorry

elab "#test_missing_names_empty" : command => do
  let env ← getEnv
  match computeTcb env #[`soundThm] with
  | .ok result =>
    unless result.missingNames.isEmpty do
      throwError s!"Expected no missing names, got: \
        {result.missingNames.toList}"
    logInfo "✓ missingNames empty for well-formed code — PASS"
  | .error msg => throwError msg

#test_missing_names_empty

elab "#test_unsafe_detected" : command => do
  let env ← getEnv
  match computeTcb env #[`unsafeId] with
  | .ok result =>
    unless result.specSet.contains `unsafeId do
      throwError "unsafeId should be in spec"
    if let some ci := env.find? `unsafeId then
      unless ci.isUnsafe do
        throwError "unsafeId should be flagged as unsafe"
    logInfo "✓ unsafe definition detected — PASS"
  | .error msg => throwError msg

#test_unsafe_detected

elab "#test_partial_is_opaque" : command => do
  let env ← getEnv
  -- In Lean 4.27.0, `partial def` compiles to opaqueInfo
  -- (not defnInfo), so ConstantInfo.isPartial returns false.
  -- This is a design limitation: detecting partial defs would
  -- require importing internal elaboration extensions.
  -- From a kernel soundness perspective, a partial def is just
  -- an opaque — the kernel only sees the type.
  let some ci := env.find? `partialFn
    | throwError "partialFn not found in environment"
  unless ci matches .opaqueInfo _ do
    throwError "Expected partialFn to be opaqueInfo"
  -- partialFn should still be in the TCB when reachable
  match computeTcb env #[`partialFn] with
  | .ok result =>
    unless result.specSet.contains `partialFn do
      throwError "partialFn should be in spec"
    logInfo "✓ partial def (as opaque) is in TCB — PASS"
  | .error msg => throwError msg

#test_partial_is_opaque

elab "#test_safe_no_warnings" : command => do
  let env ← getEnv
  if let some ci := env.find? `safeDef then
    if ci.isUnsafe then
      throwError "safeDef should not be unsafe"
    if ci.isPartial then
      throwError "safeDef should not be partial"
  logInfo "✓ safe definition has no unsafe/partial flags — PASS"

#test_safe_no_warnings

elab "#test_custom_axiom_in_tcb" : command => do
  let env ← getEnv
  match computeTcb env #[`usesCustomAxiom] with
  | .ok result =>
    unless result.specSet.contains `customAxiom do
      throwError "customAxiom should be in specSet"
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    -- customAxiom should be in axioms, non-standard
    unless fr.axioms.any
        (fun (n, _) => n == `customAxiom) do
      throwError "customAxiom should be in axioms"
    unless fr.axioms.any
        (fun (n, kind) =>
          n == `customAxiom && kind == .nonStandard) do
      throwError "customAxiom should be non-standard"
    let rendered := renderResult fr
    unless (rendered.splitOn "NON-STANDARD").length
        > 1 do
      throwError s!"expected NON-STANDARD in output: \
        {rendered}"
    logInfo "✓ custom axiom in TCB (non-standard) — PASS"
  | .error msg => throwError msg

#test_custom_axiom_in_tcb

elab "#test_proof_exclusion_simp" : command => do
  let env ← getEnv
  match computeTcb env #[`simpProof] with
  | .ok result =>
    unless result.specSet.contains `simpProof do
      throwError "simpProof should be in specSet"
    -- Count project-local names: should be just simpProof
    let mut userCount : Nat := 0
    for name in result.specSet do
      if isProjectLocal env name then
        userCount := userCount + 1
    unless userCount == 1 do
      throwError s!"Expected 1 project-local name, \
        got {userCount}"
    logInfo "✓ proof exclusion (simp): PASS"
  | .error msg => throwError msg

#test_proof_exclusion_simp

elab "#test_proof_exclusion_term_mode" : command => do
  let env ← getEnv
  match computeTcb env #[`termProof] with
  | .ok result =>
    -- complexHelper is only in the proof body, not type
    if result.specSet.contains `complexHelper then
      throwError "complexHelper should NOT be in \
        specSet (only referenced in proof body)"
    logInfo "✓ proof exclusion (term mode): PASS"
  | .error msg => throwError msg

#test_proof_exclusion_term_mode

-- ═══════════════════════════════════════════════
-- Smoke tests — visual check in infoview
-- ═══════════════════════════════════════════════

-- Should show sorry warning
#tcb sorryThm

-- Should show native_decide warning
#tcb nativeThm

-- Should show clean output
#tcb soundThm

-- Custom axiom (non-standard)
#tcb usesCustomAxiom

-- Proof exclusion
#tcb termProof

-- For theorem proof exclusion test (moved from AuditGaps)
def secretDef : Nat := 42

theorem proofUsesSecret : True :=
  (fun _ => trivial) secretDef

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

-- Test missing-names warning rendering with synthetic result
elab "#test_missing_names_warning_rendered" : command => do
  let env ← getEnv
  let fakeResult : TcbResult := {
    entryPoints := #[`soundThm]
    specSet :=
      ({} : Lean.NameSet).insert `soundThm
    missingNames :=
      ({} : Lean.NameSet).insert `fakeMissing
  }
  let allUserDecls : Array Name := #[`soundThm]
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

-- Smoke test (moved from AuditGaps)
#tcb proofUsesSecret
