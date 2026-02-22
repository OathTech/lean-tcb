/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
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

-- ═══════════════════════════════════════════════
-- Smoke tests — visual check in infoview
-- ═══════════════════════════════════════════════

-- Should show sorry warning
#tcb sorryThm

-- Should show native_decide warning
#tcb nativeThm

-- Should show clean output
#tcb soundThm
