/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Type class and instance tests

Tests that type class infrastructure — classes, instances, coercions,
and derived instances — is properly captured in the TCB.
-/

open Lean Elab Command LeanTcb

-- ═══════════════════════════════════════════════
-- Fixtures: basic type class
-- ═══════════════════════════════════════════════

class HasDouble (α : Type) where
  double : α → α

instance : HasDouble Nat where
  double n := n + n

def doubleNat (n : Nat) : Nat := HasDouble.double n

-- ═══════════════════════════════════════════════
-- Fixtures: coercion via structure
-- ═══════════════════════════════════════════════

structure Wrapper where
  inner : Nat

instance : Coe Wrapper Nat where
  coe w := w.inner

def unwrapVal (w : Wrapper) : Nat := (w : Nat)

-- ═══════════════════════════════════════════════
-- Fixtures: deriving
-- ═══════════════════════════════════════════════

inductive Light where
  | on | off
  deriving BEq

def lightsEqual (a b : Light) : Bool := a == b

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_class_in_tcb" : command => do
  let env ← getEnv
  match computeTcb env #[`doubleNat] with
  | .ok result =>
    unless result.specSet.contains `doubleNat do
      throwError "doubleNat should be in spec"
    unless result.specSet.contains `HasDouble do
      throwError "HasDouble class should be in spec"
    unless result.specSet.contains `HasDouble.double do
      throwError "HasDouble.double should be in spec"
    logInfo "✓ class in TCB: PASS"
  | .error msg => throwError msg

#test_class_in_tcb

elab "#test_instance_in_tcb" : command => do
  let env ← getEnv
  match computeTcb env #[`doubleNat] with
  | .ok result =>
    -- The instance is a def: instHasDoubleNat
    -- Check that at least one instance-related name is present
    let hasInstance := result.specSet.toList.any fun n =>
      ((toString n).splitOn "instHasDouble").length > 1
    unless hasInstance do
      throwError "HasDouble Nat instance should be in spec"
    logInfo "✓ instance in TCB: PASS"
  | .error msg => throwError msg

#test_instance_in_tcb

elab "#test_coercion_captured" : command => do
  let env ← getEnv
  match computeTcb env #[`unwrapVal] with
  | .ok result =>
    unless result.specSet.contains `unwrapVal do
      throwError "unwrapVal should be in spec"
    unless result.specSet.contains `Wrapper do
      throwError "Wrapper should be in spec"
    -- Lean inlines the Coe instance body at elaboration time,
    -- so the kernel Expr uses Wrapper.inner directly rather
    -- than referencing instCoeWrapperNat. This is NOT a
    -- soundness gap: the inlined body *is* the actual
    -- dependency, and any change to the instance would change
    -- the inlined Expr. But it means instance names won't
    -- appear in the TCB output — a reporting gap, not a
    -- semantic one.
    unless result.specSet.contains `Wrapper.inner do
      throwError "Wrapper.inner should be in spec \
        (coercion inlined to projection)"
    logInfo "✓ coercion captured: PASS"
  | .error msg => throwError msg

#test_coercion_captured

elab "#test_deriving_deps" : command => do
  let env ← getEnv
  match computeTcb env #[`lightsEqual] with
  | .ok result =>
    unless result.specSet.contains `lightsEqual do
      throwError "lightsEqual should be in spec"
    unless result.specSet.contains `Light do
      throwError "Light should be in spec"
    -- The derived BEq instance should be captured
    let hasBEq := result.specSet.toList.any fun n =>
      ((toString n).splitOn "instBEqLight").length > 1
    unless hasBEq do
      throwError "derived BEq instance should be in spec"
    logInfo "✓ deriving deps: PASS"
  | .error msg => throwError msg

#test_deriving_deps

-- ═══════════════════════════════════════════════
-- Tree / path tests
-- ═══════════════════════════════════════════════

elab "#test_tree_instance_path" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`doubleNat] with
  | .ok graph =>
    let output := renderTree env graph
    -- Tree should include HasDouble and the instance
    unless (output.splitOn "HasDouble").length > 1 do
      throwError s!"expected HasDouble in tree: {output}"
    unless (output.splitOn "instHasDouble").length > 1 do
      throwError s!"expected instance in tree: {output}"
    logInfo "✓ tree instance path: PASS"
  | .error msg => throwError msg

#test_tree_instance_path

elab "#test_why_class_method" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`doubleNat] with
  | .ok graph =>
    let output := renderPath env graph
      `doubleNat `HasDouble.double
    unless (output.splitOn "TCB Path").length > 1 do
      throwError s!"expected TCB Path header: {output}"
    unless (output.splitOn "HasDouble.double").length > 1 do
      throwError s!"expected target in path: {output}"
    logInfo "✓ why class method: PASS"
  | .error msg => throwError msg

#test_why_class_method

-- ═══════════════════════════════════════════════
-- Smoke tests
-- ═══════════════════════════════════════════════

#tcb doubleNat
#tcb unwrapVal
#tcb lightsEqual
#tcb_tree doubleNat
#tcb_why doubleNat HasDouble
