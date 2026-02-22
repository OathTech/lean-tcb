/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

open Lean Elab Command LeanTcb

/-!
# Path query tests

Tests for `findPath` and `#tcb_why` using the same fixture development
as EndToEnd (myDvd → hasNontrivialDivisor → myPrime → two_is_prime).
-/

-- ═══════════════════════════════════════════════
-- Fixtures
-- ═══════════════════════════════════════════════

def pathDvd (a b : Nat) : Prop := ∃ k, b = a * k

def pathHasNontrivDivisor (n : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d < n ∧ pathDvd d n

def pathPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬ pathHasNontrivDivisor n

theorem pathTwoIsPrime : pathPrime 2 := by
  constructor
  · omega
  · intro ⟨d, hle, hlt, ⟨k, hk⟩⟩; omega

-- A helper lemma used only in proofs — not in TCB
theorem pathDvdRefl (n : Nat) : pathDvd n n := ⟨1, by omega⟩

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_path_direct_dep" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    -- pathPrime is a direct dependency of pathTwoIsPrime
    match findPath graph `pathPrime with
    | some path =>
      -- Path should be: pathTwoIsPrime → pathPrime (length 2)
      unless path.size == 2 do
        throwError s!"expected path length 2, got {path.size}"
      unless path[0]!.1 == `pathTwoIsPrime do
        throwError "path should start with pathTwoIsPrime"
      unless path[1]!.1 == `pathPrime do
        throwError "path should end with pathPrime"
      logInfo "✓ path direct dependency: PASS"
    | none => throwError "expected a path to pathPrime"
  | .error msg => throwError msg

#test_path_direct_dep

elab "#test_path_transitive" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    -- pathDvd is a transitive dependency through the chain
    match findPath graph `pathDvd with
    | some path =>
      -- Path should go through multiple steps
      unless path.size ≥ 3 do
        throwError s!"expected path length ≥ 3, got {path.size}"
      unless path[0]!.1 == `pathTwoIsPrime do
        throwError "path should start with pathTwoIsPrime"
      unless path[path.size - 1]!.1 == `pathDvd do
        throwError "path should end with pathDvd"
      logInfo
        s!"✓ path transitive (length {path.size}): PASS"
    | none => throwError "expected a path to pathDvd"
  | .error msg => throwError msg

#test_path_transitive

elab "#test_path_entry_point" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    -- Entry point itself should return a path of length 1
    match findPath graph `pathTwoIsPrime with
    | some path =>
      unless path.size == 1 do
        throwError s!"expected path length 1, got {path.size}"
      unless path[0]!.1 == `pathTwoIsPrime do
        throwError "single-element path should be the entry point"
      unless path[0]!.2.isNone do
        throwError "entry point should have no reason"
      logInfo "✓ path entry point is self: PASS"
    | none =>
      throwError "expected a path for entry point itself"
  | .error msg => throwError msg

#test_path_entry_point

elab "#test_path_not_in_tcb" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    -- pathDvdRefl is a helper lemma, not in TCB
    match findPath graph `pathDvdRefl with
    | none =>
      logInfo "✓ path not in TCB returns none: PASS"
    | some _ =>
      throwError "pathDvdRefl should NOT be in the TCB"
  | .error msg => throwError msg

#test_path_not_in_tcb

elab "#test_path_render" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    let output := renderPath env graph
      `pathTwoIsPrime `pathPrime
    unless (output.splitOn "TCB Path").length > 1 do
      throwError s!"expected header in output: {output}"
    unless (output.splitOn "pathTwoIsPrime").length > 1 do
      throwError "expected entry point in output"
    unless (output.splitOn "pathPrime").length > 1 do
      throwError "expected target in output"
    logInfo "✓ path render: PASS"
  | .error msg => throwError msg

#test_path_render

elab "#test_path_render_not_in_tcb" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    let output := renderPath env graph
      `pathTwoIsPrime `pathDvdRefl
    unless (output.splitOn "not in the TCB").length > 1 do
      throwError s!"expected 'not in the TCB' message: {output}"
    logInfo "✓ path render not in TCB: PASS"
  | .error msg => throwError msg

#test_path_render_not_in_tcb

elab "#test_path_render_entry_point" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    let output := renderPath env graph
      `pathTwoIsPrime `pathTwoIsPrime
    unless (output.splitOn "entry point").length > 1 do
      throwError
        s!"expected 'entry point' message: {output}"
    logInfo "✓ path render entry point: PASS"
  | .error msg => throwError msg

#test_path_render_entry_point

-- ═══════════════════════════════════════════════
-- Type vs body reason distinction in path
-- ═══════════════════════════════════════════════

elab "#test_path_type_vs_body_reason" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`pathTwoIsPrime] with
  | .ok graph =>
    -- Path to pathHasNontrivDivisor goes through
    -- pathPrime (type ref) then pathHasNontrivDivisor
    -- (body ref)
    let output := renderPath env graph
      `pathTwoIsPrime `pathHasNontrivDivisor
    unless (output.splitOn "referenced in type").length
        > 1 do
      throwError s!"expected 'referenced in type' \
        for pathPrime in path: {output}"
    unless (output.splitOn "referenced in body").length
        > 1 do
      throwError s!"expected 'referenced in body' \
        for pathHasNontrivDivisor in path: {output}"
    logInfo "✓ path type vs body reason: PASS"
  | .error msg => throwError msg

#test_path_type_vs_body_reason

-- ═══════════════════════════════════════════════
-- Smoke test: #tcb_why command
-- ═══════════════════════════════════════════════

#tcb_why pathTwoIsPrime pathDvd
#tcb_why pathTwoIsPrime pathPrime
