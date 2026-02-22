/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Adversarial tests

Probes specific code paths with tricky Lean features: nested
projections, pattern matching auxiliaries, well-founded recursion,
decidable instances, noncomputable defs, and where-clause helpers.
-/

open Lean Elab Command LeanTcb

-- ═══════════════════════════════════════════════
-- Fixtures: nested Expr.proj
-- ═══════════════════════════════════════════════

structure Inner where
  val : Nat

structure Outer where
  inner : Inner

def getNestedVal (o : Outer) : Nat := o.inner.val

-- ═══════════════════════════════════════════════
-- Fixtures: pattern matching on custom inductive
-- ═══════════════════════════════════════════════

inductive Shape where
  | circle : Nat → Shape
  | rect : Nat → Nat → Shape
  | triangle : Nat → Nat → Nat → Shape

def shapeSize : Shape → Nat
  | .circle r => r
  | .rect w h => w * h
  | .triangle a b c => a + b + c

-- ═══════════════════════════════════════════════
-- Fixtures: well-founded recursion
-- ═══════════════════════════════════════════════

def wfDiv (n m : Nat) : Nat :=
  if m = 0 then 0
  else if n < m then 0
  else 1 + wfDiv (n - m) m
termination_by n

-- ═══════════════════════════════════════════════
-- Fixtures: if-then-else with Decidable
-- ═══════════════════════════════════════════════

def filterPos (xs : List Nat) : List Nat :=
  xs.filter fun n => n > 0

-- ═══════════════════════════════════════════════
-- Fixtures: noncomputable
-- ═══════════════════════════════════════════════

noncomputable def chooseNat : Nat :=
  Classical.choice ⟨0⟩

-- ═══════════════════════════════════════════════
-- Fixtures: where clause helper
-- ═══════════════════════════════════════════════

def sumWithHelper (xs : List Nat) : Nat :=
  go xs 0
where
  go : List Nat → Nat → Nat
    | [], acc => acc
    | x :: rest, acc => go rest (acc + x)

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_nested_proj" : command => do
  let env ← getEnv
  match computeTcb env #[`getNestedVal] with
  | .ok result =>
    unless result.specSet.contains `getNestedVal do
      throwError "getNestedVal should be in spec"
    unless result.specSet.contains `Outer do
      throwError "Outer should be in spec (via Expr.proj)"
    unless result.specSet.contains `Inner do
      throwError "Inner should be in spec (via nested Expr.proj)"
    logInfo "✓ nested proj: PASS"
  | .error msg => throwError msg

#test_nested_proj

elab "#test_match_deps" : command => do
  let env ← getEnv
  match computeTcb env #[`shapeSize] with
  | .ok result =>
    unless result.specSet.contains `shapeSize do
      throwError "shapeSize should be in spec"
    unless result.specSet.contains `Shape do
      throwError "Shape should be in spec"
    unless result.specSet.contains `Shape.circle do
      throwError "Shape.circle should be in spec"
    unless result.specSet.contains `Shape.rect do
      throwError "Shape.rect should be in spec"
    unless result.specSet.contains `Shape.triangle do
      throwError "Shape.triangle should be in spec"
    logInfo "✓ match deps: PASS"
  | .error msg => throwError msg

#test_match_deps

elab "#test_wf_recursion" : command => do
  let env ← getEnv
  match computeTcb env #[`wfDiv] with
  | .ok result =>
    unless result.specSet.contains `wfDiv do
      throwError "wfDiv should be in spec"
    unless result.missingNames.isEmpty do
      throwError s!"Expected no missing names, got: \
        {result.missingNames.toList}"
    logInfo "✓ wf recursion: PASS"
  | .error msg => throwError msg

#test_wf_recursion

elab "#test_ite_decidable" : command => do
  let env ← getEnv
  match computeTcb env #[`filterPos] with
  | .ok result =>
    unless result.specSet.contains `filterPos do
      throwError "filterPos should be in spec"
    -- The def body should reference List.filter at minimum
    let hasFilter := result.specSet.toList.any fun n =>
      ((toString n).splitOn "filter").length > 1
    unless hasFilter do
      throwError "filterPos TCB should include filter-related names"
    logInfo "✓ ite decidable: PASS"
  | .error msg => throwError msg

#test_ite_decidable

elab "#test_noncomputable" : command => do
  let env ← getEnv
  match computeTcb env #[`chooseNat] with
  | .ok result =>
    unless result.specSet.contains `chooseNat do
      throwError "chooseNat should be in spec"
    unless result.specSet.contains `Classical.choice do
      throwError "Classical.choice should be in spec"
    logInfo "✓ noncomputable: PASS"
  | .error msg => throwError msg

#test_noncomputable

elab "#test_where_helper" : command => do
  let env ← getEnv
  match computeTcb env #[`sumWithHelper] with
  | .ok result =>
    unless result.specSet.contains `sumWithHelper do
      throwError "sumWithHelper should be in spec"
    -- where clause elaborates to sumWithHelper.go
    unless result.specSet.contains `sumWithHelper.go do
      throwError "sumWithHelper.go should be in spec"
    logInfo "✓ where helper: PASS"
  | .error msg => throwError msg

#test_where_helper

-- ═══════════════════════════════════════════════
-- Tree / path tests
-- ═══════════════════════════════════════════════

elab "#test_tree_nested_proj_both" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`getNestedVal] with
  | .ok graph =>
    let output := renderTree env graph
    unless (output.splitOn "Outer").length > 1 do
      throwError s!"expected Outer in tree: {output}"
    unless (output.splitOn "Inner").length > 1 do
      throwError s!"expected Inner in tree: {output}"
    logInfo "✓ tree nested proj both: PASS"
  | .error msg => throwError msg

#test_tree_nested_proj_both

elab "#test_why_where_helper" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`sumWithHelper] with
  | .ok graph =>
    let output := renderPath env graph
      `sumWithHelper `sumWithHelper.go
    unless (output.splitOn "TCB Path").length > 1 do
      throwError s!"expected TCB Path header: {output}"
    unless (output.splitOn "sumWithHelper.go").length > 1 do
      throwError s!"expected target in path: {output}"
    logInfo "✓ why where helper: PASS"
  | .error msg => throwError msg

#test_why_where_helper

elab "#test_why_classical_choice" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`chooseNat] with
  | .ok graph =>
    let output := renderPath env graph
      `chooseNat `Classical.choice
    unless (output.splitOn "TCB Path").length > 1 do
      throwError s!"expected TCB Path header: {output}"
    unless (output.splitOn "Classical.choice").length > 1 do
      throwError s!"expected target in path: {output}"
    logInfo "✓ why classical choice: PASS"
  | .error msg => throwError msg

#test_why_classical_choice

-- ═══════════════════════════════════════════════
-- Smoke tests
-- ═══════════════════════════════════════════════

#tcb getNestedVal
#tcb shapeSize
#tcb wfDiv
#tcb chooseNat
#tcb sumWithHelper
#tcb_tree getNestedVal
#tcb_tree sumWithHelper
#tcb_why sumWithHelper sumWithHelper.go
#tcb_why chooseNat Classical.choice
