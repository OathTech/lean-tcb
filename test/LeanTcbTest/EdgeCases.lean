/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Edge case tests

Tests for abbrev, opaque, inductive, structure, and Expr.proj handling.
-/

open Lean Elab Command LeanTcb

-- ═══════════════════════════════════════════════
-- Edge case fixtures
-- ═══════════════════════════════════════════════

-- abbrev: should walk body (it's a def with ReducibilityHints.abbrev)
abbrev MyNat := Nat

def myAbbrevFn (n : MyNat) : MyNat := n + 1

theorem myAbbrevThm : myAbbrevFn 0 = 1 := rfl

-- opaque: should NOT walk body
opaque opaqueVal : Nat := 42

theorem opaqueThm : opaqueVal = opaqueVal := rfl

-- inductive: constructor types should be walked
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def myLength {α : Type} : MyList α → Nat
  | .nil => 0
  | .cons _ xs => 1 + myLength xs

theorem myLength_nil : myLength (MyList.nil (α := Nat)) = 0 := rfl

-- structure
structure MyPair (α β : Type) where
  fst : α
  snd : β

def mkPair {α β : Type} (a : α) (b : β) : MyPair α β := ⟨a, b⟩

theorem mkPair_fst {α β : Type} (a : α) (b : β) : (mkPair a b).fst = a := rfl

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_abbrev" : command => do
  let env ← getEnv
  match computeTcb env #[`myAbbrevThm] with
  | .ok result =>
    unless result.specSet.contains `myAbbrevThm do
      throwError "myAbbrevThm should be in spec"
    unless result.specSet.contains `myAbbrevFn do
      throwError "myAbbrevFn should be in spec"
    unless result.specSet.contains `MyNat do
      throwError "MyNat should be in spec"
    logInfo "✓ abbrev: body is walked — PASS"
  | .error msg => throwError msg

#test_abbrev

elab "#test_opaque" : command => do
  let env ← getEnv
  match computeTcb env #[`opaqueThm] with
  | .ok result =>
    unless result.specSet.contains `opaqueThm do
      throwError "opaqueThm should be in spec"
    unless result.specSet.contains `opaqueVal do
      throwError "opaqueVal should be in spec"
    logInfo "✓ opaque: only type is walked — PASS"
  | .error msg => throwError msg

#test_opaque

elab "#test_inductive" : command => do
  let env ← getEnv
  match computeTcb env #[`myLength_nil] with
  | .ok result =>
    unless result.specSet.contains `myLength_nil do
      throwError "myLength_nil should be in spec"
    unless result.specSet.contains `myLength do
      throwError "myLength should be in spec"
    unless result.specSet.contains `MyList do
      throwError "MyList should be in spec"
    unless result.specSet.contains `MyList.nil do
      throwError "MyList.nil should be in spec"
    unless result.specSet.contains `MyList.cons do
      throwError "MyList.cons should be in spec"
    logInfo "✓ inductive: constructor types walked — PASS"
  | .error msg => throwError msg

#test_inductive

elab "#test_structure" : command => do
  let env ← getEnv
  match computeTcb env #[`mkPair_fst] with
  | .ok result =>
    unless result.specSet.contains `mkPair_fst do
      throwError "mkPair_fst should be in spec"
    unless result.specSet.contains `mkPair do
      throwError "mkPair should be in spec"
    unless result.specSet.contains `MyPair do
      throwError "MyPair should be in spec"
    unless result.specSet.contains `MyPair.mk do
      throwError "MyPair.mk should be in spec"
    logInfo "✓ structure: constructor type walked — PASS"
  | .error msg => throwError msg

#test_structure

-- Expr.proj: structure projections store the type name as a
-- plain Name, not an Expr.const — collectConstants must capture it
structure ProjStruct where
  val : Nat

def getProjVal (s : ProjStruct) : Nat := s.val

theorem getProjVal_mk (n : Nat) : getProjVal ⟨n⟩ = n := rfl

elab "#test_proj_captured" : command => do
  let env ← getEnv
  match computeTcb env #[`getProjVal_mk] with
  | .ok result =>
    unless result.specSet.contains `getProjVal_mk do
      throwError "getProjVal_mk should be in spec"
    unless result.specSet.contains `getProjVal do
      throwError "getProjVal should be in spec"
    unless result.specSet.contains `ProjStruct do
      throwError "ProjStruct should be in spec \
        (via Expr.proj typeName)"
    logInfo "✓ Expr.proj typeName captured — PASS"
  | .error msg => throwError msg

#test_proj_captured

-- ═══════════════════════════════════════════════
-- Additional fixtures
-- ═══════════════════════════════════════════════

-- Private declaration in TCB
private def edgePrivateImpl : Nat := 42
def edgeUsesPrivate : Nat := edgePrivateImpl + 1

-- Deep dependency chain (10 levels)
def chain0 : Nat := 0
def chain1 : Nat := chain0 + 1
def chain2 : Nat := chain1 + 1
def chain3 : Nat := chain2 + 1
def chain4 : Nat := chain3 + 1
def chain5 : Nat := chain4 + 1
def chain6 : Nat := chain5 + 1
def chain7 : Nat := chain6 + 1
def chain8 : Nat := chain7 + 1
def chain9 : Nat := chain8 + 1

-- ═══════════════════════════════════════════════
-- Additional tests
-- ═══════════════════════════════════════════════

elab "#test_private_in_tcb" : command => do
  let env ← getEnv
  match computeTcb env #[`edgeUsesPrivate] with
  | .ok result =>
    -- Private name is mangled; find it by substring
    let mut foundInSpec := false
    for name in result.specSet do
      let s := toString name
      if (s.splitOn "edgePrivateImpl").length > 1 then
        foundInSpec := true
    unless foundInSpec do
      throwError "edgePrivateImpl should be in specSet"
    -- Also verify it appears in formatted userSpec
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
      if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allUserDecls
    let mut foundInUserSpec := false
    for (name, _) in fr.userSpec do
      let s := toString name
      if (s.splitOn "edgePrivateImpl").length > 1 then
        foundInUserSpec := true
    unless foundInUserSpec do
      throwError "edgePrivateImpl should be in userSpec"
    logInfo "✓ private def in TCB: PASS"
  | .error msg => throwError msg

#test_private_in_tcb

elab "#test_deep_chain" : command => do
  let env ← getEnv
  match computeTcb env #[`chain9] with
  | .ok result =>
    for name in #[`chain0, `chain1, `chain2, `chain3,
        `chain4, `chain5, `chain6, `chain7, `chain8,
        `chain9] do
      unless result.specSet.contains name do
        throwError s!"{name} should be in specSet"
    logInfo "✓ deep chain (10 levels): PASS"
  | .error msg => throwError msg

#test_deep_chain

elab "#test_deep_chain_tree" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`chain9] with
  | .ok graph =>
    let output := renderTree env graph
    unless (output.splitOn "chain0").length > 1 do
      throwError "expected chain0 (leaf) in tree"
    -- Non-trivial depth: should have box-drawing chars
    unless (output.splitOn "├──").length > 1
        || (output.splitOn "└──").length > 1 do
      throwError s!"expected box-drawing chars: {output}"
    logInfo "✓ deep chain tree rendering: PASS"
  | .error msg => throwError msg

#test_deep_chain_tree

-- ═══════════════════════════════════════════════
-- Empty / library entry point tests (C7)
-- ═══════════════════════════════════════════════

elab "#test_empty_entry_points" : command => do
  let env ← getEnv
  match computeTcb env #[] with
  | .ok result =>
    unless result.specSet.isEmpty do
      throwError "empty entry points should give empty spec"
    unless result.missingNames.isEmpty do
      throwError "empty entry points should give no missing"
    logInfo "✓ empty entry points: PASS"
  | .error msg => throwError msg

#test_empty_entry_points

elab "#test_empty_entry_points_graph" : command => do
  let env ← getEnv
  match computeTcbGraph env #[] with
  | .ok graph =>
    unless graph.specSet.isEmpty do
      throwError "empty entry points should give empty spec"
    logInfo "✓ empty entry points (graph): PASS"
  | .error msg => throwError msg

#test_empty_entry_points_graph

elab "#test_library_entry_tree" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`Nat.add] with
  | .ok graph =>
    let output := renderTree env graph
    unless (output.splitOn "Nat.add").length > 1 do
      throwError s!"expected Nat.add in tree: {output}"
    logInfo "✓ library entry point tree: PASS"
  | .error msg => throwError msg

#test_library_entry_tree

elab "#test_library_entry_why" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`Nat.add] with
  | .ok graph =>
    let output := renderPath env graph `Nat.add `Nat.add
    unless (output.splitOn "entry point").length > 1 do
      throwError s!"expected 'entry point' msg: {output}"
    logInfo "✓ library entry point why: PASS"
  | .error msg => throwError msg

#test_library_entry_why

-- ═══════════════════════════════════════════════
-- Smoke tests
-- ═══════════════════════════════════════════════

#tcb myLength_nil
#tcb mkPair_fst
#tcb edgeUsesPrivate
#tcb_tree chain9
#tcb_why chain9 chain0
