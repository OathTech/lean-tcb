import LeanTcb

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

-- ═══════════════════════════════════════════════
-- Smoke tests
-- ═══════════════════════════════════════════════

#tcb myLength_nil
#tcb mkPair_fst
