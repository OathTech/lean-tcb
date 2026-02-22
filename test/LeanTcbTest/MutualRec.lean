/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Mutual recursion and recursor tests

Tests that exercise the mutual companion, recursor→parent, and
constructor→parent code paths in the core worklist traversal.
-/

open Lean Elab Command LeanTcb

-- ═══════════════════════════════════════════════
-- Fixtures: mutual definitions
-- ═══════════════════════════════════════════════

mutual
  def mEven : Nat → Bool
    | 0 => true
    | n + 1 => mOdd n
  def mOdd : Nat → Bool
    | 0 => false
    | n + 1 => mEven n
end

def useEven (n : Nat) : Bool := mEven n

-- ═══════════════════════════════════════════════
-- Fixtures: mutual inductive types
-- ═══════════════════════════════════════════════

mutual
  inductive MTree (α : Type) where
    | node : α → MForest α → MTree α
  inductive MForest (α : Type) where
    | nil : MForest α
    | cons : MTree α → MForest α → MForest α
end

def mTreeVal {α : Type} : MTree α → α
  | .node a _ => a

-- ═══════════════════════════════════════════════
-- Fixtures: custom inductive for recursor test
-- ═══════════════════════════════════════════════

inductive Color where
  | red | green | blue

def colorToNat : Color → Nat
  | .red => 0
  | .green => 1
  | .blue => 2

-- ═══════════════════════════════════════════════
-- Fixtures: mutual theorem block
-- ═══════════════════════════════════════════════

mutual
  theorem mt1 : 1 + 1 = 2 := rfl
  theorem mt2 : 2 + 1 = 3 := rfl
end

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_mutual_def_companion" : command => do
  let env ← getEnv
  -- useEven calls mEven; mutual companion rule should
  -- pull mOdd into the TCB
  match computeTcb env #[`useEven] with
  | .ok result =>
    unless result.specSet.contains `useEven do
      throwError "useEven should be in spec"
    unless result.specSet.contains `mEven do
      throwError "mEven should be in spec"
    unless result.specSet.contains `mOdd do
      throwError "mOdd should be in spec (mutual companion)"
    logInfo "✓ mutual def companion: PASS"
  | .error msg => throwError msg

#test_mutual_def_companion

elab "#test_mutual_def_symmetric" : command => do
  let env ← getEnv
  -- Entering via mOdd should pull mEven
  match computeTcb env #[`mOdd] with
  | .ok result =>
    unless result.specSet.contains `mOdd do
      throwError "mOdd should be in spec"
    unless result.specSet.contains `mEven do
      throwError "mEven should be in spec (mutual companion)"
    logInfo "✓ mutual def symmetric: PASS"
  | .error msg => throwError msg

#test_mutual_def_symmetric

elab "#test_mutual_inductive" : command => do
  let env ← getEnv
  -- Entering via MTree should pull MForest as mutual companion
  match computeTcb env #[`mTreeVal] with
  | .ok result =>
    unless result.specSet.contains `mTreeVal do
      throwError "mTreeVal should be in spec"
    unless result.specSet.contains `MTree do
      throwError "MTree should be in spec"
    unless result.specSet.contains `MForest do
      throwError "MForest should be in spec (mutual companion)"
    logInfo "✓ mutual inductive: PASS"
  | .error msg => throwError msg

#test_mutual_inductive

elab "#test_recursor_parent" : command => do
  let env ← getEnv
  -- colorToNat pattern-matches on Color, so Lean uses
  -- Color.rec / Color.casesOn. The recursor→parent rule
  -- should link back to Color inductive.
  match computeTcb env #[`colorToNat] with
  | .ok result =>
    unless result.specSet.contains `colorToNat do
      throwError "colorToNat should be in spec"
    unless result.specSet.contains `Color do
      throwError "Color should be in spec (via recursor parent)"
    -- Constructors should also be present (walked from inductive)
    unless result.specSet.contains `Color.red do
      throwError "Color.red should be in spec"
    unless result.specSet.contains `Color.green do
      throwError "Color.green should be in spec"
    unless result.specSet.contains `Color.blue do
      throwError "Color.blue should be in spec"
    logInfo "✓ recursor parent: PASS"
  | .error msg => throwError msg

#test_recursor_parent

elab "#test_mutual_missing_names_empty" : command => do
  let env ← getEnv
  match computeTcb env #[`useEven] with
  | .ok result =>
    unless result.missingNames.isEmpty do
      throwError s!"Expected no missing names, got: \
        {result.missingNames.toList}"
    logInfo "✓ mutual missing names empty: PASS"
  | .error msg => throwError msg

#test_mutual_missing_names_empty

-- ═══════════════════════════════════════════════
-- Tree / path tests
-- ═══════════════════════════════════════════════

elab "#test_tree_mutual_companion_reason" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`useEven] with
  | .ok graph =>
    let output := renderTree env graph
    -- mOdd should be linked via "mutual block companion"
    unless (output.splitOn "mutual block companion").length > 1 do
      throwError s!"expected 'mutual block companion' in \
        tree: {output}"
    logInfo "✓ tree mutual companion reason: PASS"
  | .error msg => throwError msg

#test_tree_mutual_companion_reason

elab "#test_tree_recursor_parent_reason" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`colorToNat] with
  | .ok graph =>
    let output := renderTree env graph
    -- Color.rec should appear in the tree
    unless (output.splitOn "Color.rec").length > 1 do
      throwError s!"expected Color.rec in tree: {output}"
    -- With the prefer-specific-reason dedup, Color should
    -- now show "recursor enqueued parent" under Color.rec
    -- instead of the generic "referenced in type/body"
    unless (output.splitOn "recursor enqueued parent").length
        > 1 do
      throwError s!"expected 'recursor enqueued parent' in \
        tree: {output}"
    logInfo "✓ tree recursor parent reason: PASS"
  | .error msg => throwError msg

#test_tree_recursor_parent_reason

elab "#test_graph_recparent_in_depsmap" : command => do
  let env ← getEnv
  -- Verify recParent reason is recorded in depsMap even
  -- though the tree rendering deduplicates it (Color is
  -- discovered via exprRef first).
  match computeTcbGraph env #[`colorToNat] with
  | .ok graph =>
    -- Color.rec should have Color as a child with recParent
    let recDeps := match graph.depsMap.find? `Color.rec with
      | some arr => arr
      | none => #[]
    let mut hasRecParent := false
    for (n, r) in recDeps do
      if n == `Color then
        match r with
        | .recParent => hasRecParent := true
        | _ => pure ()
    unless hasRecParent do
      throwError "expected recParent reason for Color in \
        Color.rec's depsMap entry"
    logInfo "✓ graph recParent in depsMap: PASS"
  | .error msg => throwError msg

#test_graph_recparent_in_depsmap

elab "#test_why_mutual_companion" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`useEven] with
  | .ok graph =>
    let output := renderPath env graph `useEven `mOdd
    unless (output.splitOn "mutual block companion").length
        > 1 do
      throwError s!"expected 'mutual block companion' in \
        path: {output}"
    unless (output.splitOn "TCB Path").length > 1 do
      throwError s!"expected TCB Path header: {output}"
    logInfo "✓ why mutual companion: PASS"
  | .error msg => throwError msg

#test_why_mutual_companion

elab "#test_mutual_theorem_companions" : command => do
  let env ← getEnv
  -- Check whether Lean created a true mutual block
  let some ci := env.find? `mt1
    | throwError "mt1 not found in environment"
  match ci with
  | .thmInfo v =>
    if v.all.length > 1 then
      -- True mutual block: mt2 should be a companion
      match computeTcb env #[`mt1] with
      | .ok result =>
        unless result.specSet.contains `mt1 do
          throwError "mt1 should be in specSet"
        unless result.specSet.contains `mt2 do
          throwError "mt2 should be in specSet \
            (mutual companion)"
        logInfo "✓ mutual theorem companions: PASS"
      | .error msg => throwError msg
    else
      -- Lean optimized into independent blocks
      logInfo "✓ mutual theorem companions: PASS \
        (elaborator split into independent blocks, \
        v.all.length == 1)"
  | _ =>
    throwError "mt1 should be a theorem"

#test_mutual_theorem_companions

-- ═══════════════════════════════════════════════
-- Smoke tests
-- ═══════════════════════════════════════════════

#tcb useEven
#tcb mTreeVal
#tcb colorToNat
#tcb_tree useEven
#tcb_tree colorToNat
#tcb_why useEven mOdd
#tcb_why colorToNat Color
#tcb mt1
