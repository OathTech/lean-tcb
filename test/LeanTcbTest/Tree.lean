/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

open Lean Elab Command LeanTcb

/-!
# Tree rendering tests

Tests for `renderTree` and `#tcb_tree` using fixture definitions
that exercise DAG dedup and library collapsing.
-/

-- ═══════════════════════════════════════════════
-- Fixtures (same chain as EndToEnd/Path)
-- ═══════════════════════════════════════════════

def treeDvd (a b : Nat) : Prop := ∃ k, b = a * k

def treeHasNontrivDivisor (n : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d < n ∧ treeDvd d n

def treePrime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬ treeHasNontrivDivisor n

theorem treeTwoIsPrime : treePrime 2 := by
  constructor
  · omega
  · intro ⟨d, hle, hlt, ⟨k, hk⟩⟩; omega

-- Diamond dependency: treeComposite references both
-- treePrime and treeHasNontrivDivisor (which treePrime also
-- depends on), creating a DAG diamond.
def treeComposite (n : Nat) : Prop :=
  ¬ treePrime n ∧ treeHasNontrivDivisor n

theorem treeCompositeThm (n : Nat)
    (h : treeComposite n) : treeHasNontrivDivisor n :=
  h.2

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_tree_has_root" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`treeTwoIsPrime] with
  | .ok graph =>
    let output := renderTree env graph
    unless (output.splitOn "TCB Dependency Tree").length > 1 do
      throwError s!"expected header: {output}"
    unless (output.splitOn "treeTwoIsPrime").length > 1 do
      throwError "expected root entry point in tree"
    logInfo "✓ tree has root: PASS"
  | .error msg => throwError msg

#test_tree_has_root

elab "#test_tree_box_drawing" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`treeTwoIsPrime] with
  | .ok graph =>
    let output := renderTree env graph
    -- Should contain box-drawing characters
    unless (output.splitOn "├──").length > 1
        || (output.splitOn "└──").length > 1 do
      throwError
        s!"expected box-drawing chars in tree: {output}"
    logInfo "✓ tree box-drawing chars: PASS"
  | .error msg => throwError msg

#test_tree_box_drawing

elab "#test_tree_library_collapse" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`treeTwoIsPrime] with
  | .ok graph =>
    -- Default (collapsed) should show library count
    let collapsed := renderTree env graph
    unless (collapsed.splitOn "library dependencies").length > 1 do
      throwError
        s!"expected library collapse text: {collapsed}"
    -- Expanded should NOT show library collapse text
    let expanded := renderTree env graph
      { expandLibrary := true }
    -- Expanded should have more lines than collapsed
    let collapsedLines :=
      (collapsed.splitOn "\n").length
    let expandedLines :=
      (expanded.splitOn "\n").length
    unless expandedLines > collapsedLines do
      throwError
        s!"expanded ({expandedLines} lines) should have \
          more lines than collapsed ({collapsedLines})"
    logInfo "✓ tree library collapse: PASS"
  | .error msg => throwError msg

#test_tree_library_collapse

elab "#test_tree_dag_dedup" : command => do
  let env ← getEnv
  -- treeCompositeThm depends on treeComposite which depends
  -- on both treePrime and treeHasNontrivDivisor.
  -- treePrime also depends on treeHasNontrivDivisor.
  -- So treeHasNontrivDivisor should show "(see above)"
  -- on second occurrence.
  match computeTcbGraph env #[`treeCompositeThm] with
  | .ok graph =>
    let output := renderTree env graph
    -- treeHasNontrivDivisor should appear at least twice
    let occurrences :=
      (output.splitOn "treeHasNontrivDivisor").length - 1
    unless occurrences ≥ 2 do
      throwError
        s!"expected treeHasNontrivDivisor to appear ≥ 2 \
          times, got {occurrences}"
    -- One occurrence should have "(see above)"
    unless (output.splitOn "see above").length > 1 do
      throwError
        s!"expected '(see above)' for DAG dedup: {output}"
    logInfo "✓ tree DAG dedup: PASS"
  | .error msg => throwError msg

#test_tree_dag_dedup

elab "#test_tree_children_sorted" : command => do
  let env ← getEnv
  -- treeComposite directly references both treePrime and
  -- treeHasNontrivDivisor, so they are siblings under
  -- treeComposite. Alphabetically: treeHasNontrivDivisor
  -- < treePrime, so it should appear first among siblings.
  match computeTcbGraph env #[`treeCompositeThm] with
  | .ok graph =>
    let output := renderTree env graph
    let lines := output.splitOn "\n"
    -- Find first occurrence of each under treeComposite
    let mut hasNontrivIdx : Option Nat := none
    let mut primeIdx : Option Nat := none
    for i in [:lines.length] do
      let line := lines[i]!
      -- Look for direct children of treeComposite
      -- (they start with "│   ├──" or "│   └──")
      if (line.splitOn "treeHasNontrivDivisor").length > 1
          && hasNontrivIdx.isNone then
        hasNontrivIdx := some i
      if (line.splitOn "treePrime").length > 1
          && primeIdx.isNone then
        primeIdx := some i
    match hasNontrivIdx, primeIdx with
    | some hi, some pi =>
      unless hi < pi do
        throwError
          s!"treeHasNontrivDivisor (line {hi}) should \
            appear before treePrime (line {pi})"
    | _, _ =>
      throwError "expected both children in tree output"
    logInfo "✓ tree children sorted: PASS"
  | .error msg => throwError msg

#test_tree_children_sorted

-- M6: Shared dependency across entry points shows (see above)
def treeSharedDep (n : Nat) : Nat := n + 1
theorem treeSharedThm1 : treeSharedDep 0 = 1 := rfl
theorem treeSharedThm2 : treeSharedDep 1 = 2 := rfl

elab "#test_tree_cross_entry_dedup" : command => do
  let env ← getEnv
  match computeTcbGraph env
      #[`treeSharedThm1, `treeSharedThm2] with
  | .ok graph =>
    let output := renderTree env graph
    unless (output.splitOn "see above").length > 1 do
      throwError s!"expected '(see above)' for cross-entry \
        dedup: {output}"
    logInfo "✓ tree cross-entry dedup: PASS"
  | .error msg => throwError msg

#test_tree_cross_entry_dedup

-- ═══════════════════════════════════════════════
-- Fixtures: sibling sort and zero-library tests
-- ═══════════════════════════════════════════════

def treeAlpha : Nat := 1
def treeBeta : Nat := 2
def treeGamma : Nat := 3
def treeMultiChild : Nat :=
  treeAlpha + treeBeta + treeGamma

-- ═══════════════════════════════════════════════
-- Additional tests
-- ═══════════════════════════════════════════════

elab "#test_tree_all_siblings_sorted" : command => do
  let env ← getEnv
  match computeTcbGraph env #[`treeMultiChild] with
  | .ok graph =>
    let output := renderTree env graph
    let lines := output.splitOn "\n"
    let mut alphaIdx : Option Nat := none
    let mut betaIdx : Option Nat := none
    let mut gammaIdx : Option Nat := none
    for i in [:lines.length] do
      let line := lines[i]!
      if (line.splitOn "treeAlpha").length > 1
          && alphaIdx.isNone then
        alphaIdx := some i
      if (line.splitOn "treeBeta").length > 1
          && betaIdx.isNone then
        betaIdx := some i
      if (line.splitOn "treeGamma").length > 1
          && gammaIdx.isNone then
        gammaIdx := some i
    match alphaIdx, betaIdx, gammaIdx with
    | some ai, some bi, some gi =>
      unless ai < bi do
        throwError s!"treeAlpha (line {ai}) should \
          appear before treeBeta (line {bi})"
      unless bi < gi do
        throwError s!"treeBeta (line {bi}) should \
          appear before treeGamma (line {gi})"
      logInfo "✓ tree all siblings sorted: PASS"
    | _, _, _ =>
      throwError "expected all three children in tree"
  | .error msg => throwError msg

#test_tree_all_siblings_sorted

elab "#test_tree_zero_library_rendering" : command => do
  let env ← getEnv
  -- Synthetic graph with only a project-local entry point
  -- and no children at all
  let syntheticGraph : TcbGraphResult := {
    entryPoints := #[`treeAlpha]
    specSet := ({} : Lean.NameSet).insert `treeAlpha
    parentMap := {}
    depsMap := {}
  }
  let output := renderTree env syntheticGraph
  if (output.splitOn "library dependencies").length
      > 1 then
    throwError s!"should not contain \
      'library dependencies': {output}"
  if (output.splitOn "library dependency").length
      > 1 then
    throwError s!"should not contain \
      'library dependency': {output}"
  logInfo "✓ tree zero library rendering: PASS"

#test_tree_zero_library_rendering

-- ═══════════════════════════════════════════════
-- Smoke tests: #tcb_tree commands
-- ═══════════════════════════════════════════════

#tcb_tree treeTwoIsPrime
#tcb_tree! treeTwoIsPrime
#tcb_tree treeCompositeThm
#tcb_tree treeMultiChild
