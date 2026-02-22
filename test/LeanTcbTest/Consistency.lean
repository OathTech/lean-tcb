/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb

/-!
# Consistency tests

Tests `computeTcb` vs `computeTcbGraph` agreement and tighter
spec-set size assertions.
-/

open Lean Elab Command LeanTcb

-- ═══════════════════════════════════════════════
-- Fixtures
-- ═══════════════════════════════════════════════

def consDef1 : Nat := 42
def consDef2 : Nat := consDef1 + 1
theorem consThm : consDef2 = 43 := rfl

-- Mutual fixture for exact count test
mutual
  def cEven : Nat → Bool
    | 0 => true
    | n + 1 => cOdd n
  def cOdd : Nat → Bool
    | 0 => false
    | n + 1 => cEven n
end

def cUseEven (n : Nat) : Bool := cEven n

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_tcb_vs_graph_specset_agree" : command => do
  let env ← getEnv
  match computeTcb env #[`consThm],
      computeTcbGraph env #[`consThm] with
  | .ok tcb, .ok graph =>
    -- Every name in tcb.specSet should be in graph.specSet
    for name in tcb.specSet do
      unless graph.specSet.contains name do
        throwError s!"Name {name} in computeTcb but not \
          computeTcbGraph"
    -- Every name in graph.specSet should be in tcb.specSet
    for name in graph.specSet do
      unless tcb.specSet.contains name do
        throwError s!"Name {name} in computeTcbGraph but \
          not computeTcb"
    -- Compare missingNames
    for name in tcb.missingNames do
      unless graph.missingNames.contains name do
        throwError s!"Missing name {name} in computeTcb \
          but not computeTcbGraph"
    for name in graph.missingNames do
      unless tcb.missingNames.contains name do
        throwError s!"Missing name {name} in \
          computeTcbGraph but not computeTcb"
    logInfo "✓ computeTcb vs computeTcbGraph agree — PASS"
  | .error msg, _ => throwError msg
  | _, .error msg => throwError msg

#test_tcb_vs_graph_specset_agree

elab "#test_exact_user_spec_count" : command => do
  let env ← getEnv
  match computeTcb env #[`consThm] with
  | .ok result =>
    let mut userNames : Array Name := #[]
    for name in result.specSet do
      if isProjectLocal env name then
        userNames := userNames.push name
    -- Should be exactly: consThm, consDef1, consDef2
    unless userNames.size == 3 do
      throwError s!"Expected 3 project-local names, got \
        {userNames.size}: {userNames}"
    for expected in #[`consThm, `consDef1, `consDef2] do
      unless result.specSet.contains expected do
        throwError s!"{expected} should be in specSet"
    logInfo "✓ exact user spec count (3 names) — PASS"
  | .error msg => throwError msg

#test_exact_user_spec_count

elab "#test_exact_user_spec_count_mutual" : command => do
  let env ← getEnv
  match computeTcb env #[`cUseEven] with
  | .ok result =>
    let mut userNames : Array Name := #[]
    for name in result.specSet do
      if isProjectLocal env name then
        userNames := userNames.push name
    -- Should include: cUseEven, cEven, cOdd
    -- (may also include auto-generated like cEven.match_1)
    for expected in #[`cUseEven, `cEven, `cOdd] do
      unless result.specSet.contains expected do
        throwError s!"{expected} should be in specSet"
    unless userNames.size >= 3 do
      throwError s!"Expected at least 3 project-local \
        names, got {userNames.size}: {userNames}"
    logInfo "✓ exact user spec count mutual (≥3) — PASS"
  | .error msg => throwError msg

#test_exact_user_spec_count_mutual

-- ═══════════════════════════════════════════════
-- Smoke tests — visual check in infoview
-- ═══════════════════════════════════════════════

#tcb consThm
#tcb_tree consThm
