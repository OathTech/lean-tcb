import LeanTcb

open Lean Elab Command LeanTcb

/-!
# End-to-end test: a small verified development

We build a tiny "library" with definitions, helper lemmas, and a main theorem,
then use `#tcb` to classify everything. This demonstrates the tool on a
realistic (if small) example where the spec/proof-infra distinction matters.

## The development

We define a notion of "divides", a predicate "hasNontrivialDivisor",
and a predicate "myPrime". We prove a main theorem: 2 is prime.

The trusted computing base for `two_is_prime` should include:
  - The theorem statement itself
  - `myPrime`, `hasNontrivialDivisor`, `myDvd` (definitions that give meaning)

It should NOT include:
  - Helper lemmas used only in the proof (`dvd_refl`, `not_hasNontrivialDivisor_two`)
  - The proof term of `two_is_prime` itself
-/

-- ═══════════════════════════════════════════════
-- Definitions (these ARE the specification)
-- ═══════════════════════════════════════════════

/-- `myDvd a b` means `a` divides `b`. -/
def myDvd (a b : Nat) : Prop := ∃ k, b = a * k

/-- A number has a nontrivial divisor if some d with 2 ≤ d < n divides it. -/
def hasNontrivialDivisor (n : Nat) : Prop :=
  ∃ d, 2 ≤ d ∧ d < n ∧ myDvd d n

/-- A natural number is prime if it's ≥ 2 and has no nontrivial divisor. -/
def myPrime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬ hasNontrivialDivisor n

-- ═══════════════════════════════════════════════
-- Helper lemmas (proof infrastructure — kernel-checked)
-- ═══════════════════════════════════════════════

theorem myDvd_refl (n : Nat) : myDvd n n := ⟨1, by omega⟩

theorem not_hasNontrivialDivisor_two : ¬ hasNontrivialDivisor 2 := by
  intro ⟨d, hle, hlt, ⟨k, hk⟩⟩
  omega

-- ═══════════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════════

theorem two_is_prime : myPrime 2 := by
  constructor
  · omega
  · exact not_hasNontrivialDivisor_two

-- ═══════════════════════════════════════════════
-- TCB analysis
-- ═══════════════════════════════════════════════

#tcb two_is_prime

-- Verbose output (includes library dependencies)
#tcb! two_is_prime

-- ═══════════════════════════════════════════════
-- Verification tests
-- ═══════════════════════════════════════════════

elab "#test_e2e_spec_includes_definitions" : command => do
  let env ← getEnv
  match computeTcb env #[`two_is_prime] with
  | .ok result =>
    -- Main theorem is in spec
    unless result.specSet.contains `two_is_prime do
      throwError "two_is_prime should be in spec"
    -- All definitions that give meaning to the theorem are in spec
    unless result.specSet.contains `myPrime do
      throwError "myPrime should be in spec"
    unless result.specSet.contains `hasNontrivialDivisor do
      throwError "hasNontrivialDivisor should be in spec"
    unless result.specSet.contains `myDvd do
      throwError "myDvd should be in spec"
    logInfo "✓ e2e: all definitions in spec — PASS"
  | .error msg => throwError msg

#test_e2e_spec_includes_definitions

elab "#test_e2e_excludes_helper_lemmas" : command => do
  let env ← getEnv
  match computeTcb env #[`two_is_prime] with
  | .ok result =>
    -- Helper lemmas should NOT be in spec (only used in proofs)
    if result.specSet.contains `myDvd_refl then
      throwError "myDvd_refl should NOT be in spec (unused helper)"
    if result.specSet.contains `not_hasNontrivialDivisor_two then
      throwError "not_hasNontrivialDivisor_two should NOT be in spec"
    logInfo "✓ e2e: helper lemmas excluded from spec — PASS"
  | .error msg => throwError msg

#test_e2e_excludes_helper_lemmas

elab "#test_e2e_user_vs_library" : command => do
  let env ← getEnv
  match computeTcb env #[`two_is_prime] with
  | .ok result =>
    let fr := formatResult env result
    -- User spec should contain our definitions + the theorem
    unless fr.userSpec.any (·.1 == `two_is_prime) do
      throwError "two_is_prime should be in userSpec"
    unless fr.userSpec.any (·.1 == `myPrime) do
      throwError "myPrime should be in userSpec"
    unless fr.userSpec.any (·.1 == `hasNontrivialDivisor) do
      throwError "hasNontrivialDivisor should be in userSpec"
    unless fr.userSpec.any (·.1 == `myDvd) do
      throwError "myDvd should be in userSpec"
    -- User spec should NOT contain library stuff
    if fr.userSpec.any (·.1 == `Nat) then
      throwError "Nat should not be in userSpec"
    logInfo s!"✓ e2e: user spec has {fr.userSpec.size} declarations, library spec has {fr.librarySpec.size} — PASS"
  | .error msg => throwError msg

#test_e2e_user_vs_library

elab "#test_e2e_counts" : command => do
  let env ← getEnv
  match computeTcb env #[`two_is_prime] with
  | .ok result =>
    -- Sanity: spec should be much smaller than proof infrastructure
    unless result.specSet.size < result.proofInfra.size do
      throwError "spec should be much smaller than proof infra"
    let fr := formatResult env result
    -- We expect a small user spec (definitions + theorem, no helpers)
    unless fr.userSpec.size ≤ 10 do
      throwError s!"user spec unexpectedly large: {fr.userSpec.size}"
    logInfo s!"✓ e2e: {result.specSet.size} spec / {result.proofInfra.size} proof-infra — PASS"
  | .error msg => throwError msg

#test_e2e_counts
