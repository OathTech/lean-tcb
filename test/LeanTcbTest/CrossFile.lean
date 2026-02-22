/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import LeanTcb
import LeanTcbTest.CrossFileFixtures

open Lean Elab Command LeanTcb

/-!
# Cross-file classification tests

Tests that imported same-package declarations are classified as
project-local ("Must Review") rather than external library.
The fixtures (`crossDef`, `crossPred`, etc.) are defined in
`CrossFileFixtures.lean` — a separate file in the same package.
-/

-- ═══════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════

elab "#test_cross_file_imported_defs_in_userSpec" : command => do
  let env ← getEnv
  match computeTcb env #[`crossThm] with
  | .ok result =>
    let allProjectDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allProjectDecls
    -- crossDef and crossPred are from another file in the same
    -- package — they should appear in userSpec, not librarySpec
    unless fr.userSpec.any (·.1 == `crossDef) do
      throwError "crossDef should be in userSpec (project-local)"
    unless fr.userSpec.any (·.1 == `crossPred) do
      throwError "crossPred should be in userSpec (project-local)"
    unless fr.userSpec.any (·.1 == `crossThm) do
      throwError "crossThm should be in userSpec (project-local)"
    logInfo "✓ cross-file: imported defs in userSpec — PASS"
  | .error msg => throwError msg

#test_cross_file_imported_defs_in_userSpec

elab "#test_cross_file_not_in_librarySpec" : command => do
  let env ← getEnv
  match computeTcb env #[`crossThm] with
  | .ok result =>
    let allProjectDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allProjectDecls
    -- Same-package defs must NOT appear in librarySpec
    if fr.librarySpec.any (· == `crossDef) then
      throwError "crossDef should NOT be in librarySpec"
    if fr.librarySpec.any (· == `crossPred) then
      throwError "crossPred should NOT be in librarySpec"
    if fr.librarySpec.any (· == `crossThm) then
      throwError "crossThm should NOT be in librarySpec"
    logInfo "✓ cross-file: project defs not in librarySpec — PASS"
  | .error msg => throwError msg

#test_cross_file_not_in_librarySpec

elab "#test_cross_file_stdlib_still_library" : command => do
  let env ← getEnv
  match computeTcb env #[`crossThm] with
  | .ok result =>
    let allProjectDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc
    let fr := formatResult env result allProjectDecls
    -- Nat is from Init (external) — must remain in librarySpec
    unless fr.librarySpec.contains `Nat do
      throwError "Nat should be in librarySpec (external)"
    -- Nat must NOT be in userSpec
    if fr.userSpec.any (·.1 == `Nat) then
      throwError "Nat should NOT be in userSpec"
    logInfo "✓ cross-file: stdlib in librarySpec — PASS"
  | .error msg => throwError msg

#test_cross_file_stdlib_still_library

-- ═══════════════════════════════════════════════
-- Smoke test: #tcb on imported declaration
-- ═══════════════════════════════════════════════

#tcb crossThm
