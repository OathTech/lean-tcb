/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
import LeanTcb

/-!
# Cross-file test fixtures

Definitions used by `CrossFile.lean` to test that imported same-package
declarations are classified as "Must Review" (project-local) rather
than "library."  This file defines fixtures only — no tests.
-/

def crossDef (n : Nat) : Nat := n + 1

abbrev crossAbbrev := Nat

def crossPred (n : Nat) : Prop := n > 0

theorem crossThm (n : Nat) : crossPred (crossDef n) := by
  unfold crossPred crossDef; omega
