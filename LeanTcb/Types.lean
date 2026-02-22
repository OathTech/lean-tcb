/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
import Lean

/-!
# TCB analysis types

Core data types for the trust boundary classifier.
-/

open Lean

namespace LeanTcb

/-- Result of the TCB analysis for a single entry-point set. -/
structure TcbResult where
  /-- The entry-point theorem names that seeded the analysis. -/
  entryPoints : Array Name
  /-- Declarations reachable via trust-relevant traversal. -/
  specSet : Lean.NameSet
  deriving Inhabited

end LeanTcb
