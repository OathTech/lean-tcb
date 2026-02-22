import Lean

open Lean

namespace LeanTcb

/-- How a declaration was classified. -/
inductive Classification where
  | /-- Must be believed correct by a human. -/
    specification
  | /-- Kernel-verified; need not be trusted. -/
    proofInfrastructure
  deriving Inhabited, BEq, Repr

/-- Result of the TCB analysis for a single entry-point set. -/
structure TcbResult where
  /-- The entry-point theorem names that seeded the analysis. -/
  entryPoints : Array Name
  /-- All declarations reachable in the trust-relevant traversal (the spec set). -/
  specSet : Lean.NameSet
  /-- All declarations in the environment that are NOT in the spec set. -/
  proofInfra : Lean.NameSet
  deriving Inhabited

end LeanTcb
