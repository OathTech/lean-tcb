/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
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
  /-- Names referenced during traversal but not found in the
      environment. Non-empty results are suspicious. -/
  missingNames : Lean.NameSet := {}
  deriving Inhabited

/-- Why a dependency was enqueued during traversal. -/
inductive DepReason where
  | exprRef         -- referenced in trust-relevant expressions
  | ctorParent      -- constructor enqueued parent inductive
  | recParent       -- recursor enqueued parent inductive
  | mutualCompanion -- mutual block companion
  | inductCtor      -- inductive enqueued its constructor
  deriving Inhabited, BEq

/-- Human-readable label for a `DepReason`. -/
def DepReason.label : DepReason → String
  | .exprRef         => "referenced in type/body"
  | .ctorParent      => "constructor enqueued parent inductive"
  | .recParent       => "recursor enqueued parent inductive"
  | .mutualCompanion => "mutual block companion"
  | .inductCtor      => "inductive enqueued constructor"

/-- TCB result with full dependency provenance. -/
structure TcbGraphResult where
  entryPoints : Array Name
  specSet : Lean.NameSet
  missingNames : Lean.NameSet := {}
  /-- For each non-entry-point name: (parent, reason). -/
  parentMap : Lean.NameMap (Name × DepReason)
  /-- Forward adjacency: for each name, its direct children
      (with reason) within the spec set. Used for tree rendering
      to capture all edges, not just the discovery-tree edges
      in `parentMap`. -/
  depsMap : Lean.NameMap (Array (Name × DepReason)) := {}
  deriving Inhabited

def TcbGraphResult.toTcbResult (g : TcbGraphResult) : TcbResult :=
  { entryPoints := g.entryPoints
    specSet := g.specSet
    missingNames := g.missingNames }

end LeanTcb
