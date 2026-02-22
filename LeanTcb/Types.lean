/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import Lean

/-!
# TCB analysis types

Core data types for the trust boundary classifier.
-/

open Lean

namespace LeanTcb

/-- Classification of axioms in the spec set. -/
inductive AxiomKind where
  /-- Ships with Lean core (propext, Classical.choice,
      Quot.sound). -/
  | standard
  /-- User-introduced or non-standard axiom. -/
  | nonStandard
  deriving Inhabited, BEq, Repr

instance : ToString AxiomKind where
  toString
    | .standard => "standard"
    | .nonStandard => "non-standard"

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

instance : ToString TcbResult where
  toString r :=
    s!"TcbResult(entryPoints={r.entryPoints.size}, \
      specSet={r.specSet.toList.length}, \
      missingNames={r.missingNames.toList.length})"

/-- Why a dependency was enqueued during traversal. -/
inductive DepReason where
  | exprRefType      -- referenced in type
  | exprRefBody      -- referenced in body (def/abbrev only)
  | ctorParent       -- constructor enqueued parent inductive
  | recParent        -- recursor enqueued parent inductive
  | mutualCompanion  -- mutual block companion
  | inductCtor       -- inductive enqueued its constructor
  deriving Inhabited, BEq, Repr

/-- Human-readable label for a `DepReason`. -/
def DepReason.label : DepReason → String
  | .exprRefType     => "referenced in type"
  | .exprRefBody     => "referenced in body"
  | .ctorParent      => "parent inductive (constructor)"
  | .recParent       => "parent inductive (recursor)"
  | .mutualCompanion => "mutual block companion"
  | .inductCtor      => "constructor"

instance : ToString DepReason where
  toString := DepReason.label

/-- TCB result with full dependency provenance. -/
structure TcbGraphResult where
  entryPoints : Array Name
  specSet : Lean.NameSet
  missingNames : Lean.NameSet := {}
  /-- For each non-entry-point name: (parent, reason). -/
  parentMap : Lean.NameMap (Name × DepReason)
  /-- Forward adjacency: for each name, all direct children
      discovered during traversal (with reason). May include
      edges to names in `missingNames`. Used for tree rendering
      to capture all edges, not just the discovery-tree edges
      in `parentMap`. -/
  depsMap : Lean.NameMap (Array (Name × DepReason)) := {}
  deriving Inhabited

instance : ToString TcbGraphResult where
  toString g :=
    s!"TcbGraphResult(entryPoints={g.entryPoints.size}, \
      specSet={g.specSet.toList.length}, \
      missingNames={g.missingNames.toList.length})"

def TcbGraphResult.toTcbResult (g : TcbGraphResult) : TcbResult :=
  { entryPoints := g.entryPoints
    specSet := g.specSet
    missingNames := g.missingNames }

end LeanTcb
