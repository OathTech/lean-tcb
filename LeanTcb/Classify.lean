/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
import Lean
import LeanTcb.Types

/-!
# Per-declaration classification

Determines which expressions to walk for each declaration kind.
This encodes the core semantic model: def bodies are specification,
theorem proofs are not.
-/

open Lean

namespace LeanTcb

/-- Return the expressions whose referenced constants are
    trust-relevant dependencies of the given declaration.

    The key semantic model:
    - `def`/`abbrev`: type + value (body defines meaning)
    - `theorem`: type only (proof is kernel-checked)
    - `axiom`: type only (no body)
    - `opaque`: type only (body is hidden from consumers)
    - `inductive`: type only (constructor types walked separately)
    - `constructor`: type (parent inductive handled separately)
    - `recursor`: type only
    - `quot`: type only -/
def trustRelevantExprs (ci : ConstantInfo) : Array Expr :=
  match ci with
  | .defnInfo v   => #[v.type, v.value]
  | .thmInfo v    => #[v.type]
  | .axiomInfo v  => #[v.type]
  | .opaqueInfo v => #[v.type]
  | .inductInfo v => #[v.type]
  | .ctorInfo v   => #[v.type]
  | .recInfo v    => #[v.type]
  | .quotInfo v   => #[v.type]

/-- Collect all constant names referenced in an array of expressions. -/
def collectConstants (exprs : Array Expr) : Lean.NameSet :=
  exprs.foldl (fun acc e =>
    e.foldConsts acc fun n s => s.insert n) {}

/-- For a constructor, return its parent inductive name. -/
def ctorParentName (ci : ConstantInfo) : Option Name :=
  match ci with
  | .ctorInfo v => some v.induct
  | _ => none

/-- For a recursor, return the names of all parent inductives. -/
def recParentNames (ci : ConstantInfo) : Array Name :=
  match ci with
  | .recInfo v => v.all.toArray
  | _ => #[]

/-- Get all names in the same mutual block, if any.
    Returns empty if the declaration is not part of a mutual block. -/
def mutualCompanions (env : Environment) (name : Name)
    : Array Name :=
  match env.find? name with
  | some (.defnInfo v)   =>
    if v.all.length > 1 then v.all.toArray else #[]
  | some (.thmInfo v)    =>
    if v.all.length > 1 then v.all.toArray else #[]
  | some (.inductInfo v) =>
    if v.all.length > 1 then v.all.toArray else #[]
  | _ => #[]

end LeanTcb
