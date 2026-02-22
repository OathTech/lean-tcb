import Lean
import LeanTcb.Types

open Lean

namespace LeanTcb

/-- Return the expressions whose referenced constants are trust-relevant
    dependencies of the given declaration.

    The key semantic model:
    - `def`/`abbrev`: type + value (body defines meaning)
    - `theorem`: type only (proof is kernel-checked)
    - `axiom`: type only (no body)
    - `opaque`: type only (body is hidden from consumers)
    - `inductive`: type + constructor types
    - `constructor`: type (parent inductive handled separately)
    - `recursor`: type only -/
def trustRelevantExprs (ci : ConstantInfo) : Array Expr :=
  match ci with
  | .defnInfo v   => #[v.type, v.value]
  | .thmInfo v    => #[v.type]
  | .axiomInfo v  => #[v.type]
  | .opaqueInfo v => #[v.type]
  | .inductInfo v =>
    #[v.type] ++ v.ctors.toArray.map fun _ => default -- placeholder; ctors handled via enqueue
  | .ctorInfo v   => #[v.type]
  | .recInfo v    => #[v.type]
  | .quotInfo v   => #[v.type]

/-- Collect all constant names referenced in the given expressions. -/
def collectConstants (exprs : Array Expr) : Lean.NameSet :=
  exprs.foldl (fun acc e => e.foldConsts acc fun n s => s.insert n) {}

/-- For an inductive, return its constructor names. -/
def inductiveCtorNames (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some (.inductInfo v) => v.ctors.toArray
  | _ => #[]

/-- For a constructor, return its parent inductive name. -/
def ctorParentName (ci : ConstantInfo) : Option Name :=
  match ci with
  | .ctorInfo v => some v.induct
  | _ => none

/-- For a recursor, return its parent inductive name. -/
def recParentName (ci : ConstantInfo) : Option Name :=
  match ci with
  | .recInfo v => v.all.head?
  | _ => none

/-- Get all names in the same mutual block, if any. -/
def mutualCompanions (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some (.defnInfo v)  =>
    if v.all.length > 1 then v.all.toArray else #[]
  | some (.thmInfo v)   =>
    if v.all.length > 1 then v.all.toArray else #[]
  | some (.inductInfo v) =>
    if v.all.length > 1 then v.all.toArray else #[]
  | _ => #[]

end LeanTcb
