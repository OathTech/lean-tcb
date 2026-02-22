import Lean
import LeanTcb.Types

open Lean

namespace LeanTcb

/-- Standard axioms that ship with Lean's core and are generally accepted. -/
private def standardAxioms : Lean.NameSet :=
  ({} : Lean.NameSet)
    |>.insert `propext
    |>.insert `Classical.choice
    |>.insert `Quot.sound

/-- Check whether a declaration was defined in the current module (not imported). -/
def isCurrentModule (env : Environment) (n : Name) : Bool :=
  env.getModuleIdxFor? n |>.isNone

/-- Categorized output for display. -/
structure FormattedResult where
  entryPoints : Array Name
  axioms : Array (Name × Bool)  -- (name, isStandard)
  userSpec : Array Name
  librarySpec : Array Name
  specCount : Nat
  proofInfraCount : Nat

/-- Format a TcbResult for display. -/
def formatResult (env : Environment) (result : TcbResult) : FormattedResult := Id.run do
  let mut axioms : Array (Name × Bool) := #[]
  let mut userSpec : Array Name := #[]
  let mut librarySpec : Array Name := #[]

  for name in result.specSet.toList do
    match env.find? name with
    | some (.axiomInfo _) =>
      axioms := axioms.push (name, standardAxioms.contains name)
    | some _ =>
      if isCurrentModule env name then
        userSpec := userSpec.push name
      else
        librarySpec := librarySpec.push name
    | none => ()

  -- Sort for stable output
  let axiomsSorted := axioms.qsort (fun a b => Name.lt a.1 b.1)
  let userSpecSorted := userSpec.qsort (fun a b => Name.lt a b)
  let librarySpecSorted := librarySpec.qsort (fun a b => Name.lt a b)

  return {
    entryPoints := result.entryPoints
    axioms := axiomsSorted
    userSpec := userSpecSorted
    librarySpec := librarySpecSorted
    specCount := result.specSet.size
    proofInfraCount := result.proofInfra.size
  }

/-- Render the formatted result as a string for the infoview. -/
def renderResult (fr : FormattedResult) : String := Id.run do
  let mut lines : Array String := #[]

  lines := lines.push "═══ TCB Analysis ═══"
  lines := lines.push ""

  -- Entry points
  lines := lines.push s!"Entry points: {fr.entryPoints.map Name.toString}"
  lines := lines.push ""

  -- Axioms
  if fr.axioms.size > 0 then
    lines := lines.push s!"── Axioms ({fr.axioms.size}) ──"
    for (name, isStd) in fr.axioms do
      let tag := if isStd then " [standard]" else " [NON-STANDARD]"
      lines := lines.push s!"  • {name}{tag}"
    lines := lines.push ""

  -- User spec
  if fr.userSpec.size > 0 then
    lines := lines.push s!"── User Specification ({fr.userSpec.size}) ──"
    for name in fr.userSpec do
      lines := lines.push s!"  • {name}"
    lines := lines.push ""

  -- Library spec
  if fr.librarySpec.size > 0 then
    lines := lines.push s!"── Library Specification ({fr.librarySpec.size}) ──"
    for name in fr.librarySpec do
      lines := lines.push s!"  • {name}"
    lines := lines.push ""

  -- Summary
  lines := lines.push "── Summary ──"
  let total := fr.specCount + fr.proofInfraCount
  lines := lines.push s!"  Specification (TCB):      {fr.specCount}"
  lines := lines.push s!"  Proof infrastructure:     {fr.proofInfraCount}"
  lines := lines.push s!"  Total declarations:       {total}"
  if total > 0 then
    let pct := (fr.specCount * 100) / total
    lines := lines.push s!"  TCB percentage:           {pct}%"

  return String.intercalate "\n" lines.toList

end LeanTcb
