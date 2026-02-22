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

/-- Short label for a declaration's kind. -/
def declKindLabel (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo v =>
    match v.hints with
    | .abbrev => "abbrev"
    | _ => "def"
  | .thmInfo _    => "theorem"
  | .axiomInfo _  => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"
  | .quotInfo _   => "quot"

/-- Categorized output for display. -/
structure FormattedResult where
  entryPoints : Array Name
  axioms : Array (Name × Bool)  -- (name, isStandard)
  userSpec : Array (Name × String)  -- (name, kind label)
  librarySpec : Array Name
  userNotInTcb : Nat  -- user declarations NOT in spec
  deriving Inhabited

/-- Format a TcbResult for display. -/
def formatResult (env : Environment) (result : TcbResult) : FormattedResult := Id.run do
  let mut axioms : Array (Name × Bool) := #[]
  let mut userSpec : Array (Name × String) := #[]
  let mut librarySpec : Array Name := #[]

  for name in result.specSet.toList do
    match env.find? name with
    | some ci =>
      if ci matches .axiomInfo _ then
        axioms := axioms.push (name, standardAxioms.contains name)
      else if isCurrentModule env name then
        userSpec := userSpec.push (name, declKindLabel ci)
      else
        librarySpec := librarySpec.push name
    | none => ()

  -- Count user declarations not in spec
  let mut userNotInTcb : Nat := 0
  for name in result.proofInfra.toList do
    if isCurrentModule env name then
      userNotInTcb := userNotInTcb + 1

  let axiomsSorted := axioms.qsort (fun a b => Name.lt a.1 b.1)
  let userSpecSorted := userSpec.qsort (fun a b => Name.lt a.1 b.1)
  let librarySpecSorted := librarySpec.qsort (fun a b => Name.lt a b)

  return {
    entryPoints := result.entryPoints
    axioms := axiomsSorted
    userSpec := userSpecSorted
    librarySpec := librarySpecSorted
    userNotInTcb
  }

/-- Render the formatted result as a string for the infoview.
    When `verbose` is true, includes the full library dependency listing. -/
def renderResult (fr : FormattedResult) (verbose : Bool := false) : String := Id.run do
  let mut lines : Array String := #[]

  lines := lines.push "═══ TCB Analysis ═══"
  lines := lines.push ""

  -- Entry points
  lines := lines.push s!"Entry points: {fr.entryPoints.map Name.toString}"
  lines := lines.push ""

  -- Must review (user spec with kind labels)
  if fr.userSpec.size > 0 then
    lines := lines.push s!"── Must Review ({fr.userSpec.size} declarations) ──"
    -- Find max name length for alignment
    let maxLen := fr.userSpec.foldl (fun acc (n, _) => max acc (toString n).length) 0
    for (name, kind) in fr.userSpec do
      let nameStr := toString name
      let padding := String.ofList (List.replicate (maxLen - nameStr.length + 2) ' ')
      lines := lines.push s!"  • {nameStr}{padding}{kind}"
    lines := lines.push ""

  -- Axioms
  let stdAxioms := fr.axioms.filter (·.2)
  let nonStdAxioms := fr.axioms.filter (!·.2)
  lines := lines.push "── Axioms ──"
  if nonStdAxioms.size > 0 then
    lines := lines.push s!"  {nonStdAxioms.size} NON-STANDARD:"
    for (name, _) in nonStdAxioms do
      lines := lines.push s!"    ⚠ {name}"
  if stdAxioms.size > 0 then
    let stdNames := stdAxioms.map (fun (n, _) => toString n)
    lines := lines.push s!"  {stdAxioms.size} standard ({String.intercalate ", " stdNames.toList})"
  if fr.axioms.size == 0 then
    lines := lines.push "  none"
  lines := lines.push ""

  -- Library spec (verbose only)
  if verbose && fr.librarySpec.size > 0 then
    lines := lines.push s!"── Library Dependencies ({fr.librarySpec.size} declarations) ──"
    for name in fr.librarySpec do
      lines := lines.push s!"  • {name}"
    lines := lines.push ""

  -- Summary
  let userTotal := fr.userSpec.size + fr.userNotInTcb
  lines := lines.push "── Summary ──"
  let pctStr := if userTotal > 0 then s!" ({fr.userSpec.size * 100 / userTotal}% of project)" else ""
  lines := lines.push s!"  Must review:    {fr.userSpec.size} declarations{pctStr}"
  lines := lines.push s!"  Not in TCB:     {fr.userNotInTcb} declarations"
  lines := lines.push s!"  Depends on:     {fr.librarySpec.size} library declarations"

  return String.intercalate "\n" lines.toList

end LeanTcb
