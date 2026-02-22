/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
import Lean
import LeanTcb.Types
import LeanTcb.Attr

/-!
# Output formatting

Groups the raw `TcbResult` into user-facing categories (axioms,
user specification, library dependencies) and renders them for
the Lean infoview.
-/

open Lean

namespace LeanTcb

/-- Standard axioms that ship with Lean's core. -/
private def standardAxioms : Lean.NameSet :=
  ({} : Lean.NameSet)
    |>.insert `propext
    |>.insert `Classical.choice
    |>.insert `Quot.sound

/-- Whether a declaration belongs to the same Lake package as the
    current module (i.e., is "project-local" rather than from an
    external library dependency). Declarations defined in the
    current file (no module index) are always project-local. -/
def isProjectLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true  -- defined in the current file
  | some idx =>
    -- Compare package IDs; none = bootstrap/core = external
    match env.getModulePackageByIdx? idx, env.getModulePackage? with
    | some pkg, some currentPkg => pkg == currentPkg
    | _, _ => false

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
  /-- Entry-point names that seeded the analysis. -/
  entryPoints : Array Name
  /-- Axioms in the spec set, with standard/non-standard tag. -/
  axioms : Array (Name × Bool)
  /-- Current-module declarations in the spec set. -/
  userSpec : Array (Name × String)
  /-- Imported declarations in the spec set. -/
  librarySpec : Array Name
  /-- Current-module declarations NOT in the spec set. -/
  userNotInTcb : Nat
  /-- Warnings about soundness issues (sorry, native_decide, etc.). -/
  warnings : Array String := #[]
  deriving Inhabited

/-- Format a `TcbResult` into categorized groups for display.
    `allUserDecls` should contain all declaration names from
    the current module. -/
def formatResult (env : Environment) (result : TcbResult)
    (allUserDecls : Array Name) : FormattedResult :=
    Id.run do
  let mut axioms : Array (Name × Bool) := #[]
  let mut userSpec : Array (Name × String) := #[]
  let mut librarySpec : Array Name := #[]

  for name in result.specSet.toList do
    match env.find? name with
    | some ci =>
      if ci matches .axiomInfo _ then
        let isStd := standardAxioms.contains name
        axioms := axioms.push (name, isStd)
      else if isProjectLocal env name then
        userSpec := userSpec.push (name, declKindLabel ci)
      else
        librarySpec := librarySpec.push name
    | none => ()

  let mut userNotInTcb : Nat := 0
  for name in allUserDecls do
    unless result.specSet.contains name do
      userNotInTcb := userNotInTcb + 1

  let mut warnings : Array String := #[]
  for name in result.missingNames.toList do
    warnings := warnings.push
      s!"Name '{name}' was referenced but not found in \
        the environment — its transitive dependencies are \
        unknown and may be missing from this analysis"

  return {
    entryPoints := result.entryPoints
    axioms := axioms.qsort (fun a b => Name.lt a.1 b.1)
    userSpec := userSpec.qsort (fun a b => Name.lt a.1 b.1)
    librarySpec := librarySpec.qsort Name.lt
    userNotInTcb
    warnings
  }

/-- Render a formatted result as a string for the infoview.
    Set `verbose` to include the full library dependency listing.
    Pass `annCheck` to include annotation cross-check results. -/
def renderResult (fr : FormattedResult)
    (verbose : Bool := false)
    (annCheck : Option AnnotationCheck := none)
    : String := Id.run do
  let mut lines : Array String := #[]

  lines := lines.push "═══ TCB Analysis ═══"
  lines := lines.push ""

  -- Entry points
  let epNames := fr.entryPoints.map Name.toString
  lines := lines.push s!"Entry points: {epNames}"
  lines := lines.push ""

  -- Must review
  if fr.userSpec.size > 0 then
    let n := fr.userSpec.size
    lines := lines.push s!"── Must Review ({n} declarations) ──"
    let maxLen := fr.userSpec.foldl
      (fun acc (n, _) => max acc (toString n).length) 0
    for (name, kind) in fr.userSpec do
      let nameStr := toString name
      let pad := maxLen - nameStr.length + 2
      let padding := String.ofList (List.replicate pad ' ')
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
    let names := stdAxioms.map (fun (n, _) => toString n)
    let joined := String.intercalate ", " names.toList
    lines := lines.push s!"  {stdAxioms.size} standard ({joined})"
  if fr.axioms.size == 0 then
    lines := lines.push "  none"
  lines := lines.push ""

  -- Library spec (verbose only)
  if verbose && fr.librarySpec.size > 0 then
    let n := fr.librarySpec.size
    lines := lines.push
      s!"── Library Dependencies ({n} declarations) ──"
    for name in fr.librarySpec do
      lines := lines.push s!"  • {name}"
    lines := lines.push ""

  -- Annotation check
  if let some ac := annCheck then
    if ac.hasAnnotations then
      lines := lines.push "── @[tcb] Annotation Check ──"
      if ac.unannotated.size > 0 then
        let n := ac.unannotated.size
        lines := lines.push
          s!"  {n} in TCB but not annotated:"
        for name in ac.unannotated do
          lines := lines.push s!"    ⚠ {name}"
      if ac.unnecessary.size > 0 then
        let n := ac.unnecessary.size
        lines := lines.push
          s!"  {n} annotated but not in TCB:"
        for name in ac.unnecessary do
          lines := lines.push s!"    ✗ {name}"
      if ac.unannotated.isEmpty && ac.unnecessary.isEmpty then
        lines := lines.push
          "  ✓ All annotations match the computed TCB"
      lines := lines.push ""

  -- Warnings
  if fr.warnings.size > 0 then
    lines := lines.push "── Warnings ──"
    for w in fr.warnings do
      lines := lines.push s!"  ⚠ {w}"
    lines := lines.push ""

  -- Summary
  let userTotal := fr.userSpec.size + fr.userNotInTcb
  lines := lines.push "── Summary ──"
  let pctStr := if userTotal > 0
    then s!" ({fr.userSpec.size * 100 / userTotal}% of project)"
    else ""
  let n := fr.userSpec.size
  lines := lines.push s!"  Must review:    {n} declarations{pctStr}"
  lines := lines.push
    s!"  Not in TCB:     {fr.userNotInTcb} declarations"
  lines := lines.push
    s!"  Depends on:     {fr.librarySpec.size} library declarations"

  return String.intercalate "\n" lines.toList

end LeanTcb
