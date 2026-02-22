/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import Lean
import LeanTcb.Core
import LeanTcb.Format
import LeanTcb.Attr
import LeanTcb.Path
import LeanTcb.Tree

/-!
# `#tcb` command elaborator

Provides the `#tcb` and `#tcb!` commands for running TCB analysis
from within a Lean file and displaying results in the infoview.
-/

open Lean Elab Command Meta

namespace LeanTcb

/-- Emit a warning if Lake package info is unavailable. -/
private def warnIfNoPackageInfo : CommandElabM Unit := do
  let env ← getEnv
  if env.getModulePackage?.isNone then
    logWarning m!"Package info unavailable (non-Lake \
      build?) — all imported declarations classified as \
      'library'. Project-local results may be incomplete."

/-- Check project-local TCB members for soundness issues
    (sorry, native\_decide, unsafe) and emit warnings.
    Returns warning strings for inclusion in rendered output. -/
private def emitSoundnessWarnings (env : Environment)
    (specSet : Lean.NameSet)
    (missingNames : Lean.NameSet)
    : CommandElabM (Array String) := do
  let mut warnings : Array String := #[]
  let mut sorryWarned : Lean.NameSet := {}
  let mut nativeWarned : Lean.NameSet := {}
  for name in specSet do
    if isProjectLocal env name then
      let axs ← liftCoreM <| Lean.collectAxioms name
      if axs.contains `sorryAx then
        unless sorryWarned.contains name do
          sorryWarned := sorryWarned.insert name
          warnings := warnings.push
            s!"'{name}' depends on sorry — \
              proof is incomplete"
          logWarning m!"'{name}' depends on sorry — \
            proof is incomplete"
      if axs.contains ``Lean.ofReduceBool ||
          axs.contains ``Lean.ofReduceNat then
        unless nativeWarned.contains name do
          nativeWarned := nativeWarned.insert name
          warnings := warnings.push
            s!"'{name}' uses native_decide — \
              the Lean compiler is in the trust path"
          logWarning m!"'{name}' uses native_decide — \
            the Lean compiler is in the trust path"
  -- Note: `partial def` compiles to `opaqueInfo` in Lean
  -- 4.27.0, so ConstantInfo.isPartial never fires. The
  -- type-only traversal for opaqueInfo is already correct.
  for name in specSet do
    if let some ci := env.find? name then
      if ci.isUnsafe then
        warnings := warnings.push
          s!"'{name}' is unsafe — the kernel \
            provides weaker guarantees"
        if isProjectLocal env name then
          logWarning m!"'{name}' is unsafe — the \
            kernel provides weaker guarantees"
  for name in missingNames do
    logWarning m!"'{name}' was referenced but not \
      found — transitive dependencies unknown"
  return warnings

/-- `#tcb name₁ name₂ ...` analyses the trust boundary for the
    given entry points.
    `#tcb! name₁ ...` includes full library dependency listing. -/
syntax (name := tcbCmd) "#tcb" "!"? ident+ : command

@[command_elab tcbCmd]
def elabTcb : CommandElab := fun stx => do
  let verbose := !stx[1].isNone
  let ids := stx[2].getArgs
  let env ← getEnv
  warnIfNoPackageInfo

  let mut names : Array Name := #[]
  for id in ids do
    let name ← liftCoreM <|
      realizeGlobalConstNoOverloadWithInfo id
    names := names.push name

  match computeTcb env names with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isProjectLocal env n then acc.push n else acc

    let mut fr := formatResult env result allUserDecls
    let soundnessWarnings ← emitSoundnessWarnings env
      result.specSet result.missingNames
    fr := { fr with
      warnings := fr.warnings ++ soundnessWarnings }

    let userSpecNames := fr.userSpec.map (·.1)
    let checkAnns := tcb.checkAnnotations.get (← getOptions)
    let annCheck : Option AnnotationCheck :=
      if checkAnns then
        some (checkAnnotations env userSpecNames allUserDecls)
      else
        none
    let output := renderResult fr verbose annCheck

    if let some ac := annCheck then
      if ac.hasAnnotations then
        for name in ac.unannotated do
          logWarning m!"'{name}' is in the TCB but not \
            annotated @[tcb]"
        for name in ac.unnecessary do
          logWarning m!"'{name}' is annotated @[tcb] but \
            not in the computed TCB"

    logInfo m!"{output}"
  | .error msg =>
    throwError m!"TCB analysis failed: {msg}"

/-- `#tcb_tree name₁ ...` renders the dependency graph as an
    indented tree. `#tcb_tree!` expands library dependencies. -/
syntax (name := tcbTreeCmd) "#tcb_tree" "!"? ident+ : command

@[command_elab tcbTreeCmd]
def elabTcbTree : CommandElab := fun stx => do
  let expandLib := !stx[1].isNone
  let ids := stx[2].getArgs
  let env ← getEnv
  warnIfNoPackageInfo

  let mut names : Array Name := #[]
  for id in ids do
    let name ← liftCoreM <|
      realizeGlobalConstNoOverloadWithInfo id
    names := names.push name

  match computeTcbGraph env names with
  | .ok graph =>
    let _ ← emitSoundnessWarnings env
      graph.specSet graph.missingNames
    let opts : TreeRenderOpts := { expandLibrary := expandLib }
    let output := renderTree env graph opts
    logInfo m!"{output}"
  | .error msg =>
    throwError m!"TCB analysis failed: {msg}"

/-- `#tcb_why entryPoint target` shows the dependency path
    explaining why `target` is in the TCB of `entryPoint`. -/
syntax (name := tcbWhyCmd) "#tcb_why" ident ident : command

@[command_elab tcbWhyCmd]
def elabTcbWhy : CommandElab := fun stx => do
  let env ← getEnv
  warnIfNoPackageInfo
  let epId := stx[1]
  let tgtId := stx[2]
  let epName ← liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo epId
  let tgtName ← liftCoreM <|
    realizeGlobalConstNoOverloadWithInfo tgtId

  match computeTcbGraph env #[epName] with
  | .ok graph =>
    let _ ← emitSoundnessWarnings env
      graph.specSet graph.missingNames
    let output := renderPath env graph epName tgtName
    logInfo m!"{output}"
  | .error msg =>
    throwError m!"TCB analysis failed: {msg}"

end LeanTcb
