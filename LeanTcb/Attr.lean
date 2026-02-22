/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import Lean

/-!
# `@[tcb]` attribute and annotation checking

Provides the `@[tcb]` tag attribute for marking declarations as
expected TCB members, and cross-checking logic to compare annotations
against the computed spec set.
-/

open Lean

/-- When `true`, `#tcb` cross-checks computed TCB against
    `@[tcb]` annotations and warns about mismatches. -/
register_option tcb.checkAnnotations : Bool := {
  defValue := false
  descr := "Enable @[tcb] annotation cross-checking \
    in #tcb output"
}

namespace LeanTcb

/-- The `@[tcb]` attribute marks a declaration as an expected member
    of the trusted computing base. When `#tcb` runs, it cross-checks
    the computed spec set against these annotations and warns about
    mismatches. -/
-- Note: bare name `tcb` could collide with other libraries.
-- A namespaced name like `lean_tcb` would be safer but is a
-- breaking change. Deferred until an actual collision occurs.
initialize tcbAttr : TagAttribute ←
  registerTagAttribute `tcb
    "Marks a declaration as an expected TCB member."

/-- Check whether a name is covered by a `@[tcb]` annotation,
    either directly or because a parent name is annotated.

    This handles auto-generated companions: `@[tcb] inductive MyList`
    covers `MyList.nil`, `MyList.rec`, etc. and `@[tcb] def myFn`
    covers `myFn.match_1`, etc. -/
def isTcbAnnotated (env : Environment) (name : Name) : Bool :=
  tcbAttr.hasTag env name ||
  match name with
  | .str parent _ => isTcbAnnotated env parent
  | .num parent _ => isTcbAnnotated env parent
  | .anonymous => false

/-- Result of cross-checking computed TCB against annotations. -/
structure AnnotationCheck where
  /-- In the computed TCB but not covered by `@[tcb]`. -/
  unannotated : Array Name
  /-- Tagged `@[tcb]` but not in the computed TCB. -/
  unnecessary : Array Name
  /-- Whether any `@[tcb]` annotations exist in the module. -/
  hasAnnotations : Bool

/-- Walk up a name's hierarchy collecting any tagged ancestors
    into `acc`. Structurally recursive on `Name`. -/
private def collectUsedTags (taggedNames : Lean.NameSet)
    (name : Name) (acc : Lean.NameSet) : Lean.NameSet :=
  let acc := if taggedNames.contains name
    then acc.insert name else acc
  match name with
  | .str parent _ => collectUsedTags taggedNames parent acc
  | .num parent _ => collectUsedTags taggedNames parent acc
  | .anonymous => acc

/-- Cross-check computed TCB against `@[tcb]` annotations.
    Only considers current-module declarations. -/
def checkAnnotations (env : Environment)
    (userSpec : Array Name)
    (allUserDecls : Array Name) : AnnotationCheck := Id.run do
  let mut taggedNames : Lean.NameSet := {}
  for name in allUserDecls do
    if tcbAttr.hasTag env name then
      taggedNames := taggedNames.insert name

  if taggedNames.isEmpty then
    return {
      unannotated := #[]
      unnecessary := #[]
      hasAnnotations := false
    }

  let mut unannotated : Array Name := #[]
  let mut usedTags : Lean.NameSet := {}
  for name in userSpec do
    unless isTcbAnnotated env name do
      unannotated := unannotated.push name
    usedTags := collectUsedTags taggedNames name usedTags

  let mut unnecessary : Array Name := #[]
  for name in taggedNames do
    unless usedTags.contains name do
      unnecessary := unnecessary.push name

  return {
    unannotated := unannotated.qsort Name.lt
    unnecessary := unnecessary.qsort Name.lt
    hasAnnotations := true
  }

end LeanTcb
