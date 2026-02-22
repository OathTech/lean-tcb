/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
import Lean

/-!
# `@[tcb]` attribute and annotation checking

Provides the `@[tcb]` tag attribute for marking declarations as
expected TCB members, and cross-checking logic to compare annotations
against the computed spec set.
-/

open Lean

namespace LeanTcb

/-- The `@[tcb]` attribute marks a declaration as an expected member
    of the trusted computing base. When `#tcb` runs, it cross-checks
    the computed spec set against these annotations and warns about
    mismatches. -/
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

  let userSpecSet := userSpec.foldl
    (fun acc n => acc.insert n) ({} : Lean.NameSet)

  let mut unannotated : Array Name := #[]
  for name in userSpec do
    unless isTcbAnnotated env name do
      unannotated := unannotated.push name

  let mut unnecessary : Array Name := #[]
  for name in taggedNames.toList do
    unless userSpecSet.contains name do
      unnecessary := unnecessary.push name

  return {
    unannotated := unannotated.qsort Name.lt
    unnecessary := unnecessary.qsort Name.lt
    hasAnnotations := true
  }

end LeanTcb
