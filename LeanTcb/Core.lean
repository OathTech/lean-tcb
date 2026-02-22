/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import Lean
import LeanTcb.Types
import LeanTcb.Classify

/-!
# Core worklist traversal

The main TCB computation: starting from entry-point names, follows
trust-relevant dependencies and collects the transitive spec set.
-/

open Lean

namespace LeanTcb

/-- Compute the TCB with full dependency provenance.

    Starting from entry-point names, follows trust-relevant
    dependencies (type for theorems/axioms/opaques, type+value
    for defs, constructor types for inductives) and collects the
    transitive specification set. Additionally records, for each
    discovered name, which parent enqueued it and why. Entry
    points have no parent (not in `parentMap`).

    Marked `partial` because it provably terminates (finite
    environment) but proving this is not worth the effort for
    a meta-tool. -/
partial def computeTcbGraph (env : Environment)
    (entryPoints : Array Name)
    : Except String TcbGraphResult := do
  for ep in entryPoints do
    unless env.contains ep do
      throw s!"Entry point '{ep}' not found in environment"

  let entrySet := entryPoints.foldl
    (fun acc n => acc.insert n) ({} : Lean.NameSet)

  let mut queue : Array Name := entryPoints
  let mut visited : Lean.NameSet := {}
  let mut specSet : Lean.NameSet := {}
  let mut missingNames : Lean.NameSet := {}
  let mut parentMap : Lean.NameMap (Name × DepReason) := {}
  let mut edgeList : Array (Name × Name × DepReason) := #[]

  while h : queue.size > 0 do
    let name := queue[queue.size - 1]'(by omega)
    queue := queue.pop

    if visited.contains name then
      continue
    visited := visited.insert name

    let some ci := env.find? name | do
      missingNames := missingNames.insert name
      continue

    specSet := specSet.insert name

    -- Compute refs with type/body distinction
    let typeRefs : Lean.NameSet := match ci with
      | .defnInfo v => collectConstants #[v.type]
      | _ => collectConstants (trustRelevantExprs ci)
    let mut bodyOnlyRefs : Lean.NameSet := {}
    match ci with
    | .defnInfo v =>
      let bodyRefs := collectConstants #[v.value]
      for n in bodyRefs do
        unless typeRefs.contains n do
          bodyOnlyRefs := bodyOnlyRefs.insert n
    | _ => pure ()

    -- For inductives: walk constructor types and add to spec
    match ci with
    | .inductInfo v =>
      for ctorName in v.ctors do
        match env.find? ctorName with
        | some ctorCi =>
          -- Record inductive as parent of its constructor
          edgeList := edgeList.push (name, ctorName,
            .inductCtor)
          unless parentMap.contains ctorName ||
              entrySet.contains ctorName do
            parentMap := parentMap.insert ctorName
              (name, .inductCtor)
          let ctorRefs := collectConstants #[ctorCi.type]
          for r in ctorRefs do
            edgeList := edgeList.push (ctorName, r,
              .exprRefType)
            unless visited.contains r do
              unless parentMap.contains r ||
                  entrySet.contains r do
                parentMap := parentMap.insert r
                  (ctorName, .exprRefType)
              queue := queue.push r
          specSet := specSet.insert ctorName
          visited := visited.insert ctorName
        | none =>
          missingNames := missingNames.insert ctorName
    | _ => pure ()

    for r in typeRefs do
      edgeList := edgeList.push (name, r, .exprRefType)
      unless visited.contains r do
        unless parentMap.contains r ||
            entrySet.contains r do
          parentMap := parentMap.insert r
            (name, .exprRefType)
        queue := queue.push r

    for r in bodyOnlyRefs do
      edgeList := edgeList.push (name, r, .exprRefBody)
      unless visited.contains r do
        unless parentMap.contains r ||
            entrySet.contains r do
          parentMap := parentMap.insert r
            (name, .exprRefBody)
        queue := queue.push r

    -- Constructor → parent inductive
    if let some parent := ctorParentName ci then
      edgeList := edgeList.push (name, parent, .ctorParent)
      unless visited.contains parent do
        unless parentMap.contains parent ||
            entrySet.contains parent do
          parentMap := parentMap.insert parent
            (name, .ctorParent)
        queue := queue.push parent

    -- Recursor → parent inductives
    for parent in recParentNames ci do
      edgeList := edgeList.push (name, parent, .recParent)
      unless visited.contains parent do
        unless parentMap.contains parent ||
            entrySet.contains parent do
          parentMap := parentMap.insert parent
            (name, .recParent)
        queue := queue.push parent

    -- Mutual blocks: enqueue all companions
    for comp in mutualCompanions env name do
      edgeList := edgeList.push (name, comp,
        .mutualCompanion)
      unless visited.contains comp do
        unless parentMap.contains comp ||
            entrySet.contains comp do
          parentMap := parentMap.insert comp
            (name, .mutualCompanion)
        queue := queue.push comp

  -- Build depsMap from flat edge list
  let mut listMap :
      Lean.NameMap (List (Name × DepReason)) := {}
  for (parent, child, reason) in edgeList do
    let lst := match listMap.find? parent with
      | some l => l
      | none   => []
    listMap := listMap.insert parent
      ((child, reason) :: lst)
  let mut depsMap :
      Lean.NameMap (Array (Name × DepReason)) := {}
  for (parent, lst) in listMap do
    depsMap := depsMap.insert parent lst.toArray

  return {
    entryPoints, specSet, missingNames, parentMap, depsMap
  }

/-- Compute the trusted computing base for the given entry points.

    Delegates to `computeTcbGraph` and projects out the graph
    metadata, keeping only the flat spec set. -/
def computeTcb (env : Environment)
    (entryPoints : Array Name)
    : Except String TcbResult :=
  (computeTcbGraph env entryPoints).map
    TcbGraphResult.toTcbResult

end LeanTcb
