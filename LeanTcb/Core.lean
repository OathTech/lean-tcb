/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
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

/-- Compute the trusted computing base for the given entry points.

    Starting from entry-point names, follows trust-relevant
    dependencies (type for theorems/axioms/opaques, type+value
    for defs, constructor types for inductives) and collects the
    transitive specification set.

    Marked `partial` because it provably terminates (finite
    environment) but proving this is not worth the effort for
    a meta-tool. -/
partial def computeTcb (env : Environment)
    (entryPoints : Array Name)
    : Except String TcbResult := do
  for ep in entryPoints do
    unless env.contains ep do
      throw s!"Entry point '{ep}' not found in environment"

  let mut queue : Array Name := entryPoints
  let mut visited : Lean.NameSet := {}
  let mut specSet : Lean.NameSet := {}
  let mut missingNames : Lean.NameSet := {}

  while h : queue.size > 0 do
    let name := queue[queue.size - 1]'(by omega)
    queue := queue.pop

    if visited.contains name then
      continue
    visited := visited.insert name

    -- Track names not found in the environment
    let some ci := env.find? name | do
      missingNames := missingNames.insert name
      continue

    specSet := specSet.insert name

    let exprs := trustRelevantExprs ci
    let refs := collectConstants exprs

    -- For inductives: walk constructor types and add to spec
    match ci with
    | .inductInfo v =>
      for ctorName in v.ctors do
        match env.find? ctorName with
        | some ctorCi =>
          let ctorRefs := collectConstants #[ctorCi.type]
          for r in ctorRefs do
            unless visited.contains r do
              queue := queue.push r
          specSet := specSet.insert ctorName
          visited := visited.insert ctorName
        | none =>
          missingNames := missingNames.insert ctorName
    | _ => pure ()

    for r in refs do
      unless visited.contains r do
        queue := queue.push r

    -- Constructor → parent inductive
    if let some parent := ctorParentName ci then
      unless visited.contains parent do
        queue := queue.push parent

    -- Recursor → parent inductives
    for parent in recParentNames ci do
      unless visited.contains parent do
        queue := queue.push parent

    -- Mutual blocks: enqueue all companions
    for comp in mutualCompanions env name do
      unless visited.contains comp do
        queue := queue.push comp

  return { entryPoints, specSet, missingNames }

/-- Compute the TCB with full dependency provenance.

    Same worklist algorithm as `computeTcb` but additionally records,
    for each discovered name, which parent enqueued it and why.
    Entry points have no parent (not in `parentMap`). -/
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

    let exprs := trustRelevantExprs ci
    let refs := collectConstants exprs

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
              .exprRef)
            unless visited.contains r do
              unless parentMap.contains r ||
                  entrySet.contains r do
                parentMap := parentMap.insert r
                  (ctorName, .exprRef)
              queue := queue.push r
          specSet := specSet.insert ctorName
          visited := visited.insert ctorName
        | none =>
          missingNames := missingNames.insert ctorName
    | _ => pure ()

    for r in refs do
      edgeList := edgeList.push (name, r, .exprRef)
      unless visited.contains r do
        unless parentMap.contains r ||
            entrySet.contains r do
          parentMap := parentMap.insert r (name, .exprRef)
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

end LeanTcb
