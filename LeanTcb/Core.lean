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

  while h : queue.size > 0 do
    let name := queue[queue.size - 1]'(by omega)
    queue := queue.pop

    if visited.contains name then
      continue
    visited := visited.insert name

    -- Skip names not found (internal / compiler-generated)
    let some ci := env.find? name | continue

    specSet := specSet.insert name

    let exprs := trustRelevantExprs ci
    let refs := collectConstants exprs

    -- For inductives: walk constructor types and add to spec
    match ci with
    | .inductInfo v =>
      for ctorName in v.ctors do
        if let some ctorCi := env.find? ctorName then
          let ctorRefs := collectConstants #[ctorCi.type]
          for r in ctorRefs.toList do
            unless visited.contains r do
              queue := queue.push r
          specSet := specSet.insert ctorName
          visited := visited.insert ctorName
    | _ => pure ()

    for r in refs.toList do
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

  return { entryPoints, specSet }

end LeanTcb
