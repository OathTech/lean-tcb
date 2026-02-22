import Lean
import LeanTcb.Types
import LeanTcb.Classify

open Lean

namespace LeanTcb

/-- The worklist-based TCB traversal.

    Starting from entry-point names, follows trust-relevant dependencies
    (type for theorems/axioms/opaques, type+value for defs, constructor
    types for inductives) and collects the transitive specification set.

    Marked `partial` because it provably terminates (finite environment)
    but proving this is not worth the effort for a meta-tool. -/
partial def computeTcb (env : Environment) (entryPoints : Array Name)
    : Except String TcbResult := do
  -- Validate entry points exist
  for ep in entryPoints do
    unless env.contains ep do
      throw s!"Entry point '{ep}' not found in environment"

  -- Worklist traversal
  let mut queue : Array Name := entryPoints
  let mut visited : Lean.NameSet := {}
  let mut specSet : Lean.NameSet := {}

  while h : queue.size > 0 do
    let name := queue[queue.size - 1]'(by omega)
    queue := queue.pop

    if visited.contains name then
      continue
    visited := visited.insert name

    -- Look up the declaration
    let some ci := env.find? name | continue
    -- We skip names not found — they could be internal / compiler-generated

    -- Add to spec set
    specSet := specSet.insert name

    -- Collect trust-relevant constants
    let exprs := trustRelevantExprs ci
    let refs := collectConstants exprs

    -- For inductives: also walk constructor types directly
    match ci with
    | .inductInfo v =>
      for ctorName in v.ctors do
        if let some ctorCi := env.find? ctorName then
          let ctorRefs := collectConstants #[ctorCi.type]
          for r in ctorRefs.toList do
            unless visited.contains r do
              queue := queue.push r
          -- The constructor itself is spec
          specSet := specSet.insert ctorName
          visited := visited.insert ctorName
    | _ => pure ()

    -- Enqueue all trust-relevant references
    for r in refs.toList do
      unless visited.contains r do
        queue := queue.push r

    -- Handle constructor → parent inductive
    if let some parent := ctorParentName ci then
      unless visited.contains parent do
        queue := queue.push parent

    -- Handle recursor → parent inductive
    if let some parent := recParentName ci then
      unless visited.contains parent do
        queue := queue.push parent

    -- Handle mutual blocks: enqueue all companions
    let companions := mutualCompanions env name
    for comp in companions do
      unless visited.contains comp do
        queue := queue.push comp

  -- Build proof-infrastructure set (all env constants not in spec)
  let proofInfra := env.constants.fold (init := ({} : Lean.NameSet)) fun acc n _ =>
    if !specSet.contains n then acc.insert n else acc

  return {
    entryPoints
    specSet
    proofInfra
  }

end LeanTcb
