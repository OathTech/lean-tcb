/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import Lean
import LeanTcb.Types
import LeanTcb.Format

/-!
# TCB path query

Given a `TcbGraphResult`, finds and renders the dependency path from
an entry point to a target declaration, answering "why is X in the
TCB?"
-/

open Lean

namespace LeanTcb

/-- Walk parent pointers from `target` back to an entry point.

    Returns `none` if `target` is not in the spec set.
    The returned array is ordered entry point → target, with each
    element carrying an optional `DepReason` (`none` for the entry
    point itself). -/
def findPath (graph : TcbGraphResult) (target : Name)
    : Option (Array (Name × Option DepReason)) :=
  if !graph.specSet.contains target then none
  else Id.run do
    -- Walk backwards from target to entry point
    let mut chain : Array (Name × Option DepReason) := #[]
    let mut cur := target
    -- Guard: at most specSet.size steps to avoid infinite loops
    let mut fuel := graph.specSet.size
    while fuel > 0 do
      fuel := fuel - 1
      match graph.parentMap.find? cur with
      | some (parent, reason) =>
        chain := chain.push (cur, some reason)
        cur := parent
      | none =>
        -- cur is an entry point (or has no parent)
        chain := chain.push (cur, none)
        -- Reverse to get entry point → target order
        return some chain.reverse
    -- Exhausted fuel — shouldn't happen in a well-formed graph
    return none

/-- Render a dependency path for the infoview. -/
def renderPath (env : Environment) (graph : TcbGraphResult)
    (entryPoint : Name) (target : Name) : String := Id.run do
  unless graph.specSet.contains target do
    return s!"{target} is not in the TCB of {entryPoint}."

  let entrySet := graph.entryPoints.foldl
    (fun acc n => acc.insert n) ({} : Lean.NameSet)
  if entrySet.contains target then
    return s!"{target} is itself an entry point."

  match findPath graph target with
  | none => return s!"{target} is not in the TCB of {entryPoint}."
  | some path =>
    let mut lines : Array String := #[]
    let epStr := toString entryPoint
    let tgtStr := toString target
    lines := lines.push
      s!"═══ TCB Path: {epStr} → {tgtStr} ═══"
    lines := lines.push ""
    for (name, reason) in path do
      let kindStr := match env.find? name with
        | some ci => s!" [{declKindLabel ci}]"
        | none    => ""
      match reason with
      | none =>
        lines := lines.push s!"  ● {name}{kindStr}"
      | some r =>
        lines := lines.push
          s!"  → {name}{kindStr} ← {r.label}"
    return String.intercalate "\n" lines.toList

end LeanTcb
