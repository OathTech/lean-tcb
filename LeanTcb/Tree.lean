/- Copyright (c) 2026 the lean-tcb contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import Lean
import LeanTcb.Types
import LeanTcb.Format

/-!
# TCB dependency tree rendering

Renders a `TcbGraphResult` as an indented tree (like the Unix `tree`
command), showing the chain of trust-relevant dependencies from each
entry point down to leaves. Supports DAG dedup (`(see above)`) and
library dependency collapsing.
-/

open Lean

namespace LeanTcb

/-- Options for tree rendering. -/
structure TreeRenderOpts where
  /-- When `false` (default), non-project-local deps are collapsed
      to `[N library dependencies]`. When `true`, they are expanded
      like project-local deps. -/
  expandLibrary : Bool := false

/-- Look up children in a NameMap, returning `#[]` if absent. -/
private def findChildren
    (m : Lean.NameMap (Array (Name × DepReason)))
    (name : Name) : Array (Name × DepReason) :=
  match m.find? name with
  | some arr => arr
  | none     => #[]

/-- Sort and deduplicate the deps map for deterministic output.
    When a child appears multiple times under the same parent
    (e.g., via both `exprRef` and `recParent`), prefer the more
    specific structural reason over generic `exprRef`. -/
private def sortDepsMap (graph : TcbGraphResult)
    : Lean.NameMap (Array (Name × DepReason)) := Id.run do
  let mut sorted : Lean.NameMap (Array (Name × DepReason)) := {}
  for (parent, arr) in graph.depsMap do
    let mut reasonMap : Lean.NameMap DepReason := {}
    let mut order : Array Name := #[]
    for (child, reason) in arr do
      match reasonMap.find? child with
      | none =>
        reasonMap := reasonMap.insert child reason
        order := order.push child
      | some prev =>
        -- Prefer structural reasons over generic exprRef
        match prev, reason with
        | .exprRef, _ => reasonMap := reasonMap.insert child reason
        | _, _ => pure ()
    let deduped := order.filterMap fun child =>
      match reasonMap.find? child with
      | some r => some (child, r)
      | none => none
    sorted := sorted.insert parent
      (deduped.qsort fun a b => Name.lt a.1 b.1)
  return sorted

/-- Render a single tree rooted at `name`.

    `indent` is the indentation string for the current level.
    `isRoot` indicates the top-level entry point (no connector).
    `seen` tracks already-rendered nodes for DAG dedup.
    Returns `(lines, updatedSeen)`. -/
private partial def renderNode
    (env : Environment)
    (childrenMap : Lean.NameMap (Array (Name × DepReason)))
    (opts : TreeRenderOpts)
    (localNames : Lean.NameSet)
    (name : Name)
    (reason : Option DepReason)
    (indent : String)
    (isLast : Bool)
    (isRoot : Bool)
    (seen : Lean.NameSet)
    : Array String × Lean.NameSet := Id.run do
  let kindStr := match env.find? name with
    | some ci => s!" [{declKindLabel ci}]"
    | none    => ""
  let reasonStr := match reason with
    | some r => s!" ← {r.label}"
    | none   => ""

  let connector := if isRoot then "" else
    if isLast then "└── " else "├── "

  -- Check if already rendered (DAG dedup)
  if seen.contains name then
    let line :=
      s!"{indent}{connector}{name}{kindStr}\
        {reasonStr} (see above)"
    return (#[line], seen)

  let mut seen := seen.insert name
  let children := findChildren childrenMap name

  -- Separate library vs project-local children
  let mut projectChildren :
      Array (Name × DepReason) := #[]
  let mut libCount : Nat := 0
  if opts.expandLibrary then
    projectChildren := children
  else
    for (child, r) in children do
      if localNames.contains child then
        projectChildren := projectChildren.push (child, r)
      else
        libCount := libCount + 1

  let allChildren :=
    if !opts.expandLibrary && libCount > 0 then
      projectChildren.push
        (`_leanTcb.libPlaceholder, .exprRef)
    else
      projectChildren

  if allChildren.isEmpty then
    let line :=
      s!"{indent}{connector}{name}{kindStr}{reasonStr}"
    return (#[line], seen)

  let line :=
    s!"{indent}{connector}{name}{kindStr}{reasonStr}"
  let mut lines : Array String := #[line]
  let childIndent := if isRoot then "" else
    indent ++ (if isLast then "    " else "│   ")

  for i in [:allChildren.size] do
    let (child, r) := allChildren[i]!
    let childIsLast := i == allChildren.size - 1
    if child == `_leanTcb.libPlaceholder then
      let childConnector :=
        if childIsLast then "└── " else "├── "
      let depWord :=
        if libCount == 1 then "dependency" else "dependencies"
      let libLine :=
        s!"{childIndent}{childConnector}\
          [{libCount} library {depWord}]"
      lines := lines.push libLine
    else
      let (childLines, newSeen) := renderNode env
        childrenMap opts localNames child (some r)
        childIndent childIsLast false seen
      seen := newSeen
      for l in childLines do
        lines := lines.push l

  return (lines, seen)

/-- Render the full dependency tree for a `TcbGraphResult`. -/
def renderTree (env : Environment) (graph : TcbGraphResult)
    (opts : TreeRenderOpts := {}) : String := Id.run do
  let childrenMap := sortDepsMap graph
  -- Pre-compute project-local names for O(1) lookup
  let mut localNames : Lean.NameSet := {}
  for name in graph.specSet do
    if isProjectLocal env name then
      localNames := localNames.insert name
  let mut allLines : Array String := #[]
  allLines := allLines.push "═══ TCB Dependency Tree ═══"
  allLines := allLines.push ""

  let mut seen : Lean.NameSet := {}
  for ep in graph.entryPoints do
    let (lines, newSeen) := renderNode env childrenMap opts
      localNames ep none "" true true seen
    seen := newSeen
    for l in lines do
      allLines := allLines.push l
    allLines := allLines.push ""

  return String.intercalate "\n" allLines.toList

end LeanTcb
