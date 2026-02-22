/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/
import Lean
import LeanTcb.Core
import LeanTcb.Format
import LeanTcb.Attr

/-!
# `#tcb` command elaborator

Provides the `#tcb` and `#tcb!` commands for running TCB analysis
from within a Lean file and displaying results in the infoview.
-/

open Lean Elab Command Meta

namespace LeanTcb

/-- `#tcb name₁ name₂ ...` analyses the trust boundary for the
    given entry points.
    `#tcb! name₁ ...` includes full library dependency listing. -/
syntax (name := tcbCmd) "#tcb" "!"? ident+ : command

@[command_elab tcbCmd]
def elabTcb : CommandElab := fun stx => do
  let verbose := !stx[1].isNone
  let ids := stx[2].getArgs
  let env ← getEnv

  let mut names : Array Name := #[]
  for id in ids do
    let name ← liftCoreM <|
      realizeGlobalConstNoOverloadWithInfo id
    names := names.push name

  match computeTcb env names with
  | .ok result =>
    let allUserDecls := env.constants.fold
      (init := (#[] : Array Name)) fun acc n _ =>
        if isCurrentModule env n then acc.push n else acc

    let mut fr := formatResult env result allUserDecls

    -- Check entry points for sorry and native_decide
    for ep in names do
      let axs ← liftCoreM <| Lean.collectAxioms ep
      if axs.contains `sorryAx then
        let w := s!"'{ep}' depends on sorry \
          (proof is incomplete)"
        fr := { fr with
          warnings := fr.warnings.push w }
        logWarning m!"'{ep}' depends on sorry — \
          proof is incomplete"
      if axs.contains ``Lean.ofReduceBool ||
          axs.contains ``Lean.ofReduceNat then
        let w := s!"'{ep}' uses native_decide \
          (the Lean compiler is in the trust path)"
        fr := { fr with
          warnings := fr.warnings.push w }
        logWarning m!"'{ep}' uses native_decide — \
          the Lean compiler is in the trust path"

    -- Check for unsafe and partial definitions in the TCB
    for name in result.specSet.toList do
      if let some ci := env.find? name then
        if ci.isUnsafe then
          let w := s!"'{name}' is unsafe — the kernel \
            provides weaker guarantees for this declaration"
          fr := { fr with
            warnings := fr.warnings.push w }
          if isCurrentModule env name then
            logWarning m!"'{name}' is unsafe — the \
              kernel provides weaker guarantees"
        if ci.isPartial then
          let w := s!"'{name}' is partial — it may not \
            terminate, which can affect soundness"
          fr := { fr with
            warnings := fr.warnings.push w }
          if isCurrentModule env name then
            logWarning m!"'{name}' is partial — it may \
              not terminate"

    let userSpecNames := fr.userSpec.map (·.1)
    let annCheck :=
      checkAnnotations env userSpecNames allUserDecls
    let output := renderResult fr verbose annCheck

    if annCheck.hasAnnotations then
      for name in annCheck.unannotated do
        logWarning m!"'{name}' is in the TCB but not \
          annotated @[tcb]"
      for name in annCheck.unnecessary do
        logWarning m!"'{name}' is annotated @[tcb] but \
          not in the computed TCB"

    logInfo m!"{output}"
  | .error msg =>
    throwError m!"TCB analysis failed: {msg}"

end LeanTcb
