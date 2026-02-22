import Lean
import LeanTcb.Core
import LeanTcb.Format

open Lean Elab Command Meta

namespace LeanTcb

/-- `#tcb name₁ name₂ ...` — analyse the trust boundary for the given entry points.

    Displays the specification / proof-infrastructure partition in the infoview. -/
syntax (name := tcbCmd) "#tcb " ident+ : command

@[command_elab tcbCmd]
def elabTcb : CommandElab := fun stx => do
  match stx with
  | `(#tcb $ids*) =>
    let env ← getEnv
    -- Resolve each identifier to a fully-qualified name
    let mut names : Array Name := #[]
    for id in ids do
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      names := names.push name

    -- Run the analysis
    match computeTcb env names with
    | .ok result =>
      let fr := formatResult env result
      let output := renderResult fr
      logInfo m!"{output}"
    | .error msg =>
      throwError m!"TCB analysis failed: {msg}"
  | _ => throwUnsupportedSyntax

end LeanTcb
