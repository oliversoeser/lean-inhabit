import Lean.Elab.Tactic

open Lean Elab.Tactic Meta

partial def auto (goal : MVarId) : TacticM Unit :=
  goal.withContext do
    let goalType ← goal.getType'
    match goalType with
    | .bvar _ => throwError "encountered loose bound variable"
    | .fvar fvarId =>
      -- TODO: Search Local Context
      pure
    | .mvar mvarId => throwError "unhandled case: mvar"
    | .sort u => throwError "unhandled case: sort"
    | .const declName us => throwError "unhandled case: const"
    | .app fn arg => throwError "unhandled case: app"
    | .lam binderName binderType body binderInfo => throwError "unhandled case: lam"
    | .forallE binderName binderType body binderInfo => throwError "unhandled case: forallE"
    | .letE declName type value body nondep => throwError "unhandled case: letE"
    | .lit literal => throwError "unhandled case: lit"
    | .mdata data expr => throwError "unhandled case: mdata"
    | .proj typeName idx struct => throwError "unhandled case: proj"

    return

elab "auto" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    return ← auto goal

variable {φ ψ : Prop}

example (h : φ) : φ := by
  auto
  assumption
