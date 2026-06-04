import Lean.Elab.Tactic

open Lean Elab.Tactic Meta

partial def seqsolve (goal : MVarId) : TacticM Bool :=
  goal.withContext do
    /- Axiom -/
    if ← goal.assumptionCore then
      return true

    /- L⊥ -/
    if ← goal.contradictionCore {} then
      return true

    /- R→ -/
    let goalType ← goal.getType'
    if let .forallE _ _ _ _ := goalType then
      let (_, newGoal) ← goal.intro .anonymous
      replaceMainGoal [newGoal]
      let _ ← seqsolve newGoal
      return true

    /- R∧, R∨ -/
    /- TODO: Match on ∧, ∨ -/
    /- TODO: Success flag -/
    matchConstInduct goalType.getAppFn
      (fun _ => return)
      fun ival us => do
        for ctor in ival.ctors do
          try
            let newGoals ← goal.apply (mkConst ctor us) {}
            replaceMainGoal newGoals
            newGoals.forM $ fun newGoal => do
              if not $ ← seqsolve newGoal then
                failure
          catch _ =>
            pure ()
        return

    /- L→ -/

    /- L∧, L∨ -/
    /- TODO: Apply cases where possible -/

    return false

elab "seqsolve" : tactic =>
  withMainContext do
    let goals ← getGoals
    goals.forM $ fun goal => do
      let _ ← seqsolve goal

variable {φ ψ : Prop}

example : φ → φ := by
  seqsolve

example (h : φ) : φ := by
  seqsolve

example : False → φ := by
  seqsolve

example : (φ → φ) ∧ (φ → φ) := by
  seqsolve

example : False ∨ (φ → φ) := by
  seqsolve

example (h : φ ∧ ψ) : ψ := by
  cases h
  seqsolve
