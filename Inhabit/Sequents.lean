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
    if ← matchConstInduct goalType.getAppFn
      (fun _ => return false)
      fun ival us => do
        for ctor in ival.ctors do
          try
            let newGoals ← goal.apply (mkConst ctor us) {}
            replaceMainGoal newGoals
            newGoals.forM $ fun newGoal => do
              if not $ ← seqsolve newGoal then
                failure
            return true /- TODO: This doesn't actually return -/
          catch _ =>
            pure ()
        return false
    then
      return true

    /- L→ -/

    /- L∧ -/

    /- L∨ -/

    return false

elab "seqsolve" : tactic =>
  withMainContext do
    let goals ← getGoals
    goals.forM $ fun goal => do
      let _ ← seqsolve goal

example {φ : Prop} : φ → φ := by
  seqsolve

example {φ : Prop} (h : φ) : φ := by
  seqsolve

example {φ : Prop} : False → φ := by
  seqsolve

example {φ : Prop} : (φ → φ) ∧ (φ → φ) := by
  seqsolve

example {φ : Prop} : False ∨ (φ → φ) := by
  seqsolve
