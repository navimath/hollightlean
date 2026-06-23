import HolLightLean.conectors

elab "epsilon_tac" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    Lean.Elab.Tactic.evalTactic (← `(tactic|try unfold NUMERAL BIT0 BIT1 at *))
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let goalMvar ← Lean.Elab.Tactic.getMainGoal
    match_expr goalType with
    | Eq _ lhs rhs =>
      let β ← Lean.Meta.inferType lhs
      let srtv ← Lean.Meta.whnf (← Lean.Meta.inferType β)
      let v := srtv.sortLevel!
      match_expr rhs with
      | Classical.epsilon _ _ _ a =>
        let α' ← Lean.Meta.inferType a
        let α := .forallE `x α' β .default
        let srtu ← Lean.Meta.whnf (← Lean.Meta.inferType α)
        let u := srtu.sortLevel!
        let w ← Lean.Meta.mkFreshLevelMVar
        let a2 ← Lean.Meta.mkFreshExprMVar α
        let a1 := .lam `x α' lhs .default
        Lean.Meta.withLocalDecl `x default α fun g => do
          let f : Lean.Expr ← Lean.Meta.mkLambdaFVars #[g] (Lean.mkApp g a)
          let congrApp := Lean.mkAppN (.const ``congrArg [u, v]) #[α, β, a1, a2, f]
          let newMvars ← goalMvar.apply congrApp
          let [newGoal] := newMvars | unreachable!
          let newMvars ← newGoal.apply (.const ``align_epsilon [w])
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          Lean.Elab.Tactic.replaceMainGoal newMvars
        | _ => throwError "Right hand side is not of the form ε P r"
    | _ => throwError "Goal is not an equality"

elab "part_tac_1" Q:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let Q' ←  Lean.Elab.Tactic.elabTerm Q none
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let goalMvar ← Lean.Elab.Tactic.getMainGoal
    match_expr goalType with
    | Eq _ lhs rhs =>
      let α ← Lean.Meta.whnf (← Lean.Meta.inferType lhs)
      let u ← Lean.Meta.getDecLevel α
      let x := lhs.getAppPrefix ((Array.size lhs.getAppArgs) - 1)
      let some ne ← Lean.Meta.synthInstance? (.app (.const ``Nonempty [u.succ]) α)
      | throwError "Failed to find an instance of Nonempty {α} in the context."
      match_expr rhs with
        | Classical.epsilon _ _ P a S =>
          let β ← Lean.Meta.whnf (← Lean.Meta.inferType a)
          let v ← Lean.Meta.getDecLevel β
          let γ ← Lean.Meta.whnf (← Lean.Meta.inferType S)
          let w ← Lean.Meta.getDecLevel γ
          let f := .lam `_ β x .default
          let partial_app := Lean.mkAppN
            (.const ``partial_align_1 [v,w,u])
            #[β, γ, α, ne, a, S, Q', f, P]
          let newMvars ← goalMvar.apply partial_app
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          Lean.Elab.Tactic.replaceMainGoal newMvars
        | _ => throwError "Right hand side is not of the form ε P a r"
    | _ => throwError "Goal is not an equality"
