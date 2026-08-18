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

/--
Shared finishing step
-/
def partTacFinish (lemmaName : Lean.Name) (realArgs : Nat) (goalMvar : Lean.MVarId)
    (lhs a : Lean.Expr) (leadingArgs : Array (Option Lean.Expr)) (P : Lean.Expr) :
    Lean.Elab.Tactic.TacticM Unit := do
  let x := lhs.getAppPrefix ((Array.size lhs.getAppArgs) - realArgs)
  let β ← Lean.Meta.whnf (← Lean.Meta.inferType a)
  let f := .lam `_ β x .default
  let partial_app ← Lean.Meta.mkAppOptM lemmaName (leadingArgs ++ #[some f, P])
  let newMvars ← goalMvar.apply partial_app
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  Lean.Elab.Tactic.replaceMainGoal newMvars

elab "part_tac_1" Q:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let Q' ← Lean.Elab.Tactic.elabTerm Q none
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let goalMvar ← Lean.Elab.Tactic.getMainGoal
    match_expr goalType with
    | Eq _ lhs rhs =>
      match_expr rhs with
      | Classical.epsilon _ _ P a S =>
        partTacFinish `partial_align_1 1 goalMvar lhs a #[none, none, none, none, a, S, Q'] P
      | _ => throwError "Right hand side is not of the form ε P uv0 x"
    | _ => throwError "Goal is not an equality"

elab "part_tac_2" Q:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let Q' ← Lean.Elab.Tactic.elabTerm Q none
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let goalMvar ← Lean.Elab.Tactic.getMainGoal
    match_expr goalType with
    | Eq _ lhs rhs =>
      match_expr rhs with
      | Classical.epsilon _ _ P a x S =>
        let leadingArgs : Array (Option Lean.Expr) := #[none, none, none, none, none, a, x, S, Q']
        partTacFinish `partial_align_2 2 goalMvar lhs a leadingArgs P
      | _ => throwError "Right hand side is not of the form ε P uv0 x y"
    | _ => throwError "Goal is not an equality"

elab "part_tac_3" Q:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let Q' ← Lean.Elab.Tactic.elabTerm Q none
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let goalMvar ← Lean.Elab.Tactic.getMainGoal
    match_expr goalType with
    | Eq _ lhs rhs =>
      match_expr rhs with
      | Classical.epsilon _ _ P a x y S =>
        let leadingArgs : Array (Option Lean.Expr) :=
          #[none, none, none, none, none, none, none, a, x, y, S, Q']
        partTacFinish `partial_align_3 3 goalMvar lhs a leadingArgs P
      | _ => throwError "Right hand side is not of the form ε P uv0 x y z"
    | _ => throwError "Goal is not an equality"

macro "part_tac" Q:term : tactic =>
  `(tactic| first | part_tac_1 $Q | part_tac_2 $Q | part_tac_3 $Q)

/- elab "one_set_align"  : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    unfold GSPEC SETSPEC IN id;
    funext U x;
    apply Eq.propIntro <;> intro h;
    refine ⟨x, by trivial⟩;
    obtain ⟨x', h'⟩ := h;
    rw [h'.2];
    exact h'.1)) -/

/- structure Type' where
type : Type*
el : type

instance : CoeSort Type' Type where
coe A := A.type

instance {α : Type'} : Nonempty α := ⟨α.el⟩

def nat' : Type' := { type := Nat, el := Nat.zero}

def bool' : Type' := { type := Bool, el := true}

def test {a : Type'} := fun x : a => x

#check @test nat' 0

def z' : nat':= nat'.el

def arr (a : Type') (b : Type') : Type' := { type := a → b, el := fun _ => b.el}

def lambda' {a : Type'} {b : Type'} (f : a → b) : arr a b := f

def id' {a : Type'} := lambda' (fun x : a => x)

#check Sum

#check @id' (arr _ _) test
#check test id'
#check @test (arr _ _) test

noncomputable opaque eps {α : Type'} (P : α → Prop) : α := Classical.epsilon P

open Lean  PrettyPrinter Delaborator SubExpr
open TSyntax.Compat
macro "λ'" xs:explicitBinders " => " b:term : term => expandExplicitBinders ``lambda' xs b
infixr:26 " →' " => arr

/-- Delaborator for `Finset.prod`. The `pp.funBinderTypes` option controls whether
to show the domain type when the product is over `Finset.univ`. -/
@[app_delab Type'.type] meta def delabType'type : Delab :=
  whenPPOption getPPNotation <| withOverApp 1 do
  withAppArg delab

#check λ' x y : nat'=> z'

#check eps (fun _ : nat' => True) -/
