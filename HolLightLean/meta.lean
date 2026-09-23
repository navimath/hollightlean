import HolLightLean.conectors

macro "finisher_tacs" : tactic =>
  `(tactic |
    first | rfl | lia | grind | (aesop; done) | done
  )

elab "epsilon_elim" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    Lean.Elab.Tactic.evalTactic (← `(tactic|try unfold NUMERAL BIT0 BIT1 at *))
    let goalType ← Lean.Elab.Tactic.getMainTarget
    let goalMvar ← Lean.Elab.Tactic.getMainGoal
    let some (_, lhs, rhs) := goalType.eq? | throwError "Goal is not an equality"
      let β ← Lean.Meta.inferType lhs
      let srtv ← Lean.Meta.whnf (← Lean.Meta.inferType β)
      let v := srtv.sortLevel!
      let_expr Classical.epsilon _ _ _ a := rhs
        | throwError "Right hand side is not of the form ε P r"
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

/--
After epsilon_tac, prove that λ_,f satisfies the total recursive inductive predicate.
-/
elab "epsilon_align_1_total_rec_nat"  : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
  intro;
  constructor <;> (
  (try intros)
  simp_all +arith;
  finisher_tacs
    )
  ))

elab "ind_on_2_of2" : tactic => do
Lean.Elab.Tactic.evalTactic (← `(tactic|
funext m;
induction m <;>
finisher_tacs
))

elab "ind_on_2_of3" : tactic => do
Lean.Elab.Tactic.evalTactic (← `(tactic|
funext m k;
induction m <;>
finisher_tacs
))

elab "ind_on_3" : tactic => do
Lean.Elab.Tactic.evalTactic (← `(tactic|
funext m k;
induction k <;>
finisher_tacs
))

/--
Now prove that λ_,f is the unique term satisfying P

∀ x, P x → P (λ_, f) → x = λ_,f
-/
elab "epsilon_align_2_total_rec_nat"  : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
  intros _ hP hPf;
  funext N;
  specialize hP N;
  specialize hPf N;
  first
  | ind_on_2_of2
  | ind_on_2_of3
  | ind_on_3
  ))

macro "epsilon_align_total" : tactic => `(tactic | (
  epsilon_elim ;
  epsilon_align_1_total_rec_nat;
  epsilon_align_2_total_rec_nat))

/--
Shared finishing step
-/
opaque partTacFinish (lemmaName : Lean.Name) (realArgs : Nat) (goalMvar : Lean.MVarId)
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

macro "epsilon_part_elim" Q:term : tactic =>
  `(tactic| first | part_tac_1 $Q | part_tac_2 $Q | part_tac_3 $Q)

/-
Once `epsilon_part_elim` has run, there are three goals left:

  1. `P f`, the Lean function satisfies the HOL specification.
  2.  The equality holds inside the predicate `Q`.
  3.  Uniqueness.
-/

macro "epsilon_part_g1" τ:term : tactic =>
  `(tactic| ((try intros)
             (try casesm* Prod _ _, prod _ _)
             first
               | (finisher_tacs; done)
               | (induction ‹$τ› <;> simp_all; done)
               | (induction ‹$τ› <;> finisher_tacs; done)))

macro "epsilon_part_g2" : tactic =>
  `(tactic| (intros
             (try casesm* Exists _, _ ∧ _)
             (try subst_vars)
             finisher_tacs))

macro "epsilon_part_g3" τ:term : tactic =>
  `(tactic| (intros
             (try casesm* Prod _ _, prod _ _)
             first
               | (induction ‹$τ› <;> simp_all; done)
               | (induction ‹$τ› <;> finisher_tacs; done)))

syntax "epsilon_align_partial" term : tactic

macro_rules
  | `(tactic| epsilon_align_partial (fun $x : $τ => $b)) =>
    `(tactic| (epsilon_part_elim (fun $x : $τ => $b)
               on_goal 3 => (try epsilon_part_g3 $τ)
               on_goal 2 => (try epsilon_part_g2)
               on_goal 1 => (try epsilon_part_g1 $τ)))

syntax (name := holInd) "ind_align" (" using " term)? : tactic

macro_rules
  | `(tactic| ind_align $[using $e]?) =>
    `(tactic|
      (funext x
       apply Eq.propIntro <;>
         first
           | (intro h P hP
              (first
                | induction h $[using $e]?
                | induction x, h $[using $e]?) <;> finisher_tacs)
           | (intro h; apply h; intro a hc; finisher_tacs)))

macro "gspec_align" : tactic =>
  `(tactic|
    (try unfold GSPEC SETSPEC id IN
     repeat funext _
     apply Eq.propIntro
     · intro h
       first
         | refine ⟨_, ?_, rfl⟩
         | refine ⟨_, _, ?_, rfl⟩
       first | exact h | finisher_tacs
     · first
         | (rintro ⟨_, h, heq⟩; subst heq)
         | (rintro ⟨_, _, h, heq⟩; subst heq)
       first | exact h | finisher_tacs))

macro "set_align" : tactic =>
  `(tactic|
    (try simp_all
     first
       | done
       | gspec_align
       | (repeat funext _
          apply Eq.propIntro <;> intro h <;>
            first | finisher_tacs | solve_by_elim | skip)))

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
