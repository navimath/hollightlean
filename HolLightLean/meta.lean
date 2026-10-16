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
induction m
))

elab "ind_on_2_of3" : tactic => do
Lean.Elab.Tactic.evalTactic (← `(tactic|
funext m _;
induction m
))

elab "ind_on_3" : tactic => do
Lean.Elab.Tactic.evalTactic (← `(tactic|
funext _ k;
induction k
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
    | (ind_on_2_of2 <;> finisher_tacs)
    | (ind_on_2_of3 <;> finisher_tacs)
    | (ind_on_3 <;> finisher_tacs)
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

/--
Define attribute to generate (human) readable theorems
from HolTheory instance and exported theorems

- generate a theorem hol_<name> (without the thm_ part)
- First unfold the projections using the HolTheory class and the instance
  - Hence the attribute will require and argument: A class instance
- Then, apply syntatic sugars (e.g, real_add → +) to make it (human) readable

Usage: `@[hol_readable holTheoryInst]` or `@[hol_readable holTheoryInst [real_add]]`,
where the optional list adds sugar lemmas to the `hol_sugar` simp set.
The attribute can only be used in files importing this one; in this file use the
command `hol_readable thm_<name> using <instance> [<sugar lemmas>]` (see the MWE below).
-/
syntax (name := holReadable) "hol_readable " term:max (" [" ident,* "]")? : attr

-- simp set of syntactic sugars, e.g. `real_add : real_add = @Add.add ℝ _`
register_simp_attr hol_sugar

section HolReadable
open Lean Meta Elab Term

--function that unfolds the projections: basically (thm_<name> <instance>)
/-- Unfold the projections of class `className` applied to an instance,
e.g. `@HOLTheory.real_add holTheoryInst x y` ↦ `real_add x y`. -/
def unfoldInstProjections (className : Name) (e : Expr) : MetaM Expr :=
  transform e (post := fun e => do
    if let .const f _ := e.getAppFn then
      if let some info ← getProjectionFnInfo? f then
        if info.fromClass && info.ctorName.getPrefix == className then
          if let some e' ← unfoldProjInst? e then
            return .visit e'
    return .continue)

/-- Rewrite `e` with the `hol_sugar` simp set and the extra lemmas `sugar`. -/
def applyHolSugar (e : Expr) (sugar : Array Name) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  if let some ext ← getSimpExtension? `hol_sugar then
    thms ← ext.getTheorems
  for l in sugar do
    thms ← thms.addConst l
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  return (← simp e ctx).1

/-- `thm_<name>` ↦ `hol_<name>`, in the same namespace. -/
def holReadableName : Name → Name
  | .str p s =>
    .str p ("hol_" ++ if s.startsWith "thm_" then String.ofList (s.toList.drop 4) else s)
  | n => n.appendBefore "hol_"

/-- Add the theorem `hol_<name>` stating `thm_<name> inst` with the projections of `inst`
unfolded and the sugar applied. The first argument of `thm_<name>` must be the instance. -/
def mkHolReadable (declName : Name) (inst : Expr) (sugar : Array Name := #[]) : MetaM Name := do
  let info ← getConstInfo declName
  let instTy ← whnf (← inferType inst)
  let .const className _ := instTy.getAppFn | throwError "{inst} is not a class instance"
  let .forallE _ d b _ ← whnf info.type | throwError "{declName} has no {className} argument"
  unless ← isDefEq d instTy do
    throwError "the first argument of {declName} is not of type {instTy}"
  let ty ← unfoldInstProjections className (b.instantiate1 inst)
  let r ← applyHolSugar ty sugar
  let pf := mkApp (mkConst declName (info.levelParams.map mkLevelParam)) inst
  let value ← match r.proof? with
    | some p => mkEqMP p pf
    | none => pure pf
  let newName := holReadableName declName
  addDecl <| .thmDecl {
    name := newName, levelParams := info.levelParams
    type := ← instantiateMVars r.expr, value := ← instantiateMVars value }
  return newName

/-- Elaborate the instance and the sugar lemmas, then call `mkHolReadable`. -/
def elabHolReadable (declName : Name) (inst : Term) (sugar : Array Ident) : TermElabM Unit := do
  let inst ← instantiateMVars (← elabTermAndSynthesize inst none)
  let sugar ← sugar.mapM fun l => realizeGlobalConstNoOverloadWithInfo l
  discard <| mkHolReadable declName inst sugar

initialize registerBuiltinAttribute {
  name := `holReadable
  descr := "generate the readable theorem hol_<name> from thm_<name> and a class instance"
  applicationTime := .afterTypeChecking
  add := fun declName stx _ => MetaM.run' <| TermElabM.run' do
    match stx with
    | `(attr| hol_readable $inst $[[$ids,*]]?) =>
      elabHolReadable declName inst (ids.map (·.getElems) |>.getD #[])
    | _ => throwUnsupportedSyntax }

/-- Command version of the attribute `hol_readable`, usable in this file. -/
syntax (name := holReadableCmd)
  "hol_readable " ident " using " term:max (" [" ident,* "]")? : command

elab_rules : command
  | `(hol_readable $thm using $inst $[[$ids,*]]?) => Command.liftTermElabM do
    let declName ← realizeGlobalConstNoOverloadWithInfo thm
    elabHolReadable declName inst (ids.map (·.getElems) |>.getD #[])

end HolReadable

/-! MWE of `hol_readable` -/
namespace HolReadableMWE

/-- A tiny `HOLTheory`. -/
class MiniHOL where
  num : Type
  hol_eq : {α : Type} → α → α → Prop
  num_add : num → num → num
  ADD_SYM : ∀ x y : num, hol_eq (num_add x y) (num_add y x)

/-- An alignment of `num_add`, like `real_add` in `real_align`. -/
def nat_add (m n : ℕ) : ℕ := m + n

/-- Its syntactic sugar, like `real_add`. -/
theorem nat_add_eq : nat_add = (· + ·) := rfl

instance miniInst : MiniHOL where
  num := ℕ
  hol_eq := Eq
  num_add := nat_add
  ADD_SYM := Nat.add_comm

/-- An exported theorem, stated over the class as in `hol_opam`. -/
theorem thm_ADD_SYM [T : MiniHOL] :
    ∀ x y : MiniHOL.num, MiniHOL.hol_eq (MiniHOL.num_add x y) (MiniHOL.num_add y x) :=
  MiniHOL.ADD_SYM

/- #eval Lean.Elab.Term.elabTermAndSynthesize `(nat_add 1 1 = 2)
#eval applyHolSugar ( (nat_add 1 1 = 2)) -/

hol_readable thm_ADD_SYM using miniInst [nat_add_eq]

/-- info: HolReadableMWE.hol_ADD_SYM (x y : ℕ) : x + y = y + x -/
#guard_msgs in
#check hol_ADD_SYM

end HolReadableMWE


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

open Lean PrettyPrinter Delaborator SubExpr
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
example : 1 = 1 := rfl
