import HolLightLean.meta

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Alignment of infinite Type ind
-/

def ind : Type := Nat -- Nonempty Nat := inferInstance

instance : Nonempty ind := Nonempty.intro Nat.zero

def ONE_ONE {α β : Type*} [Nonempty α] [Nonempty β] :=
fun _2064 : α -> β => forall x1 : α, forall x2 : α, ((_2064 x1) = (_2064 x2)) -> x1 = x2

theorem ONE_ONE_def {α β : Type*} [Nonempty α] [Nonempty β] :
Eq (@ONE_ONE α β _ _) (fun _2064 : α -> β => ∀ x1 : α, ∀ x2 : α, (Eq (_2064 x1) (_2064 x2)) -> Eq x1 x2) :=  Eq.refl (@ONE_ONE α β _ _)

noncomputable def ONTO {α β : Type*} [Nonempty α] [Nonempty β] : (α -> β) -> Prop := fun _2069 : α -> β => ∀ y : β, ∃ x : α, Eq y (_2069 x)

theorem ONTO_def {α β : Type*} [Nonempty α] [Nonempty β] :
Eq (@ONTO α β _ _) (fun _2069 : α -> β => ∀ y : β, ∃ x : α, Eq y (_2069 x))
:= Eq.refl (@ONTO α β _ _)

theorem axiom_6 : ∃ f : ind -> ind, And (@ONE_ONE ind ind _ _ f) (Not (@ONTO ind ind _ _ f)) := by
  refine ⟨Nat.succ,?_⟩
  apply And.intro
  · unfold ONE_ONE
    intros x1 x2
    exact (Nat.succ_inj).1
  · intro h
    unfold ONTO at h
    have h0 := h Nat.zero
    obtain ⟨x, h0x⟩ := h0
    contradiction

def IND_SUC_pred : (ind -> ind) -> Prop := (fun f : ind -> ind =>
∃ z : ind, And (∀ x1 : ind, ∀ x2 : ind, Eq (Eq (f x1) (f x2)) (Eq x1 x2))
(∀ x : ind, Not (Eq (f x) z)))

noncomputable def IND_SUC : ind -> ind := @Classical.epsilon (ind -> ind) _ IND_SUC_pred

theorem IND_SUC_def : Eq IND_SUC (@Classical.epsilon (Nat -> ind) _ (fun f : ind -> ind => ∃ z : ind, And (∀ x1 : ind, ∀ x2 : ind, Eq (Eq (f x1) (f x2)) (Eq x1 x2)) (∀ x : ind, Not (Eq (f x) z)))) := Eq.refl IND_SUC

def IND_0_pred : ind -> Prop := (fun z : ind => And (∀ x1 : ind, ∀ x2 : ind, Eq
(Eq (IND_SUC x1) (IND_SUC x2)) (Eq x1 x2)) (∀ x : ind, Not (Eq (IND_SUC x) z)))

noncomputable def IND_0 : ind := @Classical.epsilon ind _ IND_0_pred

theorem IND_0_def : Eq IND_0 (@Classical.epsilon ind _ (fun z : ind => And (∀ x1 : ind, ∀ x2 : ind, Eq (Eq (IND_SUC x1) (IND_SUC x2)) (Eq x1 x2)) (∀ x : ind, Not (Eq (IND_SUC x) z)))) := Eq.refl IND_0

theorem IND_SUC_ex : ∃ f, IND_SUC_pred f := by
  obtain ⟨f,⟨h1,h2⟩⟩ := by apply axiom_6
  apply Exists.intro f
  unfold ONTO at h2
  rewrite [Classical.not_forall] at h2
  obtain ⟨z,h2⟩ := h2
  unfold IND_SUC_pred
  apply Exists.intro z
  apply And.intro
  · unfold ONE_ONE at h1
    exact fun x1 x2 ↦ Eq.propIntro (h1 x1 x2) (congrArg f)
  · intros x h
    rewrite [not_exists] at h2
    have ff := (h2 x) h.symm
    contradiction

theorem IND_SUC_prop : IND_SUC_pred IND_SUC := by
  unfold IND_SUC
  apply Classical.epsilon_spec
  exact IND_SUC_ex

theorem IND_SUC_inj : ONE_ONE IND_SUC := by
  unfold ONE_ONE
  have h := IND_SUC_prop
  unfold IND_SUC_pred at h
  obtain ⟨z,⟨inj,onto⟩⟩ := h
  intros x y h
  have inj := inj x y
  rewrite [<- inj]
  exact h

theorem IND_0_ex : exists z, IND_0_pred z := by
  have h := IND_SUC_prop
  unfold IND_SUC_pred at h
  obtain ⟨z,⟨inj,onto⟩⟩ := h
  apply Exists.intro z
  unfold IND_0_pred
  apply And.intro
  · exact inj
  · exact onto

theorem IND_0_prop : IND_0_pred IND_0 := by
  unfold IND_0
  apply Classical.epsilon_spec
  exact IND_0_ex

theorem IND_SUC_neq_0 i : IND_SUC i ≠ IND_0 := by
  have h := IND_0_prop
  unfold IND_0_pred at h
  obtain ⟨left,right⟩ := h
  intros _
  have right := right i
  contradiction

/-!
# Alignment of Nat
-/

noncomputable def NUM_REP : ind -> Prop := fun a : ind => ∀ NUM_REP' : ind -> Prop, (∀ a' : ind, (Or (Eq a' IND_0) (∃ i : ind, And (Eq a' (IND_SUC i)) (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a

theorem NUM_REP_def : Eq NUM_REP (fun a : ind => ∀ NUM_REP' : ind -> Prop,
(∀ a' : ind, (Or (Eq a' IND_0) (∃ i : ind, And (Eq a' (IND_SUC i)) (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a) := Eq.refl NUM_REP

inductive NUM_REP_id : ind -> Prop where
| NUM_REP_id_0 : NUM_REP_id IND_0
| NUM_REP_id_SUC i : NUM_REP_id i -> NUM_REP_id (IND_SUC i)

theorem NUM_REP_eq_id : NUM_REP = NUM_REP_id := by
  funext x
  apply Eq.propIntro
  · intro h
    apply h
    intros n h1
    obtain ⟨a,b⟩ := h1
    · exact NUM_REP_id.NUM_REP_id_0
    · expose_names
      obtain ⟨i,p⟩ := h_1
      rw [p.left]
      apply NUM_REP_id.NUM_REP_id_SUC i
      exact p.right
  · intro h
    induction h
    · unfold NUM_REP
      intros P h1
      have h1 := h1 IND_0
      simp only [true_or, forall_const] at h1
      exact h1
    · expose_names
      unfold NUM_REP at *; intros P h1
      have hp := a_ih P
      apply h1
      refine Or.symm (or_intro1 ?_ (IND_SUC i = IND_0))
      exact ⟨i,⟨rfl, hp h1⟩⟩

noncomputable def dest_num : Nat -> ind
| 0 => IND_0
| Nat.succ m => IND_SUC (dest_num m)

theorem dest_num_inj (n m : Nat) : dest_num n = dest_num m -> n = m := by
  induction n generalizing m
  · cases m
    · simp
    · rename Nat => m ; intro h1
      unfold dest_num at h1
      have h_aux := (IND_SUC_neq_0 (dest_num m)).symm
      have false := h_aux h1
      contradiction
  · expose_names
    cases m
    · expose_names ; intro h1
      unfold dest_num at h1
      have h_aux := (IND_SUC_neq_0 (dest_num n))
      have false := h_aux h1
      contradiction
    · rename Nat => m ; intro h ; expose_names
      unfold dest_num at h
      have h_inj := (IND_SUC_inj (dest_num n) (dest_num m)) h
      apply (Nat.succ_inj).2
      exact (h_1 m) h_inj

def mk_num_pred (i : ind) (n : Nat) := i = dest_num n

noncomputable def mk_num (i : ind) := Classical.epsilon (mk_num_pred i)

theorem axiom_7 : ∀ (a : Nat), Eq (mk_num (dest_num a)) a := by
  intro n
  unfold mk_num
  symm
  apply align_epsilon Nat
  · rfl
  · intros x h1 h2
    unfold mk_num_pred at *
    exact dest_num_inj n x (Eq.trans h1 h2)

theorem NUM_REP_eq_dest_num_img : NUM_REP = (fun i : ind => ∃ n, (i = dest_num n)) := by
  rw [NUM_REP_eq_id]
  funext i
  apply Eq.propIntro
  · intro h
    induction h
    · apply Exists.intro 0 ; rfl
    · expose_names
      obtain ⟨n,h_aux⟩ := a_ih
      rw [h_aux]
      apply Exists.intro n.succ
      rfl
  · intro h
    obtain ⟨n,hn⟩ := h
    rw [hn]
    clear hn
    induction n
    · unfold dest_num
      exact NUM_REP_id.NUM_REP_id_0
    · expose_names
      unfold dest_num
      apply NUM_REP_id.NUM_REP_id_SUC (dest_num n)
      exact h

theorem axiom_8_left {i : ind} : NUM_REP i -> ∃ n, mk_num_pred i n := by
  rw [NUM_REP_eq_id]
  intro h
  induction h
  · apply Exists.intro 0 ; rfl
  · expose_names
    obtain ⟨n,hn⟩ := a_ih
    apply Exists.intro (Nat.succ n)
    unfold mk_num_pred
    rw [hn]
    rfl

theorem axiom_8 : ∀ (i : ind), Eq (NUM_REP i) (Eq (dest_num (mk_num i)) i) := by
  intro i
  apply Eq.propIntro
  · intro h
    symm
    exact Classical.epsilon_spec (axiom_8_left h)
  · intro h
    rw [<- h, NUM_REP_eq_dest_num_img]
    simp only
    apply Exists.intro (mk_num i)
    rfl

theorem _0_def : Eq Nat.zero (mk_num IND_0) := by
  rw [Nat.zero_eq] at *
  apply align_epsilon
  · rfl
  · intros x h1 h2
    unfold mk_num_pred at *
    exact dest_num_inj _ _ (Eq.trans h1 h2)

theorem SUC_def : Eq Nat.succ (fun _2104 : Nat => mk_num (IND_SUC (dest_num _2104))) := by
  funext n
  apply align_epsilon
  · rfl
  · intros m h1 h2
    unfold mk_num_pred at *
    exact dest_num_inj _ _ (Eq.trans h1 h2)

/-!
# Aligment of arithmetical operations on Nat
-/

@[simp]
def NUMERAL (n : Nat) := n

@[simp]
def BIT0 := fun n : Nat => n + n

@[simp]
def BIT1 := fun n : Nat => Nat.succ (BIT0 n)

theorem BIT1_def : BIT1 = (fun _2143 : Nat => Nat.succ (BIT0 _2143)) := rfl

theorem NUMERAL_def : Eq NUMERAL (fun _2128 : Nat => _2128) := Eq.refl NUMERAL

theorem BIT0_def : BIT0 = @Classical.epsilon (Nat -> Nat) _ (fun y0 : Nat -> Nat => ((y0 (NUMERAL Nat.zero)) = (NUMERAL Nat.zero)) ∧ (forall y1 : Nat, (y0 (Nat.succ y1)) = (Nat.succ (Nat.succ (y0 y1))))) := by
  apply align_epsilon
  · simp only [Nat.zero_eq, Nat.succ_eq_add_one]
    unfold BIT0 NUMERAL
    grind only
  · intros f h1 h2
    unfold BIT0 NUMERAL at *
    simp only [Nat.zero_eq, Nat.add_zero, Nat.succ_eq_add_one, true_and] at h1
    funext n;
    induction n
    · simp only [Nat.add_zero]
      exact h2.left.symm
    · rename Nat => n
      have h2 := h2.right n
      have h1 := h1 n
      lia

theorem PRE_def : Eq Nat.pred (@Classical.epsilon ((Prod Nat (Prod Nat Nat)) -> Nat -> Nat) _
(fun PRE' : (Prod Nat (Prod Nat Nat)) -> Nat -> Nat =>
∀ _2151 : Prod Nat (Prod Nat Nat), And (Eq (PRE' _2151 (NUMERAL Nat.zero)) (NUMERAL Nat.zero))
(∀ n : Nat, Eq (PRE' _2151 (Nat.succ n)) n))
(@prod_mk Nat (Prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
(@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
(NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))) := by
  epsilon_tac
  · simp
  · intros f _ h
    funext n m;
    induction m
    · simp_all
    · simp_all +arith

theorem add_def : Eq Nat.add (@Classical.epsilon (Nat -> Nat -> Nat -> Nat) _
(fun add' : Nat -> Nat -> Nat -> Nat => ∀ _2155 : Nat,
And (∀ n : Nat, Eq (add' _2155 (NUMERAL Nat.zero) n) n)
(∀ m : Nat, ∀ n : Nat, Eq (add' _2155 (Nat.succ m) n) (Nat.succ (add' _2155 m n))))
(NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) := by
  epsilon_tac
  · intro n ; constructor
    · simp
    · lia
  · intros f _ _
    funext _ m _
    induction m <;> simp_all

theorem mul_def : Eq Nat.mul (@Classical.epsilon (Nat -> Nat -> Nat -> Nat) _
(fun mul' : Nat -> Nat -> Nat -> Nat => ∀ _2186 : Nat,
And (∀ n : Nat, Eq (mul' _2186 (NUMERAL Nat.zero) n) (NUMERAL Nat.zero)) (∀ m : Nat, ∀ n : Nat,
Eq (mul' _2186 (Nat.succ m) n) (Nat.add (mul' _2186 m n) n)))
(NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) := by
  epsilon_tac
  · intro n ; constructor
    · simp
    · lia
  · intros f _ h
    simp_all +arith only [NUMERAL, Nat.zero_eq, Nat.mul_eq, zero_mul, implies_true,
      Nat.succ_eq_add_one, Nat.add_eq, true_and, forall_const]
    funext n m k;
    induction m
    · simp_all
    · simp_all +arith only [Nat.succ_eq_add_one]
      rename Nat => m
      rename _ => hi
      have h_aux := (h n).right m k
      rw [← hi] at h_aux
      grind

theorem EXP_def : Eq Nat.pow (@Classical.epsilon ((Prod Nat (Prod Nat Nat)) -> Nat -> Nat -> Nat) _
(fun EXP' : (Prod Nat (Prod Nat Nat)) -> Nat -> Nat -> Nat => ∀ _2224 : Prod Nat (Prod Nat Nat),
And (∀ m : Nat, Eq (EXP' _2224 m (NUMERAL Nat.zero)) (NUMERAL (BIT1 Nat.zero)))
(∀ m : Nat, ∀ n : Nat, Eq (EXP' _2224 m (Nat.succ n)) (Nat.mul m (EXP' _2224 m n))))
(@prod_mk Nat (Prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
(@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
(NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, Nat.pow_eq, Nat.succ_eq_add_one, Nat.mul_eq, forall_const]
    apply And.intro
    · simp_all
    · grind
  · intros f _ h
    simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one]
    funext n m k;
    induction k
    · simp_all +arith
    · simp_all +arith only [Nat.pow_eq, Nat.mul_eq, forall_const, Prod.forall, Nat.succ_eq_add_one]


theorem le_def : Eq Nat.le (@Classical.epsilon ((Prod Nat Nat) -> Nat -> Nat -> Prop) _
(fun le' : (Prod Nat Nat) -> Nat -> Nat -> Prop => ∀ _2241 : Prod Nat Nat, And
(∀ m : Nat, Eq (le' _2241 m (NUMERAL Nat.zero))
(Eq m (NUMERAL Nat.zero)))
(∀ m : Nat, ∀ n : Nat, Eq (le' _2241 m (Nat.succ n)) (Or (Eq m (Nat.succ n))
(le' _2241 m n))))
(@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 Nat.zero)))))))
(NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 Nat.zero))))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one, forall_const]
    apply And.intro
    · simp
    · lia
  · intros f _ _
    simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one]
    funext n m k;
    induction k
    · simp_all +arith
    · simp_all +arith only [forall_const, Prod.forall]

theorem lt_def : Eq Nat.lt (@Classical.epsilon (Nat -> Nat -> Nat -> Prop) _
(fun lt : Nat -> Nat -> Nat -> Prop =>
∀ _2248 : Nat, And (∀ m : Nat, Eq (lt _2248 m (NUMERAL Nat.zero)) False) (∀ m : Nat, ∀ n : Nat,
Eq (lt _2248 m (Nat.succ n)) (Or (Eq m n) (lt _2248 m n))))
(NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one, forall_const]
    apply And.intro
    · simp
    · unfold Nat.lt
      lia
  · intros f _ _
    simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one]
    funext n m k;
    induction k
    · simp_all +arith
    · simp_all +arith only [forall_const]

theorem ge_def : Eq GE.ge (fun _2249 : Nat => fun _2250 : Nat => Nat.le _2250 _2249) := by
  unfold GE.ge
  simp

theorem gt_def : Eq GT.gt (fun _2261 : Nat => fun _2262 : Nat => Nat.lt _2262 _2261) := by
  unfold GT.gt
  simp

theorem MAX_def : Eq Nat.max (fun _2273 : Nat => fun _2274 : Nat =>
@COND Nat _ (Nat.le _2273 _2274) _2274 _2273) := by
  unfold Nat.max
  funext n m;
  simp only [Nat.le_eq]
  unfold COND
  grind

theorem MIN_def : Eq Nat.min (fun _2285 : Nat => fun _2286 : Nat =>
@COND Nat _ (Nat.le _2285 _2286) _2285 _2286) := by
  unfold Nat.min
  funext n m;
  simp only [Nat.le_eq]
  unfold COND
  grind

theorem minus_def : Eq Nat.sub (@Classical.epsilon (Nat -> Nat -> Nat -> Nat) _
(fun minus' : Nat -> Nat -> Nat -> Nat => ∀ _2766 : Nat,
And (∀ m : Nat, Eq (minus' _2766 m (NUMERAL Nat.zero)) m) (∀ m : Nat, ∀ n : Nat,
Eq (minus' _2766 m (Nat.succ n)) (Nat.pred (minus' _2766 m n))))
(NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one, forall_const]
    apply And.intro
    · simp
    · intros _ _
      simp
      grind
  · intros f _ _
    simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one]
    funext n m k;
    induction k
    · simp_all +arith
    · simp_all +arith only [forall_const]

theorem FACT_def : Eq Nat.factorial (@Classical.epsilon ((Prod Nat (Prod Nat (Prod Nat Nat))) -> Nat -> Nat) _ (fun FACT' : (Prod Nat (Prod Nat (Prod Nat Nat))) -> Nat -> Nat => ∀ _2944 : Prod Nat
(Prod Nat (Prod Nat Nat)), And (Eq (FACT' _2944 (NUMERAL Nat.zero)) (NUMERAL (BIT1 Nat.zero))) (∀ n : Nat, Eq (FACT' _2944 (Nat.succ n)) (Nat.mul (Nat.succ n) (FACT' _2944 n))))
(@prod_mk Nat (Prod Nat (Prod Nat Nat)) _ _
(NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
(@prod_mk Nat (Prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
(@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
(NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one, forall_const]
    apply And.intro
    · rfl
    · intros n
      unfold Nat.factorial
      simp only [Nat.succ_eq_add_one, Nat.mul_eq, mul_eq_mul_left_iff,
                Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false]
      exact Nat.factorial.eq_def n
  · intros f h1 h2
    simp_all +arith only [Nat.zero_eq, Nat.succ_eq_add_one]
    funext n m;
    induction m <;> simp_all +arith

theorem DIV_def : Eq Nat.div (@Classical.epsilon ((Prod Nat (Prod Nat Nat)) -> Nat -> Nat -> Nat) _
(fun q : (Prod Nat (Prod Nat Nat)) -> Nat -> Nat -> Nat => ∀ _3086 : Prod Nat (Prod Nat Nat),
  ∃ r : Nat -> Nat -> Nat, ∀ m : Nat, ∀ n : Nat, @COND Prop _ (Eq n (NUMERAL Nat.zero))
  (And (Eq (q _3086 m n) (NUMERAL Nat.zero)) (Eq (r m n) m))
  (And (Eq m (Nat.add (Nat.mul (q _3086 m n) n) (r m n))) (Nat.lt (r m n) n)))
(@prod_mk Nat (Prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
  (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
  (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, forall_const]
    apply Exists.intro Nat.mod
    · intros m n
      cases n
      · simp only [NUMERAL, Nat.mul_eq, mul_zero, add_zero, Nat.lt_eq, Nat.not_lt_zero, and_false]
        rw [COND_True]
        apply And.intro
        · exact Nat.div_zero m
        · exact Nat.mod_zero m
      · simp only [NUMERAL, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.mul_eq, Nat.lt_eq,
        Order.lt_add_one_iff]
        expose_names
        rw [COND_False]
        apply And.intro
        · rw [Nat.mul_comm]
          symm
          exact Nat.mod_add_div m _
        · exact Nat.le_of_lt_succ (@Nat.mod_lt m (n+1) (by lia))
  · simp_all +arith only [Nat.zero_eq, Nat.mul_eq, Nat.add_eq, Nat.lt_eq,
                          forall_const, Prod.forall, forall_exists_index]
    intros div mod hm hd
    funext n m k;
    have h1 := hd n.1 n.2.1 n.2.2
    obtain ⟨r, h1⟩ := h1
    have h1 := h1 m k
    have h2 := hm m k
    expose_names
    clear hd hm h1_1
    cases k
    · simp_all
      rewrite [COND_True] at h1 h2
      grind
    · simp_all +arith only [Nat.succ_eq_add_one, NUMERAL, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, Prod.mk.eta, Order.lt_add_one_iff]
      rewrite [COND_False] at h1 h2
      obtain ⟨h1_l, h1_r⟩ := h1
      obtain ⟨h2_l, h2_r⟩ := h2
      expose_names
      let k := n_1 + 1
      have hk : 0 < k := Nat.succ_pos _
      have h1' : r m k + k * div n m k = m := by
          simpa [k, Nat.mul_comm] using h1_l.symm
      have h := (Nat.div_mod_unique hk).mpr ⟨h1', by simpa [k] using h1_r⟩
      exact h.1

theorem MOD_def : Eq Nat.mod (@Classical.epsilon ((Prod Nat (Prod Nat Nat)) -> Nat -> Nat -> Nat) _
(fun r : (Prod Nat (Prod Nat Nat)) -> Nat -> Nat -> Nat => ∀ _3087 : Prod Nat (Prod Nat Nat),
  ∀ m : Nat, ∀ n : Nat, @COND Prop _ (Eq n (NUMERAL Nat.zero))
  (And (Eq (Nat.div m n) (NUMERAL Nat.zero))
    (Eq (r _3087 m n) m)) (And (Eq m (Nat.add (Nat.mul (Nat.div m n) n)
    (r _3087 m n))) (Nat.lt (r _3087 m n) n)))
(@prod_mk Nat (Prod Nat Nat) _ _
  (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
  (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
    (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))) := by
  epsilon_tac
  · simp_all +arith only [Nat.zero_eq, forall_const]
    intros m n
    cases n
    · simp_all only [NUMERAL, Nat.mul_eq, mul_zero, add_zero, Nat.lt_eq,
                  Nat.not_lt_zero, and_false]
      rw [COND_True]
      apply And.intro
      · exact Nat.div_zero m
      · exact Nat.mod_zero m
    · simp_all +arith only [NUMERAL, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.mul_eq,
      Nat.lt_eq, Order.lt_add_one_iff]
      expose_names
      rw [COND_False]
      apply And.intro
      · rw [Nat.mul_comm]
        symm
        exact Nat.mod_add_div m _
      · exact Nat.le_of_lt_succ (@Nat.mod_lt m (n+1) (by lia))
  · simp_all +arith only [Nat.zero_eq, Nat.mul_eq, Nat.add_eq, Nat.lt_eq,
                          forall_const, Prod.forall]
    intros div hm hd
    funext n m k;
    have h1 := hd n.1 n.2.1 n.2.2
    have h1 := h1 m k
    have h2 := hm m k
    expose_names
    clear hd hm h1_1
    cases k
    · simp_all
      rewrite [COND_True] at h1 h2
      grind
    · simp_all only [NUMERAL, Nat.succ_eq_add_one, Nat.add_eq_zero_iff, one_ne_zero,
                      and_false, Prod.mk.eta]
      rewrite [COND_False] at h1 h2
      obtain ⟨h1_l, h1_r⟩ := h1
      obtain ⟨h2_l, h2_r⟩ := h2
      grind

/- noncomputable def minimal : (Nat -> Prop) -> Nat := fun _6536 : Nat -> Prop =>
@Classical.epsilon Nat _ (fun n : Nat => And (_6536 n) (∀ m : Nat, (Nat.lt m n) -> Not (_6536 m)))
theorem minimal_def : Eq minimal (fun _6536 : Nat -> Prop => @Classical.epsilon Nat _
(fun n : Nat => And (_6536 n) (∀ m : Nat, (Nat.lt m n) -> Not (_6536 m)))) := Eq.refl minimal
 -/

/-!
# Even & Odd alignment
-/

@[simp]
def EVEN := @Even Nat _

instance EVEN_decidable (n : Nat) [h : Decidable (Even n)] : Decidable (EVEN n) := h -- #eval EVEN 2 -- true

theorem EVEN_def : Eq EVEN (@Classical.epsilon ((Prod Nat (Prod Nat (Prod Nat Nat))) -> Nat -> Prop) _
(fun EVEN' : (Prod Nat (Prod Nat (Prod Nat Nat))) -> Nat -> Prop =>
  ∀ _2603 : Prod Nat (Prod Nat (Prod Nat Nat)), And (Eq (EVEN' _2603 (NUMERAL Nat.zero)) True)
  (∀ n : Nat, Eq (EVEN' _2603 (Nat.succ n)) (Not (EVEN' _2603 n))))
(@prod_mk Nat (Prod Nat (Prod Nat Nat)) _ _
  (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (Prod Nat Nat)
  _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
   (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
   (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))) := by
  unfold EVEN
  epsilon_tac
  intros q
  · apply And.intro
    · simp
    · simp only [Nat.succ_eq_add_one, Nat.not_even_iff_odd, eq_iff_iff]
      intro n
      grind
  · intros f h1 h2
    funext t n;
    have h1_t := h1 t
    have h2_t := h2 t
    clear h1 h2
    induction n
    · simp_all only [NUMERAL, eq_iff_iff, iff_true, Nat.succ_eq_add_one, Nat.not_even_iff_odd]
    · expose_names
      rw [h1_t.right, h2_t.right]
      exact congrArg (fun P => ¬ P ) h

@[simp]
def ODD := @Odd Nat _

instance ODD_decidable (n : Nat) [h : Decidable (Odd n)] : Decidable (ODD n) := h

theorem ODD_def : Eq ODD (@Classical.epsilon ((Prod Nat (Prod Nat Nat)) -> Nat -> Prop) _
(fun ODD' : (Prod Nat (Prod Nat Nat)) -> Nat -> Prop => ∀ _2607 : Prod Nat (Prod Nat Nat), And
  (Eq (ODD' _2607 (NUMERAL Nat.zero)) False)
  (∀ n : Nat, Eq (ODD' _2607 (Nat.succ n)) (Not (ODD' _2607 n))))
(@prod_mk Nat (Prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
  (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
  (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))) := by
  unfold ODD
  epsilon_tac
  intros q
  · apply And.intro
    · simp
    · simp only [Nat.succ_eq_add_one, eq_iff_iff]
      intro n
      grind
  · intros f h1 h2
    funext t n;
    have h1_t := h1 t
    have h2_t := h2 t
    clear h1 h2
    induction n
    · simp_all only [NUMERAL, Nat.zero_eq, Nat.not_odd_zero,
        Nat.succ_eq_add_one, Nat.not_odd_iff_even, eq_iff_iff, true_and, iff_false]
    · expose_names
      rw [h1_t.right, h2_t.right]
      exact congrArg (fun P => ¬ P ) h

/-!
# well founded alignment
-/

def WF {α : Type*} [Nonempty α] := @WellFounded α

theorem well_founded_induction {α : Type*} {r : α → α → Prop} (hwf : WellFounded r) : ∀ P:α  -> Prop,
    (∀ x:α , (∀ y:α , r y x -> P y) -> P x) -> ∀ a:α, P a := by
  induction hwf
  expose_names
  exact fun P a a_1 ↦ WellFounded.fixF a a_1 (h a_1)


theorem WF_def {A : Type*} [Nonempty A] : Eq (@WF A _) (fun _6923 : A -> A -> Prop => ∀ P : A -> Prop, (∃ x : A, P x) -> ∃ x : A, And (P x) (∀ y : A, (_6923 y x) -> Not (P y))) := by
  funext R;
  apply Eq.propIntro
  · intros h P h_ex
    obtain ⟨a,h_Pa⟩ := h_ex
    rewrite [← @Classical.not_not (∃ x, P x ∧ ∀ (y : A), R y x → ¬P y)]
    intro goal
    cases (Classical.propComplete (forall y: A, ¬ P y))
    · expose_names
      rw [is_True] at h_1
      have h_1 := h_1 a
      contradiction
    · expose_names
      rw [is_False] at h_1
      apply h_1
      apply well_founded_induction h
      intros x h_2 h_Px
      apply goal
      exact ⟨x,⟨h_Px, h_2⟩⟩
  · intro h
    unfold WF
    cases (Classical.propComplete (∀ a : A, Acc R a))
    · rename _ => h_t
      rw[is_True] at h_t
      exact WellFounded.intro h_t
    · rename _ => h_f
      rw[is_False] at h_f
      apply False.elim
      simp only [not_forall] at h_f
      have h_aux := h _ h_f
      obtain ⟨x,h_x⟩ := h_aux
      obtain ⟨h_l, h_r⟩ := h_x
      apply h_l
      apply Acc.intro
      intros y h_Ryx
      rw [← @Classical.not_not (Acc R y)]
      apply h_r
      exact h_Ryx

/- /-!
# Measure alignment
-/

-- A measure is a function to Nat that creates wf order by its inverse image
noncomputable def MEASURE {A : Type*} [Nonempty A] : (A -> Nat) -> A -> A -> Prop := fun _8094 : A -> Nat => fun x : A => fun y : A => Nat.lt (_8094 x) (_8094 y)
theorem MEASURE_def {A : Type*} [Nonempty A] : Eq (@MEASURE A _) (fun _8094 : A -> Nat => fun x : A => fun y : A => Nat.lt (_8094 x) (_8094 y)) := Eq.refl (@MEASURE A _)
 -/
/-!
# NUMPAIR
-/

/--
A bijection between `Nat²` and `Nat\{0}`.

`NUMPAIR(x,y) := (2^x)·(2y+1)`
-/
def NUMPAIR : Nat -> Nat -> Nat := fun _17487 : Nat => fun _17488 : Nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 Nat.zero))) _17487) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 Nat.zero))) _17488) (NUMERAL (BIT1 Nat.zero)))

theorem NUMPAIR_def : Eq (fun x y => (2 ^ x * (2 * y + 1))) (fun _17487 : Nat => fun _17488 : Nat => Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 Nat.zero))) _17487) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 Nat.zero))) _17488) (NUMERAL (BIT1 Nat.zero)))) := Eq.refl NUMPAIR

theorem NUMPAIR_def_def x y : NUMPAIR x y = (2 ^ x * (2 * y + 1)) := rfl

theorem NUMPAIR_INJ1 : ∀ x1 y1 x2 y2 : Nat, (NUMPAIR x1 y1 = NUMPAIR x2 y2) → (x1 = x2 ∧ y1 = y2) := by
  intros x1 y1 x2 y2 h
  delta NUMPAIR NUMERAL BIT0 BIT1 at h
  simp +arith only [Nat.zero_eq, add_zero, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, Nat.pow_eq,
    Nat.mul_eq, Nat.add_eq] at h
  obtain ⟨_, _⟩ := Classical.em (x1 < x2)
  · apply False.elim
    have h_aux := (congrArg (fun x => x / (2 ^ x1)) h)
    revert h_aux
    simp +arith only [Nat.pow_succ, ne_eq, Nat.pow_eq_zero, Nat.mul_assoc, OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_div_cancel_left₀]
    lia
  · expose_names ; simp_all only [Nat.succ_eq_add_one, Nat.le_eq, Order.add_one_le_iff]
    have h_m := Nat.exists_eq_add_of_le h_1
    obtain ⟨k, h_add⟩ := h_m
    have h_aux := (congrArg (fun x => x / (2 ^ x1)) h)
    revert h_aux
    subst h_add
    simp +arith only [Nat.pow_add, ne_eq, Nat.pow_eq_zero, Nat.mul_assoc, OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_div_cancel_left₀]
    lia
  · expose_names ; simp_all only [not_lt]
    obtain ⟨_,_⟩ := h_1
    · have h_aux := (congrArg (fun x => x / (2 ^ x1)) h)
      revert h_aux
      simp +arith only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_div_cancel_left₀]
      lia
    · expose_names ; simp_all only [Nat.le_eq, Nat.succ_eq_add_one]
      have h_m := Nat.exists_eq_add_of_le h_1
      obtain ⟨k, h_add⟩ := h_m
      have h_aux := (congrArg (fun x => x / (2 ^ x2)) h)
      revert h_aux
      subst h_add
      simp +arith only [Nat.pow_add, Nat.mul_assoc, ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_div_cancel_left₀]
      intro h_eq
      lia

theorem NUMPAIR_INJ : ∀ x1 y1 x2 y2 : Nat, (NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 ∧ y1 = y2) := by
  intros x1 y1 x2 y2
  apply Eq.propIntro
  · exact (NUMPAIR_INJ1 x1 y1 x2 y2)
  · intro a
    simp_all only

theorem NUMPAIR_nonzero x y : NUMPAIR x y ≠ 0 := by
  unfold NUMPAIR NUMERAL BIT1 BIT0
  simp_all +arith only [Nat.zero_eq, add_zero, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd,
    Nat.pow_eq, Nat.mul_eq, Nat.add_eq, ne_eq, mul_eq_zero, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
    false_and, Nat.add_eq_zero_iff, false_or, one_ne_zero, and_false, or_self, not_false_eq_true]

/-!
# NUMFST and NUMSND. Inverse of NUMPAIR
-/

theorem INJ_INVERSE2 {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] :
∀ P : A -> B -> C, (∀ x1 : A, ∀ y1 : B, ∀ x2 : A, ∀ y2 : B, ((P x1 y1) = (P x2 y2)) = ((x1 = x2) ∧ (y1 = y2))) -> ∃ X : C -> A, ∃ Y : C -> B, ∀ x : A, ∀ y : B, ((X (P x y)) = x) /\ ((Y (P x y)) = y) := by
  intros f h
  refine ⟨fun z => Classical.epsilon (fun x => ∃ y, f x y = z), fun z => Classical.epsilon (fun y => ∃ x, f x y = z),?_⟩
  intros a b
  constructor <;> simp only <;> symm <;> apply align_epsilon
  · exact ⟨b, by rfl⟩
  · rintro x ⟨b1, hb1⟩ ⟨b2, hb2⟩
    specialize h x b2 a b
    rw[h] at hb2
    exact hb2.left.symm
  · exact ⟨a, by rfl⟩
  · rintro x ⟨b1, hb1⟩ ⟨b2, hb2⟩
    specialize h b2 x a b
    rw[h] at hb2
    exact hb2.right.symm


def NUMFST0_pred := fun X : Nat -> Nat => ∃ Y : Nat -> Nat, ∀ x : Nat, ∀ y : Nat, ((X (NUMPAIR x y)) = x) ∧ ((Y (NUMPAIR x y)) = y)

noncomputable def NUMFST0 := Classical.epsilon NUMFST0_pred

theorem NUMFST0_NUMPAIR x y : NUMFST0 (NUMPAIR x y) = x := by
  obtain ⟨f,⟨s,h⟩⟩ := (INJ_INVERSE2 NUMPAIR NUMPAIR_INJ)
  have h_i : ∃ q, NUMFST0_pred q := ⟨f,s,by assumption⟩
  generalize Classical.epsilon_spec h_i = a
  revert a
  unfold NUMFST0_pred
  rintro ⟨s', h'⟩
  obtain ⟨j, k⟩ := (h' x y)
  assumption

def NUMSND0_pred := fun Y : Nat -> Nat => ∃ X : Nat -> Nat, ∀ x : Nat, ∀ y : Nat, ((X (NUMPAIR x y)) = x) ∧ ((Y (NUMPAIR x y)) = y)

noncomputable def NUMSND0 := Classical.epsilon NUMSND0_pred

theorem NUMSND0_NUMPAIR x y : NUMSND0 (NUMPAIR x y) = y := by
  obtain ⟨f,⟨s,h⟩⟩ := (INJ_INVERSE2 NUMPAIR NUMPAIR_INJ)
  have h_i : ∃ q, NUMSND0_pred q := ⟨s,f,by assumption⟩
  generalize Classical.epsilon_spec h_i = a
  revert a
  unfold NUMSND0_pred
  rintro ⟨s', h'⟩
  obtain ⟨j, k⟩ := (h' x y)
  assumption


noncomputable def NUMFST : Nat -> Nat :=
  @Classical.epsilon
    ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat)
    _
    (fun X : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat =>
      ∀ _17503 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))),
       ∃ Y : Nat -> Nat, ∀ x : Nat, ∀ y : Nat, And (Eq (X _17503 (NUMPAIR x y)) x) (Eq (Y (NUMPAIR x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))

theorem NUMFST_def : Eq NUMFST (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat) _ (fun X : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat => ∀ _17503 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), ∃ Y : Nat -> Nat, ∀ x : Nat, ∀ y : Nat, And (Eq (X _17503 (NUMPAIR x y)) x) (Eq (Y (NUMPAIR x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))) := Eq.refl NUMFST

theorem NUMFST_NUMPAIR : ∀ x y, NUMFST (NUMPAIR x y) = x := by
  intros x y
  unfold NUMFST prod
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
          (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
            NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) = a
  generalize     (prod_mk (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
        (prod_mk (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
          (prod_mk (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
            (prod_mk (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
              (prod_mk (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
                (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))))) = A
  set Q := fun X : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ → ℕ ↦
        ∀ (_17503 : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ),
          ∃ Y : ℕ → ℕ, ∀ (x y : ℕ), X _17503 (NUMPAIR x y) = x ∧ Y (NUMPAIR x y) = y
  set fst := Classical.epsilon (fun X : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ ↦
        ∀ (_17503 : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ),
          ∃ Y : ℕ → ℕ, ∀ (x y : ℕ), X _17503 (NUMPAIR x y) = x ∧ Y (NUMPAIR x y) = y)
  have h : ∃ x, Q x := by unfold Q ; refine ⟨fun _ => NUMFST0, ?_⟩ ; simp only [forall_const] ; exists NUMSND0 ; intros x y ; rw[NUMFST0_NUMPAIR, NUMSND0_NUMPAIR] ; trivial
  have h_spec := Classical.epsilon_spec h
  change (Q fst) at h_spec
  obtain ⟨s, j⟩ := h_spec A
  obtain ⟨j1, j2⟩ := j x y
  exact j1

def NUMSND1_pred := fun Y : ℕ -> ℕ => forall x : ℕ, forall y : ℕ, ((NUMFST (NUMPAIR x y)) = x) ∧ ((Y (NUMPAIR x y)) = y)

noncomputable def NUMSND1 := Classical.epsilon NUMSND1_pred

theorem NUMSND1_NUMPAIR x y : NUMSND1 (NUMPAIR x y) = y := by
  obtain ⟨f,⟨s,h⟩⟩ := (INJ_INVERSE2 NUMPAIR NUMPAIR_INJ)
  have h_i : ∃ q, NUMSND1_pred q := ⟨s, by unfold NUMSND1_pred ; intros x' y' ; rw[NUMFST_NUMPAIR] ; obtain ⟨h1, h2⟩ := h x' y' ; simp_all only [and_self]⟩
  generalize Classical.epsilon_spec h_i = a
  revert a
  unfold NUMSND1_pred
  intro j
  obtain ⟨j1, j2⟩ := (j x y)
  assumption


noncomputable def NUMSND : Nat -> Nat := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat) _ (fun Y : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat => ∀ _17504 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), ∀ x : Nat, ∀ y : Nat, And (Eq (NUMFST (NUMPAIR x y)) x) (Eq (Y _17504 (NUMPAIR x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))
theorem NUMSND_def : Eq NUMSND (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat) _ (fun Y : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> Nat -> Nat => ∀ _17504 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), ∀ x : Nat, ∀ y : Nat, And (Eq (NUMFST (NUMPAIR x y)) x) (Eq (Y _17504 (NUMPAIR x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))) := Eq.refl NUMSND

theorem NUMSND_NUMPAIR x y : NUMSND (NUMPAIR x y) = y := by
  unfold NUMSND prod
  generalize (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
      (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 0))))))),
        (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 0))))))),
          (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 0))))))),
            NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 0)))))))))))) = a
  generalize         (prod_mk (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
        (prod_mk (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
          (prod_mk (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
            (prod_mk (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
              (prod_mk (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
                (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))))) = A
  set Q := (fun Y : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ → ℕ ↦ ∀ (_17504 : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (x y : ℕ), NUMFST (NUMPAIR x y) = x ∧ Y _17504 (NUMPAIR x y) = y)
  set snd := Classical.epsilon Q
  have h : ∃ x, Q x := by unfold Q ; refine ⟨fun _ => NUMSND1, ?_⟩ ; simp only [forall_const] ; intros x y ; rw[NUMFST_NUMPAIR, NUMSND1_NUMPAIR] ; trivial
  have h_spec := Classical.epsilon_spec h
  change (Q snd) at h_spec
  obtain ⟨h1, h2⟩ := h_spec A x y
  assumption

/-!
# NUMSUM
-/

/--
A bijection between Bool × Nat and Nat.

`NUMSUM(b,n) := if b then 2n+1 else 2n`
-/
noncomputable def NUMSUM : Prop -> Nat -> Nat := fun _17505 : Prop => fun _17506 : Nat => @COND Nat _ _17505 (Nat.succ (Nat.mul (NUMERAL (BIT0 (BIT1 Nat.zero))) _17506)) (Nat.mul (NUMERAL (BIT0 (BIT1 Nat.zero))) _17506)
theorem NUMSUM_def : Eq NUMSUM (fun _17505 : Prop => fun _17506 : Nat => @COND Nat _ _17505 (Nat.succ (Nat.mul (NUMERAL (BIT0 (BIT1 Nat.zero))) _17506)) (Nat.mul (NUMERAL (BIT0 (BIT1 Nat.zero))) _17506)) := Eq.refl NUMSUM
noncomputable def NUMLEFT : Nat -> Prop := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> Nat -> Prop) _ (fun X : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> Nat -> Prop => ∀ _17535 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∃ Y : Nat -> Nat, ∀ x : Prop, ∀ y : Nat, And (Eq (X _17535 (NUMSUM x y)) x) (Eq (Y (NUMSUM x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))))))
theorem NUMLEFT_def : Eq NUMLEFT (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> Nat -> Prop) _ (fun X : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> Nat -> Prop => ∀ _17535 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∃ Y : Nat -> Nat, ∀ x : Prop, ∀ y : Nat, And (Eq (X _17535 (NUMSUM x y)) x) (Eq (Y (NUMSUM x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))))))) := Eq.refl NUMLEFT
noncomputable def NUMRIGHT : Nat -> Nat := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Nat -> Nat) _ (fun Y : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Nat -> Nat => ∀ _17536 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), ∀ x : Prop, ∀ y : Nat, And (Eq (NUMLEFT (NUMSUM x y)) x) (Eq (Y _17536 (NUMSUM x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))))
theorem NUMRIGHT_def : Eq NUMRIGHT (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Nat -> Nat) _ (fun Y : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Nat -> Nat => ∀ _17536 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), ∀ x : Prop, ∀ y : Nat, And (Eq (NUMLEFT (NUMSUM x y)) x) (Eq (Y _17536 (NUMSUM x y)) y)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))))) := Eq.refl NUMRIGHT

/-!
# RECSPACE alignment
-/

noncomputable def INJN {A : Type*} [Nonempty A] : Nat -> Nat -> A -> Prop := fun _17537 : Nat => fun n : Nat => fun a : A => Eq n _17537

theorem INJN_def {A : Type*} [Nonempty A] : Eq (@INJN A _) (fun _17537 : Nat => fun n : Nat => fun a : A => Eq n _17537) := Eq.refl (@INJN A _)


noncomputable def INJA {A : Type*} [Nonempty A] : A -> Nat -> A -> Prop := fun _17542 : A => fun n : Nat => fun b : A => Eq b _17542

theorem INJA_def {A : Type*} [Nonempty A] : Eq (@INJA A _) (fun _17542 : A => fun n : Nat => fun b : A => Eq b _17542) := Eq.refl (@INJA A _)


noncomputable def INJF {A : Type*} [Nonempty A] : (Nat -> Nat -> A -> Prop) -> Nat -> A -> Prop := fun _17549 : Nat -> Nat -> A -> Prop => fun n : Nat => _17549 (NUMFST n) (NUMSND n)

theorem INJF_def {A : Type*} [Nonempty A] : Eq (@INJF A _) (fun _17549 : Nat -> Nat -> A -> Prop => fun n : Nat => _17549 (NUMFST n) (NUMSND n)) := Eq.refl (@INJF A _)


noncomputable def INJP {A : Type*} [Nonempty A] : (Nat -> A -> Prop) -> (Nat -> A -> Prop) -> Nat -> A -> Prop := fun _17554 : Nat -> A -> Prop => fun _17555 : Nat -> A -> Prop => fun n : Nat => fun a : A => @COND Prop _ (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)

theorem INJP_def {A : Type*} [Nonempty A] : Eq (@INJP A _) (fun _17554 : Nat -> A -> Prop => fun _17555 : Nat -> A -> Prop => fun n : Nat => fun a : A => @COND Prop _ (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a)) := Eq.refl (@INJP A _)


noncomputable def ZCONSTR {A : Type*} [Nonempty A] : Nat -> A -> (Nat -> Nat -> A -> Prop) -> Nat -> A -> Prop := fun _17566 : Nat => fun _17567 : A => fun _17568 : Nat -> Nat -> A -> Prop => @INJP A _ (@INJN A _ (Nat.succ _17566)) (@INJP A _ (@INJA A _ _17567) (@INJF A _ _17568))

theorem ZCONSTR_def {A : Type*} [Nonempty A] : Eq (@ZCONSTR A _) (fun _17566 : Nat => fun _17567 : A => fun _17568 : Nat -> Nat -> A -> Prop => @INJP A _ (@INJN A _ (Nat.succ _17566)) (@INJP A _ (@INJA A _ _17567) (@INJF A _ _17568))) := Eq.refl (@ZCONSTR A _)


noncomputable def ZBOT {A : Type*} [Nonempty A] : Nat -> A -> Prop := @INJP A _ (@INJN A _ (NUMERAL Nat.zero)) (@Classical.epsilon (Nat -> A -> Prop) _ (fun z : Nat -> A -> Prop => True))

theorem ZBOT_def {A : Type*} [Nonempty A] : Eq (@ZBOT A _) (@INJP A _ (@INJN A _ (NUMERAL Nat.zero)) (@Classical.epsilon (Nat -> A -> Prop) _ (fun z : Nat -> A -> Prop => True))) := Eq.refl (@ZBOT A _)

inductive _ZRECSPACE {α : Type*} [Nonempty α] : (Nat -> α -> Prop) -> Prop
| ZRECSPACE0 : _ZRECSPACE ZBOT
| ZRECSPACE1 c i r : (forall n, _ZRECSPACE (r n)) -> _ZRECSPACE (ZCONSTR c i r)

open _ZRECSPACE

def ZRECSPACE {α : Type*} [Nonempty α] := @_ZRECSPACE α _

theorem ZRECSPACE_def {A : Type*} [Nonempty A] : Eq (@ZRECSPACE A _) (fun a : Nat -> A -> Prop => ∀ ZRECSPACE' : (Nat -> A -> Prop) -> Prop, (∀ a' : Nat -> A -> Prop, (Or (Eq a' (@ZBOT A _)) (∃ c : Nat, ∃ i : A, ∃ r : Nat -> Nat -> A -> Prop, And (Eq a' (@ZCONSTR A _ c i r)) (∀ n : Nat, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a) := by
  funext x
  expose_names
  apply Eq.propIntro
  · intro h
    induction h
    · intros h1 h2
      apply h2
      apply Or.intro_left
      rfl
    · intros h1 h2
      expose_names
      apply h2
      apply Or.intro_right
      exists c, i, r
      apply And.intro
      · rfl
      · intro n
        exact a_ih n h1 h2
  · intros h1
    apply h1
    intros a h_or
    obtain ⟨h_r,h_l⟩ := h_or
    · exact _ZRECSPACE.ZRECSPACE0
    · rename _ => h_aux
      obtain ⟨c,⟨i,⟨r,h_and⟩⟩⟩ := h_aux
      obtain ⟨h_r,h_l⟩ := h_and
      subst a
      apply _ZRECSPACE.ZRECSPACE1
      exact h_l

def recspace := fun (α : Type*) [Nonempty α] => SUBTYPE (@ZRECSPACE0 α _)

instance (α : Type*) [Nonempty α] : Nonempty (recspace α) := instNonemptySUBTYPE (@ZRECSPACE0 α _)

def _dest_rec {α : Type*} [Nonempty α] : (recspace α) -> Nat -> α -> Prop :=
  fun A => dest _ A

noncomputable def _mk_rec {α : Type*} [Nonempty α] : (Nat -> α -> Prop) -> recspace α :=
  fun A => mk _ A

noncomputable def BOTTOM {A : Type*} [Nonempty A] : recspace A := @_mk_rec A _ (@ZBOT A _)

theorem BOTTOM_def {A : Type*} [Nonempty A] : Eq (@BOTTOM A _) (@_mk_rec A _ (@ZBOT A _)) := Eq.refl (@BOTTOM A _)

noncomputable def CONSTR {A : Type*} [Nonempty A] : Nat -> A -> (Nat -> recspace A) -> recspace A := fun _17591 : Nat => fun _17592 : A => fun _17593 : Nat -> recspace A => @_mk_rec A _ (@ZCONSTR A _ _17591 _17592 (fun n : Nat => @_dest_rec A _ (_17593 n)))

theorem CONSTR_def {A : Type*} [Nonempty A] : Eq (@CONSTR A _) (fun _17591 : Nat => fun _17592 : A => fun _17593 : Nat -> recspace A => @_mk_rec A _ (@ZCONSTR A _ _17591 _17592 (fun n : Nat => @_dest_rec A _ (_17593 n)))) := Eq.refl (@CONSTR A _)

theorem axiom_9 : ∀ {A : Type*} [Nonempty A] (a : recspace A), Eq (@_mk_rec A _ (@_dest_rec A _ a)) a := by
  intros α _ a
  apply mk_dest

theorem axiom_10 : ∀ {A : Type*} [Nonempty A] (r : Nat -> A -> Prop), Eq (@ZRECSPACE A _ r) (Eq (@_dest_rec A _ (@_mk_rec A _ r)) r) := by
  intros α _ r
  apply dest_mk

theorem NUMSUM_INJ (b1 : Prop) (x1 : Nat) (b2 : Prop) (x2 : Nat) : (NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 ∧ x1 = x2) := by
  apply Eq.propIntro <;> unfold NUMSUM NUMERAL BIT0 BIT1 <;>
  simp_all +arith only [eq_iff_iff, Nat.zero_eq, Nat.succ_eq_add_one, Nat.mul_eq, implies_true]; intro h ; cases (Classical.propComplete b1) <;> cases (Classical.propComplete b2) <;> expose_names
  · rewrite[h_1, h_2, COND_True] at h
    rw[COND_True] at h
    exact ⟨by grind,
          by simp only [Nat.add_right_cancel_iff, mul_eq_mul_left_iff,
              Nat.add_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, and_false, or_false] at h ; exact h⟩
  · rewrite[h_1, h_2, COND_True] at h
    rw[COND_False] at h
    exact ⟨by apply False.elim ; grind, by apply False.elim ; grind⟩
  · rewrite[h_1, h_2, COND_True] at h
    rw[COND_False] at h
    exact ⟨by apply False.elim ; grind, by apply False.elim ; grind⟩
  · rewrite[h_1, h_2, COND_False] at h
    rw[COND_False] at h
    exact ⟨by grind,
          by simp only [mul_eq_mul_left_iff, Nat.add_eq_zero_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or, and_false, or_false] at h ; exact h⟩

theorem NUMLEFT_NUMSUM : ∀ b x, NUMLEFT (NUMSUM b x) = b := by
  intros b x
  let P : ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> Nat -> Prop) → Prop :=
    fun X => ∀ _17535 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))),
      ∃ Y : Nat -> Nat, ∀ x : Prop, ∀ y : Nat,
        And (Eq (X _17535 (NUMSUM x y)) x) (Eq (Y (NUMSUM x y)) y)
  have hP : ∃ X, P X := by
    refine ⟨fun _ n => Classical.epsilon (fun b' => ∃ x', NUMSUM b' x' = n), ?_⟩
    intro _
    refine ⟨fun n => Classical.epsilon (fun x' => ∃ b', NUMSUM b' x' = n), ?_⟩
    intros b x
    refine ⟨?_, ?_⟩
    · have h_ex : ∃ b', ∃ x', NUMSUM b' x' = NUMSUM b x := ⟨b, x, rfl⟩
      obtain ⟨x', h_eq⟩ := Classical.epsilon_spec h_ex
      exact ((Iff.of_eq (NUMSUM_INJ _ _ _ _)).1 h_eq).1
    · have h_ex : ∃ x', ∃ b', NUMSUM b' x' = NUMSUM b x := ⟨x, b, rfl⟩
      obtain ⟨b', h_eq⟩ := Classical.epsilon_spec h_ex
      exact ((Iff.of_eq (NUMSUM_INJ _ _ _ _)).1 h_eq).2
  have h_NUMLEFT : P (Classical.epsilon P) := Classical.epsilon_spec hP
  obtain ⟨_Y, hY⟩ := h_NUMLEFT _
  exact (hY b x).1

theorem NUMRIGHT_NUMSUM : ∀ b x, NUMRIGHT (NUMSUM b x) = x := by
  intros b x
  let P : ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Nat -> Nat) → Prop :=
    fun Y => ∀ _17536 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))),
      ∀ x : Prop, ∀ y : Nat,
        And (Eq (NUMLEFT (NUMSUM x y)) x) (Eq (Y _17536 (NUMSUM x y)) y)
  have hP : ∃ Y, P Y := by
    refine ⟨fun _ n => Classical.epsilon (fun x' => ∃ b', NUMSUM b' x' = n), ?_⟩
    intros _ b x
    refine ⟨NUMLEFT_NUMSUM b x, ?_⟩
    have h_ex : ∃ x', ∃ b', NUMSUM b' x' = NUMSUM b x := ⟨x, b, rfl⟩
    obtain ⟨b', h_eq⟩ := Classical.epsilon_spec h_ex
    exact ((Iff.of_eq (NUMSUM_INJ _ _ _ _)).1 h_eq).2
  have h_NUMRIGHT : P (Classical.epsilon P) := Classical.epsilon_spec hP
  exact (h_NUMRIGHT _ b x).2


theorem INJN_INJ {A : Type*} [Nonempty A] : ∀ n1 n2 : Nat, ((@INJN A _ n1) = (@INJN A _ n2)) = (n1 = n2) := by
  intros n1 n2
  apply Eq.propIntro <;> intro h
  · unfold INJN at h
    have h_1 := congrArg (fun f => f n1) h
    have h_2 := congrArg (fun f => f (Nonempty.some (inferInstance))) h_1
    simp only [eq_iff_iff, true_iff] at h_2
    exact h_2
  · rw[h]

theorem INJA_INJ {A : Type*} [Nonempty A] : ∀ (a1 a2 : A), ((@INJA A _ a1) = (@INJA A _ a2)) = (a1 = a2) := by
  intros a1 a2
  apply Eq.propIntro <;> intro h
  · unfold INJA at h
    have h_1 := congrArg (fun f => f 0 a1) h
    simp only [eq_iff_iff, true_iff] at h_1
    exact h_1
  · rw[h]

theorem INJF_INJ {A : Type*} [Nonempty A] :
    ∀ f1 f2 : Nat → Nat → A → Prop,
      (@INJF A _ f1 = @INJF A _ f2) = (f1 = f2) := by
  intro f1 f2; apply Eq.propIntro
  · intro e; funext x y a
    have h := congrFun (congrFun e (NUMPAIR x y)) a
    simp only [INJF] at h
    rw[NUMFST_NUMPAIR, NUMSND_NUMPAIR] at h
    exact h
  · intro e; subst e; rfl

theorem INJP_INJ {A : Type*} [Nonempty A] :
    ∀ f1 f1' f2 f2' : Nat → A → Prop,
      (@INJP A _ f1 f2 = @INJP A _ f1' f2') = (f1 = f1' ∧ f2 = f2') := by
  intro f1 f1' f2 f2'; apply Eq.propIntro
  · intro e; constructor
    · funext x a
      have h := congrFun (congrFun e (NUMSUM True x)) a
      simp only [INJP] at h
      rw [NUMLEFT_NUMSUM, NUMRIGHT_NUMSUM, COND_True, COND_True] at h
      exact h
    · funext x a
      have h := congrFun (congrFun e (NUMSUM False x)) a
      simp only [INJP] at h
      rw [NUMLEFT_NUMSUM, NUMRIGHT_NUMSUM, COND_False, COND_False] at h
      exact h
  · intro ⟨e1, e2⟩; subst e1; subst e2; rfl

theorem ZCONSTR_INJ {A : Type*} [Nonempty A]
    {c1 c2 : Nat} {i1 i2 : A} {r1 r2 : Nat → Nat → A → Prop} :
    @ZCONSTR A _ c1 i1 r1 = ZCONSTR c2 i2 r2 → c1 = c2 ∧ i1 = i2 ∧ r1 = r2 := by
  unfold ZCONSTR; intro e
  rw [INJP_INJ] at e; obtain ⟨e1, e2⟩ := e
  rw [INJN_INJ] at e1
  rw [INJP_INJ] at e2; obtain ⟨e2a, e3⟩ := e2
  rw [INJA_INJ] at e2a; rw [INJF_INJ] at e3
  exact ⟨Nat.succ_injective e1, e2a, e3⟩

theorem MK_REC_INJ {A : Type*} [Nonempty A] :
    ∀ x y : Nat → A → Prop,
      @_mk_rec A _ x = @_mk_rec A _ y →
      (@ZRECSPACE A _ x ∧ @ZRECSPACE A _ y) → x = y := by
  intro x y e ⟨hx, hy⟩
  rw [axiom_10] at hx; rw [axiom_10] at hy
  rw [← hx, ← hy]; congr 1

theorem CONSTR_INJ {A : Type*} [Nonempty A] :
    ∀ c1 : Nat, ∀ i1 : A, ∀ r1 : Nat → recspace A,
    ∀ c2 : Nat, ∀ i2 : A, ∀ r2 : Nat → recspace A,
      (@CONSTR A _ c1 i1 r1 = @CONSTR A _ c2 i2 r2) =
      (c1 = c2 ∧ i1 = i2 ∧ r1 = r2) := by
  intro c1 i1 r1 c2 i2 r2; apply Eq.propIntro
  · unfold CONSTR; intro e
    have e' := (MK_REC_INJ _ _ e)
    have h_aux := ZCONSTR c1 i1 (fun n ↦ _dest_rec (r1 n))
    have h_ZR1 : @ZRECSPACE A _ (@ZCONSTR A _ c1 i1 (fun n => @_dest_rec A _ (r1 n))) := by
      apply _ZRECSPACE.ZRECSPACE1
      intro n; exact (r1 n).property
    have h_ZR2 : @ZRECSPACE A _ (@ZCONSTR A _ c2 i2 (fun n => @_dest_rec A _ (r2 n))) := by
      apply _ZRECSPACE.ZRECSPACE1
      intro n; exact (r2 n).property
    have e' := MK_REC_INJ _ _ e ⟨h_ZR1, h_ZR2⟩
    obtain ⟨hc, hi, hr⟩ := ZCONSTR_INJ e'
    refine ⟨hc, hi, ?_⟩
    funext n
    exact Subtype.ext (congrFun hr n)
  · intro ⟨e1, e2, e3⟩; subst e1; subst e2; subst e3; rfl


theorem Nodd_double (n : Nat) : Odd (2 * n) = false := by
  simp only [Bool.false_eq_true, eq_iff_iff, iff_false,
             Nat.not_odd_iff_even, even_two, Even.mul_right]

theorem Neven_double (n : Nat) : Even (2 * n) = true := by
  simp only [even_two, Even.mul_right]

noncomputable def FNIL {A : Type*} [Nonempty A] : Nat -> A := fun _17624 : Nat => @Classical.epsilon A _ (fun x : A => True)

theorem FNIL_def {A : Type*} [Nonempty A] : Eq (@FNIL A _) (fun _17624 : Nat => @Classical.epsilon A _ (fun x : A => True)) := Eq.refl (@FNIL A _)

/-!
# CHAR Type alignment
-/

axiom CHAR : Type


/-!
# SUM Type ⊕ alignment
-/

def SUM (α β : Type*) [Nonempty α] [Nonempty β] := Sum α β
def INL {α β : Type*} [Nonempty α] [Nonempty β] := @Sum.inl α β
def INR {α β : Type*} [Nonempty α] [Nonempty β] := @Sum.inr α β

instance {A B : Type*} [h : Nonempty A] [Nonempty B] : Nonempty (SUM A B) := ⟨INL h.some⟩

theorem SUM_equiv {A B : Type*} [Nonempty A] [Nonempty B] : SUM A B = Sum A B := rfl

noncomputable def _dest_sum : forall {A B : Type*} [Nonempty A] [Nonempty B], SUM A B -> recspace (prod A B) :=
fun p => match p with
| Sum.inl a => CONSTR (NUMERAL Nat.zero) (a, Classical.epsilon (fun _ => True)) (fun _ => BOTTOM)
| Sum.inr b => CONSTR (Nat.succ (NUMERAL Nat.zero)) (Classical.epsilon (fun _ => True) , b) (fun _ => BOTTOM)

noncomputable def _mk_sum : ∀ {α β : Type*} [Nonempty α] [Nonempty β], recspace (prod α β) -> SUM α β :=
  fun f => Classical.epsilon (fun p => f = _dest_sum p)

theorem _dest_sum_inj : forall {A B : Type*} [Nonempty A] [Nonempty B] (f g : SUM A B), _dest_sum f = _dest_sum g -> f = g := by
  intros A B _ _ f g h
  induction f <;> induction g <;> unfold _dest_sum at h <;> expose_names <;>
  simp_all only [Nat.zero_eq] <;> rw[CONSTR_INJ] at h
  · have h := congrArg (fun p => p.fst) (h.right.left) ; simp only at h
    rw[h]
  · have h_f := h.left ; simp at h_f
  · have h_f := h.left ; simp at h_f
  · have h := congrArg (fun p => p.snd) (h.right.left) ; simp only at h
    rw[h]

theorem axiom_11 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (a : SUM A B), Eq (@_mk_sum A B _ _ (@_dest_sum A B _ _ a)) a := by
  intros A B _ _ a
  unfold _mk_sum
  apply _dest_sum_inj
  symm
  apply (@Classical.epsilon_spec (SUM A B) (fun p => _dest_sum a = _dest_sum p))
  exact ⟨a, by rfl⟩

theorem axiom_12 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (r : recspace (prod A B)), Eq ((fun a : recspace (prod A B) => ∀ sum' : (recspace (prod A B)) -> Prop, (∀ a' : recspace (prod A B), (Or (∃ a'' : A, Eq a' ((fun a''' : A => @CONSTR (prod A B) _ (NUMERAL Nat.zero) (@prod_mk A B _ _ a''' (@Classical.epsilon B _ (fun v : B => True))) (fun n : Nat => @BOTTOM (prod A B) _)) a'')) (∃ a'' : B, Eq a' ((fun a''' : B => @CONSTR (prod A B) _ (Nat.succ (NUMERAL Nat.zero)) (@prod_mk A B _ _ (@Classical.epsilon A _ (fun v : A => True)) a''') (fun n : Nat => @BOTTOM (prod A B) _)) a''))) -> sum' a') -> sum' a) r) (Eq (@_dest_sum A B _ _ (@_mk_sum A B _ _ r)) r) := by
  intros A B _ _ r
  simp only [Nat.zero_eq, Nat.succ_eq_add_one]
  apply Eq.propIntro <;> intro h
  · unfold _mk_sum
    symm
    apply @Classical.epsilon_spec (SUM A B) (fun p => r = _dest_sum p)
    apply (h (fun r : recspace (prod A B) => exists x : SUM A B, r = _dest_sum x))
    intros r' h_exists
    obtain ⟨a,h_1⟩ := h_exists
    · exact ⟨INL a, h_1⟩
    · expose_names
      obtain ⟨b, h_2⟩ := h_1
      exact ⟨INR b, h_2⟩
  · intros P h_1
    unfold prod_mk at h_1
    apply h_1
    rw[← h]
    cases _mk_sum r <;> expose_names
    · left
      exact ⟨val, rfl⟩
    · right
      exact ⟨val, rfl⟩

theorem INL_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@INL A B _ _) (fun a : A => @_mk_sum A B _ _ ((fun a' : A => @CONSTR (prod A B) _ (NUMERAL Nat.zero) (@prod_mk A B _ _ a' (@Classical.epsilon B _ (fun v : B => True))) (fun n : Nat => @BOTTOM (prod A B) _)) a)) := by
  funext a;
  unfold _mk_sum INL _dest_sum
  apply align_epsilon
  · simp only [Nat.zero_eq]
    unfold prod_mk
    rfl
  · intro S h1 _
    simp_all only [Nat.zero_eq, Nat.succ_eq_add_one]
    apply _dest_sum_inj
    unfold _dest_sum ; simp only [Nat.zero_eq, Nat.succ_eq_add_one]
    exact h1.symm

/- universe u

axiom test : Type u

@[instance]
axiom ne_test : Nonempty test

#check inferInstanceAs (Nonempty test) -/


theorem INR_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@INR A B _ _) (fun a : B => @_mk_sum A B _ _ ((fun a' : B => @CONSTR (prod A B) _ (Nat.succ (NUMERAL Nat.zero)) (@prod_mk A B _ _ (@Classical.epsilon A _ (fun v : A => True)) a') (fun n : Nat => @BOTTOM (prod A B) _)) a)) := by
  funext b;
  unfold _mk_sum INR _dest_sum
  apply align_epsilon
  · simp only [Nat.zero_eq]
    unfold prod_mk
    rfl
  · intro S h1 _
    simp_all only [Nat.zero_eq, Nat.succ_eq_add_one]
    apply _dest_sum_inj
    unfold _dest_sum ; simp only [Nat.zero_eq, Nat.succ_eq_add_one]
    exact h1.symm


noncomputable def OUTL_HOL {A B : Type*} [Nonempty A] [Nonempty B] := (@Classical.epsilon ((prod Nat (prod Nat (prod Nat Nat))) -> (SUM A B) -> A) _ (fun OUTL' :
((prod Nat (prod Nat (prod Nat Nat))) -> (SUM A B) -> A)
=> ∀ _17649 : prod Nat (prod Nat (prod Nat Nat)), ∀ x : A, Eq (OUTL' _17649 (@INL A B _ _ x)) x)
(@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))))

noncomputable def OUTL {A B : Type*} [Nonempty A] [Nonempty B] : (SUM A B) -> A := fun S => match S with
| Sum.inl a => a
| Sum.inr b => OUTL_HOL (INR b)

open Classical in theorem OUTL_def {A B : Type*} [Nonempty A] [Nonempty B] : (@OUTL A B _ _) = (@OUTL_HOL A B _ _) := by
  unfold OUTL_HOL
  set P := (fun OUTL' : prod ℕ ( prod ℕ (prod ℕ ℕ)) → SUM A B → A ↦ ∀ (_17649 : prod ℕ (prod ℕ (prod ℕ ℕ))) (x : A), OUTL' _17649 (INL x) = x)
  funext S
  part_tac (fun S : SUM A B => ∃ b : B, S = INR b)
  · unfold P ; simp only [forall_const] ; intro x ; rfl
  · rintro S1 ⟨b, Sr⟩
    rw[Sr] ; unfold OUTL INR OUTL_HOL ; rfl
  · intros f n S' hP hf hTriv
    unfold P at hP hf
    specialize hP n
    specialize hf n
    specialize hTriv S'
    cases S' <;> rename_i val
    · specialize hf val
      unfold INL at hf ; rw[hf]
      rfl
    · exact hTriv ⟨val, by rfl⟩

noncomputable def OUTR_HOL {A B : Type*} [Nonempty A] [Nonempty B] : (SUM A B) -> B := @Classical.epsilon ((prod Nat (prod Nat (prod Nat Nat))) -> (SUM A B) -> B) _ (fun OUTR' : (prod Nat (prod Nat (prod Nat Nat))) -> (SUM A B) -> B => ∀ _17651 : prod Nat (prod Nat (prod Nat Nat)), ∀ y : B, Eq (OUTR' _17651 (@INR A B _ _ y)) y) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))

noncomputable def OUTR {A B : Type*} [Nonempty A] [Nonempty B] : (SUM A B) -> B := fun S => match S with
| Sum.inl a => OUTR_HOL (INL a)
| Sum.inr b => b

theorem OUTR_def {A B : Type*} [h1 : Nonempty A] [h2 : Nonempty B] : (@OUTR A B _ _) = (@OUTR_HOL A B _ _) := by
--  funext S
  unfold OUTR_HOL
  set P := (fun OUTR' : prod ℕ ( prod ℕ (prod ℕ ℕ)) → SUM A B → B ↦ ∀ (_17651 : prod ℕ (prod ℕ (prod ℕ ℕ))) (y : B), OUTR' _17651 (INR y) = y)
  funext S
  part_tac (fun S : SUM A B => ∃ a : A, S = INL a)
  · unfold P ; simp only [forall_const] ; intro x ; rfl
  · rintro S1 ⟨b, Sr⟩
    rw[Sr] ; unfold OUTR INL OUTR_HOL ; rfl
  · intros f n S' hP hf hTriv
    unfold P at hP hf
    specialize hP n
    specialize hf n
    specialize hTriv S'
    cases S' <;> rename_i val
    · exact hTriv ⟨val, by rfl⟩
    · specialize hf val
      unfold INR at hf ; rw[hf]
      rfl

/-!
# Option Alignment
-/

--instance {A : Type*} [Nonempty A] : Nonempty (Option A) := ⟨none⟩

noncomputable def _dest_option {A : Type*} [Nonempty A] : (Option A) -> recspace A := fun (o : Option A) => match o with
| none => CONSTR (NUMERAL Nat.zero) (Classical.epsilon (fun _ => True)) (fun _ => BOTTOM)
| some a => CONSTR (Nat.succ (NUMERAL Nat.zero)) a (fun _ => BOTTOM)

def _mk_option_pred {A : Type*} [Nonempty A] (r : recspace A) : Option A -> Prop := fun o => _dest_option o = r

noncomputable def _mk_option {A : Type*} [Nonempty A] : (recspace A) -> Option A := fun r => Classical.epsilon (_mk_option_pred r)

theorem _dest_option_inj {A : Type*} [Nonempty A] (o1 o2 : Option A) : _dest_option o1 = _dest_option o2 → o1 = o2 :=
  fun h => (by induction o1 <;> induction o2 <;> delta _dest_option at * <;> simp_all <;> rw [(@CONSTR_INJ A _)] at h <;> simp_all)

theorem axiom_13 : ∀ {A : Type*} [Nonempty A] (o : Option A), Eq (@_mk_option A _ (@_dest_option A _ o)) o := by
  intros A _ o
  unfold _mk_option
  have h : ∃ x : Option A, _mk_option_pred (_dest_option o) x := ⟨o, rfl⟩
  have h_ε := (Classical.epsilon_spec h)
  unfold _mk_option_pred at h_ε
  apply _dest_option_inj
  exact h_ε

def option_pred {A : Type*} [Nonempty A] (r : recspace A) :=
  ∀ option' : recspace A -> Prop,
      (∀ a' : recspace A,
       a' = CONSTR (NUMERAL Nat.zero) (Classical.epsilon (fun _ : A => True)) (fun _ : Nat => BOTTOM) ∨
       (exists a'' : A, a' = CONSTR (Nat.succ (NUMERAL Nat.zero)) a'' (fun _ : Nat => BOTTOM)) ->
       option' a') -> option' r

inductive option_ind {A : Type*} [Nonempty A] : recspace A → Prop where
| option_ind0 : option_ind (CONSTR (NUMERAL Nat.zero) (Classical.epsilon (fun _ : A => True)) (fun _ : Nat => BOTTOM))
| option_ind1 a'' : option_ind (CONSTR (Nat.succ (NUMERAL Nat.zero)) a'' (fun _ : Nat => BOTTOM))

theorem option_eq {A : Type*} [Nonempty A] : @option_pred A _ = @option_ind A _ := by
  funext r
  apply Eq.propIntro <;> intro h
  · apply h
    rintro a ⟨_,⟨a,_⟩⟩
    · exact @option_ind.option_ind0 A _
    · expose_names
      obtain ⟨a',h_2⟩ := h_1 ; subst a
      apply option_ind.option_ind1
  · induction h <;> unfold option_pred <;> intros r h <;> apply h
    · left ; rfl
    · right ; exact ⟨_, rfl⟩

theorem axiom_14 : ∀ {A : Type*} [Nonempty A] (r : recspace A), Eq ((fun a : recspace A => ∀ option' : (recspace A) -> Prop, (∀ a' : recspace A, (Or (Eq a' (@CONSTR A _ (NUMERAL Nat.zero) (@Classical.epsilon A _ (fun v : A => True)) (fun n : Nat => @BOTTOM A _))) (∃ a'' : A, Eq a' ((fun a''' : A => @CONSTR A _ (Nat.succ (NUMERAL Nat.zero)) a''' (fun n : Nat => @BOTTOM A _)) a''))) -> option' a') -> option' a) r) (Eq (@_dest_option A _ (@_mk_option A _ r)) r) := by
  intros A _ r
  have lma_aux : (option_pred r) = ((@_dest_option A _ (@_mk_option A _ r)) = r) := by
    apply Eq.propIntro <;> intro h
    · apply (@Classical.epsilon_spec _ (_mk_option_pred r))
      rw[option_eq] at h ; induction h
      · exact ⟨none, rfl⟩
      · exact ⟨some _, rfl⟩
    · rw[← h]
      intros P h_1
      apply h_1
      cases _mk_option r
      · left ; rfl
      · right ; exact ⟨_, rfl⟩
  exact lma_aux

def NONE {A : Type*} [Nonempty A] := @none A

@[simp]
theorem NONE_none {A : Type*} [Nonempty A] : @NONE A _ = @none A := rfl

theorem NONE_def {A : Type*} [Nonempty A] : Eq (@none A) (@_mk_option A _ (@CONSTR A _ (NUMERAL Nat.zero) (@Classical.epsilon A _ (fun v : A => True)) (fun n : Nat => @BOTTOM A _))) := by
  rw[← axiom_13 none] ; rfl

def SOME {A : Type*} [Nonempty A] := @some A

@[simp]
theorem SOME_some {A : Type*} [Nonempty A] : @SOME A _ = @some A := rfl

theorem SOME_def {A : Type*} [Nonempty A] : Eq (@some A) (fun a : A => @_mk_option A _ ((fun a' : A => @CONSTR A _ (Nat.succ (NUMERAL Nat.zero)) a' (fun n : Nat => @BOTTOM A _)) a)) := by
  funext a ; rw[← axiom_13 (@some A a)] ; rfl

/-!
# List alignment
-/

/-
instance {A : Type*} : Nonempty (List A) := ⟨[]⟩
 -/

def FCONS {A : Type*} [Nonempty A] (a : A) (f : Nat -> A) (n : Nat) : A := @Nat.rec (fun _ => A) a (fun m _ => f m) n

theorem FCONS_def {A : Type*} [Nonempty A] : Eq (@FCONS A _) (@Classical.epsilon ((Prod Nat (Prod Nat (Prod Nat (Prod Nat Nat)))) -> A -> (Nat -> A) -> Nat -> A) _ (fun FCONS' : (Prod Nat (Prod Nat (Prod Nat (Prod Nat Nat)))) -> A -> (Nat -> A) -> Nat -> A => ∀ _17623 : Prod Nat (Prod Nat (Prod Nat (Prod Nat Nat))), And (∀ a : A, ∀ f : Nat -> A, Eq (FCONS' _17623 a f (NUMERAL Nat.zero)) a) (∀ a : A, ∀ f : Nat -> A, ∀ n : Nat, Eq (FCONS' _17623 a f (Nat.succ n)) (f n))) (@prod_mk Nat (Prod Nat (Prod Nat (Prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (Prod Nat (Prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (Prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))))) := by
  epsilon_tac <;> unfold FCONS
  · intro b ; constructor <;> intros a f <;> simp_all only [implies_true, NUMERAL, Nat.zero_eq, Nat.rec_zero]
  · intros P _ h2
    simp_all only [Nat.zero_eq, implies_true, Prod.forall, Nat.succ_eq_add_one]
    ext b a f n
    obtain ⟨h_l, h_r⟩ := (h2 b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2)
    have h_l := h_l a f
    have h_r := h_r a f n
    induction n <;> simp_all only
    · simp_all only [NUMERAL, Nat.rec_zero, implies_true, and_self]

noncomputable def _dest_list {A : Type*} [Nonempty A] (l : List A) : recspace A :=
  match l with
  | List.nil => CONSTR (NUMERAL Nat.zero) (Classical.epsilon (fun _ => True)) (fun _ => BOTTOM)
  | List.cons a l => CONSTR (Nat.succ (NUMERAL Nat.zero)) a (FCONS (_dest_list l) (fun _ => BOTTOM))

theorem FCONS_inj_0 {A : Type*} [Nonempty A] (a : A) (f : Nat → A) : FCONS a f (NUMERAL Nat.zero) = a := rfl

theorem _dest_list_inj {A : Type*} [Nonempty A] (l1 l2 : List A) : _dest_list l1 = _dest_list l2 → l1 = l2 := by
  intro h
  induction l1 generalizing l2 <;> induction l2 <;> unfold _dest_list at h <;>
  rw[CONSTR_INJ] at h <;> obtain ⟨h_l,⟨h_rl,h_rr⟩⟩ := h <;>
  simp_all only [List.nil_eq,
    Nat.zero_eq, Nat.succ_eq_add_one, Nat.left_eq_add, one_ne_zero]
  · symm ; simp_all only [Nat.add_eq_left, one_ne_zero]
  · expose_names ; simp only [List.cons.injEq, true_and]
    apply tail_ih
    rw[← FCONS_inj_0 (_dest_list tail), ← FCONS_inj_0 (_dest_list tail_1), h_rr]

def _mk_list_pred {A : Type*} [Nonempty A] (r : recspace A) : List A -> Prop :=
  fun l => _dest_list l = r

noncomputable def _mk_list {A : Type*} [Nonempty A] (r : recspace A) : List A := @Classical.epsilon (List A) _ (_mk_list_pred r)

theorem axiom_15 : ∀ {A : Type*} [Nonempty A] (a : List A), Eq (@_mk_list A _ (@_dest_list A _ a)) a := by
  intros A _ a
  unfold _mk_list
  symm
  apply align_epsilon
  · rfl
  · intros x h_a h_x
    unfold _mk_list_pred at *
    exact _dest_list_inj _ _ (Eq.trans h_a h_x.symm)

def list_pred {A : Type*} [Nonempty A] (r : recspace A) :=
∀ list' : (recspace A) -> Prop, (∀ a' : recspace A, (Or (Eq a' (@CONSTR A _ (NUMERAL Nat.zero) (@Classical.epsilon A _ (fun v : A => True)) (fun n : Nat => @BOTTOM A _))) (∃ a0 : A, ∃ a1 : recspace A, And (Eq a' ((fun a0' : A => fun a1' : recspace A => @CONSTR A _ (Nat.succ (NUMERAL Nat.zero)) a0' (@FCONS (recspace A) _ a1' (fun n : Nat => @BOTTOM A _))) a0 a1)) (list' a1))) -> list' a') -> list' r

inductive list_ind {A : Type*} [Nonempty A] : recspace A → Prop where
| list_ind0 : list_ind (CONSTR (NUMERAL Nat.zero) (Classical.epsilon (fun _ : A => True)) (fun _ : Nat => BOTTOM))
| list_ind1 h t : list_ind (CONSTR (NUMERAL Nat.zero).succ h (FCONS (_dest_list t) (fun _ : Nat => BOTTOM)))

theorem list_pred_eq_ind {A : Type*} [Nonempty A] : @list_pred A _ = list_ind := by
  funext r
  apply Eq.propIntro <;> intro h
  · unfold list_pred at h ; apply h
    intros r' h1 ; rcases h1
    · rename_i h1 ; rw[h1] ; exact list_ind.list_ind0
    · rename_i h1 ; obtain ⟨head, tail, ⟨h_l,h_r⟩⟩ := h1
      simp_all only [Nat.zero_eq, Nat.succ_eq_add_one, forall_eq_or_imp, forall_exists_index, and_imp] ; cases h_r
      · have h_nil : _dest_list [] = (CONSTR (NUMERAL Nat.zero) (Classical.epsilon fun x ↦ True) fun x ↦ @BOTTOM A _) := rfl
        rw[← h_nil] ; exact list_ind.list_ind1 head []
      · expose_names
        have h_cons : _dest_list (h_1::t) = (@CONSTR A _ (NUMERAL Nat.zero).succ h_1 (@FCONS (recspace A) _ (@_dest_list A _ t) fun x ↦ @BOTTOM A _)) := rfl
        rw[← h_cons] ; exact list_ind.list_ind1 head (h_1 :: t)
  · unfold list_pred ; intros l' h' ; apply h' ; induction h
    · left ; rfl
    · rename_i head tail ; right ; exists head ; exists (_dest_list tail) ; constructor
      · rfl
      · apply h' ; induction tail
        · left ; rfl
        · right ; rename_i hd' tl' tail_ih ; exists hd' ; exists (_dest_list tl') ; exact ⟨rfl, by apply h' ; exact tail_ih⟩

theorem axiom_16' : ∀ {A : Type*} [Nonempty A] (r : recspace A), list_pred r = ((@_dest_list A _ (@_mk_list A _ r)) = r) := by
  intros A _ r
  apply Eq.propIntro <;> intro h
  · unfold _mk_list ; apply @Classical.epsilon_spec _ (_mk_list_pred r)
    rw[list_pred_eq_ind] at h ; induction h
    · exact ⟨[],rfl⟩
    · expose_names ; exact ⟨h::t , rfl⟩
  · rw[← h] ; unfold list_pred ; intros P h1 ; apply h1
    cases _mk_list r <;> simp_all only [Nat.zero_eq, Nat.succ_eq_add_one, forall_eq_or_imp,
      forall_exists_index, and_imp]
    · left ; rfl
    · right ; expose_names
      exists head ; exists (_dest_list tail) ; constructor
      · rfl
      · obtain ⟨h_l, h_r⟩ := h1
        have h_r := h_r r head (_dest_list tail) ; induction tail
        · exact h_l
        · rename_i h_r_1 head_1 tail tail_ih
          simp_all only [implies_true, forall_const]
          apply h_r_1
          · rfl
          · simp_all only

theorem axiom_16 : ∀ {A : Type*} [Nonempty A] (r : recspace A), Eq ((fun a : recspace A => ∀ list' : (recspace A) -> Prop, (∀ a' : recspace A, (Or (Eq a' (@CONSTR A _ (NUMERAL Nat.zero) (@Classical.epsilon A _ (fun v : A => True)) (fun n : Nat => @BOTTOM A _))) (exists a0 : A, exists a1 : recspace A, And (Eq a' ((fun a0' : A => fun a1' : recspace A => @CONSTR A _ (Nat.succ (NUMERAL Nat.zero)) a0' (@FCONS (recspace A) _ a1' (fun n : Nat => @BOTTOM A _))) a0 a1)) (list' a1))) -> list' a') -> list' a) r) (Eq (@_dest_list A _ (@_mk_list A _ r)) r) := by exact axiom_16'

noncomputable def NIL {A : Type*} [Nonempty A] : List A := @List.nil A

theorem NIL_def {A : Type*} [Nonempty A] : Eq (@List.nil A) (@_mk_list A _ (@CONSTR A _ (NUMERAL Nat.zero) (@Classical.epsilon A _ (fun v : A => True)) (fun n : Nat => @BOTTOM A _))) := by
  unfold _mk_list
  apply align_epsilon
  · unfold _mk_list_pred _dest_list ; rfl
  · intro x h1 h2 ; unfold _mk_list_pred at h1 h2
    exact _dest_list_inj _ _ (Eq.trans h1 h2.symm)

def CONS {A : Type*} [Nonempty A] := @List.cons A

theorem CONS_def {A : Type*} [Nonempty A] : Eq (@CONS A _) (fun a0 : A => fun a1 : List A => @_mk_list A _ ((fun a0' : A => fun a1' : recspace A => @CONSTR A _ (Nat.succ (NUMERAL Nat.zero)) a0' (@FCONS (recspace A) _ a1' (fun n : Nat => @BOTTOM A _))) a0 (@_dest_list A _ a1))) := by
  funext a l
  unfold _mk_list
  apply align_epsilon
  · unfold _mk_list_pred  ; rfl
  · intro x h1 h2 ; unfold _mk_list_pred at h1 h2
    exact _dest_list_inj _ _ (Eq.trans h1 h2.symm)


noncomputable def ISO {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B) -> (B -> A) -> Prop := fun _17732 : A -> B => fun _17733 : B -> A => And (∀ x : B, Eq (_17732 (_17733 x)) x) (∀ y : A, Eq (_17733 (_17732 y)) y)
theorem ISO_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@ISO A B _ _) (fun _17732 : A -> B => fun _17733 : B -> A => And (∀ x : B, Eq (_17732 (_17733 x)) x) (∀ y : A, Eq (_17733 (_17732 y)) y)) := Eq.refl (@ISO A B _ _)

noncomputable def GEQ {A : Type*} [Nonempty A] := @Eq A
theorem GEQ_def {A : Type*} [Nonempty A] : Eq (@GEQ A _) (fun a : A => fun b : A => Eq a b) := by rfl

def APPEND {A : Type*} [Nonempty A] : (List A) -> (List A) -> List A := List.append

theorem APPEND_def {A : Type*} [Nonempty A] : Eq (@APPEND A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (List A) -> (List A) -> List A) _ (fun APPEND' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (List A) -> (List A) -> List A => ∀ _18098 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), And (∀ l : List A, Eq (APPEND' _18098 (@NIL A _) l) l) (∀ h : A, ∀ t : List A, ∀ l : List A, Eq (APPEND' _18098 (@List.cons A h t) l) (@List.cons A h (APPEND' _18098 t l)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))) := by
  unfold APPEND
  epsilon_tac
  · simp only [List.append_eq, List.append_left_eq_self, forall_const, List.cons_append, and_true] ; rfl
  · intros f hQ hQf
    funext B' l1 l2
    specialize hQ B'
    specialize hQf B'
    induction l1 generalizing l2
    · have hQ := hQ.1 l2
      have hQf := hQf.1 l2
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 h t l2
      have hQf := hQf.2 h t l2
      specialize ih l2
      rw[ih] at hQ
      lia

def REVERSE {A : Type*} [Nonempty A] : (List A) -> List A := @List.reverse A

theorem REVERSE_def {A : Type*} [Nonempty A] : Eq (@REVERSE A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (List A) -> List A) _ (fun REVERSE' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (List A) -> List A => ∀ _18102 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), And (Eq (REVERSE' _18102 (@NIL A _)) (@NIL A _)) (∀ l : List A, ∀ x : A, Eq (REVERSE' _18102 (@List.cons A x l)) (@APPEND A _ (REVERSE' _18102 l) (@List.cons A x (@NIL A _))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))))))) := by
  unfold REVERSE
  epsilon_tac
  · simp only [forall_const]
    simp_all only [List.reverse_cons]
    apply And.intro
    · rfl
    · intro l x
      rfl
  · intros f hQ hQf
    funext B' l
    specialize hQ B'
    specialize hQf B'
    induction l
    · have hQ := hQ.1
      have hQf := hQf.1
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 t h
      have hQf := hQf.2 t h
      rw[ih] at hQ
      lia

noncomputable def LENGTH {A : Type*} [Nonempty A] : (List A) -> Nat := @List.length A
theorem LENGTH_def {A : Type*} [Nonempty A] : Eq (@LENGTH A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (List A) -> Nat) _ (fun LENGTH' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (List A) -> Nat => ∀ _18106 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), And (Eq (LENGTH' _18106 (@NIL A _)) (NUMERAL Nat.zero)) (∀ h : A, ∀ t : List A, Eq (LENGTH' _18106 (@List.cons A h t)) (Nat.succ (LENGTH' _18106 t)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))) := by
  unfold LENGTH
  epsilon_tac
  · simp_all only [Nat.zero_eq, List.length_cons, Nat.succ_eq_add_one, forall_const, and_true]
    rfl
  · intros f hQ hQf
    funext B' l
    specialize hQ B'
    specialize hQf B'
    induction l
    · have hQ := hQ.1
      have hQf := hQf.1
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 h t
      have hQf := hQf.2 h t
      rw[ih] at hQ
      lia

def MAP {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B) -> (List A) -> List B := @List.map A B

theorem MAP_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@MAP A B _ _) (@Classical.epsilon ((prod Nat (prod Nat Nat)) -> (A -> B) -> (List A) -> List B) _ (fun MAP' : (prod Nat (prod Nat Nat)) -> (A -> B) -> (List A) -> List B => ∀ _18113 : prod Nat (prod Nat Nat), And (∀ f : A -> B, Eq (MAP' _18113 f (@NIL A _)) (@NIL B _)) (∀ f : A -> B, ∀ h : A, ∀ t : List A, Eq (MAP' _18113 f (@List.cons A h t)) (@List.cons B (f h) (MAP' _18113 f t)))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))) := by
  unfold MAP
  epsilon_tac
  · intro B'
    simp_all only [List.map_cons, implies_true, and_true]
    intro f
    rfl
  · intros f hQ hQf
    funext B' g l
    specialize hQ B'
    specialize hQf B'
    induction l
    · have hQ := hQ.1 g
      have hQf := hQf.1 g
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 g h t
      have hQf := hQf.2 g h t
      rw[ih] at hQ
      lia


def BUTLAST {A : Type*} [Nonempty A] : (List A) -> List A := List.dropLast

theorem BUTLAST_def {A : Type*} [Nonempty A] : Eq (@BUTLAST A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (List A) -> List A) _ (fun BUTLAST' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (List A) -> List A => ∀ _18121 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), And (Eq (BUTLAST' _18121 (@NIL A _)) (@NIL A _)) (∀ h : A, ∀ t : List A, Eq (BUTLAST' _18121 (@List.cons A h t)) (@COND (List A) _ (Eq t (@NIL A _)) (@NIL A _) (@List.cons A h (BUTLAST' _18121 t))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))))))) := by
  unfold BUTLAST
  epsilon_tac
  · intro B'
    simp_all only
    apply And.intro
    · rfl
    · intro h t
      simp only [COND]
      cases t
      · simp ; rfl
      · rename_i h' t'
        simp only [List.dropLast_cons_cons, right_eq_ite_iff]
        intro H ; contradiction
  · intros f hQ hQf
    funext B' l
    specialize hQ B'
    specialize hQf B'
    induction l
    · have hQ := hQ.1
      have hQf := hQf.1
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 h t
      have hQf := hQf.2 h t
      rw[ih] at hQ
      lia

noncomputable def HD_HOL {A : Type*} [Nonempty A] : (List A) -> A := @Classical.epsilon ((prod Nat Nat) -> (List A) -> A) _ (fun HD' : (prod Nat Nat) -> (List A) -> A => ∀ _18090 : prod Nat Nat, ∀ t : List A, ∀ h : A, Eq (HD' _18090 (@List.cons A h t)) h) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))

noncomputable def HD {A : Type*} [Nonempty A] (l : List A) : A :=
List.headD l (HD_HOL [])

theorem HD_def {A : Type*} [Nonempty A] : (@HD A _) = (@HD_HOL A _) := by
  unfold HD_HOL
  funext l
  part_tac (fun l : List A => l = [])
  · simp_all only [forall_const]
    intro h t
    rfl
  · intros l' h
    unfold HD HD_HOL
    subst h
    simp_all only [NUMERAL, BIT0, BIT1, Nat.zero_eq, add_zero, Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, List.headD_eq_head?_getD, List.head?_nil, Option.getD_none]
    rfl
  · intros f a' l' h1 h2 h3
    specialize h1 a'
    specialize h2 a'
    cases l'
    · exact h3 [] (rfl)
    · rename_i hd t
      specialize h1 t hd
      specialize h2 t hd
      simp_all only [forall_eq]

noncomputable def TL_HOL {A : Type*} [Nonempty A] := @Classical.epsilon ((prod Nat Nat) -> (List A) -> List A) _ (fun TL' : (prod Nat Nat) -> (List A) -> List A => ∀ _18094 : prod Nat Nat, ∀ h : A, ∀ t : List A, Eq (TL' _18094 (@List.cons A h t)) t) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))

noncomputable def TL {A : Type*} [Nonempty A] : List A → List A := fun l =>
match l with
| [] => @TL_HOL A _ l
| hd :: t => List.tail (hd :: t)

theorem TL_def {A : Type*} [Nonempty A] : Eq (@TL A _) (@TL_HOL A _) := by
  unfold TL_HOL
  funext l
  part_tac (fun l : List A => l = [])
  · simp_all only [forall_const]
    intro h t
    rfl
  · intros l' h
    unfold TL TL_HOL
    subst h
    simp_all only [NUMERAL, BIT0, BIT1, Nat.zero_eq, add_zero, Nat.succ_eq_add_one, zero_add,
      Nat.reduceAdd]
    rfl
  · intros f a' l' h1 h2 h3
    specialize h1 a'
    specialize h2 a'
    cases l'
    · exact h3 [] (rfl)
    · rename_i hd t
      specialize h1 hd t
      specialize h2 hd t
      simp_all only [forall_eq]

noncomputable def LAST_HOL {A : Type*} [Nonempty A] : (List A) -> A := @Classical.epsilon ((prod Nat (prod Nat (prod Nat Nat))) -> (List A) -> A) _ (fun LAST' : (prod Nat (prod Nat (prod Nat Nat))) -> (List A) -> A => ∀ _18117 : prod Nat (prod Nat (prod Nat Nat)), ∀ h : A, ∀ t : List A, Eq (LAST' _18117 (@List.cons A h t)) (@COND A _ (Eq t (@NIL A _)) h (LAST' _18117 t))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))

noncomputable def LAST {A : Type*} [Nonempty A] (l : List A) : A :=
List.getLastD l (LAST_HOL [])

theorem LAST_def {A : Type*} [Nonempty A] : (@LAST A _) = (@LAST_HOL A _) := by
  unfold LAST_HOL
  funext l
  part_tac (fun l : List A => l = [])
  · intros r hd t
    simp only
    by_cases h1 : t = NIL
    · subst h1
      unfold LAST NIL COND
      simp only [List.getLastD_eq_getLast?, List.getLast?_singleton, Option.getD_some, ↓reduceIte]
    · simp only [h1]
      unfold LAST COND
      simp only [↓reduceIte]
      rw[← Ne.eq_def] at h1
      have h_aux : ∀ a b : A, ∀ t : List A, t ≠ [] → (a::t).getLastD b = t.getLastD b := by intros a1 b1 t1 h' ; cases t1 ; try contradiction ; simp_all only [ne_eq,
        reduceCtorEq, not_false_eq_true, List.getLastD_eq_getLast?, List.getLast?_cons_cons]
      apply h_aux
      exact h1
  · intros l' h
    unfold LAST LAST_HOL
    subst h
    simp_all only [Nat.zero_eq]
    rfl
  · intros f a' l' h1 h2 h3
    specialize h1 a'
    specialize h2 a'
    induction l'
    · exact h3 [] (rfl)
    · rename_i hd t ih
      specialize h1 hd t
      specialize h2 hd t
      simp_all only [forall_eq]

def REPLICATE {A : Type*} [Nonempty A] : Nat -> A -> List A := List.replicate

theorem REPLICATE_def {A : Type*} [Nonempty A] : Eq (@REPLICATE A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))) -> Nat -> A -> List A) _ (fun REPLICATE' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))) -> Nat -> A -> List A => ∀ _18125 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))), And (∀ x : A, Eq (REPLICATE' _18125 (NUMERAL Nat.zero) x) (@NIL A _)) (∀ n : Nat, ∀ x : A, Eq (REPLICATE' _18125 (Nat.succ n) x) (@List.cons A x (REPLICATE' _18125 n x)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))))))))) := by
  unfold REPLICATE
  epsilon_tac
  · intro _18125
    simp_all only [NUMERAL, Nat.zero_eq, List.replicate_zero, List.nil_eq, forall_const, Nat.succ_eq_add_one]
    apply And.intro
    · rfl
    · intro n x
      rfl
  · intros f hQ hQf
    funext B' n a
    specialize hQ B'
    specialize hQf B'
    induction n
    · have hQ := hQ.1 a
      have hQf := hQf.1 a
      unfold NIL at hQf hQ
      simp_all only [NUMERAL, Nat.zero_eq, List.replicate_zero, List.nil_eq, forall_const, Nat.succ_eq_add_one]
    · rename_i n ih
      have hQ := hQ.2 n a
      have hQf := hQf.2 n a
      rw[ih] at hQ
      lia

noncomputable def NULL {A : Type*} [Nonempty A] : (List A) -> Prop := fun l => l.isEmpty

theorem NULL_def {A : Type*} [Nonempty A] : Eq (@NULL A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat Nat))) -> (List A) -> Prop) _ (fun NULL' : (prod Nat (prod Nat (prod Nat Nat))) -> (List A) -> Prop => ∀ _18129 : prod Nat (prod Nat (prod Nat Nat)), And (Eq (NULL' _18129 (@NIL A _)) True) (∀ h : A, ∀ t : List A, Eq (NULL' _18129 (@List.cons A h t)) False)) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))) := by
  unfold NULL
  epsilon_tac
  · aesop
  · intros f hQ hQf
    funext B' l
    specialize hQ B'
    specialize hQf B'
    induction l
    · have hQ := hQ.1
      have hQf := hQf.1
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 h t
      have hQf := hQf.2 h t
      lia

open Classical in noncomputable def ALL {A : Type*} [Nonempty A] : (A -> Prop) -> (List A) -> Prop := fun P l => l.all P

theorem ALL_def {A : Type*} [Nonempty A] : Eq (@ALL A _) (@Classical.epsilon ((prod Nat (prod Nat Nat)) -> (A -> Prop) -> (List A) -> Prop) _ (fun ALL' : (prod Nat (prod Nat Nat)) -> (A -> Prop) -> (List A) -> Prop => ∀ _18136 : prod Nat (prod Nat Nat), And (∀ P : A -> Prop, Eq (ALL' _18136 P (@NIL A _)) True) (∀ h : A, ∀ P : A -> Prop, ∀ t : List A, Eq (ALL' _18136 P (@List.cons A h t)) (And (P h) (ALL' _18136 P t)))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))) := by
  unfold ALL
  epsilon_tac
  · intros B
    constructor
    · intros P
      unfold NIL
      simp only [List.all_nil]
    · intros h P t
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  · intros f hQ hQf
    funext B' P
    specialize hQ B'
    specialize hQf B'
    funext l
    induction l
    · have hQ := hQ.1 P
      have hQf := hQf.1 P
      unfold NIL at hQf hQ
      rw[hQf] ; exact hQ
    · rename_i h t ih
      have hQ := hQ.2 h P t
      have hQf := hQf.2 h P t
      rw[ih] at hQ
      rw[hQf]
      exact hQ

open Classical in noncomputable def EX {A : Type*} [Nonempty A] : (A -> Prop) -> (List A) -> Prop := fun P l => l.any P
/- could be replaced by λ P l, (∃ x ∈ l, P x)
  since we are in classical logic, propositions are decidable both definitions are equivalent by `List.any_eq`.
-/

theorem EX_def {A : Type*} [Nonempty A] : Eq (@EX A _) (@Classical.epsilon ((prod Nat Nat) -> (A -> Prop) -> (List A) -> Prop) _ (fun EX' : (prod Nat Nat) -> (A -> Prop) -> (List A) -> Prop => ∀ _18143 : prod Nat Nat, And (∀ P : A -> Prop, Eq (EX' _18143 P (@NIL A _)) False) (∀ h : A, ∀ P : A -> Prop, ∀ t : List A, Eq (EX' _18143 P (@List.cons A h t)) (Or (P h) (EX' _18143 P t)))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))) := by
  unfold EX
  epsilon_tac
  · intros B
    constructor
    · intros P
      unfold NIL
      simp only [List.any_nil, Bool.false_eq_true]
    · intros h P t
      simp_all only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  · intros f hQ hQf
    funext B' P
    specialize hQ B'
    specialize hQf B'
    funext l
    induction l
    · have hQ := hQ.1 P
      have hQf := hQf.1 P
      unfold NIL at hQf hQ
      rw[hQf] ; exact hQ
    · rename_i h t ih
      have hQ := hQ.2 h P t
      have hQf := hQf.2 h P t
      rw[ih] at hQ
      rw[hQf]
      exact hQ

noncomputable def ITLIST {A B : Type*} [Nonempty A] [Nonempty B] (f : A -> B -> B) (l : List A) (b : B) : B := @List.foldr A B f b l

theorem ITLIST_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@ITLIST A B _ _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> (List A) -> B -> B) _ (fun ITLIST' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> (List A) -> B -> B => ∀ _18151 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), And (∀ f : A -> B -> B, ∀ b : B, Eq (ITLIST' _18151 f (@NIL A _) b) b) (∀ h : A, ∀ f : A -> B -> B, ∀ t : List A, ∀ b : B, Eq (ITLIST' _18151 f (@List.cons A h t) b) (f h (ITLIST' _18151 f t b)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))) := by
  unfold ITLIST
  epsilon_tac
  · intros R
    constructor
    · intros P b
      unfold NIL
      simp_all only [List.foldr_nil]
    · intros h P t b
      simp_all only [List.foldr_cons]
  · intros f hQ hQf
    funext B' P
    specialize hQ B'
    specialize hQf B'
    funext l b
    induction l
    · have hQ := hQ.1 P b
      have hQf := hQf.1 P b
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 h P t b
      have hQf := hQf.2 h P t b
      rw[ih] at hQ
      rw[hQf]
      exact hQ

noncomputable def MEM {A : Type*} [Nonempty A] : A -> (List A) -> Prop := fun a l => a ∈ l

theorem MEM_def {A : Type*} [Nonempty A] : Eq (@MEM A _) (@Classical.epsilon ((prod Nat (prod Nat Nat)) -> A -> (List A) -> Prop) _ (fun MEM' : (prod Nat (prod Nat Nat)) -> A -> (List A) -> Prop => ∀ _18158 : prod Nat (prod Nat Nat), And (∀ x : A, Eq (MEM' _18158 x (@NIL A _)) False) (∀ h : A, ∀ x : A, ∀ t : List A, Eq (MEM' _18158 x (@List.cons A h t)) (Or (Eq x h) (MEM' _18158 x t)))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))) := by
  unfold MEM
  epsilon_tac
  · intros R
    constructor
    · intros a
      unfold NIL
      simp_all only [List.not_mem_nil]
    · intros hd a t
      simp_all only [List.mem_cons]
  · intros f hQ hQf
    funext B' a
    specialize hQ B'
    specialize hQf B'
    funext l
    induction l
    · have hQ := hQ.1 a
      have hQf := hQf.1 a
      unfold NIL at hQf hQ
      lia
    · rename_i h t ih
      have hQ := hQ.2 h a t
      have hQf := hQf.2 h a t
      rw[ih] at hQ
      rw[hQf]
      exact hQ

open Classical in def ALL2 {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (List A) -> (List B) -> Prop := fun P lA lB => lA.length = lB.length ∧ (List.zip lA lB).all (fun (a,b) => P a b)

noncomputable def ALL2_HOL {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (List A) -> (List B) -> Prop := @Classical.epsilon ((prod Nat (prod Nat (prod Nat Nat))) -> (A -> B -> Prop) -> (List A) -> (List B) -> Prop) _ (fun ALL2' : (prod Nat (prod Nat (prod Nat Nat))) -> (A -> B -> Prop) -> (List A) -> (List B) -> Prop => ∀ _18166 : prod Nat (prod Nat (prod Nat Nat)), And (∀ P : A -> B -> Prop, ∀ l2 : List B, Eq (ALL2' _18166 P (@NIL A _) l2) (Eq l2 (@NIL B _))) (∀ h1' : A, ∀ P : A -> B -> Prop, ∀ t1 : List A, ∀ l2 : List B, Eq (ALL2' _18166 P (@List.cons A h1' t1) l2) (@COND Prop _ (Eq l2 (@NIL B _)) False (And (P h1' (@HD B _ l2)) (ALL2' _18166 P t1 (@TL B _ l2)))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))

theorem ALL2_def {A B : Type*} [Nonempty A] [Nonempty B] : (@ALL2 A B _ _) = (@ALL2_HOL  A B _ _) := by
  unfold ALL2_HOL
  epsilon_tac
  · intro r
    refine ⟨fun P l2 => ?_, fun h P t l2 => ?_⟩
    · simp [ALL2, NIL, eq_comm]
    · cases l2 with
      | nil => simp [ALL2, NIL, COND]
      | cons b tb => simp [ALL2, NIL, COND, HD, TL] ; tauto
  · intro g hA hg
    funext r P lA
    induction lA with
    | nil => funext l2 ; exact ((hA r).1 P l2).trans ((hg r).1 P l2).symm
    | cons h t ih =>
      funext l2
      rw [(hA r).2 h P t l2, (hg r).2 h P t l2, congrFun ih (TL l2)]

noncomputable def MAP2_HOL {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C) -> (List A) -> (List B) -> List C := @Classical.epsilon ((prod Nat (prod Nat (prod Nat Nat))) -> (A -> B -> C) -> (List A) -> (List B) -> List C) _ (fun MAP2' : (prod Nat (prod Nat (prod Nat Nat))) -> (A -> B -> C) -> (List A) -> (List B) -> List C => ∀ _18174 : prod Nat (prod Nat (prod Nat Nat)), And (∀ f : A -> B -> C, ∀ l : List B, Eq (MAP2' _18174 f (@NIL A _) l) (@NIL C _)) (∀ h1' : A, ∀ f : A -> B -> C, ∀ t1 : List A, ∀ l : List B, Eq (MAP2' _18174 f (@List.cons A h1' t1) l) (@List.cons C (f h1' (@HD B _ l)) (MAP2' _18174 f t1 (@TL B _ l))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))

noncomputable def MAP2_Ind {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] :
    (prod Nat (prod Nat (prod Nat Nat))) -> (A -> B -> C) -> (List A) -> (List B) -> List C :=
  fun R f lA lB => match lA with
    | [] => []
    | h :: t => f h (HD lB) :: MAP2_Ind R f t (TL lB)

open Classical in
noncomputable def MAP2 {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C) -> (List A) -> (List B) -> List C :=
fun f lA lB => if lA.length = lB.length then (List.zip lA lB).map (fun (a,b) => f a b)
               else MAP2_HOL f lA lB

/-- `MAP2_HOL` is forced to agree with the structurally recursive `MAP2_Ind`. -/
theorem MAP2_HOL_eq_Ind {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] :
    ∀ (f : A -> B -> C) (lA : List A) (lB : List B),
      MAP2_HOL f lA lB = MAP2_Ind (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))))) f lA lB := by
  set P := (fun MAP2' : prod ℕ (prod ℕ (prod ℕ ℕ)) → (A -> B -> C) → List A → List B → List C ↦
    ∀ _18174 : prod ℕ (prod ℕ (prod ℕ ℕ)),
      (∀ (f : A -> B -> C) (l : List B), MAP2' _18174 f NIL l = NIL) ∧
      (∀ (h1' : A) (f : A -> B -> C) (t1 : List A) (l : List B),
        MAP2' _18174 f (h1' :: t1) l = f h1' (HD l) :: MAP2' _18174 f t1 (TL l)))
  set R := (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))
  have spec := @Classical.epsilon_spec _ P ⟨MAP2_Ind, by
    intro _18174 ; exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩⟩
  intro f lA
  induction lA with
  | nil => intro lB ; exact (spec R).1 f lB
  | cons h t ih =>
    intro lB
    exact ((spec R).2 h f t lB).trans (congrArg (fun z => f h (HD lB) :: z) (ih (TL lB)))

/-- `MAP2_Ind` ignores its numeric tag. -/
theorem MAP2_Ind_tag_irrel {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C]
    (r r' : prod Nat (prod Nat (prod Nat Nat))) :
    ∀ (f : A -> B -> C) (lA : List A) (lB : List B), MAP2_Ind r f lA lB = MAP2_Ind r' f lA lB := by
  intro f lA
  induction lA with
  | nil => intro lB ; rfl
  | cons h t ih => intro lB ; exact congrArg (fun z => f h (HD lB) :: z) (ih (TL lB))

/-- On equal-length lists `zip`-then-`map` agrees with `MAP2_Ind`. -/
theorem map2Ind_eq {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C]
    (R : prod Nat (prod Nat (prod Nat Nat))) (f : A -> B -> C) :
    ∀ (lA : List A) (lB : List B), lA.length = lB.length →
      (List.zip lA lB).map (fun (a,b) => f a b) = MAP2_Ind R f lA lB := by
  intro lA
  induction lA with
  | nil => intro lB _ ; rfl
  | cons h t ih =>
    intro lB hlen
    cases lB with
    | nil => exact absurd hlen (by simp)
    | cons b tb =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      change (List.zip (h :: t) (b :: tb)).map _ = f h (HD (b :: tb)) :: MAP2_Ind R f t (TL (b :: tb))
      rw [List.zip_cons_cons, List.map_cons, ih tb hlen]
      rfl

theorem MAP2_def {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (@MAP2 A B C _ _ _) = (@MAP2_HOL A B C _ _ _) := by
  unfold MAP2_HOL
  epsilon_tac
  · intro r
    have hM : ∀ (f : A -> B -> C) (lA : List A) (lB : List B), MAP2 f lA lB = MAP2_Ind r f lA lB := by
      intro f lA lB
      change (if lA.length = lB.length then (List.zip lA lB).map (fun (a,b) => f a b)
              else MAP2_HOL f lA lB) = _
      by_cases h : lA.length = lB.length
      · rw [if_pos h] ; exact map2Ind_eq r f lA lB h
      · rw [if_neg h]
        exact (MAP2_HOL_eq_Ind f lA lB).trans (MAP2_Ind_tag_irrel _ r f lA lB)
    refine ⟨fun f l => ?_, fun h f t l => ?_⟩
    · change MAP2 f NIL l = NIL
      rw [hM] ; rfl
    · change MAP2 f (h :: t) l = f h (HD l) :: MAP2 f t (TL l)
      rw [hM, hM] ; rfl
  · intro g hM hg
    funext r f lA
    induction lA with
    | nil => funext l ; exact ((hM r).1 f l).trans ((hg r).1 f l).symm
    | cons h t ih =>
      funext l
      rw [(hM r).2 h f t l, (hg r).2 h f t l, congrFun ih (TL l)]

noncomputable def EL_HOL {A : Type*} [Nonempty A] : Nat -> (List A) -> A := @Classical.epsilon ((prod Nat Nat) -> Nat -> (List A) -> A) _ (fun EL' : (prod Nat Nat) -> Nat -> (List A) -> A => ∀ _18178 : prod Nat Nat, And (∀ l : List A, Eq (EL' _18178 (NUMERAL Nat.zero) l) (@HD A _ l)) (∀ n : Nat, ∀ l : List A, Eq (EL' _18178 (Nat.succ n) l) (EL' _18178 n (@TL A _ l)))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))

noncomputable def EL_Ind {A : Type*} [Nonempty A] : (prod Nat Nat) -> Nat -> (List A) -> A :=
  fun R n l => match n with
    | 0 => HD l
    | Nat.succ m => EL_Ind R m (TL l)

/-- Within range, the ε-defined `EL_HOL` really is list indexing. -/
theorem EL_HOL_get {A : Type*} [Nonempty A] :
    ∀ (n : Nat) (l : List A) (h : n < l.length), EL_HOL n l = l.get ⟨n, h⟩ := by
  set P := (fun EL' : prod ℕ ℕ → ℕ → List A → A ↦ ∀ _18178 : prod ℕ ℕ,
    (∀ l : List A, EL' _18178 (NUMERAL Nat.zero) l = HD l) ∧
    (∀ (n : ℕ) (l : List A), EL' _18178 (Nat.succ n) l = EL' _18178 n (TL l)))
  set R := (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))
  have spec := @Classical.epsilon_spec _ P ⟨EL_Ind, by
    intro _18178 ; exact ⟨fun _ => rfl, fun _ _ => rfl⟩⟩
  intro n
  induction n with
  | zero =>
    intro l h
    cases l with
    | nil => exact absurd h (by simp)
    | cons b tb => exact ((spec R).1 (b :: tb)).trans rfl
  | succ n ih =>
    intro l h
    cases l with
    | nil => exact absurd h (by simp)
    | cons b tb =>
      have h' : n < tb.length := by simp only [List.length_cons] at h ; omega
      exact ((spec R).2 n (b :: tb)).trans (ih tb h')

open Classical in
noncomputable def EL {A : Type*} [Nonempty A] : Nat -> (List A) -> A := fun n l =>
  if h : n < l.length then l.get ⟨n, h⟩ else EL_HOL n l

theorem EL_def {A : Type*} [Nonempty A] : Eq (@EL A _) (@Classical.epsilon ((prod Nat Nat) -> Nat -> (List A) -> A) _ (fun EL' : (prod Nat Nat) -> Nat -> (List A) -> A => ∀ _18178 : prod Nat Nat, And (∀ l : List A, Eq (EL' _18178 (NUMERAL Nat.zero) l) (@HD A _ l)) (∀ n : Nat, ∀ l : List A, Eq (EL' _18178 (Nat.succ n) l) (EL' _18178 n (@TL A _ l)))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))) := by
  funext n l
  change (if h : n < l.length then l.get ⟨n, h⟩ else EL_HOL n l) = EL_HOL n l
  by_cases h : n < l.length
  · rw [dif_pos h] ; exact (EL_HOL_get n l h).symm
  · rw [dif_neg h]

open Classical in noncomputable def FILTER {A : Type*} [Nonempty A] : (A -> Prop) -> (List A) -> List A := fun P l => @List.filter A P l

theorem FILTER_def {A : Type*} [Nonempty A] : Eq (@FILTER A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> Prop) -> (List A) -> List A) _ (fun FILTER' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> Prop) -> (List A) -> List A => ∀ _18185 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), And (∀ P : A -> Prop, Eq (FILTER' _18185 P (@NIL A _)) (@NIL A _)) (∀ h : A, ∀ P : A -> Prop, ∀ t : List A, Eq (FILTER' _18185 P (@List.cons A h t)) (@COND (List A) _ (P h) (@List.cons A h (FILTER' _18185 P t)) (FILTER' _18185 P t)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))) := by
  unfold FILTER
  epsilon_tac
  · intros B
    constructor
    · intros P
      unfold NIL
      simp_all only [List.filter_nil]
    · intros h P t
      simp[COND]
      by_cases hP : P h <;> simp[hP]
  · intros f hQ hQf
    funext B' P
    specialize hQ B'
    specialize hQf B'
    funext l
    induction l
    · have hQ := hQ.1 P
      have hQf := hQf.1 P
      unfold NIL at hQf hQ
      rw[hQf] ; exact hQ
    · rename_i h t ih
      have hQ := hQ.2 h P t
      have hQf := hQf.2 h P t
      rw[ih] at hQ
      rw[hQf]
      exact hQ

noncomputable def ASSOC_HOL {A B : Type*} [Nonempty A] [Nonempty B] : A -> (List (prod A B)) -> B := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat Nat)))) -> A -> (List (prod A B)) -> B) _ (fun ASSOC' : (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) -> A -> (List (prod A B)) -> B => ∀ _18192 : prod Nat (prod Nat (prod Nat (prod Nat Nat))), ∀ h : prod A B, ∀ a : A, ∀ t : List (prod A B), Eq (ASSOC' _18192 a (@List.cons (prod A B) h t)) (@COND B _ (Eq (@prod_fst A B _ _ h) a) (@prod_snd A B _ _ h) (ASSOC' _18192 a t))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))))

open Classical in noncomputable def ASSOC {A B : Type*} [Nonempty A] [Nonempty B] : A -> (List (prod A B)) -> B := fun a l => match l with
| [] => ASSOC_HOL a []
| (a',b)::l' => if a = a' then b else ASSOC a l'

theorem ASSOC_def {A B : Type*} [Nonempty A] [Nonempty B] : (@ASSOC A B _ _) = (@ASSOC_HOL A B _ _) := by
  unfold ASSOC_HOL
  funext a l
  set P := (fun ASSOC' : prod ℕ (prod ℕ (prod ℕ (prod ℕ ℕ))) → A → List (prod A B) → B ↦
        ∀ (_18192 : prod ℕ (prod ℕ (prod ℕ (prod ℕ ℕ)))) (h : prod A B) (a : A) (t : List (prod A B)),
          ASSOC' _18192 a (h :: t) = COND (prod_fst h = a) (prod_snd h) (ASSOC' _18192 a t))
  set R := (prod_mk (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
        (prod_mk (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
          (prod_mk (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))
            (prod_mk (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero))))))))
              (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero))))))))))))
  part_tac (fun l : List (prod A B) => l = [])
  · unfold P
    intros r p hd t
    simp only
    by_cases h1 : (prod_fst p = hd)
    · subst h1
      unfold COND
      simp only [↓reduceIte]
      unfold ASSOC
      cases p ; unfold prod_fst ; simp only [↓reduceIte] ; rfl
    · simp only [h1]
      unfold ASSOC COND
      simp only [↓reduceIte]
      cases p ; unfold prod_fst at h1 ; simp only at h1 ; cases t <;> have h := by simpa [eq_comm] using h1
      · simp [h, ASSOC, ASSOC_HOL]
      · simp only [h, ↓reduceIte] ; rfl
  · intros a' l h
    unfold ASSOC ASSOC_HOL
    simp_all only [P]
    rfl
  · intros f r a' l' h1 h2 h3
    unfold P at h1 h2
    specialize h1 r
    specialize h2 r
    induction l'
    · apply h3 a' [] (by rfl)
    · rename_i hd t ih
      specialize h1 hd a' t
      specialize h2 hd a' t
      simp_all only [forall_eq]

noncomputable def ITLIST2 {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C -> C) -> (List A) -> (List B) -> C -> C := fun f lA lB c =>
match lA with
|[] => c
|a::l => (f a (HD lB) (ITLIST2 f l (TL lB) c))

theorem ITLIST2_def {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : Eq (@ITLIST2 A B C _ _ _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> B -> C -> C) -> (List A) -> (List B) -> C -> C) _ (fun ITLIST2' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> B -> C -> C) -> (List A) -> (List B) -> C -> C => ∀ _18201 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), And (∀ f : A -> B -> C -> C, ∀ l2 : List B, ∀ b : C, Eq (ITLIST2' _18201 f (@NIL A _) l2 b) b) (∀ h1' : A, ∀ f : A -> B -> C -> C, ∀ t1 : List A, ∀ l2 : List B, ∀ b : C, Eq (ITLIST2' _18201 f (@List.cons A h1' t1) l2 b) (f h1' (@HD B _ l2) (ITLIST2' _18201 f t1 (@TL B _ l2) b)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))))))))) := by
  epsilon_tac
  · intro r
    exact ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · intro g hI hg
    funext r f lA
    induction lA with
    | nil => funext lB b ; exact ((hI r).1 f lB b).trans ((hg r).1 f lB b).symm
    | cons h t ih =>
      funext lB b
      rw [(hI r).2 h f t lB b, (hg r).2 h f t lB b]
      exact congrArg (fun z => f h (HD lB) z) (congrFun (congrFun ih (TL lB)) b)

noncomputable def ZIP_HOL {A B : Type*} [Nonempty A] [Nonempty B] := @Classical.epsilon ((prod Nat (prod Nat Nat)) -> (List A) -> (List B) -> List (prod A B)) _ (fun ZIP' : (prod Nat (prod Nat Nat)) -> (List A) -> (List B) -> List (prod A B) => ∀ _18205 : prod Nat (prod Nat Nat), And (∀ l2 : List B, Eq (ZIP' _18205 (@NIL A _) l2) (@NIL (prod A B) _)) (∀ h1' : A, ∀ t1 : List A, ∀ l2 : List B, Eq (ZIP' _18205 (@List.cons A h1' t1) l2) (@List.cons (prod A B) (@prod_mk A B _ _ h1' (@HD B _ l2)) (ZIP' _18205 t1 (@TL B _ l2))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))

noncomputable def ZIP_Ind {A B : Type*} [Nonempty A] [Nonempty B] : ((prod Nat (prod Nat Nat)) -> (List A) -> (List B) -> List (prod A B)) := fun R lA lB => match lA with
    | [] => []
    | h::t => prod_mk h (HD lB) :: ZIP_Ind R t (TL lB)

@[simp]
theorem ZIP_HOL_empty {A B : Type*} [Nonempty A] [Nonempty B] : ∀ l : List B, ZIP_HOL (@NIL A _) l = [] := by
  intro lB
  set P := (fun ZIP' : prod ℕ (prod ℕ ℕ) → List A → List B → List (prod A B)  ↦ ∀ (_18205 : prod ℕ (prod ℕ ℕ)), (∀ (l2 : List B), ZIP' _18205 NIL l2 = NIL) ∧ ∀ (h1' : A) (t1 : List A) (l2 : List B), ZIP' _18205 (h1' :: t1) l2 = prod_mk h1' (HD l2) :: ZIP' _18205 t1 (TL l2))
  set R := (prod_mk (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (prod_mk (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))
  have spec := @Classical.epsilon_spec _ P ⟨ZIP_Ind ,by
  intro _18205
  apply And.intro
  · intro l2
    rfl
  · intro h1' t1 l2
    rfl⟩
  have := (spec R).1 lB
  exact this

instance {A B : Type*} [Nonempty A] [Nonempty B] : CoeSort (List (A × B)) (List (prod A B)) := ⟨fun x => x⟩

instance {A B : Type*} [Nonempty A] [Nonempty B] : CoeSort (List (prod A B)) (List (A × B)) := ⟨fun x => x⟩

noncomputable def ZIP {A B : Type*} [Nonempty A] [Nonempty B] : (List A) -> (List B) -> List (prod A B) :=
  fun lA lB => if lA.length = lB.length then List.zip lA lB else ZIP_HOL lA lB

/-- `ZIP_HOL` is forced to agree with the structurally recursive `ZIP_Ind`. -/
theorem ZIP_HOL_eq_ZIP_Ind {A B : Type*} [Nonempty A] [Nonempty B] :
    ∀ (lA : List A) (lB : List B), ZIP_HOL lA lB = ZIP_Ind
      (prod_mk (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (prod_mk (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))
      lA lB := by
  set P := (fun ZIP' : prod ℕ (prod ℕ ℕ) → List A → List B → List (prod A B)  ↦ ∀ (_18205 : prod ℕ (prod ℕ ℕ)), (∀ (l2 : List B), ZIP' _18205 NIL l2 = NIL) ∧ ∀ (h1' : A) (t1 : List A) (l2 : List B), ZIP' _18205 (h1' :: t1) l2 = prod_mk h1' (HD l2) :: ZIP' _18205 t1 (TL l2))
  set R := (prod_mk (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (prod_mk (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero))))))))))
  have spec := @Classical.epsilon_spec _ P ⟨ZIP_Ind, by
    intro _18205 ; exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩⟩
  intro lA
  induction lA with
  | nil => intro lB ; exact (spec R).1 lB
  | cons h t ih =>
    intro lB
    exact ((spec R).2 h t lB).trans
      (congrArg (fun z => prod_mk h (HD lB) :: z) (ih (TL lB)))

/-- `ZIP_Ind` ignores its numeric tag. -/
theorem ZIP_Ind_tag_irrel {A B : Type*} [Nonempty A] [Nonempty B]
    (r r' : prod Nat (prod Nat Nat)) :
    ∀ (lA : List A) (lB : List B), ZIP_Ind r lA lB = ZIP_Ind r' lA lB := by
  intro lA
  induction lA with
  | nil => intro lB ; rfl
  | cons h t ih =>
    intro lB
    exact congrArg (fun z => prod_mk h (HD lB) :: z) (ih (TL lB))

/-- On equal-length lists `List.zip` satisfies the same recursion as `ZIP_Ind`. -/
theorem zipInd_eq {A B : Type*} [Nonempty A] [Nonempty B] (R : prod Nat (prod Nat Nat)) :
    ∀ (lA : List A) (lB : List B), lA.length = lB.length → List.zip lA lB = ZIP_Ind R lA lB := by
  intro lA
  induction lA with
  | nil => intro lB _ ; rfl
  | cons h t ih =>
    intro lB hlen
    cases lB with
    | nil => exact absurd hlen (by simp)
    | cons b tb =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      change List.zip (h :: t) (b :: tb) = prod_mk h (HD (b :: tb)) :: ZIP_Ind R t (TL (b :: tb))
      rw [List.zip_cons_cons, ih tb hlen]
      rfl

theorem ZIP_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@ZIP A B _ _) (@ZIP_HOL A B _ _) := by
  unfold ZIP_HOL
  epsilon_tac
  · intro r
    have hZIP : ∀ (lA : List A) (lB : List B), ZIP lA lB = ZIP_Ind r lA lB := by
      intro lA lB
      change (if lA.length = lB.length then List.zip lA lB else ZIP_HOL lA lB) = _
      by_cases h : lA.length = lB.length
      · rw [if_pos h] ; exact zipInd_eq r lA lB h
      · rw [if_neg h]
        exact (ZIP_HOL_eq_ZIP_Ind lA lB).trans (ZIP_Ind_tag_irrel _ r lA lB)
    refine ⟨fun l2 => ?_, fun h t l2 => ?_⟩
    · change ZIP NIL l2 = NIL
      rw [hZIP] ; rfl
    · change ZIP (h :: t) l2 = prod_mk h (HD l2) :: ZIP t (TL l2)
      rw [hZIP, hZIP] ; rfl
  · intro f hZ hf
    funext r lA lB
    induction lA generalizing lB with
    | nil => exact ((hZ r).1 lB).trans ((hf r).1 lB).symm
    | cons h t ih => rw [(hZ r).2 h t lB, (hf r).2 h t lB, ih]

/- --stronger version without the nonemptiness requisite.
def allpairs {A B : Type*} : (A -> B -> Prop) -> (List A) -> (List B) -> Prop := fun R lA lB => ∀ a ∈ lA, ∀ b ∈ lB, R a b -/

open Classical in noncomputable def ALLPAIRS {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (List A) -> (List B) -> Prop := fun R lA lB => lA.all (fun a => lB.all (fun b => R a b))

theorem ALLPAIRS_def {A B : Type*} [Nonempty A] [Nonempty B] : Eq (@ALLPAIRS A B _ _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (A -> B -> Prop) -> (List A) -> (List B) -> Prop) _ (fun ALLPAIRS' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (A -> B -> Prop) -> (List A) -> (List B) -> Prop => ∀ _18213 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), And (∀ f : A -> B -> Prop, ∀ l : List B, Eq (ALLPAIRS' _18213 f (@NIL A _) l) True) (∀ h : A, ∀ f : A -> B -> Prop, ∀ t : List A, ∀ l : List B, Eq (ALLPAIRS' _18213 f (@List.cons A h t) l) (And (@ALL B _ (f h) l) (ALLPAIRS' _18213 f t l)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))))))))))) := by
  epsilon_tac
  · intro r
    refine ⟨fun f l => ?_, fun h f t l => ?_⟩
    · simp [ALLPAIRS, NIL]
    · simp [ALLPAIRS, ALL, List.all_cons, Bool.and_eq_true]
  · intro g hA hg
    funext r f lA
    induction lA with
    | nil => funext l ; exact ((hA r).1 f l).trans ((hg r).1 f l).symm
    | cons h t ih =>
      funext l
      rw [(hA r).2 h f t l, (hg r).2 h f t l, congrFun ih l]

noncomputable def PAIRWISE {A : Type*} [Nonempty A] : (A -> A -> Prop) -> (List A) -> Prop := List.Pairwise

theorem PAIRWISE_def {A : Type*} [Nonempty A] : Eq (@PAIRWISE A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (A -> A -> Prop) -> (List A) -> Prop) _ (fun PAIRWISE' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (A -> A -> Prop) -> (List A) -> Prop => ∀ _18220 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), And (∀ r : A -> A -> Prop, Eq (PAIRWISE' _18220 r (@NIL A _)) True) (∀ h : A, ∀ r : A -> A -> Prop, ∀ t : List A, Eq (PAIRWISE' _18220 r (@List.cons A h t)) (And (@ALL A _ (r h) t) (PAIRWISE' _18220 r t)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))))) := by
  unfold PAIRWISE
  epsilon_tac
  · intros R
    constructor
    · intros P
      unfold NIL
      simp_all only [List.Pairwise.nil]
    · intros h P t
      simp only [List.pairwise_cons, eq_iff_iff, and_congr_left_iff]
      intro h1
      constructor <;> intro h2
      · unfold ALL
        simp only [List.all_eq_true, decide_eq_true_eq] ; exact h2
      · unfold ALL at h2 ; simp only [List.all_eq_true, decide_eq_true_eq] at h2 ; exact h2
  · intros f hQ hQf
    funext B' P
    specialize hQ B'
    specialize hQf B'
    funext l
    induction l
    · have hQ := hQ.1 P
      have hQf := hQf.1 P
      unfold NIL at hQf hQ
      rw[hQf] ; exact hQ
    · rename_i h t ih
      have hQ := hQ.2 h P t
      have hQf := hQf.2 h P t
      rw[ih] at hQ
      rw[hQf]
      exact hQ

def list_of_seq {A : Type*} [Nonempty A] : (Nat -> A) -> Nat -> List A := fun f n => let
  F : (Fin n) → A := fun i => (f i.val)
@List.ofFn A n F

theorem list_of_seq_def {A : Type*} [Nonempty A] : Eq (@list_of_seq A _) (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (Nat -> A) -> Nat -> List A) _ (fun list_of_seq' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (Nat -> A) -> Nat -> List A => ∀ _18227 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))), And (∀ s : Nat -> A, Eq (list_of_seq' _18227 s (NUMERAL Nat.zero)) (@NIL A _)) (∀ s : Nat -> A, ∀ n : Nat, Eq (list_of_seq' _18227 s (Nat.succ n)) (@APPEND A _ (list_of_seq' _18227 s n) (@List.cons A (s n) (@NIL A _))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero))))))))))))))))))) := by
  epsilon_tac
  · intro r
    refine ⟨fun s => ?_, fun s n => ?_⟩
    · simp [list_of_seq, NIL]
    · change List.ofFn (fun i : Fin (n+1) => s i.val) = APPEND (List.ofFn (fun i : Fin n => s i.val)) (s n :: NIL)
      rw [List.ofFn_succ']
      simp [APPEND, NIL]
  · intro g hL hg
    funext r s n
    induction n with
    | zero => exact ((hL r).1 s).trans ((hg r).1 s).symm
    | succ n ih => rw [(hL r).2 s n, (hg r).2 s n, ih]

/-!
# nadd (nearly additive sequences) alignment
-/

/--
Distance between two natural numbers : `DIST(x,y)=(x-y)+(y-x)`. Note that if `x>y`, then `Nat.sub y x = 0`.
-/
@[simp]
def DIST : (prod Nat Nat) -> Nat :=
  fun p : Nat × Nat => ((p.fst) - (p.snd)) + ((p.snd) - (p.fst))

theorem DIST_def : Eq DIST (fun _23033 : prod Nat Nat => Nat.add (Nat.sub (@Prod.fst Nat Nat _23033) (@Prod.snd Nat Nat _23033)) (Nat.sub (@Prod.snd Nat Nat _23033) (@Prod.fst Nat Nat _23033))) := Eq.refl DIST

@[simp]
lemma DIST_REFL : ∀ n, DIST (n,n) = 0 :=
  by intro n ; unfold DIST ; simp only [tsub_self, add_zero]
@[simp]
lemma DIST_SYM (x y : Nat) : DIST (x,y) = DIST (y,x) := by unfold DIST ; lia
@[simp]
lemma DIST_TRIANGLE (x y z : Nat) : DIST (x,z) ≤  DIST (x,y) + DIST (y,z) := by
  unfold DIST ; lia

--is easier to express nearly additive sequences as nearly multiplicative ones
def is_nadd : (Nat -> Nat) -> Prop := fun f : Nat -> Nat =>
  ∃ B : Nat, ∀ m n : Nat, DIST ((m * (f n)),(n *(f m))) ≤ (B * (m + n))

theorem is_nadd_def : Eq is_nadd (fun _23343 : Nat -> Nat => ∃ B : Nat, ∀ m : Nat, ∀ n : Nat, Nat.le (DIST (@prod_mk Nat Nat _ _ (Nat.mul m (_23343 n)) (Nat.mul n (_23343 m)))) (Nat.mul B (Nat.add m n))) := Eq.refl is_nadd

--non-emptiness condition of is_nadd
theorem is_nadd_times (n : Nat) : is_nadd (fun x ↦ n * x) := by
  unfold is_nadd ; simp only ; exact ⟨0, fun m1 m2  => by unfold DIST ; lia⟩

/--
`{f : Nat → Nat | is_nadd f}`
-/
def nadd := SUBTYPE (is_nadd_times 0)
instance : Nonempty nadd := instNonemptySUBTYPE (is_nadd_times 0)

noncomputable def mk_nadd : (Nat -> Nat) -> nadd := mk (is_nadd_times 0)
def dest_nadd : nadd -> (Nat -> Nat) := dest (is_nadd_times 0)

@[simp]
theorem dest_nadd_fun (f : Nat → Nat) (h : is_nadd f) : dest_nadd ⟨f, h⟩ = f := by rfl

theorem axiom_19 : ∀ (a : nadd), Eq (mk_nadd (dest_nadd a)) a := mk_dest (is_nadd_times 0)
theorem axiom_20 : ∀ (r : Nat -> Nat), (is_nadd r) = ((dest_nadd (mk_nadd r)) = r) := dest_mk (is_nadd_times 0)
theorem axiom_20_aux : ∀ (r : Nat -> Nat), (is_nadd r) → ((dest_nadd (mk_nadd r)) = r) := fun r => (Iff.of_eq (axiom_20 r)).1

def nadd_eq : nadd -> nadd -> Prop :=
  fun f : nadd => fun g : nadd => ∃ B : Nat, ∀ n : Nat, DIST ((dest_nadd f n, dest_nadd g n)) ≤ B
theorem nadd_eq_def : Eq nadd_eq (fun _23362 : nadd => fun _23363 : nadd => ∃ B : Nat, ∀ n : Nat, Nat.le (DIST (@prod_mk Nat Nat _ _ (dest_nadd _23362 n) (dest_nadd _23363 n))) B) := Eq.refl nadd_eq

theorem nadd_eq_rfl (f : nadd) : nadd_eq f f := by
  unfold nadd_eq DIST ; exact ⟨0,by lia⟩

theorem nadd_eq_symm (f g : nadd) : nadd_eq f g → nadd_eq g f := by
  intro h ; unfold nadd_eq at * ;
  obtain ⟨B, hB⟩ := h ; exact ⟨B, fun n => by rw[DIST_SYM] ; exact hB n⟩

theorem nadd_eq_trans (f1 f2 f3 : nadd) : nadd_eq f1 f2 → nadd_eq f2 f3 → nadd_eq f1 f3 := by
  intros h12 h23 ; unfold nadd_eq at *
  obtain ⟨B12,hb12⟩ := h12
  obtain ⟨B23,hb23⟩ := h23
  exists B12+B23
  intros n
  specialize hb12 n
  specialize hb23 n
  have h_dt := DIST_TRIANGLE (dest_nadd f1 n) (dest_nadd f2 n) (dest_nadd f3 n)
  lia

theorem nadd_eq_rw (f1 f2 f3 : nadd) : nadd_eq f1 f2 → nadd_eq f1 f3 = nadd_eq f2 f3 := by
  intros h12
  apply Eq.propIntro <;> intros h
  · exact nadd_eq_trans f2 f1 f3 (nadd_eq_symm f1 f2 h12) h
  · exact nadd_eq_trans _ _ _ h12 h


instance : Setoid nadd where
r := nadd_eq
iseqv := ⟨nadd_eq_rfl, nadd_eq_symm _ _, nadd_eq_trans _ _ _⟩

noncomputable def nadd_of_num : Nat -> nadd := fun n : Nat => mk_nadd (fun m : Nat => n * m)
theorem nadd_of_num_def : Eq nadd_of_num (fun _23374 : Nat => mk_nadd (fun n : Nat => Nat.mul _23374 n)) := Eq.refl nadd_of_num

def nadd_le : nadd -> nadd -> Prop := fun f : nadd => fun g : nadd => ∃ B : Nat, ∀ n : Nat, (dest_nadd f n) ≤ ((dest_nadd g n) + B)
theorem nadd_le_def : Eq nadd_le (fun _23381 : nadd => fun _23382 : nadd => ∃ B : Nat, ∀ n : Nat, Nat.le (dest_nadd _23381 n) (Nat.add (dest_nadd _23382 n) B)) := Eq.refl nadd_le
instance : LE nadd := ⟨nadd_le⟩
@[refl]
theorem nadd_le_rfl (f : nadd) : nadd_le f f := ⟨0, fun n => by rfl⟩
@[trans]
theorem nadd_le_trans (f1 f2 f3 : nadd) : nadd_le f1 f2 → nadd_le f2 f3 → nadd_le f1 f3 := by
  intros h12 h23
  unfold nadd_le at *
  obtain ⟨B12,hb12⟩ := h12
  obtain ⟨B23,hb23⟩ := h23
  exists B12+B23
  intros n
  specialize hb12 n
  specialize hb23 n
  have h_dt := DIST_TRIANGLE (dest_nadd f1 n) (dest_nadd f2 n) (dest_nadd f3 n)
  lia

noncomputable def nadd_add : nadd -> nadd -> nadd := fun f : nadd => fun g: nadd => mk_nadd (fun n : Nat => (dest_nadd f n) + (dest_nadd g n))
theorem nadd_add_def : Eq nadd_add (fun _23397 : nadd => fun _23398 : nadd => mk_nadd (fun n : Nat => Nat.add (dest_nadd _23397 n) (dest_nadd _23398 n))) := Eq.refl nadd_add
noncomputable instance : Add nadd := ⟨nadd_add⟩

lemma is_nadd_add_aux (f g : Nat → Nat) : is_nadd f → is_nadd g → is_nadd (fun n => f n + g n) := by
  rintro ⟨Bf, hf⟩ ⟨Bg, hg⟩
  unfold is_nadd ; exists (Bf + Bg) ; intros m n
  specialize hf m n ; specialize hg m n
  unfold DIST at * ; simp_all +arith only ; lia

theorem is_nadd_add (f g : nadd) : is_nadd (fun n ↦ dest_nadd f n + dest_nadd g n) := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  exact is_nadd_add_aux f g hf hg

@[symm]
theorem nadd_add_sym (f g : nadd) : nadd_add f g = nadd_add g f := by
  unfold nadd_add ; lia
@[simp]
theorem nadd_add_assoc (f1 f2 f3 : nadd) : nadd_add (nadd_add f1 f2) f3 = nadd_add f1 (nadd_add f2 f3) := by
  unfold nadd_add
  congr ; funext m  ; simp_all +arith only ;
  have h_a1 := (Iff.of_eq (axiom_20 (fun n ↦ dest_nadd f1 n + dest_nadd f2 n))).1
  have h_a2 := (Iff.of_eq (axiom_20 (fun n ↦ dest_nadd f2 n + dest_nadd f3 n))).1
  rw[h_a1 (is_nadd_add f1 f2), h_a2 (is_nadd_add f2 f3)]
  simp only
  lia

theorem nadd_add_of_num (n m : Nat) : nadd_of_num (n + m) = nadd_add (nadd_of_num n) (nadd_of_num m) := by
  unfold nadd_of_num nadd_add
  congr ; funext k ;
  rw[(Iff.of_eq (axiom_20 _)).1 (is_nadd_times n), (Iff.of_eq (axiom_20 _)).1 (is_nadd_times m)]
  lia

theorem nadd_add_eq_rw (f1 f2 f3 : nadd) : nadd_eq f1 f2 → nadd_eq (nadd_add f1 f3) (nadd_add f2 f3) := by
  rintro ⟨B,h⟩ ; unfold nadd_add nadd_eq at *
  rw[(Iff.of_eq (axiom_20 _)).1 (is_nadd_add f1 f3),
    (Iff.of_eq (axiom_20 _)).1 (is_nadd_add f2 f3)] ; simp only
  exists B ; intro n ; specialize h n
  unfold DIST dest_nadd dest at * ; simp_all ; lia

theorem nadd_add_proper x y p q : nadd_eq x p → nadd_eq y q → nadd_eq (nadd_add x y) (nadd_add p q) := by
  rintro ⟨Bxp, hxp⟩ ⟨Byq, hyq⟩
  unfold nadd_eq nadd_add
  rw[axiom_20_aux _ (is_nadd_add x y), axiom_20_aux _ (is_nadd_add p q)]
  simp only ; unfold dest_nadd dest DIST at * ; simp_all only
  exists (Bxp + Byq) ; intro n
  specialize hxp n
  specialize hyq n
  lia

noncomputable def nadd_mul : nadd -> nadd -> nadd := fun f : nadd => fun g : nadd => mk_nadd (fun n : Nat => dest_nadd f (dest_nadd g n))
theorem nadd_mul_def : Eq nadd_mul (fun _23411 : nadd => fun _23412 : nadd => mk_nadd (fun n : Nat => dest_nadd _23411 (dest_nadd _23412 n))) := Eq.refl nadd_mul
noncomputable instance : Mul nadd := ⟨nadd_mul⟩

noncomputable def nadd_rinv : nadd -> (Nat -> Nat) := fun f : nadd => fun n : Nat => (n * n) / (dest_nadd f n)
theorem nadd_rinv_def : Eq nadd_rinv (fun _23548 : nadd => fun n : Nat => Nat.div (Nat.mul n n) (dest_nadd _23548 n)) := Eq.refl nadd_rinv

noncomputable def nadd_inv : nadd -> nadd := fun f : nadd => @COND nadd _ (nadd_eq f (nadd_of_num (NUMERAL Nat.zero))) (nadd_of_num (NUMERAL Nat.zero)) (mk_nadd (nadd_rinv f))
theorem nadd_inv_def : Eq nadd_inv (fun _23562 : nadd => @COND nadd _ (nadd_eq _23562 (nadd_of_num (NUMERAL Nat.zero))) (nadd_of_num (NUMERAL Nat.zero)) (mk_nadd (nadd_rinv _23562))) := Eq.refl nadd_inv
noncomputable instance : Inv nadd := ⟨nadd_inv⟩

theorem nadd_add_lcancel_Eq f1 f2 f3 : nadd_add f1 f2 = nadd_add f1 f3 → f2 = f3 := by
  intro h_add
  obtain ⟨f1,h1⟩ := f1 ; obtain ⟨f2,h2⟩ := f2 ; obtain ⟨f3,h3⟩ := f3
  unfold nadd_add at h_add
  congr
  have h_a1 : is_nadd fun n ↦ dest_nadd ⟨f1, h1⟩ n + dest_nadd ⟨f2, h2⟩ n := by apply is_nadd_add
  have h_a2 : is_nadd fun n ↦ dest_nadd ⟨f1, h1⟩ n + dest_nadd ⟨f3, h3⟩ n := by apply is_nadd_add
  have h_add := mk_inj _ _ _ h_a1 h_a2 h_add ; clear h_a1 h_a2
  funext a
  have h_add := congrArg (fun f => f a) h_add ; simp only [Nat.add_left_cancel_iff] at h_add
  simp_all only
  exact h_add

theorem nadd_add_lcancel_nadd_eq f1 f2 f3 : nadd_add f1 f2 ≈ nadd_add f1 f3 → f2 ≈ f3 := by
  rintro ⟨B, h⟩
  obtain ⟨f1,h1⟩ := f1 ; obtain ⟨f2,h2⟩ := f2 ; obtain ⟨f3,h3⟩ := f3
  exists B ; intro n ; specialize h n ; revert h
  unfold nadd_add ; simp only [dest_nadd_fun]
  have h_a1 : is_nadd fun n ↦ f1 n + f2 n := by apply is_nadd_add_aux _ _ h1 h2
  have h_a2 : is_nadd fun n ↦ f1 n + f3 n := by apply is_nadd_add_aux _ _ h1 h3
  unfold dest_nadd mk_nadd
  rw[(dest_mk_aux _ _ h_a1), (dest_mk_aux _ _ h_a2)]
  unfold DIST ; lia

/-!
# hreal (non negative real numbers) alignment
hreal is the type of nearly additive (aka nearly multiplicative) sequences on the natural numbers quotiented by the equivalence relation `nadd_eq`, this type defines the positive real numbers.
For more info, see Eudoxus reals: https://ncatlab.org/nlab/show/Eudoxus+real+number
-/

def hreal := QUOTIENT nadd_eq
instance : Nonempty hreal := instNonemptyQUOTIENT nadd_eq

noncomputable def mk_hreal : (nadd -> Prop) -> hreal := mk_quotient nadd_eq
def dest_hreal : hreal -> nadd -> Prop := dest_quotient nadd_eq

theorem axiom_21 : ∀ (a : hreal), Eq (mk_hreal (dest_hreal a)) a := mk_dest_quotient nadd_eq

theorem axiom_22 : ∀ (r : nadd -> Prop), Eq ((fun s : nadd -> Prop => ∃ x : nadd, Eq s (nadd_eq x)) r) (Eq (dest_hreal (mk_hreal r)) r) := dest_mk_quotient nadd_eq
theorem axiom_22_aux : ∀ (r : nadd -> Prop), ((fun s : nadd -> Prop => ∃ x : nadd, s = (nadd_eq x)) r) → ((dest_hreal (mk_hreal r)) = r) := fun r => (Iff.of_eq (axiom_22 r)).1

noncomputable def hreal_of_num : Nat -> hreal := fun m : Nat => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u)

theorem hreal_of_num_def : Eq hreal_of_num (fun m : Nat => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u)) := Eq.refl hreal_of_num

noncomputable def hreal_add : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, ∃ y' : nadd, And (nadd_eq (nadd_add x' y') u) (And (dest_hreal x x') (dest_hreal y y')))

theorem hreal_add_def : Eq hreal_add (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, ∃ y' : nadd, And (nadd_eq (nadd_add x' y') u) (And (dest_hreal x x') (dest_hreal y y')))) := Eq.refl hreal_add

theorem hreal_add_of_num (n m : Nat) : hreal_of_num (n + m) = hreal_add (hreal_of_num n) (hreal_of_num m) := by
  unfold hreal_of_num hreal_add
  congr
  funext s
  apply Eq.propIntro <;> intro h
  · exists (nadd_of_num n), (nadd_of_num m)
    constructor <;> rw[nadd_add_of_num] at h
    · exact h
    · constructor
      · rw[axiom_22_aux _ ⟨nadd_of_num n, by rfl⟩] ; exact nadd_eq_rfl (nadd_of_num n)
      · rw[axiom_22_aux _ ⟨nadd_of_num m, by rfl⟩] ; exact nadd_eq_rfl (nadd_of_num m)
  · obtain ⟨x,y,⟨h_l,⟨h_rl,h_rr⟩⟩⟩ := h
    rw[axiom_22_aux _ ⟨nadd_of_num n, by rfl⟩] at h_rl
    rw[axiom_22_aux _ ⟨nadd_of_num m, by rfl⟩] at h_rr
    rw[nadd_add_of_num]
    have := nadd_add_eq_rw (nadd_of_num n) x (nadd_of_num m) h_rl
    apply nadd_eq_trans _ _ _ this ; clear this
    have h_aux := nadd_add_eq_rw (nadd_of_num m) y x h_rr
    rw[nadd_add_sym] at h_aux
    apply nadd_eq_trans _ _ _ h_aux ; rw[nadd_add_sym] ; exact h_l

@[simp]
theorem hreal_of_num_succ n : hreal_of_num (Nat.succ n) = hreal_add (hreal_of_num n) (hreal_of_num 1) := by
  simp only [Nat.succ_eq_add_one] ; exact hreal_add_of_num n 1

@[simp]
theorem hreal_add_sym p q : hreal_add p q = hreal_add q p := by
  unfold hreal_add ; congr ; funext u ;
  apply Eq.propIntro <;>
  rintro ⟨x,y,⟨h_l,⟨h_px,h_qy⟩⟩⟩ <;>
  rw[nadd_add_sym x y] at h_l <;>
  exact ⟨y,x,⟨h_l,⟨h_qy,h_px⟩⟩⟩

theorem hreal_add_of_mk_hreal p q :
  hreal_add (mk_hreal (nadd_eq p)) (mk_hreal (nadd_eq q))
  = mk_hreal (nadd_eq (nadd_add p q)) := by
  unfold hreal_add ; congr ; funext u ; apply Eq.propIntro
  · rintro ⟨x,y,⟨h_l,⟨h_1,h_2⟩⟩⟩
    unfold dest_hreal mk_hreal at h_1 h_2
    have h_aux := (Iff.of_eq (dest_mk_quotient nadd_eq (nadd_eq p))).1 (is_eq_class_of nadd_eq p)
    rw[h_aux] at h_1 ; clear h_aux
    have h_aux := (Iff.of_eq (dest_mk_quotient nadd_eq (nadd_eq q))).1 (is_eq_class_of nadd_eq q)
    rw[h_aux] at h_2 ; clear h_aux
    refine nadd_eq_trans (nadd_add p q) (nadd_add x y) u ?_ h_l
    exact nadd_add_proper _ _ _ _ h_1 h_2
  · intro h
    exists p, q
    constructor
    · exact h
    · constructor
      · have h_aux := (Iff.of_eq (dest_mk_quotient nadd_eq (nadd_eq p))).1 (is_eq_class_of nadd_eq p)
        unfold dest_hreal mk_hreal
        rw[h_aux] ; exact nadd_eq_rfl p
      · have h_aux := (Iff.of_eq (dest_mk_quotient nadd_eq (nadd_eq q))).1 (is_eq_class_of nadd_eq q)
        unfold dest_hreal mk_hreal
        rw[h_aux] ; exact nadd_eq_rfl q

@[simp]
theorem mk_hreal_nadd_eq p : mk_hreal (nadd_eq (elt_of _ p)) = p := by
  apply mk_quotient_elt_of
      (Rrefl := nadd_eq_rfl)
      (Rsymm := fun a b => propext ⟨nadd_eq_symm a b, nadd_eq_symm b a⟩)
      (Rtrans := nadd_eq_trans)

@[simp]
theorem hreal_add_assoc p q r : hreal_add (hreal_add p q) r = hreal_add p (hreal_add q r) := by
  rw [← mk_hreal_nadd_eq p, ← mk_hreal_nadd_eq q, ← mk_hreal_nadd_eq r,
      hreal_add_of_mk_hreal, hreal_add_of_mk_hreal,
      hreal_add_of_mk_hreal, hreal_add_of_mk_hreal, nadd_add_assoc]

theorem hreal_add_lcancel p q r : hreal_add p r = hreal_add q r -> p = q := by
  intro h
  rw [← mk_hreal_nadd_eq p, ← mk_hreal_nadd_eq q, ← mk_hreal_nadd_eq r,
      hreal_add_of_mk_hreal, hreal_add_of_mk_hreal] at h
  unfold mk_hreal mk_quotient at h
  have h2 := mk_inj _ _ _ (is_eq_class_of nadd_eq _) (is_eq_class_of nadd_eq _) h
  have h3 : nadd_eq (nadd_add (elt_of _ p) (elt_of _ r)) (nadd_add (elt_of _ q) (elt_of _ r)) := by
    apply eq_class_intro (Rsymm := fun a b => propext ⟨nadd_eq_symm a b, nadd_eq_symm b a⟩) (Rrefl := nadd_eq_rfl) ; exact h2
  rw [nadd_add_sym (elt_of _ p) (elt_of _ r), nadd_add_sym (elt_of _ q) (elt_of _ r)] at h3
  have h4 := nadd_add_lcancel_nadd_eq _ _ _ h3
  apply eq_class_intro_elt (Rrefl := nadd_eq_rfl) (Rsymm := fun a b => propext ⟨nadd_eq_symm a b, nadd_eq_symm b a⟩) (Rtrans := nadd_eq_trans)
  exact h4

noncomputable def hreal_mul : hreal -> hreal -> hreal := fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, ∃ y' : nadd, And (nadd_eq (nadd_mul x' y') u) (And (dest_hreal x x') (dest_hreal y y')))

theorem hreal_mul_def : Eq hreal_mul (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, ∃ y' : nadd, And (nadd_eq (nadd_mul x' y') u) (And (dest_hreal x x') (dest_hreal y y')))) := Eq.refl hreal_mul
noncomputable def hreal_le : hreal -> hreal -> Prop := fun x : hreal => fun y : hreal => @Classical.epsilon Prop _ (fun u : Prop => ∃ x' : nadd, ∃ y' : nadd, And (Eq (nadd_le x' y') u) (And (dest_hreal x x') (dest_hreal y y')))
theorem hreal_le_def : Eq hreal_le (fun x : hreal => fun y : hreal => @Classical.epsilon Prop _ (fun u : Prop => ∃ x' : nadd, ∃ y' : nadd, And (Eq (nadd_le x' y') u) (And (dest_hreal x x') (dest_hreal y y')))) := Eq.refl hreal_le
noncomputable def hreal_inv : hreal -> hreal := fun x : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, And (nadd_eq (nadd_inv x') u) (dest_hreal x x'))
theorem hreal_inv_def : Eq hreal_inv (fun x : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, And (nadd_eq (nadd_inv x') u) (dest_hreal x x'))) := Eq.refl hreal_inv

/-!
# treal alignment
treal is just the product type `hreal × hreal`
-/

noncomputable def treal_of_num : Nat -> prod hreal hreal := fun _23807 : Nat => @prod_mk hreal hreal _ _ (hreal_of_num _23807) (hreal_of_num (NUMERAL Nat.zero))
theorem treal_of_num_def : Eq treal_of_num (fun _23807 : Nat => @prod_mk hreal hreal _ _ (hreal_of_num _23807) (hreal_of_num (NUMERAL Nat.zero))) := Eq.refl treal_of_num

noncomputable def treal_neg : (prod hreal hreal) -> prod hreal hreal := fun _23812 : prod hreal hreal => @prod_mk hreal hreal _ _ (@prod_snd hreal hreal _ _ _23812) (@prod_fst hreal hreal _ _ _23812)
theorem treal_neg_def : Eq treal_neg (fun _23812 : prod hreal hreal => @prod_mk hreal hreal _ _ (@prod_snd hreal hreal _ _ _23812) (@prod_fst hreal hreal _ _ _23812)) := Eq.refl treal_neg

noncomputable def treal_add : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23821 : prod hreal hreal => fun _23822 : prod hreal hreal => @prod_mk hreal hreal _ _ (hreal_add (@prod_fst hreal hreal _ _ _23821) (@prod_fst hreal hreal _ _ _23822)) (hreal_add (@prod_snd hreal hreal _ _ _23821) (@prod_snd hreal hreal _ _ _23822))
theorem treal_add_def : Eq treal_add (fun _23821 : prod hreal hreal => fun _23822 : prod hreal hreal => @prod_mk hreal hreal _ _ (hreal_add (@prod_fst hreal hreal _ _ _23821) (@prod_fst hreal hreal _ _ _23822)) (hreal_add (@prod_snd hreal hreal _ _ _23821) (@prod_snd hreal hreal _ _ _23822))) := Eq.refl treal_add

theorem treal_add_of_num p q : treal_of_num (p + q) = treal_add (treal_of_num p) (treal_of_num q) := by
  unfold treal_of_num treal_add prod_mk prod_fst prod_snd
  rw [hreal_add_of_num p q]
  congr 1
  exact hreal_add_of_num 0 0

theorem treal_add_symm p q : treal_add p q = treal_add q p := by
  unfold treal_add prod_mk prod_fst prod_snd
  rw [hreal_add_sym p.1 q.1, hreal_add_sym p.2 q.2]

noncomputable instance : Add hreal := ⟨hreal_add⟩

noncomputable instance : AddCommSemigroup hreal where
  add := hreal_add
  add_assoc := hreal_add_assoc
  add_comm := hreal_add_sym

noncomputable def treal_mul : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal := fun _23843 : prod hreal hreal => fun _23844 : prod hreal hreal => @prod_mk hreal hreal _ _ (hreal_add (hreal_mul (@prod_fst hreal hreal _ _ _23843) (@prod_fst hreal hreal _ _ _23844)) (hreal_mul (@prod_snd hreal hreal _ _ _23843) (@prod_snd hreal hreal _ _ _23844))) (hreal_add (hreal_mul (@prod_fst hreal hreal _ _ _23843) (@prod_snd hreal hreal _ _ _23844)) (hreal_mul (@prod_snd hreal hreal _ _ _23843) (@prod_fst hreal hreal _ _ _23844)))
theorem treal_mul_def : Eq treal_mul (fun _23843 : prod hreal hreal => fun _23844 : prod hreal hreal => @prod_mk hreal hreal _ _ (hreal_add (hreal_mul (@prod_fst hreal hreal _ _ _23843) (@prod_fst hreal hreal _ _ _23844)) (hreal_mul (@prod_snd hreal hreal _ _ _23843) (@prod_snd hreal hreal _ _ _23844))) (hreal_add (hreal_mul (@prod_fst hreal hreal _ _ _23843) (@prod_snd hreal hreal _ _ _23844)) (hreal_mul (@prod_snd hreal hreal _ _ _23843) (@prod_fst hreal hreal _ _ _23844)))) := Eq.refl treal_mul

noncomputable def treal_le : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23865 : prod hreal hreal => fun _23866 : prod hreal hreal => hreal_le (hreal_add (@prod_fst hreal hreal _ _ _23865) (@prod_snd hreal hreal _ _ _23866)) (hreal_add (@prod_fst hreal hreal _ _ _23866) (@prod_snd hreal hreal _ _ _23865))
theorem treal_le_def : Eq treal_le (fun _23865 : prod hreal hreal => fun _23866 : prod hreal hreal => hreal_le (hreal_add (@prod_fst hreal hreal _ _ _23865) (@prod_snd hreal hreal _ _ _23866)) (hreal_add (@prod_fst hreal hreal _ _ _23866) (@prod_snd hreal hreal _ _ _23865))) := Eq.refl treal_le

noncomputable def treal_inv : (prod hreal hreal) -> prod hreal hreal := fun _23887 : prod hreal hreal => @COND (prod hreal hreal) _ (Eq (@prod_fst hreal hreal _ _ _23887) (@prod_snd hreal hreal _ _ _23887)) (@prod_mk hreal hreal _ _ (hreal_of_num (NUMERAL Nat.zero)) (hreal_of_num (NUMERAL Nat.zero))) (@COND (prod hreal hreal) _ (hreal_le (@prod_snd hreal hreal _ _ _23887) (@prod_fst hreal hreal _ _ _23887)) (@prod_mk hreal hreal _ _ (hreal_inv (@Classical.epsilon hreal _ (fun d : hreal => Eq (@prod_fst hreal hreal _ _ _23887) (hreal_add (@prod_snd hreal hreal _ _ _23887) d)))) (hreal_of_num (NUMERAL Nat.zero))) (@prod_mk hreal hreal _ _ (hreal_of_num (NUMERAL Nat.zero)) (hreal_inv (@Classical.epsilon hreal _ (fun d : hreal => Eq (@prod_snd hreal hreal _ _ _23887) (hreal_add (@prod_fst hreal hreal _ _ _23887) d))))))
theorem treal_inv_def : Eq treal_inv (fun _23887 : prod hreal hreal => @COND (prod hreal hreal) _ (Eq (@prod_fst hreal hreal _ _ _23887) (@prod_snd hreal hreal _ _ _23887)) (@prod_mk hreal hreal _ _ (hreal_of_num (NUMERAL Nat.zero)) (hreal_of_num (NUMERAL Nat.zero))) (@COND (prod hreal hreal) _ (hreal_le (@prod_snd hreal hreal _ _ _23887) (@prod_fst hreal hreal _ _ _23887)) (@prod_mk hreal hreal _ _ (hreal_inv (@Classical.epsilon hreal _ (fun d : hreal => Eq (@prod_fst hreal hreal _ _ _23887) (hreal_add (@prod_snd hreal hreal _ _ _23887) d)))) (hreal_of_num (NUMERAL Nat.zero))) (@prod_mk hreal hreal _ _ (hreal_of_num (NUMERAL Nat.zero)) (hreal_inv (@Classical.epsilon hreal _ (fun d : hreal => Eq (@prod_snd hreal hreal _ _ _23887) (hreal_add (@prod_fst hreal hreal _ _ _23887) d))))))) := Eq.refl treal_inv

noncomputable def treal_eq : (prod hreal hreal) -> (prod hreal hreal) -> Prop := fun _23896 : prod hreal hreal => fun _23897 : prod hreal hreal => Eq (hreal_add (@prod_fst hreal hreal _ _ _23896) (@prod_snd hreal hreal _ _ _23897)) (hreal_add (@prod_fst hreal hreal _ _ _23897) (@prod_snd hreal hreal _ _ _23896))
theorem treal_eq_def : Eq treal_eq (fun _23896 : prod hreal hreal => fun _23897 : prod hreal hreal => Eq (hreal_add (@prod_fst hreal hreal _ _ _23896) (@prod_snd hreal hreal _ _ _23897)) (hreal_add (@prod_fst hreal hreal _ _ _23897) (@prod_snd hreal hreal _ _ _23896))) := Eq.refl treal_eq

@[refl]
theorem treal_eq_rfl x : treal_eq x x := rfl

@[symm]
theorem treal_eq_sym x y : treal_eq x y -> treal_eq y x := by
  unfold treal_eq prod_fst prod_snd
  exact Eq.symm

@[trans]
theorem treal_eq_trans x y z : treal_eq x y -> treal_eq y z -> treal_eq x z := by
  unfold treal_eq prod_fst prod_snd
  intros xy yz
  apply hreal_add_lcancel _ _ (hreal_add y.1 y.2)
  change hreal_add x.1 z.2 + hreal_add y.1 y.2 = hreal_add z.1 x.2 + hreal_add y.1 y.2
  change x.1 + z.2 + (y.1 + y.2) = z.1 + x.2 + (y.1 + y.2)
  have xy' : x.1 + y.2 = y.1 + x.2 := xy
  have yz' : y.1 + z.2 = z.1 + y.2 := yz
  calc x.1 + z.2 + (y.1 + y.2)
      = (x.1 + y.2) + (y.1 + z.2) := by simp [add_comm, add_left_comm]
    _ = (y.1 + x.2) + (z.1 + y.2) := by rw [xy', yz']
    _ = z.1 + x.2 + (y.1 + y.2) := by simp [add_comm, add_left_comm]

instance : Setoid (prod hreal hreal) := ⟨treal_eq, ⟨treal_eq_rfl,@treal_eq_sym,@treal_eq_trans⟩⟩

/-!
# real alignment
Reals in HOL Light are defined as the Quotient type of `treal` over the relation `(x1,y1)≈(x2,y2) ↔ x1+y2 = y1+x2` where `+` is `hreal_add`
-/

def real := QUOTIENT (treal_eq)
instance : Nonempty real := instNonemptyQUOTIENT (treal_eq)

namespace real

noncomputable def mk_real : ((prod hreal hreal) → Prop) → real := mk_quotient treal_eq
def dest_real : real → (prod hreal hreal) → Prop := dest_quotient treal_eq

theorem axiom_23 : ∀ (a : real), (mk_real (dest_real a)) = a := fun a => mk_dest_quotient treal_eq a

theorem axiom_24 : ∀ (r : (prod hreal hreal) -> Prop), Eq ((fun s : (prod hreal hreal) -> Prop => ∃ x : prod hreal hreal, Eq s (treal_eq x)) r) (Eq (dest_real (mk_real r)) r) := dest_mk_quotient treal_eq

theorem axiom_24_aux : ∀ (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop => ∃ x : prod hreal hreal, Eq s (treal_eq x)) r) → (Eq (dest_real (mk_real r)) r) := fun r => (Iff.of_eq (axiom_24 r)).1

end real
/- noncomputable def real_of_num : Nat -> real := fun m : Nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)
theorem real_of_num_def : Eq real_of_num (fun m : Nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)) := Eq.refl real_of_num -/
