import HolLightLean.up_to_real
import HolLightLean.hol_up_real_opam
import HolLightLean.hol_up_real_terms
open HolLightLean.hol_up_real_opam
open HolLightLean.hol_up_real_terms

set_option linter.style.longLine false

noncomputable instance {n : Nat} : OfNat real n := ⟨real_of_num n⟩
noncomputable instance : Neg real := ⟨real_neg⟩
noncomputable instance : Add real := ⟨real_add⟩
noncomputable instance : Sub real := ⟨real_sub⟩
noncomputable instance : Mul real := ⟨real_mul⟩
noncomputable instance : Inv real := ⟨real_inv⟩
noncomputable instance : Div real := ⟨real_div⟩
noncomputable instance : Pow real Nat := ⟨real_pow⟩
noncomputable instance : LE real := ⟨real_le⟩
noncomputable instance : LT real := ⟨real_lt⟩
noncomputable instance : Max real := ⟨real_max⟩
noncomputable instance : Min real := ⟨real_min⟩

noncomputable instance instFieldReal : Field real where
  zero := 0
  one := 1
  add := real_add
  mul := real_mul
  neg := real_neg
  inv := real_inv
  add_assoc := fun a b c => (thm_REAL_ADD_ASSOC a b c).symm
  add_comm := thm_REAL_ADD_SYM
  zero_add := thm_REAL_ADD_LID
  add_zero := thm_REAL_ADD_RID
  zero_mul := thm_REAL_MUL_LZERO
  mul_zero := thm_REAL_MUL_RZERO
  mul_assoc := fun a b c => (thm_REAL_MUL_ASSOC a b c).symm
  mul_comm := thm_REAL_MUL_SYM
  mul_one := thm_REAL_MUL_RID
  one_mul := thm_REAL_MUL_LID
  mul_inv_cancel := thm_REAL_MUL_RINV
  inv_zero := thm_REAL_INV_0
  left_distrib := thm_REAL_ADD_LDISTRIB
  right_distrib := thm_REAL_ADD_RDISTRIB
  neg_add_cancel := thm_REAL_ADD_LINV
  exists_pair_ne := ⟨real_of_num 0, real_of_num 1, by intro h; rw[thm_REAL_OF_NUM_EQ 0 1] at h; lia⟩
  npow := fun n a => real_pow a n
  npow_zero := fun a => (thm_real_pow a).1
  npow_succ := fun n a => ((thm_real_pow a).2 n).trans (thm_REAL_MUL_SYM a (real_pow a n))
  nsmul := nsmulRec
  zsmul := zsmulRec
  nnqsmul := _
  qsmul := _

theorem real_lt_iff_le_not_ge : ∀ a b, real_lt a b ↔ real_le a b ∧ ¬ real_le b a := by
  intros a b
  constructor
  · intro h
    have h_1 := thm_REAL_LT_IMP_LE a b h
    exact ⟨h_1, by rw[(thm_real_lt b a)] at h ; exact h⟩
  · rintro ⟨l,r⟩
    rw[(thm_real_lt b a)] ; exact r

noncomputable instance instLinearOrderReal : LinearOrder real where
  le := real_le
  lt := real_lt
  le_refl := thm_REAL_LE_REFL
  le_trans := fun a b c hab hbc => thm_REAL_LE_TRANS a b c ⟨hab, hbc⟩
  le_antisymm := fun a b hab hba => by rw[← thm_REAL_LE_ANTISYM a b] ; exact ⟨hab,hba⟩
  le_total := thm_REAL_LE_TOTAL
  lt_iff_le_not_ge := real_lt_iff_le_not_ge
  toDecidableLE := Classical.decRel _

instance instIsOrderedAddMonoidReal : IsOrderedAddMonoid real where
  add_le_add_left a b hab c := by
    have h := thm_REAL_LE_LADD_IMP c a b hab
    rewrite [(thm_REAL_ADD_SYM c a), (thm_REAL_ADD_SYM c b)] at h
    exact h

instance instContravariantClassReal :
    ContravariantClass real real (· + ·) (· ≤ ·) where
  elim a b c h := by
   simp only [add_le_add_iff_left] at * ; exact h

instance : ZeroLEOneClass real := ⟨thm_REAL_LE_01⟩

noncomputable instance instIsStrictOrderedRingReal : IsStrictOrderedRing real where
mul_lt_mul_of_pos_left := fun a ha0 b c hbc => thm_REAL_LT_LMUL a b c ⟨ha0,hbc⟩
mul_lt_mul_of_pos_right := fun a ha0 b c hbc => thm_REAL_LT_RMUL b c a ⟨hbc,ha0⟩

noncomputable def real_sup : (Set real) → real := by
  intro P
  by_cases h : ∃ x, P x
  · by_cases i : ∃ M, ∀ x, P x → x ≤ M
    · let Q : Set real :=
        fun M =>
          (∀ x : real, P x → x ≤ M) ∧
          (∀ M' : real, (∀ x : real, P x → x ≤ M') → M ≤ M')
      exact Classical.epsilon Q
    · exact 0
  · exact 0

noncomputable def real_inf : (Set real) → real := by
  intro P
  by_cases h : ∃ x, P x
  · by_cases i : ∃ m, ∀ x, P x → m ≤ x
    · let Q : Set real :=
        fun m =>
          (∀ x : real, P x → m ≤ x) ∧
          (∀ m' : real, (∀ x : real, P x → m'≤ x) → m'≤ m)
      exact Classical.epsilon Q
    · exact 0
  · exact 0

theorem real_IsLUB_pred_csSup : ∀ (s : Set real),
  s.Nonempty → BddAbove s → IsLUB s (real_sup s) := by
    intro S hS h1
    unfold IsLUB IsLeast upperBounds lowerBounds real_sup
    constructor <;>
    simp only [dite_eq_ite, Set.mem_setOf_eq] <;>
    intro r hr <;>
    have he : ∃ x, S x := hS <;>
    simp only [he] <;>
    by_cases hM : ∃ M, ∀ (x : real), S x → x ≤ M <;>
    simp only [hM] <;>
    try contradiction
    · have h_aux := @Classical.epsilon_spec _ _ (thm_REAL_COMPLETE S ⟨he, hM⟩)
      exact h_aux.1 r hr
    · have h_aux := @Classical.epsilon_spec _ _ (thm_REAL_COMPLETE S ⟨he, hM⟩)
      exact h_aux.2 r hr

def real_IsGLB_pred (S : Set real) (m : real) : Prop :=
  (∀ x, S x → m ≤ x) ∧
  ∀ m', (∀ x, S x → m' ≤ x) → m' ≤ m

def real_IsLUB_pred (S : Set real) (M : real) : Prop :=
  (∀ x, S x → x ≤ M) ∧
  ∀ M', (∀ x, S x → x ≤ M') → M ≤ M'

lemma real_IsGLB_pred_neg_iff_isLUB_pred_neg {S : Set real} {m : real}
: real_IsGLB_pred S m ↔ real_IsLUB_pred (-S) (-m) := by
    constructor
    · intro h
      rcases h with ⟨h_lb, h_greatest⟩
      constructor
      · intro x hx
        change S (-x) at hx
        have := h_lb (-x) hx
        linarith
      · intro M hM
        have hLower : ∀ x, S x → -M ≤ x := by
          intro x hx
          have := hM (-x)
          have hx' : (-S) (-x) := by
            change S (- (- x))
            simpa using hx
          have h := this hx'
          linarith
        have := h_greatest (-M) hLower
        linarith
    · intro h
      rcases h with ⟨h_ub, h_least⟩
      constructor
      · intro x hx
        have h := h_ub (-x)
        have hx' : (-S) (-x) := by
          change S (- (- x))
          simpa using hx
        have := h hx'
        linarith
      · intro m' hm'
        have hUpper : ∀ x, (-S) x → x ≤ -m' := by
          intro x hx
          change S (-x) at hx
          have := hm' (-x) hx
          linarith
        have := h_least (-m') hUpper
        linarith

theorem real_IsLUB_pred_unique {S : Set real} {a b : real} :
    real_IsLUB_pred S a → real_IsLUB_pred S b → a = b := by
      rintro ⟨ha_upper, ha_least⟩ ⟨hb_upper, hb_least⟩
      apply le_antisymm
      · exact ha_least b hb_upper
      · exact hb_least a ha_upper

theorem real_isGLB_csInf_aux : ∀ S : Set real,
  S.Nonempty → BddBelow S → IsGLB S (- real_sup (-S)) := by
    intros S hS hb
    rw[← bddAbove_neg] at hb
    rw[← isLUB_neg]
    have hnS : (-S).Nonempty := Set.Nonempty.neg hS
    apply real_IsLUB_pred_csSup (-S) hnS hb

lemma set_neg_neg : ∀ S : Set real, ∀  x : real, S x ↔ (-S) (-x) := by
  intros S x
  constructor <;> intro h
  · change S (-(-x))
    simp only [neg_neg] ; exact h
  · change S (-(-x))  at h ; simp only [neg_neg] at h ; exact h

theorem real_inf_neg_sup : ∀ (S : Set real), - (real_inf S) = real_sup (-S) := by
    intro S
    unfold real_inf real_sup
    by_cases h : (∃ x, S x)
    · simp only [h, ↓reduceDIte, dite_eq_ite]
      by_cases (∃ m, ∀ (x : real), S x → m ≤ x) <;> rename_i h1 <;>
      have h_aux1 : ∃ x, (-S) x := by apply (Set.nonempty_def).1 (Set.Nonempty.neg h)
      · have h_aux2 : ∃ M, ∀ (x : real), (-S) x → x ≤ M := by
              obtain ⟨m,h1⟩ := h1 ; exists (-m) ; intro x h' ; specialize h1 (-x) h' ; grind only
        simp only [h1, ↓reduceIte, h_aux1, h_aux2]
        apply real_IsLUB_pred_unique
        · apply (@real_IsGLB_pred_neg_iff_isLUB_pred_neg S).1
          refine Classical.epsilon_spec ?_
          exact ⟨- real_sup (-S), real_isGLB_csInf_aux S (Set.nonempty_def.2 h) h1⟩
        · refine Classical.epsilon_spec ?_
          exact ⟨real_sup (-S), real_IsLUB_pred_csSup (-S) (Set.nonempty_def.2 h_aux1) h_aux2⟩
      · have h_aux2 : ¬ ∃ M, ∀ (x : real), (-S) x → x ≤ M
        := by rintro ⟨m,h1'⟩ ;
                have : ∃ m, ∀ (x : real), S x → m ≤ x
                := ⟨-m, by intro x h' ;
                            have : (-S) (-x) :=
                              (set_neg_neg  S x).1 h' ;
                            specialize h1' (-x) this ;
                            grind⟩ ;
                contradiction
        simp[h1, h_aux1,h_aux2 ]
    · have h_neg : ¬ ∃ x, (-S) x := by rintro ⟨x',h'⟩ ;
                                        have : ∃ x, S x := ⟨-x', h'⟩ ;
                                        contradiction
      simp[h, h_neg]

theorem real_IsGLB_pred_csInf : ∀ (s : Set real),
    s.Nonempty → BddBelow s → IsGLB s (real_inf s) := by
      intros S hS hbB
      have : (real_inf S) = - real_sup (-S)
        := by
          rw[← neg_neg (real_inf S)] ;
          apply congrArg (fun a : real => - a) ;
          exact real_inf_neg_sup S
      rw[this]
      exact real_isGLB_csInf_aux S hS hbB

theorem real_csSup_of_not_bddAbove : ∀ (s : Set real),
  ¬BddAbove s → real_sup s = real_sup ∅ := by
    intros S h ; unfold real_sup ; unfold BddAbove upperBounds at h
    rw[Set.nonempty_def] at h
    by_cases hS : ∃ x, S x <;>
    change ¬ ∃ M, ∀ (x : real), S x → x ≤ M at h <;>
    simp only [hS, ↓reduceDIte, h, dite_eq_ite, right_eq_ite_iff,
        forall_exists_index] <;>
    intro x1 h0 x2 h0_1 <;>
    apply align_epsilon <;> contradiction

theorem real_csInf_of_not_bddBelow : ∀ (s : Set real),
 ¬BddBelow s → real_inf s = real_inf ∅ := by
    intros S h ; unfold real_inf
    unfold BddBelow lowerBounds at h
    rw[Set.nonempty_def] at h
    by_cases hS : ∃ x, S x <;>
    change ¬ ∃ m, ∀ (x : real), S x → m ≤ x at h <;>
    simp only [hS, ↓reduceDIte, h, dite_eq_ite, right_eq_ite_iff,
        forall_exists_index] <;>
    intro x1 h0 x2 h0_1 <;>
    apply align_epsilon <;> contradiction

noncomputable instance instConditionallyCompleteLinearOrderReal :
    ConditionallyCompleteLinearOrder real where
  __ := instLinearOrderReal
  sup := fun a b => real_max a b
  inf := fun a b => real_min a b
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le := fun _ _ _ => max_le
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf := fun _ _ _ => le_min
  sSup := real_sup
  sInf := real_inf
  isLUB_csSup := real_IsLUB_pred_csSup
  isGLB_csInf := real_IsGLB_pred_csInf
  csSup_of_not_bddAbove := real_csSup_of_not_bddAbove
  csInf_of_not_bddBelow := real_csInf_of_not_bddBelow

noncomputable def iso_real_Real : real ≃+*o ℝ :=
  (ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso (β := real) (γ := ℝ)).default

noncomputable def iso_Real_real : ℝ ≃+*o real := iso_real_Real.symm

theorem iso_Real_real_inv : iso_real_Real = iso_Real_real.symm := OrderRingIso.ext (congrFun rfl)

noncomputable def mk_real := iso_real_Real ∘ (real.mk_real)
def dest_real := real.dest_real ∘ iso_Real_real

theorem axiom_23 : ∀ (a : Real), (mk_real (dest_real a)) = a := fun a =>
by
  unfold mk_real dest_real
  simp only [Function.comp_apply]
  rw[real.axiom_23 (iso_Real_real a)]
  unfold iso_Real_real
  simp only [OrderRingIso.apply_symm_apply]


theorem axiom_24 : ∀ (r : (prod hreal hreal) -> Prop), Eq ((fun s : (prod hreal hreal) -> Prop =>
∃ x : prod hreal hreal, Eq s (treal_eq x)) r) (Eq (dest_real (mk_real r)) r) := fun r => by
    unfold mk_real dest_real
    rw[real.axiom_24 r]
    simp only [Function.comp_apply, iso_Real_real_inv, OrderRingIso.apply_symm_apply]

/-
theorem axiom_24_aux : ∀ (r : (prod hreal hreal) -> Prop), ((fun s : (prod hreal hreal) -> Prop =>
    ∃ x : prod hreal hreal, Eq s (treal_eq x)) r) → (Eq (dest_real (mk_real r)) r) := fun r =>
        (Iff.of_eq (axiom_24 r)).1
-/

theorem real_symm_apply_eq (x : real) (y : Real) : iso_real_Real x = y ↔ x = iso_Real_real y := by
  unfold iso_Real_real
  apply Iff.intro <;> intro a <;> subst a
  · simp_all only [OrderRingIso.symm_apply_apply]
  · simp_all only [OrderRingIso.apply_symm_apply]


noncomputable def real_le : Real -> Real -> Prop := fun x : Real => fun y : Real =>
        (@LE.le real _
        (iso_Real_real x) (iso_Real_real y)
        )

theorem real_le_eq : _root_.real_le = @LE.le ℝ _ := by
  funext x y
  unfold _root_.real_le
  simp only [iso_Real_real]
  ext ; constructor <;>
  intro a <;>
  simp_all only [map_le_map_iff]

theorem real_le_def : @LE.le ℝ _ = (fun x1 : Real => fun y1 : Real => @Classical.epsilon Prop _ (fun u : Prop => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, ((treal_le x1' y1') = u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))) := by
  rw[← real_le_eq]
  unfold _root_.real_le
  funext x y
  simp only [dest_real, Function.comp_apply]
  generalize iso_Real_real x = a
  generalize iso_Real_real y = b
  rfl

noncomputable def real_add : Real -> Real -> Real := fun x : Real => fun y : Real =>
    iso_real_Real
        (@Add.add real _
        (iso_Real_real x) (iso_Real_real y)
        )

theorem real_add_eq : _root_.real_add = @Add.add ℝ _ := by
    funext r s
    unfold _root_.real_add
    simp only [iso_Real_real, real_symm_apply_eq]
    symm
    exact iso_real_Real.symm.map_add r s

theorem real_add_def : @Add.add ℝ _ = fun x1 : Real => fun y1 : Real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1'))) := by
  rw[← real_add_eq]
  funext x y
  unfold _root_.real_add
  simp only [iso_Real_real,real_symm_apply_eq]
  unfold mk_real
  simp only [Function.comp_apply, OrderRingIso.symm_apply_apply]
  congr

noncomputable def real_mul : Real -> Real -> Real := fun x y : Real =>
    iso_real_Real
        (@Mul.mul real _
        (iso_Real_real x) (iso_Real_real y)
        )

theorem real_mul_eq : _root_.real_mul = @Mul.mul Real _ := by
    funext r s
    unfold _root_.real_mul
    simp only [iso_Real_real, real_symm_apply_eq]
    symm
    exact iso_real_Real.symm.map_mul r s

theorem real_mul_def : @Mul.mul Real _ = (fun x1 : Real => fun y1 : Real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))) := by
  rw[← real_mul_eq]
  funext x y
  unfold _root_.real_mul
  simp only [iso_Real_real,real_symm_apply_eq]
  unfold mk_real
  simp only [Function.comp_apply, OrderRingIso.symm_apply_apply]
  congr

noncomputable def real_neg : Real → Real := fun x : Real =>
  iso_real_Real
    (@Neg.neg real _
      (iso_Real_real x)
    )

theorem real_neg_eq : _root_.real_neg = @Neg.neg Real _ := by
  funext r
  unfold _root_.real_neg
  simp only [iso_Real_real, real_symm_apply_eq]
  symm
  exact iso_real_Real.symm.map_neg r

theorem real_neg_def :
    @Neg.neg Real _ =
      (fun x1 : Real =>
        mk_real (fun u : prod hreal hreal =>
          ∃ x1' : prod hreal hreal,
            (treal_eq (treal_neg x1') u) ∧
            (dest_real x1 x1'))) := by
  rw [← real_neg_eq]
  funext x
  unfold _root_.real_neg
  simp only [iso_Real_real, real_symm_apply_eq]
  unfold mk_real
  simp only [Function.comp_apply, OrderRingIso.symm_apply_apply]
  congr

noncomputable def real_inv : Real → Real := fun x : Real =>
  iso_real_Real
    (@Inv.inv real _
      (iso_Real_real x)
    )

theorem real_inv_eq : _root_.real_inv = @Inv.inv Real _ := by
  funext r
  unfold _root_.real_inv
  simp only [iso_Real_real, real_symm_apply_eq]
  symm
  exact map_inv₀ iso_real_Real.symm r

theorem real_inv_def :
    @Inv.inv Real _ =
      (fun x : Real =>
        mk_real (fun u : prod hreal hreal =>
          ∃ x' : prod hreal hreal,
            (treal_eq (treal_inv x') u) ∧
            (dest_real x x'))) := by
  rw [← real_inv_eq]
  funext x
  unfold _root_.real_inv
  simp only [iso_Real_real, real_symm_apply_eq]
  unfold mk_real
  simp only [Function.comp_apply, OrderRingIso.symm_apply_apply]
  congr

noncomputable def real_sub : Real → Real → Real := fun x y =>
  iso_real_Real
    (@Sub.sub real _
      (iso_Real_real x)
      (iso_Real_real y))

theorem real_sub_eq : _root_.real_sub = @Sub.sub Real _ := by
  funext r s
  unfold _root_.real_sub
  simp only [iso_Real_real, real_symm_apply_eq]
  symm
  exact iso_real_Real.symm.map_sub r s

theorem real_sub_def : @Sub.sub Real _ = fun _24112 : Real => fun _24113 : Real => real_add _24112 (real_neg _24113) := by
  rw [← real_sub_eq]
  funext x y
  unfold _root_.real_sub
  simp only [iso_Real_real, real_symm_apply_eq]
  unfold _root_.real_add _root_.real_neg
  simp only [OrderRingIso.symm_apply_apply, iso_Real_real]
  rfl

noncomputable def real_lt : Real → Real → Prop := fun x y : Real =>
        (@LT.lt real _
        (iso_Real_real x) (iso_Real_real y)
        )

theorem real_lt_eq : _root_.real_lt = @LT.lt Real _ := by
  funext x y
  unfold _root_.real_lt
  simp only [eq_iff_iff]
  exact map_lt_map_iff (iso_Real_real)

theorem real_lt_def :
    @LT.lt Real _ =
      (fun x y : Real => ¬ (real_le y x)) := by
  funext x y
  unfold LT.lt
  rw [real_le_eq]
  simp_all only [not_le, eq_iff_iff]
  rfl

def real_ge : ℝ → ℝ → Prop := (fun x y : Real => real_le y x)

theorem real_ge_def :
    @GE.ge Real _ =
      (fun x y : Real => real_le y x) := by
  funext x y
  unfold GE.ge
  rw [real_le_eq]

def real_gt : ℝ → ℝ → Prop := (fun x y : Real => real_lt y x)

theorem real_gt_def :
    @GT.gt Real _ =
      (fun x y : Real => real_lt y x) := by
  funext x y
  unfold GT.gt _root_.real_lt
  ext ; symm
  exact map_lt_map_iff (iso_real_Real.symm)

noncomputable def real_div : Real → Real → Real := (fun x y : Real => real_mul x (real_inv y))

theorem real_div_def :
    @Div.div Real _ =
      (fun x y : Real => real_mul x (real_inv y)) := by
  funext x y
  unfold Div.div
  rw [_root_.real_mul_eq, _root_.real_inv_eq]
  rfl

noncomputable def real_max : ℝ → ℝ → ℝ := (fun x y : Real => @COND Real _ (real_le x y) y x)

theorem real_max_def :
    max =
      (fun x y : Real =>
        @COND Real _ (real_le x y) y x) := by
  funext x y
  unfold max
  rw [_root_.real_le_eq]
  unfold COND
  split_ifs <;> grind

noncomputable def real_min : ℝ → ℝ → ℝ := (fun x y : Real => @COND Real _ (real_le x y) x y)

theorem real_min_def :
    min =
      (fun x y : Real =>
        @COND Real _ (real_le x y) x y) := by
  funext x y
  unfold min
  rw [_root_.real_le_eq]
  unfold COND
  split_ifs <;> grind

noncomputable def real_of_num : Nat -> Real := fun m : Nat => mk_real (fun u : prod hreal hreal =>
    treal_eq (treal_of_num m) u)

theorem real_of_num_def : _root_.real_of_num = @Nat.cast ℝ _ := by
    funext n
    unfold _root_.real_of_num mk_real
    simp only [Function.comp_apply]
    induction n
    · simp ; rfl
    · expose_names
      simp_all only [prod_def, real_symm_apply_eq, map_natCast, Nat.cast_add, Nat.cast_one, map_add,
        map_one]
      have : (HolLightLean.hol_up_real_terms.real_of_num 1) = 1 := by exact Eq.refl (HolLightLean.hol_up_real_terms.real_of_num 1)
      rw[← h, ← this]
      have := (thm_REAL_OF_NUM_ADD n 1).symm
      simp only [HolLightLean.hol_up_real_terms.real_of_num] at this
      exact this

def real_abs : Real → Real := abs

theorem real_abs_def : abs = (fun _24160 : Real => @COND Real _ (real_le (real_of_num (NUMERAL Nat.zero)) _24160) _24160 (real_neg _24160)) := by
  funext x
  unfold abs
  rw [_root_.real_le_eq, _root_.real_of_num_def, _root_.real_neg_eq]
  unfold COND
  split_ifs <;> simp_all only [NUMERAL, Nat.zero_eq, CharP.cast_eq_zero, neg_le_self_iff,
    sup_of_le_left] ; grind


noncomputable def real_pow : Real →  Nat→ Real := fun x y =>
  iso_real_Real
    (@Pow.pow real Nat _
    (iso_Real_real x)
      y)

theorem real_pow_eq : _root_.real_pow = @Pow.pow Real Nat _ := by
  funext r s
  unfold _root_.real_pow
  simp only [iso_Real_real, real_symm_apply_eq]
  symm
  exact map_pow (iso_real_Real.symm) r s

theorem real_pow_def : @Pow.pow Real Nat _ = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Real -> Nat -> Real) _ (fun real_pow' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Real -> Nat -> Real => ∀ _24171 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ x : Real, (real_pow' _24171 x (NUMERAL Nat.zero)) = (_root_.real_of_num (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : Real, ∀ n : Nat, (real_pow' _24171 x (Nat.succ n)) = (real_mul x (real_pow' _24171 x n)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))))))))))) := by
  epsilon_tac
  · intros r
    constructor
    · intro x
      simp only [NUMERAL, Nat.zero_eq, _root_.real_of_num_def, BIT1, BIT0, add_zero,
        Nat.succ_eq_add_one, zero_add, Nat.cast_one]
      rfl
    · intro x n ;
      simp[_root_.real_mul_eq, Pow.pow, Mul.mul, pow_succ'] ; rfl
  · intros HOL_POW h h1
    funext r x n
    specialize h r
    specialize h1 r
    simp_all only [NUMERAL, Nat.zero_eq, BIT1, BIT0, add_zero, Nat.succ_eq_add_one, zero_add]
    induction n
    · grind
    · grind

noncomputable def real_sgn : Real -> Real := fun x => x / abs x

theorem real_sgn_eq : _root_.real_sgn = Real.sign := by
  funext x
  unfold _root_.real_sgn
  by_cases h : x ≤ 0
  · by_cases h : x < 0
    · rw[Real.sign_of_neg h, abs_of_neg h]
      grind
    · simp_all
      have : x = 0 := by grind
      subst this
      simp_all only [Std.le_refl, abs_zero, div_zero, Real.sign_zero]
  · simp_all only [not_le]
    rw[Real.sign_of_pos h, abs_of_pos h]
    grind


theorem real_sgn_def : Real.sign = (fun _26684 : Real => @COND Real _ (real_lt (real_of_num (NUMERAL Nat.zero)) _26684) (real_of_num (NUMERAL (BIT1 Nat.zero))) (@COND Real _ (real_lt _26684 (real_of_num (NUMERAL Nat.zero))) (real_neg (real_of_num (NUMERAL (BIT1 Nat.zero)))) (real_of_num (NUMERAL Nat.zero)))) := by
  funext x
  simp only [COND, real_lt_eq, _root_.real_of_num_def, NUMERAL, Nat.zero_eq, CharP.cast_eq_zero,
    BIT1, BIT0, add_zero, Nat.succ_eq_add_one, zero_add, Nat.cast_one, real_neg_eq]
  split_ifs
  · (expose_names; exact Real.sign_of_pos h)
  · (expose_names; exact Real.sign_of_neg h_1)
  · simp_all ; grind

/-!
### `SQRT`

`SQRT` is transported from `real` to `ℝ` like the other operations, but its `_eq` lemma
cannot be a one-line `map_*`: HOL Light defines it with `ε`, so it is not the image of a
homomorphism.  Instead we transport `sgn`, `pow` and `abs` across the isomorphism and use
that the specification determines its solution uniquely (`eq_of_sign_eq_of_sq_eq`).
-/

theorem iso_inj {a b : real} (h : iso_real_Real a = iso_real_Real b) : a = b :=
  iso_real_Real.injective h

theorem iso_pow (a : real) (n : Nat) : iso_real_Real (HolLightLean.hol_up_real_terms.real_pow a n) = (iso_real_Real a) ^ n :=
  map_pow iso_real_Real a n

theorem iso_abs (a : real) : iso_real_Real (HolLightLean.hol_up_real_terms.real_abs a) = |iso_real_Real a| := by
  have h0 : iso_real_Real (0 : real) = 0 := map_zero _
  unfold HolLightLean.hol_up_real_terms.real_abs COND
  split_ifs with h
  · have hge : (0:ℝ) ≤ iso_real_Real a := by
      rw [← h0] ; exact (map_le_map_iff iso_real_Real).2 h
    exact (abs_of_nonneg hge).symm
  · have hlt : iso_real_Real a < 0 := by
      rw [← h0] ; exact (map_lt_map_iff iso_real_Real).2 (lt_of_not_ge h)
    change iso_real_Real (-a) = _
    rw [map_neg, abs_of_neg hlt]

theorem iso_sgn (a : real) : iso_real_Real (HolLightLean.hol_up_real_terms.real_sgn a) = Real.sign (iso_real_Real a) := by
  have h0 : iso_real_Real (0 : real) = 0 := map_zero _
  have h1 : iso_real_Real (1 : real) = 1 := map_one _
  unfold HolLightLean.hol_up_real_terms.real_sgn COND
  split_ifs with hp hn
  · have hpos : (0:ℝ) < iso_real_Real a := by
      rw [← h0] ; exact (map_lt_map_iff iso_real_Real).2 hp
    rw [Real.sign_of_pos hpos] ; exact h1
  · have hneg : iso_real_Real a < 0 := by
      rw [← h0] ; exact (map_lt_map_iff iso_real_Real).2 hn
    rw [Real.sign_of_neg hneg]
    change iso_real_Real (-(1:real)) = -1
    rw [map_neg, h1]
  · have ha : a = 0 := le_antisymm (not_lt.1 hp) (not_lt.1 hn)
    subst ha
    change iso_real_Real (0:real) = Real.sign (iso_real_Real (0:real))
    rw [h0, Real.sign_zero]

noncomputable def SQRT_HOL := fun x : Real => if x ≥ 0 then Real.sqrt x else - (Real.sqrt (-x))

theorem eq_of_sign_eq_of_sq_eq {x y : ℝ} (hs : Real.sign x = Real.sign y) (hq : x ^ 2 = y ^ 2) :
    x = y := by
  have habs : |x| = |y| := by
    have h := congrArg Real.sqrt hq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h
  rcases abs_eq_abs.1 habs with h | h
  · exact h
  · subst h
    rw [Real.sign_neg] at hs
    have hy : Real.sign y = 0 := by linarith
    rw [Real.sign_eq_zero_iff] at hy
    simp [hy]

theorem sqrt_hol_spec (s : ℝ) :
    Real.sign (SQRT_HOL s) = Real.sign s ∧ (SQRT_HOL s) ^ 2 = |s| := by
  unfold SQRT_HOL
  rcases lt_trichotomy s 0 with h | h | h
  · rw [if_neg (by simpa using h)]
    refine ⟨?_, ?_⟩
    · rw [Real.sign_neg, Real.sign_of_pos (Real.sqrt_pos.2 (neg_pos.2 h)), Real.sign_of_neg h]
    · rw [neg_sq, Real.sq_sqrt (neg_nonneg.2 h.le), abs_of_neg h]
  · subst h ; simp
  · rw [if_pos h.le]
    exact ⟨by rw [Real.sign_of_pos (Real.sqrt_pos.2 h), Real.sign_of_pos h],
           by rw [Real.sq_sqrt h.le, abs_of_pos h]⟩

noncomputable def real_SQRT : Real -> Real := fun x =>
  iso_real_Real (HolLightLean.hol_up_real_terms.SQRT (iso_Real_real x))

theorem real_SQRT_eq : real_SQRT = SQRT_HOL := by
  have hsymm : ∀ y : Real, iso_real_Real (iso_Real_real y) = y :=
    fun y => iso_real_Real.apply_symm_apply y
  have hSQ : ∀ w : real, HolLightLean.hol_up_real_terms.SQRT w = Classical.epsilon (fun y : real =>
      HolLightLean.hol_up_real_terms.real_sgn y = HolLightLean.hol_up_real_terms.real_sgn w ∧
      HolLightLean.hol_up_real_terms.real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero))) = HolLightLean.hol_up_real_terms.real_abs w) :=
    fun w => congrFun HolLightLean.hol_up_real_terms.SQRT_def w
  funext x
  have hxz : iso_real_Real (iso_Real_real x) = x := hsymm x
  have hsat : ∃ y : real, HolLightLean.hol_up_real_terms.real_sgn y = HolLightLean.hol_up_real_terms.real_sgn (iso_Real_real x) ∧
      HolLightLean.hol_up_real_terms.real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero))) = HolLightLean.hol_up_real_terms.real_abs (iso_Real_real x) := by
    refine ⟨iso_Real_real (SQRT_HOL x), ?_, ?_⟩
    · refine iso_inj ?_
      rw [iso_sgn, iso_sgn, hsymm, hxz]
      exact (sqrt_hol_spec x).1
    · refine iso_inj ?_
      rw [iso_pow, iso_abs, hsymm, hxz]
      exact (sqrt_hol_spec x).2
  have hspec := Classical.epsilon_spec hsat
  rw [← hSQ (iso_Real_real x)] at hspec
  have hs1 : Real.sign (real_SQRT x) = Real.sign x := by
    have h := congrArg iso_real_Real hspec.1
    rwa [iso_sgn, iso_sgn, hxz] at h
  have hs2 : (real_SQRT x) ^ 2 = |x| := by
    have h := congrArg iso_real_Real hspec.2
    rwa [iso_pow, iso_abs, hxz] at h
  exact eq_of_sign_eq_of_sq_eq (hs1.trans (sqrt_hol_spec x).1.symm)
    (hs2.trans (sqrt_hol_spec x).2.symm)

theorem SQRT_def : SQRT_HOL = (fun _27235 : Real => @Classical.epsilon Real _ (fun y : Real => ((real_sgn y) = (real_sgn _27235)) ∧ ((real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero)))) = (real_abs _27235)))) := by
  simp only [real_sgn_eq, real_pow_eq, _root_.real_abs, NUMERAL, BIT0, BIT1]
  funext s
  change SQRT_HOL s = Classical.epsilon (fun y : ℝ => Real.sign y = Real.sign s ∧ y ^ 2 = |s|)
  apply align_epsilon
  · exact sqrt_hol_spec s
  · rintro x _ ⟨hx1, hx2⟩
    exact eq_of_sign_eq_of_sq_eq (((sqrt_hol_spec s).1).trans hx1.symm)
      (((sqrt_hol_spec s).2).trans hx2.symm)
