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

theorem real_lt_def :
    @LT.lt Real _ =
      (fun x y : Real => ¬ (real_le y x)) := by
  funext x y
  unfold LT.lt
  rw [real_le_eq]
  simp_all only [not_le, eq_iff_iff]
  rfl

theorem real_ge_def :
    @GE.ge Real _ =
      (fun x y : Real => real_le y x) := by
  funext x y
  unfold GE.ge
  rw [real_le_eq]

theorem real_gt_def :
    @GT.gt Real _ =
      (fun x y : Real => real_lt y x) := by
  funext x y
  unfold GT.gt _root_.real_lt
  ext ; symm
  exact map_lt_map_iff (iso_real_Real.symm)

theorem real_div_def :
    @Div.div Real _ =
      (fun x y : Real => real_mul x (real_inv y)) := by
  funext x y
  unfold Div.div
  rw [_root_.real_mul_eq, _root_.real_inv_eq]
  rfl

theorem real_max_def :
    max =
      (fun x y : Real =>
        @COND Real _ (real_le x y) y x) := by
  funext x y
  unfold max
  rw [_root_.real_le_eq]
  unfold COND
  split_ifs <;> grind

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
      simp_all only [prod_def, Nat.cast_add, Nat.cast_one]
      rw[← h, treal_add_of_num]
      sorry


theorem real_abs_def :
    abs =
      (fun x : Real =>
        @COND Real _
          (_root_.real_le (_root_.real_of_num (NUMERAL Nat.zero)) x)
          x
          (real_neg x)) := by
  funext x
  unfold abs
  rw [_root_.real_le_eq, _root_.real_of_num_def, _root_.real_neg_eq]
  unfold COND
  split_ifs <;> simp_all only [NUMERAL, Nat.zero_eq, CharP.cast_eq_zero, neg_le_self_iff,
    sup_of_le_left] ; grind


noncomputable def real_abs : Real -> Real := fun _24160 : Real => @COND Real _ (real_le (real_of_num (NUMERAL Nat.zero)) _24160) _24160 (real_neg _24160)

noncomputable def real_pow : Real -> Nat -> Real := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Real -> Nat -> Real) _ (fun real_pow' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Real -> Nat -> Real => ∀ _24171 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ x : Real, (real_pow' _24171 x (NUMERAL Nat.zero)) = (real_of_num (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : Real, ∀ n : Nat, (real_pow' _24171 x (Nat.succ n)) = (real_mul x (real_pow' _24171 x n)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))))))))))
theorem real_pow_def : real_pow = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Real -> Nat -> Real) _ (fun real_pow' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> Real -> Nat -> Real => ∀ _24171 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ x : Real, (real_pow' _24171 x (NUMERAL Nat.zero)) = (real_of_num (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : Real, ∀ n : Nat, (real_pow' _24171 x (Nat.succ n)) = (real_mul x (real_pow' _24171 x n)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))))))))))) := by apply Eq.refl real_pow


noncomputable def real_sgn : Real -> Real := fun _26684 : Real => @COND Real _ (real_lt (real_of_num (NUMERAL Nat.zero)) _26684) (real_of_num (NUMERAL (BIT1 Nat.zero))) (@COND Real _ (real_lt _26684 (real_of_num (NUMERAL Nat.zero))) (real_neg (real_of_num (NUMERAL (BIT1 Nat.zero)))) (real_of_num (NUMERAL Nat.zero)))
theorem real_sgn_def : real_sgn = (fun _26684 : Real => @COND Real _ (real_lt (real_of_num (NUMERAL Nat.zero)) _26684) (real_of_num (NUMERAL (BIT1 Nat.zero))) (@COND Real _ (real_lt _26684 (real_of_num (NUMERAL Nat.zero))) (real_neg (real_of_num (NUMERAL (BIT1 Nat.zero)))) (real_of_num (NUMERAL Nat.zero)))) := by apply Eq.refl real_sgn

noncomputable def SQRT : Real -> Real := fun _27235 : Real => @Classical.epsilon Real _ (fun y : Real => ((real_sgn y) = (real_sgn _27235)) ∧ ((real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero)))) = (real_abs _27235)))
theorem SQRT_def : SQRT = (fun _27235 : Real => @Classical.epsilon Real _ (fun y : Real => ((real_sgn y) = (real_sgn _27235)) ∧ ((real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero)))) = (real_abs _27235)))) := by apply Eq.refl SQRT

noncomputable def DECIMAL : Nat -> Nat -> Real := fun _27914 : Nat => fun _27915 : Nat => real_div (real_of_num _27914) (real_of_num _27915)
theorem DECIMAL_def : DECIMAL = (fun _27914 : Nat => fun _27915 : Nat => real_div (real_of_num _27914) (real_of_num _27915)) := by apply Eq.refl DECIMAL

noncomputable def integer : Real -> Prop := fun _28801 : Real => ∃ n : Nat, (real_abs _28801) = (real_of_num n)
theorem integer_def : integer = (fun _28801 : Real => ∃ n : Nat, (real_abs _28801) = (real_of_num n)) := by apply Eq.refl integer
