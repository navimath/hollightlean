import HolLightLean.up_to_real
import HolLightLean.hol_up_real_opam
import HolLightLean.hol_up_real_terms
open HolLightLean.hol_up_real_opam
open HolLightLean.hol_up_real_terms

noncomputable instance {n : Nat} : OfNat real n := ⟨real_of_num n⟩
noncomputable instance : Neg real := ⟨real_neg⟩
noncomputable instance : Neg (real → Prop) := ⟨fun P : real -> Prop => (fun x : real => P (-x))⟩
noncomputable instance : Neg (Set real) := ⟨fun S : Set real => (fun x : real => S (-x))⟩
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
  zero := real_of_num 0
  one := real_of_num 1
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
        := by rintro ⟨m,h1'⟩ ; --proof by contradiction
                have : ∃ m, ∀ (x : real), S x → m ≤ x
                := ⟨-m, by intro x h' ;
                            have : (-S) (-x) :=
                              (set_neg_neg  S x).1 h' ;
                            specialize h1' (-x) this ;
                            grind⟩ ;
                contradiction
        simp[h1, h_aux1,h_aux2 ] --rfl 0=0
    · have h_neg : ¬ ∃ x, (-S) x := by rintro ⟨x',h'⟩ ;
                                        have : ∃ x, S x := ⟨-x', h'⟩ ;
                                        contradiction
      simp[h, h_neg] --rfl 0=0

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
