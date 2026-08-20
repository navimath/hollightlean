import HolLightLean.real_align
-- import HolLightLean.hol_up_real_opam
-- import HolLightLean.hol_up_real_terms
-- open HolLightLean.hol_up_real_opam
-- open HolLightLean.hol_up_real_terms

set_option linter.style.longLine false
set_option linter.unusedVariables false


-- noncomputable def DECIMAL : Nat -> Nat -> Real := fun _27914 : Nat => fun _27915 : Nat => real_div (real_of_num _27914) (real_of_num _27915)
-- theorem DECIMAL_def : DECIMAL = (fun _27914 : Nat => fun _27915 : Nat => real_div (real_of_num _27914) (real_of_num _27915)) := by apply Eq.refl DECIMAL

/-!
# Integer alignments
-/

noncomputable def int_of_real : Real -> ℤ := fun r => ⌊r⌋
def real_of_int : ℤ -> Real := fun z : ℤ => ↑z

theorem axiom_25 : ∀ (a : Int), (int_of_real (real_of_int a)) = a := fun a => Int.floor_intCast a

noncomputable def integer : Real -> Prop := fun _28801 : Real => ∃ n : Nat, (real_abs _28801) = (real_of_num n)
theorem integer_def : integer = (fun _28801 : Real => ∃ n : Nat, (real_abs _28801) = (real_of_num n)) := by apply Eq.refl integer

def int_pred_of_real (r : ℝ) := ((∃ k, r = Int.ofNat k) ∨ (∃ k, r = Int.negSucc k))

theorem Int_of_integer : ∀ a : ℝ, integer a → int_pred_of_real a := by
  intro a h
  unfold int_pred_of_real
  unfold integer real_abs at h
  rw[real_of_num_def] at h
  obtain ⟨n,h⟩ := h
  by_cases ha : a ≤ 0
  · rw[abs_of_nonpos ha] at h
    rw[← neg_neg a, h]
    norm_cast
    simp_all only [Int.ofNat_eq_natCast, Nat.neg_cast_eq_cast, exists_eq_right,
      Int.neg_ofNat_eq_negSucc_iff, Nat.exists_eq_add_one]
    grind
  · simp_all only [not_le, Int.ofNat_eq_natCast, Int.cast_natCast]
    rw[abs_of_pos ha] at h
    grind

theorem Int_of_floor_eq : ∀ r : ℝ, ⌊r⌋ = r → int_pred_of_real r := by
  intro r h
  unfold int_pred_of_real
  rw[← h]
  norm_cast
  by_cases hr : r < 0
  · have : ⌊r⌋ < 0 := by exact Int.floor_lt_zero.mpr hr
    apply Or.inr
    cases hc : ⌊r⌋
    · simp_all only [Int.ofNat_eq_natCast, Int.cast_natCast, reduceCtorEq, exists_const]
      contradiction
    · simp only [Int.negSucc.injEq, exists_eq']
  · simp_all only [not_lt, Int.ofNat_eq_natCast]
    apply Or.inl
    have : ⌊r⌋ ≥ 0 := Int.floor_nonneg.2 hr
    refine ⟨Int.toNat ⌊r⌋, by grind⟩

theorem axiom_26 : ∀ (r : Real), ((fun x : Real => integer x) r) = ((real_of_int (int_of_real r)) = r) := by
  intro r
  apply Eq.propIntro <;> simp only <;> intro h
  · unfold real_of_int int_of_real
    obtain ⟨k,h_1⟩ := Int_of_integer r h
    · rw[h_1]
      simp_all only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.floor_natCast]
    · expose_names
      obtain ⟨k,h_1⟩ := h_1
      rw[h_1, @Int.floor_intCast]
  · unfold integer real_abs ; rw[real_of_num_def]
    unfold real_of_int int_of_real at h
    have := Int_of_floor_eq r h
    apply Or.elim this <;> rintro ⟨k,h'⟩
    · subst h'
      simp_all only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.floor_natCast, Nat.abs_cast,
        Nat.cast_inj, exists_eq']
    · refine ⟨k + 1, ?_⟩
      rw [h']
      simp_all
      grind

@[simp]
def int_le := @LE.le ℤ _

theorem int_le_def : int_le = (fun _28827 : ℤ => fun _28828 : ℤ => real_le (real_of_int _28827) (real_of_int _28828)) := by
  funext x y
  rw[int_le, real_le_eq]
  simp_all only [real_of_int, Int.cast_le]

@[simp]
def int_lt := @LT.lt ℤ _

theorem int_lt_def : int_lt = (fun _28839 : ℤ => fun _28840 : ℤ => real_lt (real_of_int _28839) (real_of_int _28840)) := by
  funext x y
  rw[int_lt, real_lt_eq]
  simp_all only [real_of_int, Int.cast_lt]

@[simp]
def int_ge := @GE.ge ℤ _

theorem int_ge_def :
    int_ge = (fun x : ℤ => fun y : ℤ => real_ge (real_of_int x) (real_of_int y)) := by
  funext x y
  unfold int_ge real_ge
  rw[real_le_eq]
  simp_all only [ge_iff_le, real_of_int, Int.cast_le]

@[simp]
def int_gt := @GT.gt ℤ _

theorem int_gt_def :
    int_gt = (fun x : ℤ => fun y : ℤ => real_gt (real_of_int x) (real_of_int y)) := by
  funext x y
  unfold int_gt real_gt
  rw[real_lt_eq]
  simp_all only [gt_iff_lt, real_of_int, Int.cast_lt]

@[simp]
def int_of_num : Nat -> ℤ := Int.ofNat

theorem int_of_num_def : int_of_num = (fun _28875 : Nat => int_of_real (real_of_num _28875)) := by
  funext n
  simp only [int_of_num, Int.ofNat_eq_natCast, int_of_real, real_of_num_def, Int.floor_natCast]

@[simp]
noncomputable def int_neg : ℤ -> ℤ := Int.neg

theorem int_neg_def : int_neg = (fun _28880 : ℤ => int_of_real (real_neg (real_of_int _28880))) := by
  funext z
  simp only [int_neg, int_of_real, real_neg_eq, real_of_int]
  norm_cast
  rw[Int.floor_intCast]
  rfl

@[simp]
noncomputable def int_add : ℤ -> ℤ -> ℤ := Int.add

theorem int_add_def : int_add = (fun _28889 : ℤ => fun _28890 : ℤ => int_of_real (real_add (real_of_int _28889) (real_of_int _28890))) := by
  funext x y
  simp only [int_add, Int.add_def, int_of_real, real_add_eq, real_of_int]
  rw[← @Int.floor_intCast ℝ _ _ _ _ (x+y)]
  have : @Add.add ℝ _ ↑x ↑y = ↑(x + y) := by norm_num ; rfl
  rw[this]

@[simp]
noncomputable def int_sub : ℤ -> ℤ -> ℤ := Int.sub

theorem int_sub_def : int_sub = (fun _28921 : ℤ => fun _28922 : ℤ => int_of_real (real_sub (real_of_int _28921) (real_of_int _28922))) := by
  funext x y
  simp only [int_sub, int_of_real, real_sub_eq, real_of_int]
  rw[← @Int.floor_intCast ℝ _ _ _ _ (x.sub y)]
  have : @Sub.sub ℝ _ ↑x ↑y = ↑(x - y) := by norm_num ; rfl
  rw[this] ; rfl

@[simp]
noncomputable def int_mul : ℤ → ℤ → ℤ := Int.mul

theorem int_mul_def :
    int_mul =
      (fun x : ℤ => fun y : ℤ =>
        int_of_real (real_mul (real_of_int x) (real_of_int y))) := by
  funext x y
  simp only [int_mul, Int.mul_def, int_of_real, real_mul_eq, real_of_int]
  rw [← @Int.floor_intCast ℝ _ _ _ _ (x * y)]
  have : @Mul.mul ℝ _ ↑x ↑y = ↑(x * y) := by
    norm_num
    rfl
  rw [this]

@[simp]
noncomputable def int_abs : ℤ → ℤ := abs

theorem int_abs_def : int_abs = (fun x : ℤ => int_of_real (real_abs (real_of_int x))) := by
  funext x
  simp only [int_abs, int_of_real, real_abs, real_of_int]
  norm_cast
  rw [@Int.floor_intCast ℝ _ _ _ _ (abs (x))]

@[simp]
noncomputable def int_sgn : ℤ → ℤ := Int.sign

theorem int_sgn_def : int_sgn = (fun x : ℤ => int_of_real (real_sgn (real_of_int x))) := by
  funext x
  simp only [int_sgn, int_of_real, real_sgn_eq, real_of_int]
  rw[Real.sign_intCast]
  rw [@Int.floor_intCast ℝ _ _ _ _ (x.sign)]

@[simp]
noncomputable def int_max : ℤ → ℤ → ℤ := max

theorem int_max_def :
    int_max =
      (fun x : ℤ => fun y : ℤ =>
        int_of_real (real_max (real_of_int x) (real_of_int y))) := by
  funext x y
  simp only [int_max, int_of_real, real_of_int]
  have : @max ℝ _ ↑x ↑y = ↑(max x y) := by norm_cast
  have h2 : real_max ↑x ↑y = max ↑x ↑y := by unfold real_max ; rw[real_max_def]
  rw[h2, this]
  rw [@Int.floor_intCast ℝ _ _ _ _ (max x y)]

@[simp]
noncomputable def int_min : ℤ -> ℤ -> ℤ := min

theorem int_min_def : int_min = (fun _29042 : ℤ => fun _29043 : ℤ => int_of_real (real_min (real_of_int _29042) (real_of_int _29043))) := by
  funext x y
  simp only [int_min, int_of_real, real_of_int]
  have : @min ℝ _ ↑x ↑y = ↑(min x y) := by norm_cast
  have h2 : real_min ↑x ↑y = min ↑x ↑y := by unfold real_min; rw[real_min_def]
  rw[h2, this]
  rw [@Int.floor_intCast ℝ _ _ _ _ (min x y)]

@[simp]
noncomputable def int_pow : ℤ → Nat → ℤ := Int.pow

theorem int_pow_def :
    int_pow =
      (fun x : ℤ => fun n : Nat =>
        int_of_real (real_pow (real_of_int x) n)) := by
  funext x n
  simp only [int_pow, Int.pow_eq, int_of_real, real_pow_eq, real_of_int]
  rw [← @Int.floor_intCast ℝ _ _ _ _ (x ^ n)]
  have : @Pow.pow ℝ _ _ ↑x n = ↑(x ^ n) := by
    norm_num
    rfl
  rw [this]

@[simp]
noncomputable def div : ℤ -> ℤ -> ℤ := Int.ediv

theorem div_def : div = (@Classical.epsilon ((prod Nat (prod Nat Nat)) -> ℤ -> ℤ -> ℤ) _ (fun q : (prod Nat (prod Nat Nat)) -> ℤ -> ℤ -> ℤ => ∀ _29412 : prod Nat (prod Nat Nat), ∃ r : ℤ -> ℤ -> ℤ, ∀ m : ℤ, ∀ n : ℤ, @COND Prop _ (n = (int_of_num (NUMERAL Nat.zero))) (((q _29412 m n) = (int_of_num (NUMERAL Nat.zero))) ∧ ((r m n) = m)) ((int_le (int_of_num (NUMERAL Nat.zero)) (r m n)) ∧ ((int_lt (r m n) (int_abs n)) ∧ (m = (int_add (int_mul (q _29412 m n) n) (r m n)))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero))))))))))) := by
  epsilon_tac
  · intro ascii
    constructor ; pick_goal 2
    · exact Mod.mod
    · intro a b
      simp only [COND, NUMERAL, Nat.zero_eq]
      split
      · simp_all only [int_of_num, Int.ofNat_eq_natCast, CharP.cast_eq_zero, div, Mod.mod]
        exact ⟨Int.ediv_zero a, Int.emod_zero a⟩
      · simp_all only [int_of_num, Int.ofNat_eq_natCast, CharP.cast_eq_zero, int_le, int_lt, int_abs, int_add, int_mul, Mod.mod, div]
        expose_names
        have := ((@Int.ediv_emod_unique'' a b (a.emod b) (a.ediv b) h).1 ⟨rfl, rfl⟩)
        grind
  · intro dany hdiv hany
    funext ascii a b
    obtain ⟨rany,hany⟩ := hany ascii
    obtain ⟨rmod, hdiv⟩ := hdiv ascii
    specialize hany a b
    specialize hdiv a b
    simp_all only [prod_def, COND, int_of_num, NUMERAL, Nat.zero_eq, Int.ofNat_eq_natCast,
      CharP.cast_eq_zero, div, int_le, int_lt, int_abs, int_add, int_mul, Int.mul_def, Int.add_def,
      forall_const, Prod.forall]
    by_cases hb : b = 0
    · simp_all only [↓reduceIte]
    · simp[hb] at hdiv hany
      have := ((@Int.ediv_emod_unique'' a b (rmod a b) (a.ediv b) hb).2)
      have := ((@Int.ediv_emod_unique'' a b (rany a b) ((dany ascii) a b) hb).2)
      have hdiv1 : a / b = (dany ascii) a b := by grind
      have hdiv2 : a / b = a.ediv b := by grind
      rw[← hdiv1,hdiv2]

@[simp]
noncomputable def rem : ℤ -> ℤ -> ℤ := Int.emod

theorem rem_def : rem = (@Classical.epsilon ((prod Nat (prod Nat Nat)) -> ℤ -> ℤ -> ℤ) _ (fun r : (prod Nat (prod Nat Nat)) -> ℤ -> ℤ -> ℤ => ∀ _29413 : prod Nat (prod Nat Nat), ∀ m : ℤ, ∀ n : ℤ, @COND Prop _ (n = (int_of_num (NUMERAL Nat.zero))) (((div m n) = (int_of_num (NUMERAL Nat.zero))) ∧ ((r _29413 m n) = m)) ((int_le (int_of_num (NUMERAL Nat.zero)) (r _29413 m n)) ∧ ((int_lt (r _29413 m n) (int_abs n)) ∧ (m = (int_add (int_mul (div m n) n) (r _29413 m n)))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))) := by
  epsilon_tac
  · intro ascii x y
    simp only [COND, NUMERAL, Nat.zero_eq]
    split <;> expose_names
    · simp only [div, h, int_of_num, Int.ofNat_eq_natCast, CharP.cast_eq_zero, rem]
      exact ⟨Int.ediv_zero x, Int.emod_zero x⟩
    · simp only [int_of_num, Int.ofNat_eq_natCast, CharP.cast_eq_zero, int_le, rem, int_lt,
      int_abs, int_add, int_mul, div, Int.mul_def, Int.add_def]
      have := ((@Int.ediv_emod_unique'' x y (x.emod y) (x.ediv y) h)).1 ⟨rfl,rfl⟩
      grind
  · intro rany hrem hrany
    funext ascii a b
    specialize hrem ascii a b
    specialize hrany ascii a b
    simp_all[COND, int_of_num, NUMERAL, Nat.zero_eq, Int.ofNat_eq_natCast,
      CharP.cast_eq_zero, div, int_le, int_lt, int_abs, int_add, int_mul, Int.mul_def, Int.add_def]
    grind

noncomputable def eq2 {A : Type _} [Nonempty A] : A -> A -> (A -> A -> Prop) -> Prop := fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689
theorem eq2_def {A : Type _} [Nonempty A] : (@eq2 A _) = (fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689) := by apply Eq.refl (@eq2 A _)

@[simp]
noncomputable def real_mod : Real -> Real -> Real -> Prop := fun _29709 : Real => fun _29710 : Real => fun _29711 : Real => ∃ q : Real, (integer q) ∧ ((real_sub _29710 _29711) = (real_mul q _29709))

theorem real_mod_def : real_mod = (fun _29709 : Real => fun _29710 : Real => fun _29711 : Real => ∃ q : Real, (integer q) ∧ ((real_sub _29710 _29711) = (real_mul q _29709))) := by apply Eq.refl real_mod

@[simp]
noncomputable def int_divides : ℤ -> ℤ -> Prop := Dvd.dvd

theorem int_divides_def : int_divides = (fun _29730 : ℤ => fun _29731 : ℤ => ∃ x : ℤ, _29731 = (int_mul _29730 x)) := by apply Eq.refl int_divides

@[simp]
noncomputable def int_mod : ℤ -> ℤ -> ℤ -> Prop := fun _29750 : ℤ => fun _29751 : ℤ => fun _29752 : ℤ => int_divides _29750 (int_sub _29751 _29752)

theorem int_mod_def : int_mod = (fun _29750 : ℤ => fun _29751 : ℤ => fun _29752 : ℤ => int_divides _29750 (int_sub _29751 _29752)) := by apply Eq.refl int_mod

@[simp]
noncomputable def int_coprime : (prod ℤ ℤ) -> Prop := fun p => IsCoprime p.1 p.2

theorem int_coprime_def : int_coprime = (fun _29777 : prod ℤ ℤ => ∃ x : ℤ, ∃ y : ℤ, (int_add (int_mul (@prod_fst ℤ ℤ _ _ _29777) x) (int_mul (@prod_snd ℤ ℤ _ _ _29777) y)) = (int_of_num (NUMERAL (BIT1 Nat.zero)))) := by
  funext x
  simp only [int_coprime, IsCoprime, int_add, int_mul, prod_fst, Int.mul_def, prod_snd, Int.add_def,
    int_of_num, NUMERAL, BIT1, BIT0, Nat.zero_eq, add_zero, Nat.succ_eq_add_one, zero_add,
    Int.ofNat_eq_natCast, Nat.cast_one, eq_iff_iff]
  refine exists₂_congr (by grind)

@[simp]
noncomputable def int_gcd : (prod ℤ ℤ) -> ℤ := fun (x,y) => ↑(Int.gcd x y)

theorem int_gcd_def : int_gcd = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (prod ℤ ℤ) -> ℤ) _ (fun d : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (prod ℤ ℤ) -> ℤ => ∀ _31046 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∀ a : ℤ, ∀ b : ℤ, (int_le (int_of_num (NUMERAL Nat.zero)) (d _31046 (@prod_mk ℤ ℤ _ _ a b))) ∧ ((int_divides (d _31046 (@prod_mk ℤ ℤ _ _ a b)) a) ∧ ((int_divides (d _31046 (@prod_mk ℤ ℤ _ _ a b)) b) ∧ (∃ x : ℤ, ∃ y : ℤ, (d _31046 (@prod_mk ℤ ℤ _ _ a b)) = (int_add (int_mul a x) (int_mul b y)))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))))))) := by
  epsilon_tac
  · intro ascii a b
    simp only [int_le, int_of_num, NUMERAL, Nat.zero_eq, Int.ofNat_eq_natCast, CharP.cast_eq_zero,
      int_gcd, prod_mk, Nat.cast_nonneg, int_divides, int_add, int_mul, Int.mul_def, Int.add_def,
      true_and]
    exact ⟨Int.gcd_dvd_left a b, ⟨Int.gcd_dvd_right a b,exists_gcd_eq_mul_add_mul a b⟩⟩
  · intro f hgcd hf
    funext ascii (x,y)
    specialize hgcd ascii x y
    specialize hf ascii x y
    simp_all only [int_le, int_of_num, NUMERAL, Nat.zero_eq, Int.ofNat_eq_natCast,
      CharP.cast_eq_zero, prod_mk, int_divides, int_add, int_mul, Int.mul_def, Int.add_def, int_gcd,
      Nat.cast_nonneg, true_and]
    have : (f ascii (x,y)).toNat = (f ascii (x,y)) := by apply Int.toNat_of_nonneg hf.1
    have h_2 := (@Int.gcd_eq_iff x y (f ascii (x,y)).toNat).2
    rw[this] at h_2
    specialize h_2 ⟨hf.2.1,⟨hf.2.2.1, ?_⟩⟩
    · intro c hx hy
      obtain ⟨a,b,hab⟩ := hf.2.2.2
      rw[hab]
      refine (Int.dvd_add_right (Int.dvd_mul_of_dvd_left hx)).mpr (Int.dvd_mul_of_dvd_left hy)
    rw[← this, h_2]

@[simp]
noncomputable def int_lcm : (prod ℤ ℤ) -> ℤ := fun (x,y) => ↑(Int.lcm x y)
theorem int_lcm_def : int_lcm = (fun _31047 : prod ℤ ℤ => @COND ℤ _ ((int_mul (@prod_fst ℤ ℤ _ _ _31047) (@prod_snd ℤ ℤ _ _ _31047)) = (int_of_num (NUMERAL Nat.zero))) (int_of_num (NUMERAL Nat.zero)) (div (int_abs (int_mul (@prod_fst ℤ ℤ _ _ _31047) (@prod_snd ℤ ℤ _ _ _31047))) (int_gcd (@prod_mk ℤ ℤ _ _ (@prod_fst ℤ ℤ _ _ _31047) (@prod_snd ℤ ℤ _ _ _31047))))) := by
  funext (x,y)
  simp only [int_lcm, COND, int_mul, prod_fst, prod_snd, Int.mul_def, int_of_num, NUMERAL,
    Nat.zero_eq, Int.ofNat_eq_natCast, CharP.cast_eq_zero, mul_eq_zero, div, int_abs, abs_mul,
    int_gcd, prod_mk]
  split <;> expose_names <;> norm_cast
  · apply Or.elim h <;> intro h0
    · subst x; exact Int.lcm_zero_left y
    · subst y; exact Int.lcm_zero
  · have := Int.lcm_eq_mul_div x y
    simp_all only [not_or, Int.natCast_ediv, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs,
      Int.cast_eq]
    rfl

/-! ## Non-aligned maps -/

noncomputable def num_of_int : ℤ -> Nat := (fun _31320 : ℤ => @Classical.epsilon Nat _ (fun n : Nat => (int_of_num n) = _31320))
theorem num_of_int_def : num_of_int = (fun _31320 : ℤ => @Classical.epsilon Nat _ (fun n : Nat => (int_of_num n) = _31320)) := rfl

noncomputable def num_divides : Nat -> Nat -> Prop := fun _31352 : Nat => fun _31353 : Nat => int_divides (int_of_num _31352) (int_of_num _31353)
theorem num_divides_def : num_divides = (fun _31352 : Nat => fun _31353 : Nat => int_divides (int_of_num _31352) (int_of_num _31353)) := by apply Eq.refl num_divides

noncomputable def num_mod : Nat -> Nat -> Nat -> Prop := fun _31364 : Nat => fun _31365 : Nat => fun _31366 : Nat => int_mod (int_of_num _31364) (int_of_num _31365) (int_of_num _31366)
theorem num_mod_def : num_mod = (fun _31364 : Nat => fun _31365 : Nat => fun _31366 : Nat => int_mod (int_of_num _31364) (int_of_num _31365) (int_of_num _31366)) := by apply Eq.refl num_mod

noncomputable def num_coprime : (prod Nat Nat) -> Prop := fun _31385 : prod Nat Nat => int_coprime (@prod_mk ℤ ℤ _ _ (int_of_num (@prod_fst Nat Nat _ _ _31385)) (int_of_num (@prod_snd Nat Nat _ _ _31385)))
theorem num_coprime_def : num_coprime = (fun _31385 : prod Nat Nat => int_coprime (@prod_mk ℤ ℤ _ _ (int_of_num (@prod_fst Nat Nat _ _ _31385)) (int_of_num (@prod_snd Nat Nat _ _ _31385)))) := by apply Eq.refl num_coprime

noncomputable def num_gcd : (prod Nat Nat) -> Nat := fun _31394 : prod Nat Nat => num_of_int (int_gcd (@prod_mk ℤ ℤ _ _ (int_of_num (@prod_fst Nat Nat _ _ _31394)) (int_of_num (@prod_snd Nat Nat _ _ _31394))))
theorem num_gcd_def : num_gcd = (fun _31394 : prod Nat Nat => num_of_int (int_gcd (@prod_mk ℤ ℤ _ _ (int_of_num (@prod_fst Nat Nat _ _ _31394)) (int_of_num (@prod_snd Nat Nat _ _ _31394))))) := by apply Eq.refl num_gcd

noncomputable def num_lcm : (prod Nat Nat) -> Nat := fun _31403 : prod Nat Nat => num_of_int (int_lcm (@prod_mk ℤ ℤ _ _ (int_of_num (@prod_fst Nat Nat _ _ _31403)) (int_of_num (@prod_snd Nat Nat _ _ _31403))))
theorem num_lcm_def : num_lcm = (fun _31403 : prod Nat Nat => num_of_int (int_lcm (@prod_mk ℤ ℤ _ _ (int_of_num (@prod_fst Nat Nat _ _ _31403)) (int_of_num (@prod_snd Nat Nat _ _ _31403))))) := by apply Eq.refl num_lcm

noncomputable def prime : Nat -> Prop := fun _32188 : Nat => (¬ (_32188 = (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : Nat, (num_divides x _32188) -> (x = (NUMERAL (BIT1 Nat.zero))) ∨ (x = _32188))
theorem prime_def : prime = (fun _32188 : Nat => (¬ (_32188 = (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : Nat, (num_divides x _32188) -> (x = (NUMERAL (BIT1 Nat.zero))) ∨ (x = _32188))) := by apply Eq.refl prime

noncomputable def real_zpow : Real -> ℤ -> Real := fun _32346 : Real => fun _32347 : ℤ => @COND Real _ (int_le (int_of_num (NUMERAL Nat.zero)) _32347) (real_pow _32346 (num_of_int _32347)) (real_inv (real_pow _32346 (num_of_int (int_neg _32347))))
theorem real_zpow_def : real_zpow = (fun _32346 : Real => fun _32347 : ℤ => @COND Real _ (int_le (int_of_num (NUMERAL Nat.zero)) _32347) (real_pow _32346 (num_of_int _32347)) (real_inv (real_pow _32346 (num_of_int (int_neg _32347))))) := by apply Eq.refl real_zpow

/-!
# Set Theory alignment
-/

@[simp]
noncomputable def IN {A : Type _} [Nonempty A] : A -> (A -> Prop) -> Prop := fun (a : A) (S : Set A) => a ∈ S
theorem IN_def {A : Type _} [Nonempty A] : (@IN A _) = (fun _32403 : A => fun _32404 : A -> Prop => _32404 _32403) := by apply Eq.refl (@IN A _)

@[simp]
noncomputable def GSPEC {A : Type _} [Nonempty A] : (A -> Prop) -> A -> Prop := id
theorem GSPEC_def {A : Type _} [Nonempty A] : (@GSPEC A _) = (fun _32415 : A -> Prop => _32415) := by apply Eq.refl (@GSPEC A _)

@[simp]
noncomputable def SETSPEC {A : Type _} [Nonempty A] : A -> Prop -> A -> Prop := fun x P => {x' | P ∧ x = x'}
theorem SETSPEC_def {A : Type _} [Nonempty A] : (@SETSPEC A _) = (fun _32420 : A => fun _32421 : Prop => fun _32422 : A => _32421 ∧ (_32420 = _32422)) := by apply Eq.refl (@SETSPEC A _)

@[simp]
noncomputable def EMPTY {A : Type _} [Nonempty A] : A -> Prop := Set.instEmptyCollection.emptyCollection
theorem EMPTY_def {A : Type _} [Nonempty A] : (@EMPTY A _) = (fun x : A => False) := by apply Eq.refl (@EMPTY A _)

@[simp]
noncomputable def INSERT {A : Type _} [Nonempty A] : A -> (A -> Prop) -> A -> Prop := fun a S x => IN x (Set.insert a S)
theorem INSERT_def {A : Type _} [Nonempty A] : (@INSERT A _) = (fun _32459 : A => fun _32460 : A -> Prop => fun y : A => (@IN A _ y _32460) ∨ (y = _32459)) := by
  unfold INSERT IN Set.insert
  grind

/--
Closes a goal of the form
`<lean set> = GSPEC (fun v => ∃ x, SETSPEC v (Q x) x)`
-/
elab "gspec_align" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (try unfold GSPEC SETSPEC id IN);
    (first | funext a b c d | funext a b c | funext a b | funext a);
    (try apply propext);
    apply Iff.intro;
    (first
      | (intro h; exact ⟨_, ⟨h, rfl⟩⟩)
      | (intro h; refine ⟨_, ⟨?_, rfl⟩⟩; first | assumption | simp_all | grind)
      | (intro h; exact ⟨_, _, ⟨h, rfl⟩⟩)
      | (intro h; refine ⟨_, _, ⟨?_, rfl⟩⟩; first | assumption | simp_all | grind));
    (first
      | (rintro ⟨_, ⟨hx, heq⟩⟩; subst heq; first | exact hx | simp_all | grind)
      | (rintro ⟨_, _, ⟨hx, heq⟩⟩; subst heq; first | exact hx | simp_all | grind))))

elab "two_set_align"  : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
  (try simp_all);
  first
  | done
  | (funext U V x;
          apply Eq.propIntro <;> intro h;
          refine ⟨x, by try trivial⟩;
          obtain ⟨x', h'⟩ := h;
          rw [h'.2];
          exact h'.1)
  | (funext U V;
     apply Eq.propIntro <;> intro h <;>
     try grind <;> try solve_by_elim;
     );
  | (funext U;
     apply Eq.propIntro <;> intro h <;>
     try grind <;> try solve_by_elim;
     );
  | gspec_align
    )
  )

@[simp]
noncomputable def UNIV {A : Type _} [Nonempty A] : A -> Prop := Set.univ
theorem UNIV_def {A : Type _} [Nonempty A] : (@UNIV A _) = (fun x : A => True) := by apply Eq.refl (@UNIV A _)

@[simp]
noncomputable def UNION {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun (U V : Set A) => (U ∪ V: Set A)
theorem UNION_def {A : Type _} [Nonempty A] : (@UNION A _) = (fun _32471 : A -> Prop => fun _32472 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_0 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_0 ((@IN A _ x _32471) ∨ (@IN A _ x _32472)) x)) := by
  unfold UNION
  two_set_align

@[simp]
noncomputable def UNIONS {A : Type _} [Nonempty A] : ((A -> Prop) -> Prop) -> A -> Prop := fun F : Set (Set A) => ⋃₀ F

@[simp]
theorem UNIONS_def {A : Type _} [Nonempty A] : (@UNIONS A _) = (fun _32483 : (A -> Prop) -> Prop => @GSPEC A _ (fun GEN_PVAR_1 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_1 (∃ u : A -> Prop, (@IN (A -> Prop) _ u _32483) ∧ (@IN A _ x u)) x)) := by
  unfold UNIONS
  gspec_align

@[simp]
noncomputable def INTER {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun (U V : Set A) => (U ∩ V : Set A)

theorem INTER_def {A : Type _} [Nonempty A] : (@INTER A _) = (fun _32488 : A -> Prop => fun _32489 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_2 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_2 ((@IN A _ x _32488) ∧ (@IN A _ x _32489)) x)) := by
  unfold INTER ; two_set_align

@[simp]
noncomputable def INTERS {A : Type _} [Nonempty A] : ((A -> Prop) -> Prop) -> A -> Prop := fun F : Set (Set A) => ⋂₀ F

theorem INTERS_def {A : Type _} [Nonempty A] : (@INTERS A _) = (fun _32500 : (A -> Prop) -> Prop => @GSPEC A _ (fun GEN_PVAR_3 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_3 (∀ u : A -> Prop, (@IN (A -> Prop) _ u _32500) -> @IN A _ x u) x)) := by
  unfold INTERS
  gspec_align

@[simp]
noncomputable def DIFF {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun (U V : Set A) => U \ V

theorem DIFF_def {A : Type _} [Nonempty A] : (@DIFF A _) = (fun _32505 : A -> Prop => fun _32506 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_4 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_4 ((@IN A _ x _32505) ∧ (¬ (@IN A _ x _32506))) x)) := by
  unfold DIFF
  two_set_align

@[simp]
noncomputable def DELETE {A : Type _} [Nonempty A] : (A -> Prop) -> A -> A -> Prop := fun (S : Set A) (a : A) => S \ ({a} : Set A)
theorem DELETE_def {A : Type _} [Nonempty A] : (@DELETE A _) = (fun _32517 : A -> Prop => fun _32518 : A => @GSPEC A _ (fun GEN_PVAR_6 : A => ∃ y : A, @SETSPEC A _ GEN_PVAR_6 ((@IN A _ y _32517) ∧ (¬ (y = _32518))) y)) := by
  unfold DELETE ; two_set_align

@[simp]
noncomputable def SUBSET {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop := fun (U V : Set A) => U ⊆ V
theorem SUBSET_def {A : Type _} [Nonempty A] : (@SUBSET A _) = (fun _32529 : A -> Prop => fun _32530 : A -> Prop => ∀ x : A, (@IN A _ x _32529) -> @IN A _ x _32530) := by apply Eq.refl (@SUBSET A _)

@[simp]
noncomputable def PSUBSET {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop := fun (U V : Set A) => U ⊂ V
theorem PSUBSET_def {A : Type _} [Nonempty A] : (@PSUBSET A _) = (fun _32541 : A -> Prop => fun _32542 : A -> Prop => (@SUBSET A _ _32541 _32542) ∧ (¬ (_32541 = _32542))) := by
  unfold PSUBSET SUBSET
  funext U V
  grind[Set.ssubset_iff_subset_ne]

@[simp]
noncomputable def DISJOINT {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop := fun (U V : Set A) => Disjoint U V

theorem DISJOINT_def {A : Type _} [Nonempty A] : (@DISJOINT A _) = (fun _32553 : A -> Prop => fun _32554 : A -> Prop => (@INTER A _ _32553 _32554) = (@EMPTY A _)) := by
  two_set_align <;> expose_names
  · exact Disjoint.inter_eq h
  · exact Set.disjoint_iff_inter_eq_empty.mpr h

@[simp]
noncomputable def SING {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := fun S => ∃ a : A, S = ({a} : Set A)
theorem SING_def {A : Type _} [Nonempty A] : (@SING A _) = (fun _32565 : A -> Prop => ∃ x : A, _32565 = (@INSERT A _ x (@EMPTY A _))) := by
  two_set_align <;> expose_names <;>
  ( obtain ⟨a, h⟩ := h
    rw[h]
    refine ⟨a, ?_⟩
    funext x ; simp_all only [INSERT, IN, eq_iff_iff, Set.insert]
    subst h
    simp_all only [Set.mem_empty_iff_false, or_false, Set.setOf_eq_eq_singleton, Set.mem_singleton_iff]
    rfl)

@[simp]
noncomputable def FINITE {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := Set.Finite
theorem FINITE_def {A : Type _} [Nonempty A] : (@FINITE A _) = (fun a : A -> Prop => ∀ FINITE' : (A -> Prop) -> Prop, (∀ a' : A -> Prop, ((a' = (@EMPTY A _)) ∨ (∃ x : A, ∃ s : A -> Prop, (a' = (@INSERT A _ x s)) ∧ (FINITE' s))) -> FINITE' a') -> FINITE' a) := by
  simp_all only [FINITE, EMPTY]
  unfold INSERT Set.insert Set.Finite
  funext U
  apply Eq.propIntro <;> intro h
  · intro Fin_HOL h'
    have h'U := h' U
    apply h'
    refine Set.Finite.induction_on U h (Or.inl rfl) ?_
    · intro a S hSa ha hInd
      apply Or.elim hInd <;>
      simp_all only [forall_eq_or_imp, forall_exists_index, and_imp, insert,
        Set.insert, Set.mem_empty_iff_false, or_false, Set.setOf_eq_eq_singleton]
      · intro hS0
        refine Or.inr ⟨a,⟨(S : A → Prop),⟨by funext y ; aesop, by grind⟩⟩⟩
      · intro a S hS hFinS
        aesop
  · expose_names
    specialize h FINITE
    simp_all only [IN, Set.mem_setOf_eq, FINITE, forall_eq_or_imp, Set.finite_empty,
      forall_exists_index, and_imp, true_and]
    apply h
    intro S a U hS hU
    have : S = Set.insert a U := by exact Set.setOf_inj.mp hS
    rw[← hS, this]
    exact Set.finite_insert.2 hU

@[simp]
noncomputable def INFINITE {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := fun _32574 : A -> Prop => ¬ (@FINITE A _ _32574)
theorem INFINITE_def {A : Type _} [Nonempty A] : (@INFINITE A _) = (fun _32574 : A -> Prop => ¬ (@FINITE A _ _32574)) := by apply Eq.refl (@INFINITE A _)

@[simp]
noncomputable def IMAGE {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> B -> Prop := fun f (S : Set A) => f '' S

theorem IMAGE_def {A B : Type _} [Nonempty A] [Nonempty B] : (@IMAGE A B _ _) = (fun _32579 : A -> B => fun _32580 : A -> Prop => @GSPEC B _ (fun GEN_PVAR_7 : B => ∃ y : B, @SETSPEC B _ GEN_PVAR_7 (∃ x : A, (@IN A _ x _32580) ∧ (y = (_32579 x))) y)) := by
  unfold IMAGE GSPEC SETSPEC IN id
  funext f S b
  apply Eq.propIntro <;> intro h
  · obtain ⟨a,_⟩ := h
    exact ⟨b,⟨⟨a,by grind⟩,rfl⟩⟩
  · obtain ⟨a,⟨⟨x,h1⟩,h2⟩⟩ := h
    rw[h2]
    exact ⟨x,by grind⟩

@[simp]
def hasImage {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun f (S : Set A) (U : Set B) => f '' S ⊆ U

@[simp]
noncomputable def INJ {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun f (S : Set A) (U : Set B) => hasImage f S U ∧ Set.InjOn f S

theorem INJ_def {A B : Type _} [Nonempty A] [Nonempty B] : (@INJ A B _ _) = (fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (∀ x : A, (@IN A _ x _32592) -> @IN B _ (_32591 x) _32593) ∧ (∀ x : A, ∀ y : A, ((@IN A _ x _32592) ∧ ((@IN A _ y _32592) ∧ ((_32591 x) = (_32591 y)))) -> x = y)) := by
  unfold INJ IN hasImage Set.InjOn
  grind

@[simp]
noncomputable def SURJ {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun f (S : Set A) (U : Set B) => hasImage f S U ∧ Set.SurjOn f S U

theorem SURJ_def {A B : Type _} [Nonempty A] [Nonempty B] : (@SURJ A B _ _) = (fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (∀ x : A, (@IN A _ x _32613) -> @IN B _ (_32612 x) _32614) ∧ (∀ x : B, (@IN B _ x _32614) -> ∃ y : A, (@IN A _ y _32613) ∧ ((_32612 y) = x))) := by
  unfold SURJ hasImage Set.SurjOn IN
  grind

@[simp]
noncomputable def BIJ {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun f (S : Set A) (U : Set B) => hasImage f S U ∧ Set.BijOn f S U

theorem BIJ_def {A B : Type _} [Nonempty A] [Nonempty B] : (@BIJ A B _ _) = (fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _ _ _32633 _32634 _32635) ∧ (@SURJ A B _ _ _32633 _32634 _32635)) := by
  delta BIJ hasImage Set.BijOn Set.MapsTo SURJ INJ Set.InjOn Set.SurjOn
  grind

@[simp]
noncomputable def CHOICE {A : Type _} [Nonempty A] : (A -> Prop) -> A := fun (S : Set A) => Classical.epsilon S

theorem CHOICE_def {A : Type _} [Nonempty A] : (@CHOICE A _) = (fun _32654 : A -> Prop => @Classical.epsilon A _ (fun x : A => @IN A _ x _32654)) := rfl

@[simp]
noncomputable def REST {A : Type _} [Nonempty A] : (A -> Prop) -> A -> Prop := fun _32659 : A -> Prop => @DELETE A _ _32659 (@CHOICE A _ _32659)
theorem REST_def {A : Type _} [Nonempty A] : (@REST A _) = (fun _32659 : A -> Prop => @DELETE A _ _32659 (@CHOICE A _ _32659)) := by apply Eq.refl (@REST A _)

@[simp]
noncomputable def CROSS {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop := fun (S : Set A) (U : Set B) => Set.prod S U

theorem CROSS_def {A B : Type _} [Nonempty A] [Nonempty B] : (@CROSS A B _ _) = (fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) _ (fun GEN_PVAR_132 : prod A B => ∃ x : A, ∃ y : B, @SETSPEC (prod A B) _ GEN_PVAR_132 ((@IN A _ x _47408) ∧ (@IN B _ y _47409)) (@prod_mk A B _ _ x y))) := by
  unfold CROSS
  two_set_align

-- an arbitrary element `a : A`
@[simp]
noncomputable def ARB {A : Type _} [Nonempty A] : A := @Classical.epsilon A _ (fun x : A => False)
theorem ARB_def {A : Type _} [Nonempty A] : (@ARB A _) = (@Classical.epsilon A _ (fun x : A => False)) := by apply Eq.refl (@ARB A _)

/--
Let `S : Set A`, `EXTENSIONAL S` returns a set of functions `f : A → B` such that for every term `a : A` not in `S`, `f a : B` is an arbitrary term.
-/
@[simp]
noncomputable def EXTENSIONAL {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (A -> B) -> Prop := fun (S : Set A) => {f | ∀ a : A, ¬ S a → f a = ARB}
theorem EXTENSIONAL_def {A B : Type _} [Nonempty A] [Nonempty B] : (@EXTENSIONAL A B _ _) = (fun _48182 : A -> Prop => @GSPEC (A -> B) _ (fun GEN_PVAR_141 : A -> B => ∃ f : A -> B, @SETSPEC (A -> B) _ GEN_PVAR_141 (∀ x : A, (¬ (@IN A _ x _48182)) -> (f x) = (@ARB B _)) f)) := by
  unfold EXTENSIONAL ARB
  two_set_align <;> expose_names
  · refine ⟨V, ⟨?_,rfl⟩⟩
    intro x hU
    apply h
    exact hU
  · intro x hU
    obtain ⟨f,h⟩ := h
    rw[h.2]
    refine h.1 x ?_
    exact hU

open Classical in @[simp]
noncomputable def RESTRICTION {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (A -> B) -> A -> B := fun (S : Set A) f a => if h : a ∈ S then S.restrict f ⟨a,h⟩ else (@ARB B _)

theorem RESTRICTION_def {A B : Type _} [Nonempty A] [Nonempty B] : (@RESTRICTION A B _ _) = (fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B _ (@IN A _ _48236 _48234) (_48235 _48236) (@ARB B _)) := by
  unfold RESTRICTION COND IN
  funext S f x
  split_ifs <;> expose_names
  · simp_all only [Set.restrict_apply]
  · rfl

/--
Let `S : Set K` and `F : Set (K → A)`, `cartesian_product S F` is the set of functions from `K → A` such that for every `k ∈ S`, it gives the set `F k`.
-/
@[simp]
noncomputable def cartesian_product {A K : Type _} [Nonempty A] [Nonempty K] : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop := fun S F => ↑(Set.pi {k | S k} (fun k => F k) ∩ EXTENSIONAL S)
theorem cartesian_product_def {A K : Type _} [Nonempty A] [Nonempty K] : (@cartesian_product A K _ _) = (fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) _ (fun GEN_PVAR_142 : K -> A => ∃ f : K -> A, @SETSPEC (K -> A) _ GEN_PVAR_142 ((@EXTENSIONAL K A _ _ _48429 f) ∧ (∀ i : K, (@IN K _ i _48429) -> @IN A _ (f i) (_48430 i))) f)) := by
  unfold cartesian_product Set.pi
  simp only [Set.mem_setOf_eq, SETSPEC, EXTENSIONAL, ARB, IN, GSPEC, id]
  funext S F f
  apply Eq.propIntro <;> intro h
  · refine ⟨f,⟨?_,?_⟩⟩
    · constructor
      · intro a ha
        exact h.2 a ha
      · intro i a
        apply h.1
        exact a
    · grind
  · obtain ⟨f',⟨⟨h1,h2⟩,hr⟩⟩ := h
    rw[hr]
    subst hr
    apply And.intro
    · intro i a
      apply h2
      exact a
    · intro a a_1
      apply h1
      simp_all only [not_false_eq_true]

noncomputable def product_map {A B K : Type _} [Nonempty A] [Nonempty B] [Nonempty K] : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B := fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _ _ _49478 (fun i : K => _49479 i (x i))
theorem product_map_def {A B K : Type _} [Nonempty A] [Nonempty B] [Nonempty K] : (@product_map A B K _ _ _) = (fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _ _ _49478 (fun i : K => _49479 i (x i))) := by apply Eq.refl (@product_map A B K _ _ _)

@[simp]
noncomputable def disjoint_union {A K : Type _} [Nonempty A] [Nonempty K] : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop := fun (S : Set K) F => {(i,x) | S i ∧  F i x}
theorem disjoint_union_def {A K : Type _} [Nonempty A] [Nonempty K] : (@disjoint_union A K _ _) = (fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) _ (fun GEN_PVAR_145 : prod K A => ∃ i : K, ∃ x : A, @SETSPEC (prod K A) _ GEN_PVAR_145 ((@IN K _ i _49614) ∧ (@IN A _ x (_49615 i))) (@prod_mk K A _ _ i x))) := by
  simp_all only [prod_def, GSPEC, SETSPEC, IN, id_eq]
  funext S U p
  unfold disjoint_union prod_mk
  apply Eq.propIntro <;> intro h
  · refine ⟨p.1,p.2,⟨?_,?_⟩⟩
    · simp_all only [prod_def]
      exact h
    · rfl
  · obtain ⟨i,x,h⟩ := h
    rw[h.2]
    exact ⟨h.1.1,h.1.2⟩

open Classical in
noncomputable def set_of_list {A : Type _} [Nonempty A] : (List A) -> A -> Prop := fun L => (L.toFinset : Set A)

theorem set_of_list_def {A : Type _} [Nonempty A] : (@set_of_list A _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (List A) -> A -> Prop) _ (fun set_of_list' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (List A) -> A -> Prop => ∀ _56511 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))), ((set_of_list' _56511 (@NIL A _)) = (@EMPTY A _)) ∧ (∀ h : A, ∀ t : List A, (set_of_list' _56511 (@CONS A _ h t)) = (@INSERT A _ h (set_of_list' _56511 t)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero))))))))))))))))))) := by
  epsilon_tac
  · intro ascii
    simp_all only [set_of_list, NIL, List.toFinset_nil, Finset.coe_empty, EMPTY, CONS,
      List.toFinset_cons, Finset.coe_insert, List.coe_toFinset, true_and]
    intro h t
    rfl
  · intro f H hf
    funext ascii L
    specialize H ascii
    specialize hf ascii
    unfold INSERT Set.insert at *
    simp_all only [set_of_list, NIL, List.toFinset_nil, Finset.coe_empty, EMPTY, CONS,
      List.toFinset_cons, Finset.coe_insert, List.coe_toFinset, IN, Set.mem_setOf_eq, true_and]
    induction L
    · simp_all only [List.not_mem_nil, Set.setOf_false]
    · expose_names
      have hf := hf.2 head tail
      specialize H head tail
      have : insert head {a | a ∈ tail} = {a | a ∈ head :: tail} := by simp_all only [List.mem_cons] ; rfl
      rw[hf, ← this, H, ← tail_ih]
      rfl

noncomputable def pairwise {A : Type _} [Nonempty A] : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => ∀ x : A, ∀ y : A, ((@IN A _ x _56703) ∧ ((@IN A _ y _56703) ∧ (¬ (x = y)))) -> _56702 x y
theorem pairwise_def {A : Type _} [Nonempty A] : (@pairwise A _) = (fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => ∀ x : A, ∀ y : A, ((@IN A _ x _56703) ∧ ((@IN A _ y _56703) ∧ (¬ (x = y)))) -> _56702 x y) := by apply Eq.refl (@pairwise A _)

noncomputable def UNION_OF {A : Type _} [Nonempty A] : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun (P : Set (Set (Set A))) (Q : Set (Set A)) => { s | ∃ u ∈ P, u ⊆ Q ∧ ⋃₀ u = s }
theorem UNION_OF_def {A : Type _} [Nonempty A] : (@UNION_OF A _) = (fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, (_57415 u) ∧ ((∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57416 c) ∧ ((@UNIONS A _ u) = s))) := by
  unfold UNION_OF UNIONS IN
  rfl

noncomputable def INTERSECTION_OF {A : Type _} [Nonempty A] : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun (P : Set (Set (Set A))) (Q : Set (Set A)) => { s | ∃ u ∈ P, u ⊆ Q ∧ ⋂₀ u = s }
theorem INTERSECTION_OF_def {A : Type _} [Nonempty A] : (@INTERSECTION_OF A _) = (fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, (_57427 u) ∧ ((∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57428 c) ∧ ((@INTERS A _ u) = s))) := by
  unfold INTERSECTION_OF INTERS IN
  rfl

noncomputable def ARBITRARY {A : Type _} [Nonempty A] : ((A -> Prop) -> Prop) -> Prop := fun _57563 : (A -> Prop) -> Prop => True
theorem ARBITRARY_def {A : Type _} [Nonempty A] : (@ARBITRARY A _) = (fun _57563 : (A -> Prop) -> Prop => True) := by apply Eq.refl (@ARBITRARY A _)

/-!
## Aligments involving finite sets
-/

/--
Auxiliary structural recursion behind `FINREC`: `FINRECaux f b n s a` says that `a` is
obtained from `b` by applying `f` to `n` (distinct) elements taken out of `s`, and that
`s` is exhausted after those `n` steps.
-/
def FINRECaux {A B : Type _} (f : A -> B -> B) (b : B) : Nat -> Set A -> B -> Prop
  | 0, s, a => s = (∅ : Set A) ∧ a = b
  | n + 1, s, a => ∃ x : A, ∃ c : B, x ∈ s ∧ FINRECaux f b n (s \ {x}) c ∧ a = f x c

/--
`FINREC (b₀, s, f)` is the inductive set defined by a base element `b₀`, a set `s` and a function `f`. The set contains the pairs of elements `(b,n)` such that
  - `(b₀,0) ∈ FINREC(b₀,∅,f)`
  - `(f x b, n+1) ∈ FINREC(b₀,s,f)` whenever `(b,n) ∈ FINREC(b₀,s\{x},f)`
Intuitively, `FINREC(b₀, s, f)` is the set of all iterations of `f` for some `b₀ : B` over elements of `S`
-/
def FINREC {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop :=
  fun f b s a n => FINRECaux f b n s a
theorem FINREC_def {A B : Type _} [Nonempty A] [Nonempty B] : (@FINREC A B _ _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop) _ (fun FINREC' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop => ∀ _42261 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), (∀ f : A -> B -> B, ∀ s : A -> Prop, ∀ a : B, ∀ b : B, (FINREC' _42261 f b s a (NUMERAL Nat.zero)) = ((s = (@EMPTY A _)) ∧ (a = b))) ∧ (∀ b : B, ∀ s : A -> Prop, ∀ n : Nat, ∀ a : B, ∀ f : A -> B -> B, (FINREC' _42261 f b s a (Nat.succ n)) = (∃ x : A, ∃ c : B, (@IN A _ x s) ∧ ((FINREC' _42261 f b (@DELETE A _ s x) c n) ∧ (a = (f x c)))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))) := by
  epsilon_tac
  · intro tag
    refine ⟨?_, ?_⟩
    · intro f s a b'
      rfl
    · intro b' s n a f
      rfl
  · intro g _ hg
    unfold NUMERAL at hg
    funext tag f b' s a n
    induction n generalizing s a with
    | zero => rw [(hg tag).1 f s a b'] ; rfl
    | succ n ih => rw [(hg tag).2 b' s n a f] ; simp only [← ih] ; rfl

open Classical in
/-- The `ε`-definition of `ITSET` coming from HOL Light, kept as the fallback value. -/
noncomputable def HITSET {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B -> B) -> (A -> Prop) -> B -> B :=
  fun f s b => Classical.epsilon (fun g : Set A -> B =>
    g ∅ = b ∧ ∀ (x : A) (s : Set A), Set.Finite s ->
      g (insert x s) = if x ∈ s then g s else f x (g s)) s

open Classical in
/-- `foldSet f b s` folds `f` over the elements of the finite set `s`, starting from `b`.
The enumeration order of `s` is arbitrary, so this is only well behaved when `f` is
left-commutative (see `foldSet_insert`). -/
noncomputable def foldSet {A B : Type _} (f : A -> B -> B) (b : B) (s : Set A) : B :=
  if h : s.Finite then h.toFinset.toList.foldr f b else b

theorem foldSet_empty {A B : Type _} (f : A -> B -> B) (b : B) : foldSet f b (∅ : Set A) = b := by
  rw [foldSet, dif_pos Set.finite_empty]
  simp

open Classical in
theorem foldSet_insert {A B : Type _} (f : A -> B -> B) [LeftCommutative f] (b : B)
    (x : A) (s : Set A) (hs : s.Finite) :
    foldSet f b (insert x s) = if x ∈ s then foldSet f b s else f x (foldSet f b s) := by
  by_cases hx : x ∈ s
  · rw [if_pos hx, Set.insert_eq_self.2 hx]
  · rw [if_neg hx, foldSet, foldSet, dif_pos (hs.insert x), dif_pos hs]
    have hx' : x ∉ hs.toFinset := by simpa using hx
    have hperm := Finset.toList_insert hx'
    have hset : (hs.insert x).toFinset = insert x hs.toFinset := by
      ext y ; simp
    rw [show ((hs.insert x).toFinset).toList.foldr f b = (insert x hs.toFinset).toList.foldr f b by
      rw [hset]]
    rw [hperm.foldr_eq b]
    rfl

open Classical in
/-- The HOL Light recursion equations pin down a function on *finite* sets. -/
theorem itset_unique {A B : Type _} (f : A -> B -> B) (b : B) (g g' : Set A -> B)
    (hg : g ∅ = b ∧ ∀ (x : A) (s : Set A), Set.Finite s ->
      g (insert x s) = if x ∈ s then g s else f x (g s))
    (hg' : g' ∅ = b ∧ ∀ (x : A) (s : Set A), Set.Finite s ->
      g' (insert x s) = if x ∈ s then g' s else f x (g' s)) :
    ∀ s : Set A, s.Finite -> g s = g' s := by
  intro s hs
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [hg.1, hg'.1]
  | insert hx ht ih =>
    rename_i a t
    rw [hg.2 a t ht, hg'.2 a t ht, ih]

open Classical in
theorem HITSET_eq_foldSet {A B : Type _} [Nonempty A] [Nonempty B] (f : A -> B -> B)
    [LeftCommutative f] (b : B) (s : Set A) (hs : s.Finite) : HITSET f s b = foldSet f b s := by
  have hsat : ∃ g : Set A -> B, g ∅ = b ∧ ∀ (x : A) (s : Set A), Set.Finite s ->
      g (insert x s) = if x ∈ s then g s else f x (g s) :=
    ⟨foldSet f b, foldSet_empty f b, fun x s hs => foldSet_insert f b x s hs⟩
  have spec := Classical.epsilon_spec hsat
  exact itset_unique f b _ _ spec ⟨foldSet_empty f b, fun x s hs => foldSet_insert f b x s hs⟩ s hs

open Classical in
/-- `ITSET f s b` iterates `f` over the elements of `s`. Whenever the HOL Light
specification actually determines a value -- that is, on finite `s` with left-commutative
`f` -- it is computed by `foldSet`; elsewhere it falls back to the HOL Light `ε`-term. -/
noncomputable def ITSET {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B -> B) -> (A -> Prop) -> B -> B :=
  fun f s b => if LeftCommutative f ∧ Set.Finite s then foldSet f b s else HITSET f s b
open Classical in
theorem ITSET_def {A B : Type _} [Nonempty A] [Nonempty B] : (@ITSET A B _ _) = (fun _43111 : A -> B -> B => fun _43112 : A -> Prop => fun _43113 : B => @Classical.epsilon ((A -> Prop) -> B) _ (fun g : (A -> Prop) -> B => ((g (@EMPTY A _)) = _43113) ∧ (∀ x : A, ∀ s : A -> Prop, (@FINITE A _ s) -> (g (@INSERT A _ x s)) = (@COND B _ (@IN A _ x s) (g s) (_43111 x (g s))))) _43112) := by
  funext f s b
  change (if LeftCommutative f ∧ Set.Finite s then foldSet f b s else HITSET f s b) = HITSET f s b
  by_cases h : LeftCommutative f ∧ Set.Finite s
  · rw [if_pos h]
    haveI := h.1
    exact (HITSET_eq_foldSet f b s h.2).symm
  · rw [if_neg h]

noncomputable def HCARD {A : Type _} [Nonempty A] : (A -> Prop) -> Nat := fun S : Set A => ITSET (fun _ => Nat.succ) S 0

open Classical in
noncomputable def CARD {A : Type _} [Nonempty A] : (A -> Prop) -> Nat := fun S : Set A => if S.Finite then S.ncard else HCARD S

open Classical in
theorem ncard_eq_ITSET_succ {A : Type _} [Nonempty A] :
    ∀ S : Set A, S.Finite →
      Set.ncard S = @ITSET A Nat _ _ (fun _ : A => fun n : Nat => Nat.succ n) S (NUMERAL Nat.zero) := by
  have hlen : ∀ l : List A,
      l.foldr (fun _ : A => fun n : Nat => Nat.succ n) (NUMERAL Nat.zero) = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp
  haveI hlc : LeftCommutative (fun _ : A => fun n : Nat => Nat.succ n) := ⟨fun _ _ _ => rfl⟩
  intro S hS
  unfold ITSET
  rw [if_pos ⟨hlc, hS⟩, foldSet, dif_pos hS, hlen, Finset.length_toList,
    Set.ncard_eq_toFinset_card S hS]

open Classical in
theorem CARD_def {A : Type _} [Nonempty A] : (@CARD A _) = (fun _43314 : A -> Prop => @ITSET A Nat _ _ (fun x : A => fun n : Nat => Nat.succ n) _43314 (NUMERAL Nat.zero)) := by
  funext S
  change (if Set.Finite S then Set.ncard S else HCARD S) = _
  by_cases hS : Set.Finite (S : Set A)
  · rw [if_pos hS] ; exact ncard_eq_ITSET_succ S hS
  · rw [if_neg hS] ; rfl


open Classical in
/-- The usable half of the `CARD` alignment: `CARD_def` only pins down the HOL `ε`-term. -/
theorem CARD_eq_ncard {A : Type _} [Nonempty A] {S : Set A} (hS : S.Finite) :
    CARD S = Set.ncard S := by
  change (if Set.Finite S then Set.ncard S else HCARD S) = _
  rw [if_pos hS]

noncomputable def HAS_SIZE {A : Type _} [Nonempty A] : (A -> Prop) -> Nat -> Prop :=
  fun (s : Set A) (n : Nat) => s.Finite ∧ s.ncard = n
theorem HAS_SIZE_def {A : Type _} [Nonempty A] : (@HAS_SIZE A _) = (fun _43489 : A -> Prop => fun _43490 : Nat => (@FINITE A _ _43489) ∧ ((@CARD A _ _43489) = _43490)):= by
  funext s n
  apply propext
  constructor
  · rintro ⟨hf, hc⟩ ; exact ⟨hf, (CARD_eq_ncard hf).trans hc⟩
  · rintro ⟨hf, hc⟩ ; exact ⟨hf, (CARD_eq_ncard hf).symm.trans hc⟩

open Classical in
noncomputable def list_of_set {A : Type _} [Nonempty A] : (A -> Prop) -> List A := fun _56512 : A -> Prop => @Classical.epsilon (List A) _ (fun l : List A => ((@set_of_list A _ l) = _56512) ∧ ((@LENGTH A _ l) = (@CARD A _ _56512)))
theorem list_of_set_def {A : Type _} [Nonempty A] : (@list_of_set A _) = (fun _56512 : A -> Prop => @Classical.epsilon (List A) _ (fun l : List A => ((@set_of_list A _ l) = _56512) ∧ ((@LENGTH A _ l) = (@CARD A _ _56512)))) := by apply Eq.refl (@list_of_set A _)

/-
open Classical in
Partial alignment for `list_of_set`. HOL Light's specification only says that the list
enumerates `S` and has the right length -- it does not fix the *order*, so `list_of_set`
cannot be equated with any particular concrete enumeration (e.g. `hS.toFinset.toList`):
for `#S >= 2` several lists satisfy the spec and `epsilon` may pick any of them.
What does hold, for finite `S`, is the specification itself.

theorem list_of_set_spec {A : Type _} [Nonempty A] (S : Set A) (hS : S.Finite) :
    set_of_list (list_of_set S) = S ∧ LENGTH (list_of_set S) = CARD S := by
  apply Classical.epsilon_spec (p := fun l : List A => set_of_list l = S ∧ LENGTH l = CARD S)
  refine ⟨hS.toFinset.toList, ?_, ?_⟩
  · change (List.toFinset (hS.toFinset.toList) : Set A) = S
    rw [Finset.toList_toFinset, Set.Finite.coe_toFinset]
  · change (hS.toFinset.toList).length = CARD S
    rw [Finset.length_toList]
    change _ = (if Set.Finite S then Set.ncard S else HCARD S)
    rw [if_pos hS, Set.ncard_eq_toFinset_card S hS]
-/

/-- `A` and `B` may live in different universes, hence the `Cardinal.lift`s. -/
noncomputable def le_c {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop :=
  fun (s : Set A) (t : Set B) => Cardinal.lift.{v} (Cardinal.mk ↥s) ≤ Cardinal.lift.{u} (Cardinal.mk ↥t)

open Classical in
theorem le_c_iff {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) :
    le_c s t ↔ ∃ f : A -> B, (∀ x : A, x ∈ s -> f x ∈ t) ∧
      (∀ x : A, ∀ y : A, (x ∈ s ∧ y ∈ s ∧ f x = f y) -> x = y) := by
  unfold le_c
  rw [Cardinal.lift_mk_le']
  constructor
  · rintro ⟨e⟩
    refine ⟨fun x => if h : x ∈ s then (e ⟨x, h⟩ : B) else Classical.arbitrary B, ?_, ?_⟩
    · intro x hx
      dsimp only
      rw [dif_pos hx]
      exact (e ⟨x, hx⟩).2
    · rintro x y ⟨hx, hy, hxy⟩
      dsimp only at hxy
      rw [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (e.injective (Subtype.ext hxy))
  · rintro ⟨f, hmap, hinj⟩
    refine ⟨⟨fun x => ⟨f x.1, hmap x.1 x.2⟩, ?_⟩⟩
    intro x y hxy
    exact Subtype.ext (hinj x.1 y.1 ⟨x.2, y.2, congrArg Subtype.val hxy⟩)

theorem le_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@le_c A B _ _) = (fun _64157 : A -> Prop => fun _64158 : B -> Prop => ∃ f : A -> B, (∀ x : A, (@IN A _ x _64157) -> @IN B _ (f x) _64158) ∧ (∀ x : A, ∀ y : A, ((@IN A _ x _64157) ∧ ((@IN A _ y _64157) ∧ ((f x) = (f y)))) -> x = y)) := by
  funext s t
  exact propext (le_c_iff s t)

noncomputable def lt_c {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop :=
  fun (s : Set A) (t : Set B) => Cardinal.lift.{v} (Cardinal.mk ↥s) < Cardinal.lift.{u} (Cardinal.mk ↥t)
theorem lt_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@lt_c A B _ _) = (fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _ _ _64169 _64170) ∧ (¬ (@le_c B A _ _ _64170 _64169))) := by
  funext s t
  apply propext
  unfold lt_c le_c
  exact lt_iff_le_not_ge

noncomputable def eq_c {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop :=
  fun (s : Set A) (t : Set B) => Cardinal.lift.{v} (Cardinal.mk ↥s) = Cardinal.lift.{u} (Cardinal.mk ↥t)

open Classical in
theorem eq_c_iff {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) :
    eq_c s t ↔ ∃ f : A -> B, (∀ x : A, x ∈ s -> f x ∈ t) ∧
      (∀ y : B, y ∈ t -> ∃! x : A, x ∈ s ∧ f x = y) := by
  unfold eq_c
  rw [Cardinal.lift_mk_eq']
  constructor
  · rintro ⟨e⟩
    refine ⟨fun x => if h : x ∈ s then (e ⟨x, h⟩ : B) else Classical.arbitrary B, ?_, ?_⟩
    · intro x hx
      dsimp only
      rw [dif_pos hx]
      exact (e ⟨x, hx⟩).2
    · intro y hy
      refine ⟨(e.symm ⟨y, hy⟩ : A), ⟨(e.symm ⟨y, hy⟩).2, ?_⟩, ?_⟩
      · dsimp only
        rw [dif_pos (e.symm ⟨y, hy⟩).2]
        have h : e ⟨(e.symm ⟨y, hy⟩ : A), (e.symm ⟨y, hy⟩).2⟩ = ⟨y, hy⟩ := by
          rw [Subtype.coe_eta] ; exact e.apply_symm_apply _
        exact congrArg Subtype.val h
      · rintro x ⟨hx, hfx⟩
        dsimp only at hfx
        rw [dif_pos hx] at hfx
        have h : e ⟨x, hx⟩ = ⟨y, hy⟩ := Subtype.ext hfx
        have h2 : (⟨x, hx⟩ : ↥s) = e.symm ⟨y, hy⟩ := by
          rw [← h, Equiv.symm_apply_apply]
        exact congrArg Subtype.val h2
  · rintro ⟨f, hmap, huniq⟩
    refine ⟨Equiv.ofBijective (fun x : ↥s => (⟨f x.1, hmap x.1 x.2⟩ : ↥t)) ⟨?_, ?_⟩⟩
    · intro x y hxy
      obtain ⟨z, _, hz⟩ := huniq (f x.1) (hmap x.1 x.2)
      exact Subtype.ext ((hz x.1 ⟨x.2, rfl⟩).trans (hz y.1 ⟨y.2, (congrArg Subtype.val hxy).symm⟩).symm)
    · rintro ⟨y, hy⟩
      obtain ⟨x, ⟨hx, hfx⟩, _⟩ := huniq y hy
      exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

theorem eq_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@eq_c A B _ _) = (fun _64181 : A -> Prop => fun _64182 : B -> Prop => ∃ f : A -> B, (∀ x : A, (@IN A _ x _64181) -> @IN B _ (f x) _64182) ∧ (∀ y : B, (@IN B _ y _64182) -> @EXISTSUNIQUE A _ (fun x : A => (@IN A _ x _64181) ∧ ((f x) = y)))) := by
  funext s t
  exact propext (eq_c_iff s t)

noncomputable def ge_c {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop :=
  fun (s : Set A) (t : Set B) => Cardinal.lift.{u} (Cardinal.mk ↥t) ≤ Cardinal.lift.{v} (Cardinal.mk ↥s)
theorem ge_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@ge_c A B _ _) = (fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _ _ _64194 _64193) := by apply Eq.refl (@ge_c A B _ _)

noncomputable def gt_c {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop :=
  fun (s : Set A) (t : Set B) => Cardinal.lift.{u} (Cardinal.mk ↥t) < Cardinal.lift.{v} (Cardinal.mk ↥s)
theorem gt_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@gt_c A B _ _) = (fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _ _ _64206 _64205) := by apply Eq.refl (@gt_c A B _ _)


noncomputable def COUNTABLE {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := fun (S : Set A) => S.Countable
theorem COUNTABLE_def {A : Type _} [Nonempty A] : (@COUNTABLE A _) = (fun _64356 : A -> Prop => @ge_c Nat A _ _ (@UNIV Nat _) _64356) := by
  funext S
  unfold COUNTABLE
  apply propext
  rw [Set.countable_iff_exists_injOn]
  rw [show (@ge_c Nat A _ _ (@UNIV Nat _) S) = @le_c A Nat _ _ S (@UNIV Nat _) from rfl,
    le_c_iff, UNIV]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, fun x _ => trivial, fun x y h => hf h.1 h.2.1 h.2.2⟩
  · rintro ⟨f, _, hinj⟩
    exact ⟨f, fun x hx y hy hxy => hinj x y ⟨hx, hy, hxy⟩⟩

/-!
## Real valued sets
-/

open Classical in
noncomputable def sup : (Real -> Prop) -> Real := fun S : Set Real =>
  if Set.Nonempty S ∧ BddAbove S then sSup S
  else @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x S) -> real_le x a) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x S) -> real_le x b) -> real_le a b))

open Classical in
theorem sup_def : sup = (fun _64361 : Real -> Prop => @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x _64361) -> real_le x a) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x _64361) -> real_le x b) -> real_le a b))) := by
  funext S
  change (if Set.Nonempty S ∧ BddAbove S then sSup S else _) = _
  by_cases h : Set.Nonempty S ∧ BddAbove S
  · rw [if_pos h]
    apply align_epsilon
    · simp only [real_le_eq, IN]
      exact ⟨fun x hx => le_csSup h.2 hx, fun b hb => csSup_le h.1 hb⟩
    · intro y hP hy
      simp only [real_le_eq, IN] at hP hy
      exact le_antisymm (hP.2 y hy.1) (hy.2 _ hP.1)
  · rw [if_neg h]

open Classical in
noncomputable def inf : (Real -> Prop) -> Real := fun S : Set Real =>
  if Set.Nonempty S ∧ BddBelow S then sInf S
  else @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x S) -> real_le a x) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x S) -> real_le b x) -> real_le b a))

open Classical in
theorem inf_def : inf = (fun _65220 : Real -> Prop => @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x _65220) -> real_le a x) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x _65220) -> real_le b x) -> real_le b a))) := by
  funext S
  change (if Set.Nonempty S ∧ BddBelow S then sInf S else _) = _
  by_cases h : Set.Nonempty S ∧ BddBelow S
  · rw [if_pos h]
    apply align_epsilon
    · simp only [real_le_eq, IN]
      exact ⟨fun x hx => csInf_le h.2 hx, fun b hb => le_csInf h.1 hb⟩
    · intro y hP hy
      simp only [real_le_eq, IN] at hP hy
      exact le_antisymm (hy.2 _ hP.1) (hP.2 y hy.1)
  · rw [if_neg h]

noncomputable def has_inf : (Real -> Prop) -> Real -> Prop := fun S b => IsGLB S b

theorem has_inf_def : has_inf = (fun _66570 : Real -> Prop => fun _66571 : Real => ∀ c : Real, (∀ x : Real, (@IN Real _ x _66570) -> real_le c x) = (real_le c _66571)) := by
  simp only [real_le_eq, IN]
  unfold has_inf
  funext S b
  apply propext
  constructor
  · intro h c
    apply propext
    exact ⟨fun hc => h.2 hc, fun hcb x hx => le_trans hcb (h.1 hx)⟩
  · intro h
    refine ⟨fun {x} hx => ?_, fun c hc => (Iff.of_eq (h c)).1 hc⟩
    exact (Iff.of_eq (h b)).2 le_rfl x hx

noncomputable def has_sup : (Real -> Prop) -> Real -> Prop := fun S b => IsLUB S b

theorem has_sup_def : has_sup = (fun _66582 : Real -> Prop => fun _66583 : Real => ∀ c : Real, (∀ x : Real, (@IN Real _ x _66582) -> real_le x c) = (real_le _66583 c)) := by
  simp only [real_le_eq, IN]
  unfold has_sup
  funext S b
  apply propext
  constructor
  · intro h c
    apply propext
    exact ⟨fun hc => h.2 hc, fun hbc x hx => le_trans (h.1 hx) hbc⟩
  · intro h
    refine ⟨fun {x} hx => ?_, fun c hc => (Iff.of_eq (h c)).1 hc⟩
    exact (Iff.of_eq (h b)).2 le_rfl x hx

noncomputable def dotdot : Nat -> Nat -> Nat -> Prop := fun n m => (Set.Icc n m : Set ℕ)
theorem dotdot_def : dotdot = (fun _67008 : Nat => fun _67009 : Nat => @GSPEC Nat _ (fun GEN_PVAR_231 : Nat => ∃ x : Nat, @SETSPEC Nat _ GEN_PVAR_231 ((Nat.le _67008 x) ∧ (Nat.le x _67009)) x)) := by
  unfold dotdot
  two_set_align

noncomputable def neutral {A : Type _} [Nonempty A] : (A -> A -> A) -> A := fun _68920 : A -> A -> A => @Classical.epsilon A _ (fun x : A => ∀ y : A, ((_68920 x y) = y) ∧ ((_68920 y x) = y))
theorem neutral_def {A : Type _} [Nonempty A] : (@neutral A _) = (fun _68920 : A -> A -> A => @Classical.epsilon A _ (fun x : A => ∀ y : A, ((_68920 x y) = y) ∧ ((_68920 y x) = y))) := by apply Eq.refl (@neutral A _)

noncomputable def monoidal {A : Type _} [Nonempty A] : (A -> A -> A) -> Prop := fun _68925 : A -> A -> A => (∀ x : A, ∀ y : A, (_68925 x y) = (_68925 y x)) ∧ ((∀ x : A, ∀ y : A, ∀ z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) ∧ (∀ x : A, (_68925 (@neutral A _ _68925) x) = x))
theorem monoidal_def {A : Type _} [Nonempty A] : (@monoidal A _) = (fun _68925 : A -> A -> A => (∀ x : A, ∀ y : A, (_68925 x y) = (_68925 y x)) ∧ ((∀ x : A, ∀ y : A, ∀ z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) ∧ (∀ x : A, (_68925 (@neutral A _ _68925) x) = x))) := by apply Eq.refl (@monoidal A _)

noncomputable def support {A B : Type _} [Nonempty A] [Nonempty B] : (B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop := fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_239 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_239 ((@IN A _ x _69012) ∧ (¬ ((_69011 x) = (@neutral B _ _69010)))) x)
theorem support_def {A B : Type _} [Nonempty A] [Nonempty B] : (@support A B _ _) = (fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_239 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_239 ((@IN A _ x _69012) ∧ (¬ ((_69011 x) = (@neutral B _ _69010)))) x)) := by apply Eq.refl (@support A B _ _)

/-!
### `iterate` as a Mathlib big operator

HOL Light's `iterate op s f` multiplies `f` over `s` when the *support*
`{x ∈ s | f x ≠ neutral op}` is finite, and returns `neutral op` otherwise -- `s` itself
may perfectly well be infinite.  That is exactly the contract of Mathlib's `finprod`
(`∏ᶠ i ∈ s, f i`) and `finsum` (`∑ᶠ i ∈ s, f i`), so the two agree unconditionally on any
commutative monoid.
-/
noncomputable def iterate {A B : Type _} [Nonempty A] [Nonempty B] : (B -> B -> B) -> (A -> Prop) -> (A -> B) -> B := fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B _ (@FINITE A _ (@support A B _ _ _69031 _69033 _69032)) (@ITSET A B _ _ (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _ _ _69031 _69033 _69032) (@neutral B _ _69031)) (@neutral B _ _69031)
theorem iterate_def {A B : Type _} [Nonempty A] [Nonempty B] : (@iterate A B _ _) = (fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B _ (@FINITE A _ (@support A B _ _ _69031 _69033 _69032)) (@ITSET A B _ _ (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _ _ _69031 _69033 _69032) (@neutral B _ _69031)) (@neutral B _ _69031)) := by apply Eq.refl (@iterate A B _ _)

/-- `1` is the unique two-sided unit of multiplication, so it is what `neutral` picks. -/
theorem neutral_mul {M : Type _} [CommMonoid M] [Nonempty M] :
    @neutral M _ (fun x y : M => x * y) = 1 := by
  symm
  unfold neutral
  apply align_epsilon
  · intro y ; exact ⟨one_mul y, mul_one y⟩
  · intro x _ hx
    have h := (hx 1).1
    dsimp only at h
    rw [mul_one] at h
    exact h.symm

theorem support_mul {A M : Type _} [Nonempty A] [CommMonoid M] [Nonempty M]
    (f : A -> M) (s : Set A) :
    @support A M _ _ (fun x y : M => x * y) f s = s ∩ Function.mulSupport f := by
  unfold support GSPEC SETSPEC id IN
  rw [neutral_mul]
  funext x
  apply propext
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩⟩
    exact ⟨hy.1, hy.2⟩
  · rintro ⟨hx, hf⟩
    exact ⟨x, ⟨⟨hx, hf⟩, rfl⟩⟩

theorem leftCommutative_mul {A M : Type _} [CommMonoid M] (f : A -> M) :
    LeftCommutative (fun (x : A) (a : M) => f x * a) :=
  ⟨fun a b c => by rw [← mul_assoc, ← mul_assoc, mul_comm (f a)]⟩

theorem ITSET_mul_eq_prod {A M : Type _} [Nonempty A] [CommMonoid M] [Nonempty M]
    (f : A -> M) (S : Set A) (hS : S.Finite) :
    @ITSET A M _ _ (fun x a => f x * a) S 1 = ∏ x ∈ hS.toFinset, f x := by
  unfold ITSET
  rw [if_pos ⟨leftCommutative_mul f, hS⟩, foldSet, dif_pos hS]
  rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList]
  induction hS.toFinset.toList with
  | nil => simp
  | cons a t ih => simp [ih]

theorem iterate_eq_finprod {A M : Type _} [Nonempty A] [CommMonoid M] [Nonempty M]
    (s : Set A) (f : A -> M) :
    @iterate A M _ _ (fun x y : M => x * y) s f = ∏ᶠ i ∈ s, f i := by
  unfold iterate COND FINITE
  rw [support_mul, neutral_mul]
  by_cases h : (s ∩ Function.mulSupport f).Finite
  · rw [if_pos h, finprod_mem_eq_prod f h, ITSET_mul_eq_prod f _ h]
  · rw [if_neg h, finprod_mem_eq_one_of_infinite h]

theorem neutral_add {M : Type _} [AddCommMonoid M] [Nonempty M] :
    @neutral M _ (fun x y : M => x + y) = 0 := by
  symm
  unfold neutral
  apply align_epsilon
  · intro y ; exact ⟨zero_add y, add_zero y⟩
  · intro x _ hx
    have h := (hx 0).1
    dsimp only at h
    rw [add_zero] at h
    exact h.symm

theorem support_add {A M : Type _} [Nonempty A] [AddCommMonoid M] [Nonempty M]
    (f : A -> M) (s : Set A) :
    @support A M _ _ (fun x y : M => x + y) f s = s ∩ Function.support f := by
  unfold support GSPEC SETSPEC id IN
  rw [neutral_add]
  funext x
  apply propext
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩⟩
    exact ⟨hy.1, hy.2⟩
  · rintro ⟨hx, hf⟩
    exact ⟨x, ⟨⟨hx, hf⟩, rfl⟩⟩

theorem leftCommutative_add {A M : Type _} [AddCommMonoid M] (f : A -> M) :
    LeftCommutative (fun (x : A) (a : M) => f x + a) :=
  ⟨fun a b c => by rw [← add_assoc, ← add_assoc, add_comm (f a)]⟩

theorem ITSET_add_eq_sum {A M : Type _} [Nonempty A] [AddCommMonoid M] [Nonempty M]
    (f : A -> M) (S : Set A) (hS : S.Finite) :
    @ITSET A M _ _ (fun x a => f x + a) S 0 = ∑ x ∈ hS.toFinset, f x := by
  unfold ITSET
  rw [if_pos ⟨leftCommutative_add f, hS⟩, foldSet, dif_pos hS]
  rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList]
  induction hS.toFinset.toList with
  | nil => simp
  | cons a t ih => simp [ih]

theorem iterate_eq_finsum {A M : Type _} [Nonempty A] [AddCommMonoid M] [Nonempty M]
    (s : Set A) (f : A -> M) :
    @iterate A M _ _ (fun x y : M => x + y) s f = ∑ᶠ i ∈ s, f i := by
  unfold iterate COND FINITE
  rw [support_add, neutral_add]
  by_cases h : (s ∩ Function.support f).Finite
  · rw [if_pos h, finsum_mem_eq_sum f h, ITSET_add_eq_sum f _ h]
  · rw [if_neg h, finsum_mem_eq_zero_of_infinite h]

/--
HOL Light's ordered iteration for non-commutative operations along a linear order.
-/
noncomputable def iterato {A K : Type _} [Nonempty A] [Nonempty K] : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) _ (fun itty : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => ∀ _76787 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∀ dom : A -> Prop, ∀ neut : A, ∀ op : A -> A -> A, ∀ ltle : K -> K -> Prop, ∀ k : K -> Prop, ∀ f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A _ ((@FINITE K _ (@GSPEC K _ (fun GEN_PVAR_265 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_265 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i))) ∧ (¬ ((@GSPEC K _ (fun GEN_PVAR_266 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_266 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i)) = (@EMPTY K _)))) (@LET K A _ _ (fun i : K => @LET_END A _ (op (f i) (itty _76787 dom neut op ltle (@GSPEC K _ (fun GEN_PVAR_267 : K => ∃ j : K, @SETSPEC K _ GEN_PVAR_267 ((@IN K _ j (@DELETE K _ k i)) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) j)) f))) (@COND K _ (∃ i : K, (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i)))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))))) neut)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))))))
theorem iterato_def {A K : Type _} [Nonempty A] [Nonempty K] : (@iterato A K _ _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) _ (fun itty : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => ∀ _76787 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∀ dom : A -> Prop, ∀ neut : A, ∀ op : A -> A -> A, ∀ ltle : K -> K -> Prop, ∀ k : K -> Prop, ∀ f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A _ ((@FINITE K _ (@GSPEC K _ (fun GEN_PVAR_265 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_265 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i))) ∧ (¬ ((@GSPEC K _ (fun GEN_PVAR_266 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_266 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i)) = (@EMPTY K _)))) (@LET K A _ _ (fun i : K => @LET_END A _ (op (f i) (itty _76787 dom neut op ltle (@GSPEC K _ (fun GEN_PVAR_267 : K => ∃ j : K, @SETSPEC K _ GEN_PVAR_267 ((@IN K _ j (@DELETE K _ k i)) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) j)) f))) (@COND K _ (∃ i : K, (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i)))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))))) neut)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))))))) := by apply Eq.refl (@iterato A K _ _)

noncomputable def nproduct {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Nat) -> Nat :=
  fun (s : Set A) (f : A -> Nat) => ∏ᶠ i ∈ s, f i
theorem nproduct_def {A : Type _} [Nonempty A] : (@nproduct A _) = (@iterate A Nat _ _ Nat.mul) := by
  funext s f
  exact (iterate_eq_finprod s f).symm

noncomputable def iproduct {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> ℤ) -> ℤ :=
  fun (s : Set A) (f : A -> ℤ) => ∏ᶠ i ∈ s, f i
theorem iproduct_def {A : Type _} [Nonempty A] : (@iproduct A _) = (@iterate A ℤ _ _ int_mul) := by
  funext s f
  exact (iterate_eq_finprod s f).symm

noncomputable def product {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Real) -> Real :=
  fun (s : Set A) (f : A -> Real) => ∏ᶠ i ∈ s, f i
theorem product_def {A : Type _} [Nonempty A] : (@product A _) = (@iterate A Real _ _ real_mul) := by
  rw [real_mul_eq]
  funext s f
  exact (iterate_eq_finprod s f).symm

noncomputable def isum {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> ℤ) -> ℤ :=
  fun (s : Set A) (f : A -> ℤ) => ∑ᶠ i ∈ s, f i
theorem isum_def {A : Type _} [Nonempty A] : (@isum A _) = (@iterate A ℤ _ _ int_add) := by
  funext s f
  exact (iterate_eq_finsum s f).symm

noncomputable def nsum {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Nat) -> Nat :=
  fun (s : Set A) (f : A -> Nat) => ∑ᶠ i ∈ s, f i
theorem nsum_def {A : Type _} [Nonempty A] : (@nsum A _) = (@iterate A Nat _ _ Nat.add) := by
  funext s f
  exact (iterate_eq_finsum s f).symm

noncomputable def sum {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Real) -> Real :=
  fun (s : Set A) (f : A -> Real) => ∑ᶠ i ∈ s, f i
theorem sum_def {A : Type _} [Nonempty A] : (@sum A _) = (@iterate A Real _ _ real_add) := by
  rw [real_add_eq]
  funext s f
  exact (iterate_eq_finsum s f).symm

theorem finsum_Icc_eq_range (m : Nat) (g : Nat -> ℝ) :
    (∑ᶠ i ∈ (Set.Icc 0 m : Set Nat), g i) = ∑ i ∈ Finset.range (m + 1), g i := by
  rw [← Finset.coe_Icc, finsum_mem_coe_finset]
  congr 1
  ext i
  simp

/--
A function `f : ℝ → ℝ` is a polynomial if it is of the form `∑_{i=0..m} c i * x^i` for every `x : ℝ`
-/
noncomputable def polynomial_function : (Real -> Real) -> Prop :=
  fun f => ∃ p : Polynomial ℝ, ∀ x : ℝ, f x = Polynomial.eval x p
theorem polynomial_function_def : polynomial_function = (fun _94200 : Real -> Real => ∃ m : Nat, ∃ c : Nat -> Real, ∀ x : Real, (_94200 x) = (@sum Nat _ (dotdot (NUMERAL Nat.zero) m) (fun i : Nat => real_mul (c i) (real_pow x i)))):= by
  funext f
  apply propext
  unfold polynomial_function sum dotdot NUMERAL
  simp only [real_mul_eq, real_pow_eq, Nat.zero_eq]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.natDegree, p.coeff, fun x => ?_⟩
    rw [hp x, finsum_Icc_eq_range]
    exact Polynomial.eval_eq_sum_range x
  · rintro ⟨m, c, hc⟩
    refine ⟨∑ i ∈ Finset.range (m + 1), Polynomial.C (c i) * Polynomial.X ^ i, fun x => ?_⟩
    rw [hc x, finsum_Icc_eq_range]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rfl

/-!
## Vector space constructors
-/
open Classical in
noncomputable def dimindex {A : Type _} [Nonempty A] : (A -> Prop) -> Nat :=
  fun _ => if Finite A then Nat.card A else 1

open Classical in
theorem dimindex_def {A : Type _} [Nonempty A] : (@dimindex A _) = (fun _94242 : A -> Prop => @COND Nat _ (@FINITE A _ (@UNIV A _)) (@CARD A _ (@UNIV A _)) (NUMERAL (BIT1 Nat.zero))):= by
  funext S
  unfold UNIV
  change (if Finite A then Nat.card A else 1) = if (Set.univ : Set A).Finite then _ else _
  by_cases h : Finite A
  · rw [if_pos h, if_pos (Set.finite_univ_iff.2 h),
      CARD_eq_ncard (Set.finite_univ_iff.2 h), Set.ncard_univ]
  · rw [if_neg h, if_neg (fun hc => h (Set.finite_univ_iff.1 hc))]
    rfl

/-!
## Vectors and finite index types

These follow HOL Light's type-definition mechanism, as the Rocq alignment does: each index
type is the subtype of `Nat` cut out by a range predicate, together with a proof that the
predicate is inhabited by `1`.  `SUBTYPE`/`mk`/`dest` from `conectors.lean` then supply the
constructor, the destructor and the two defining axioms.
-/

open Classical in
/-- HOL Light has no empty types, so `dimindex` is always at least `1`. -/
theorem one_le_dimindex {A : Type _} [Nonempty A] : 1 ≤ @dimindex A _ (@UNIV A _) := by
  unfold dimindex
  by_cases h : Finite A
  · rw [if_pos h] ; haveI := h ; exact Nat.card_pos
  · rw [if_neg h]

def finite_image_pred (A : Type _) [Nonempty A] : Nat -> Prop :=
  fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero)) (@dimindex A _ (@UNIV A _)))

/-- It is inhabited by `1`, which is what legitimises the type definition. -/
theorem finite_image_gen (A : Type _) [Nonempty A] : finite_image_pred A 1 :=
  Set.mem_Icc.2 ⟨le_refl 1, one_le_dimindex⟩

def finite_image (A : Type _) [Nonempty A] := SUBTYPE (finite_image_gen A)

instance {A : Type _} [Nonempty A] : Nonempty (finite_image A) :=
  instNonemptySUBTYPE (finite_image_gen A)

noncomputable def finite_index {A : Type _} [Nonempty A] : Nat -> finite_image A :=
  mk (finite_image_gen A)

def dest_finite_image {A : Type _} [Nonempty A] : (finite_image A) -> Nat :=
  dest (finite_image_gen A)

theorem axiom_27 : ∀ {A : Type*} [Nonempty A] (a : finite_image A), (@finite_index A _ (@dest_finite_image A _ a)) = a :=
  fun {A} _ => mk_dest (finite_image_gen A)

theorem axiom_28 : ∀ {A : Type*} [Nonempty A] (r : Nat), ((fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero)) (@dimindex A _ (@UNIV A _)))) r) = ((@dest_finite_image A _ (@finite_index A _ r)) = r) :=
  fun {A} _ => dest_mk (finite_image_gen A)

def cart_pred (A B : Type _) [Nonempty A] [Nonempty B] : ((finite_image B) -> A) -> Prop :=
  fun _ => True

theorem cart_gen (A B : Type _) [Nonempty A] [Nonempty B] :
    cart_pred A B (fun _ => Classical.arbitrary A) := trivial

noncomputable def cart (A B : Type _) [Nonempty A] [Nonempty B] := SUBTYPE (cart_gen A B)

instance {A B : Type _} [Nonempty A] [Nonempty B] : Nonempty (cart A B) :=
  instNonemptySUBTYPE (cart_gen A B)

noncomputable def mk_cart {A B : Type _} [Nonempty A] [Nonempty B] :
    ((finite_image B) -> A) -> cart A B := mk (cart_gen A B)

noncomputable def dest_cart {A B : Type _} [Nonempty A] [Nonempty B] :
    (cart A B) -> (finite_image B) -> A := dest (cart_gen A B)

def finite_sum_pred (A B : Type _) [Nonempty A] [Nonempty B] : Nat -> Prop :=
  fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero))
    (Nat.add (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))))

theorem finite_sum_gen (A B : Type _) [Nonempty A] [Nonempty B] : finite_sum_pred A B 1 :=
  Set.mem_Icc.2 ⟨le_refl 1, le_trans one_le_dimindex (Nat.le_add_right _ _)⟩

def finite_sum (A B : Type _) [Nonempty A] [Nonempty B] := SUBTYPE (finite_sum_gen A B)

instance {A B : Type _} [Nonempty A] [Nonempty B] : Nonempty (finite_sum A B) :=
  instNonemptySUBTYPE (finite_sum_gen A B)

noncomputable def mk_finite_sum {A B : Type _} [Nonempty A] [Nonempty B] :
    Nat -> finite_sum A B := mk (finite_sum_gen A B)

def dest_finite_sum {A B : Type _} [Nonempty A] [Nonempty B] :
    (finite_sum A B) -> Nat := dest (finite_sum_gen A B)

open Classical in
def finite_diff_pred (A B : Type _) [Nonempty A] [Nonempty B] : Nat -> Prop :=
  fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero))
    (@COND Nat _ (Nat.lt (@dimindex B _ (@UNIV B _)) (@dimindex A _ (@UNIV A _)))
      (Nat.sub (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _)))
      (NUMERAL (BIT1 Nat.zero))))

open Classical in
theorem finite_diff_gen (A B : Type _) [Nonempty A] [Nonempty B] : finite_diff_pred A B 1 := by
  refine Set.mem_Icc.2 ⟨le_refl 1, ?_⟩
  unfold COND
  split_ifs with h
  · have h' : @dimindex B _ (@UNIV B _) < @dimindex A _ (@UNIV A _) := h
    change 1 ≤ (@dimindex A _ (@UNIV A _)) - (@dimindex B _ (@UNIV B _))
    omega
  · exact le_refl 1

def finite_diff (A B : Type _) [Nonempty A] [Nonempty B] := SUBTYPE (finite_diff_gen A B)

instance {A B : Type _} [Nonempty A] [Nonempty B] : Nonempty (finite_diff A B) :=
  instNonemptySUBTYPE (finite_diff_gen A B)

noncomputable def mk_finite_diff {A B : Type _} [Nonempty A] [Nonempty B] :
    Nat -> finite_diff A B := mk (finite_diff_gen A B)

def dest_finite_diff {A B : Type _} [Nonempty A] [Nonempty B] :
    (finite_diff A B) -> Nat := dest (finite_diff_gen A B)

def finite_prod_pred (A B : Type _) [Nonempty A] [Nonempty B] : Nat -> Prop :=
  fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero))
    (Nat.mul (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))))

theorem finite_prod_gen (A B : Type _) [Nonempty A] [Nonempty B] : finite_prod_pred A B 1 :=
  Set.mem_Icc.2 ⟨le_refl 1, Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by have := @one_le_dimindex A _ ; omega)
                     (by have := @one_le_dimindex B _ ; omega))⟩

def finite_prod (A B : Type _) [Nonempty A] [Nonempty B] := SUBTYPE (finite_prod_gen A B)

instance {A B : Type _} [Nonempty A] [Nonempty B] : Nonempty (finite_prod A B) :=
  instNonemptySUBTYPE (finite_prod_gen A B)

noncomputable def mk_finite_prod {A B : Type _} [Nonempty A] [Nonempty B] :
    Nat -> finite_prod A B := mk (finite_prod_gen A B)

def dest_finite_prod {A B : Type _} [Nonempty A] [Nonempty B] :
    (finite_prod A B) -> Nat := dest (finite_prod_gen A B)

def tybit_pred (X : Type _) [Nonempty X] : (recspace X) -> Prop :=
  fun a : recspace X => ∀ tybit' : (recspace X) -> Prop,
    (∀ a' : recspace X, (∃ a2 : X, a' = ((fun a3 : X => @CONSTR X _ (NUMERAL Nat.zero) a3
      (fun _ : Nat => @BOTTOM X _)) a2)) -> tybit' a') -> tybit' a

theorem tybit_gen (X : Type _) [Nonempty X] :
    tybit_pred X (@CONSTR X _ (NUMERAL Nat.zero) (Classical.arbitrary X)
      (fun _ : Nat => @BOTTOM X _)) :=
  fun _ h => h _ ⟨Classical.arbitrary X, rfl⟩

noncomputable def tybit0 (A : Type _) [Nonempty A] := SUBTYPE (tybit_gen (finite_sum A A))

instance {A : Type _} [Nonempty A] : Nonempty (tybit0 A) :=
  instNonemptySUBTYPE (tybit_gen (finite_sum A A))

noncomputable def _mk_tybit0 {A : Type _} [Nonempty A] :
    (recspace (finite_sum A A)) -> tybit0 A := mk (tybit_gen (finite_sum A A))

noncomputable def _dest_tybit0 {A : Type _} [Nonempty A] :
    (tybit0 A) -> recspace (finite_sum A A) := dest (tybit_gen (finite_sum A A))

noncomputable def tybit1 (A : Type _) [Nonempty A] :=
  SUBTYPE (tybit_gen (finite_sum (finite_sum A A) Unit))

instance {A : Type _} [Nonempty A] : Nonempty (tybit1 A) :=
  instNonemptySUBTYPE (tybit_gen (finite_sum (finite_sum A A) Unit))

noncomputable def _mk_tybit1 {A : Type _} [Nonempty A] :
    (recspace (finite_sum (finite_sum A A) Unit)) -> tybit1 A :=
  mk (tybit_gen (finite_sum (finite_sum A A) Unit))

noncomputable def _dest_tybit1 {A : Type _} [Nonempty A] :
    (tybit1 A) -> recspace (finite_sum (finite_sum A A) Unit) :=
  dest (tybit_gen (finite_sum (finite_sum A A) Unit))

theorem axiom_29 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (a : cart A B), (@mk_cart A B _ _ (@dest_cart A B _ _ a)) = a :=
  fun {A B} _ _ => mk_dest (cart_gen A B)

theorem axiom_30 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (r : (finite_image B) -> A), ((fun f : (finite_image B) -> A => True) r) = ((@dest_cart A B _ _ (@mk_cart A B _ _ r)) = r) :=
  fun {A B} _ _ => dest_mk (cart_gen A B)

theorem axiom_31 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (a : finite_sum A B), (@mk_finite_sum A B _ _ (@dest_finite_sum A B _ _ a)) = a :=
  fun {A B} _ _ => mk_dest (finite_sum_gen A B)

theorem axiom_32 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (r : Nat), ((fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero)) (Nat.add (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))))) r) = ((@dest_finite_sum A B _ _ (@mk_finite_sum A B _ _ r)) = r) :=
  fun {A B} _ _ => dest_mk (finite_sum_gen A B)

theorem axiom_33 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (a : finite_diff A B), (@mk_finite_diff A B _ _ (@dest_finite_diff A B _ _ a)) = a :=
  fun {A B} _ _ => mk_dest (finite_diff_gen A B)

theorem axiom_34 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (r : Nat), ((fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero)) (@COND Nat _ (Nat.lt (@dimindex B _ (@UNIV B _)) (@dimindex A _ (@UNIV A _))) (Nat.sub (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))) (NUMERAL (BIT1 Nat.zero))))) r) = ((@dest_finite_diff A B _ _ (@mk_finite_diff A B _ _ r)) = r) :=
  fun {A B} _ _ => dest_mk (finite_diff_gen A B)

theorem axiom_35 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (a : finite_prod A B), (@mk_finite_prod A B _ _ (@dest_finite_prod A B _ _ a)) = a :=
  fun {A B} _ _ => mk_dest (finite_prod_gen A B)

theorem axiom_36 : ∀ {A B : Type*} [Nonempty A] [Nonempty B] (r : Nat), ((fun x : Nat => @IN Nat _ x (dotdot (NUMERAL (BIT1 Nat.zero)) (Nat.mul (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))))) r) = ((@dest_finite_prod A B _ _ (@mk_finite_prod A B _ _ r)) = r) :=
  fun {A B} _ _ => dest_mk (finite_prod_gen A B)

theorem axiom_37 : ∀ {A : Type*} [Nonempty A] (a : tybit0 A), (@_mk_tybit0 A _ (@_dest_tybit0 A _ a)) = a :=
  fun {A} _ => mk_dest (tybit_gen (finite_sum A A))

theorem axiom_38 : ∀ {A : Type*} [Nonempty A] (r : recspace (finite_sum A A)), ((fun a : recspace (finite_sum A A) => ∀ tybit0' : (recspace (finite_sum A A)) -> Prop, (∀ a' : recspace (finite_sum A A), (∃ a'' : finite_sum A A, a' = ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL Nat.zero) a''' (fun n : Nat => @BOTTOM (finite_sum A A) _)) a'')) -> tybit0' a') -> tybit0' a) r) = ((@_dest_tybit0 A _ (@_mk_tybit0 A _ r)) = r) :=
  fun {A} _ => dest_mk (tybit_gen (finite_sum A A))

theorem axiom_39 : ∀ {A : Type*} [Nonempty A] (a : tybit1 A), (@_mk_tybit1 A _ (@_dest_tybit1 A _ a)) = a :=
  fun {A} _ => mk_dest (tybit_gen (finite_sum (finite_sum A A) Unit))

theorem axiom_40 : ∀ {A : Type*} [Nonempty A] (r : recspace (finite_sum (finite_sum A A) Unit)), ((fun a : recspace (finite_sum (finite_sum A A) Unit) => ∀ tybit1' : (recspace (finite_sum (finite_sum A A) Unit)) -> Prop, (∀ a' : recspace (finite_sum (finite_sum A A) Unit), (∃ a'' : finite_sum (finite_sum A A) Unit, a' = ((fun a''' : finite_sum (finite_sum A A) Unit => @CONSTR (finite_sum (finite_sum A A) Unit) _ (NUMERAL Nat.zero) a''' (fun n : Nat => @BOTTOM (finite_sum (finite_sum A A) Unit) _)) a'')) -> tybit1' a') -> tybit1' a) r) = ((@_dest_tybit1 A _ (@_mk_tybit1 A _ r)) = r) :=
  fun {A} _ => dest_mk (tybit_gen (finite_sum (finite_sum A A) Unit))


noncomputable def dollar {A N' : Type _} [Nonempty A] [Nonempty N'] : (cart A N') -> Nat -> A := fun _94652 : cart A N' => fun _94653 : Nat => @dest_cart A N' _ _ _94652 (@finite_index N' _ _94653)
theorem dollar_def {A N' : Type _} [Nonempty A] [Nonempty N'] : (@dollar A N' _ _) = (fun _94652 : cart A N' => fun _94653 : Nat => @dest_cart A N' _ _ _94652 (@finite_index N' _ _94653)) := by apply Eq.refl (@dollar A N' _ _)

noncomputable def lambda {A B : Type _} [Nonempty A] [Nonempty B] : (Nat -> A) -> cart A B := fun _94688 : Nat -> A => @Classical.epsilon (cart A B) _ (fun f : cart A B => ∀ i : Nat, ((Nat.le (NUMERAL (BIT1 Nat.zero)) i) ∧ (Nat.le i (@dimindex B _ (@UNIV B _)))) -> (@dollar A B _ _ f i) = (_94688 i))
theorem lambda_def {A B : Type _} [Nonempty A] [Nonempty B] : (@lambda A B _ _) = (fun _94688 : Nat -> A => @Classical.epsilon (cart A B) _ (fun f : cart A B => ∀ i : Nat, ((Nat.le (NUMERAL (BIT1 Nat.zero)) i) ∧ (Nat.le i (@dimindex B _ (@UNIV B _)))) -> (@dollar A B _ _ f i) = (_94688 i))) := by apply Eq.refl (@lambda A B _ _)

noncomputable def pastecart {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A M) -> (cart A N') -> cart A (finite_sum M N') := fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') _ _ (fun i : Nat => @COND A _ (Nat.le i (@dimindex M _ (@UNIV M _))) (@dollar A M _ _ _94979 i) (@dollar A N' _ _ _94980 (Nat.sub i (@dimindex M _ (@UNIV M _)))))
theorem pastecart_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@pastecart A M N' _ _ _) = (fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') _ _ (fun i : Nat => @COND A _ (Nat.le i (@dimindex M _ (@UNIV M _))) (@dollar A M _ _ _94979 i) (@dollar A N' _ _ _94980 (Nat.sub i (@dimindex M _ (@UNIV M _)))))) := by apply Eq.refl (@pastecart A M N' _ _ _)

noncomputable def fstcart {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A (finite_sum M N')) -> cart A M := fun _94991 : cart A (finite_sum M N') => @lambda A M _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94991 i)
theorem fstcart_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@fstcart A M N' _ _ _) = (fun _94991 : cart A (finite_sum M N') => @lambda A M _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94991 i)) := by apply Eq.refl (@fstcart A M N' _ _ _)

noncomputable def sndcart {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A (finite_sum M N')) -> cart A N' := fun _94996 : cart A (finite_sum M N') => @lambda A N' _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94996 (Nat.add i (@dimindex M _ (@UNIV M _))))
theorem sndcart_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@sndcart A M N' _ _ _) = (fun _94996 : cart A (finite_sum M N') => @lambda A N' _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94996 (Nat.add i (@dimindex M _ (@UNIV M _))))) := by apply Eq.refl (@sndcart A M N' _ _ _)

noncomputable def _100406 {A : Type _} [Nonempty A] : (finite_sum A A) -> tybit0 A := fun a : finite_sum A A => @_mk_tybit0 A _ ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum A A) _)) a)
theorem _100406_def {A : Type _} [Nonempty A] : (@_100406 A _) = (fun a : finite_sum A A => @_mk_tybit0 A _ ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum A A) _)) a)) := by apply Eq.refl (@_100406 A _)

noncomputable def mktybit0 {A : Type _} [Nonempty A] : (finite_sum A A) -> tybit0 A := @_100406 A _
theorem mktybit0_def {A : Type _} [Nonempty A] : (@mktybit0 A _) = (@_100406 A _) := by apply Eq.refl (@mktybit0 A _)

noncomputable def _100425 {A : Type _} [Nonempty A] : (finite_sum (finite_sum A A) Unit) -> tybit1 A := fun a : finite_sum (finite_sum A A) Unit => @_mk_tybit1 A _ ((fun a' : finite_sum (finite_sum A A) Unit => @CONSTR (finite_sum (finite_sum A A) Unit) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum (finite_sum A A) Unit) _)) a)
theorem _100425_def {A : Type _} [Nonempty A] : (@_100425 A _) = (fun a : finite_sum (finite_sum A A) Unit => @_mk_tybit1 A _ ((fun a' : finite_sum (finite_sum A A) Unit => @CONSTR (finite_sum (finite_sum A A) Unit) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum (finite_sum A A) Unit) _)) a)) := by apply Eq.refl (@_100425 A _)

noncomputable def mktybit1 {A : Type _} [Nonempty A] : (finite_sum (finite_sum A A) Unit) -> tybit1 A := @_100425 A _
theorem mktybit1_def {A : Type _} [Nonempty A] : (@mktybit1 A _) = (@_100425 A _) := by apply Eq.refl (@mktybit1 A _)

noncomputable def vector {A N' : Type _} [Nonempty A] [Nonempty N'] : (List A) -> cart A N' := fun _102119 : List A => @lambda A N' _ _ (fun i : Nat => @EL A _ (Nat.sub i (NUMERAL (BIT1 Nat.zero))) _102119)
theorem vector_def {A N' : Type _} [Nonempty A] [Nonempty N'] : (@vector A N' _ _) = (fun _102119 : List A => @lambda A N' _ _ (fun i : Nat => @EL A _ (Nat.sub i (NUMERAL (BIT1 Nat.zero))) _102119)) := by apply Eq.refl (@vector A N' _ _)

noncomputable def PCROSS {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] :
    ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop :=
  fun (s : Set (cart A M)) (t : Set (cart A N')) => Set.image2 pastecart s t
theorem PCROSS_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@PCROSS A M N' _ _ _) = (fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) _ (fun GEN_PVAR_363 : cart A (finite_sum M N') => ∃ x : cart A M, ∃ y : cart A N', @SETSPEC (cart A (finite_sum M N')) _ GEN_PVAR_363 ((@IN (cart A M) _ x _102146) ∧ (@IN (cart A N') _ y _102147)) (@pastecart A M N' _ _ _ x y))):= by
  funext s t
  unfold PCROSS GSPEC SETSPEC id IN
  funext z
  apply propext
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, y, ⟨hx, hy⟩, rfl⟩
  · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

open Classical in
/-- Structural recursion behind `CASEWISE`: walk the clause list and fire the first clause
whose pattern matches `x`; on an empty list the value is unspecified, as in HOL Light. -/
noncomputable def CASEWISEaux {A B C D : Type _} [Nonempty A] [Nonempty B] [Nonempty C]
    [Nonempty D] :
    List (prod (B -> C) (D -> B -> A)) -> D -> C -> A
  | [], _, _ => Classical.epsilon (fun _ : A => True)
  | h :: t, f, x =>
      if ∃ y : B, prod_fst h y = x
      then prod_snd h f (Classical.epsilon (fun y : B => prod_fst h y = x))
      else CASEWISEaux t f x

noncomputable def CASEWISE {_138002 _138038 _138042 _138043 : Type _} [Nonempty _138002] [Nonempty _138038] [Nonempty _138042] [Nonempty _138043] : (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 :=
  CASEWISEaux
theorem CASEWISE_def {_138002 _138038 _138042 _138043 : Type _} [Nonempty _138002] [Nonempty _138038] [Nonempty _138042] [Nonempty _138043] : (@CASEWISE _138002 _138038 _138042 _138043 _ _ _ _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) _ (fun CASEWISE' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => ∀ _102751 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ f : _138043, ∀ x : _138042, (CASEWISE' _102751 (@NIL (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _) f x) = (@Classical.epsilon _138002 _ (fun y : _138002 => True))) ∧ (∀ h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), ∀ t : List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), ∀ f : _138043, ∀ x : _138042, (CASEWISE' _102751 (@CONS (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _ h t) f x) = (@COND _138002 _ (∃ y : _138038, (@prod_fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) = x) (@prod_snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h f (@Classical.epsilon _138038 _ (fun y : _138038 => (@prod_fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) = x))) (CASEWISE' _102751 t f x)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))))):= by
  epsilon_tac
  · intro tag
    simp only [NIL, CONS, COND]
    exact ⟨fun f x => rfl, fun h t f x => rfl⟩
  · intro g _ hg
    unfold NIL CONS COND at hg
    funext tag l f x
    induction l with
    | nil => rw [(hg tag).1 f x] ; rfl
    | cons h t ih => rw [(hg tag).2 h t f x, ← ih] ; rfl

noncomputable def admissible {_138333 _138336 _138340 _138341 _138346 : Type _} [Nonempty _138333] [Nonempty _138336] [Nonempty _138340] [Nonempty _138341] [Nonempty _138346] : (_138340 -> _138333 -> Prop) -> ((_138340 -> _138336) -> _138346 -> Prop) -> (_138346 -> _138333) -> ((_138340 -> _138336) -> _138346 -> _138341) -> Prop := fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => ∀ f : _138340 -> _138336, ∀ g : _138340 -> _138336, ∀ a : _138346, ((_103819 f a) ∧ ((_103819 g a) ∧ (∀ z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a)
theorem admissible_def {_138333 _138336 _138340 _138341 _138346 : Type _} [Nonempty _138333] [Nonempty _138336] [Nonempty _138340] [Nonempty _138341] [Nonempty _138346] : (@admissible _138333 _138336 _138340 _138341 _138346 _ _ _ _ _) = (fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => ∀ f : _138340 -> _138336, ∀ g : _138340 -> _138336, ∀ a : _138346, ((_103819 f a) ∧ ((_103819 g a) ∧ (∀ z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a)) := by apply Eq.refl (@admissible _138333 _138336 _138340 _138341 _138346 _ _ _ _ _)

noncomputable def tailadmissible {A B P : Type _} [Nonempty A] [Nonempty B] [Nonempty P] : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop := fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => ∃ P' : (A -> B) -> P -> Prop, ∃ G : (A -> B) -> P -> A, ∃ H : (A -> B) -> P -> B, (∀ f : A -> B, ∀ a : P, ∀ y : A, ((P' f a) ∧ (_103850 y (G f a))) -> _103850 y (_103852 a)) ∧ ((∀ f : A -> B, ∀ g : A -> B, ∀ a : P, (∀ z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) ∧ (((G f a) = (G g a)) ∧ ((H f a) = (H g a)))) ∧ (∀ f : A -> B, ∀ a : P, (_103851 f a) -> (_103853 f a) = (@COND B _ (P' f a) (f (G f a)) (H f a))))
theorem tailadmissible_def {A B P : Type _} [Nonempty A] [Nonempty B] [Nonempty P] : (@tailadmissible A B P _ _ _) = (fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => ∃ P' : (A -> B) -> P -> Prop, ∃ G : (A -> B) -> P -> A, ∃ H : (A -> B) -> P -> B, (∀ f : A -> B, ∀ a : P, ∀ y : A, ((P' f a) ∧ (_103850 y (G f a))) -> _103850 y (_103852 a)) ∧ ((∀ f : A -> B, ∀ g : A -> B, ∀ a : P, (∀ z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) ∧ (((G f a) = (G g a)) ∧ ((H f a) = (H g a)))) ∧ (∀ f : A -> B, ∀ a : P, (_103851 f a) -> (_103853 f a) = (@COND B _ (P' f a) (f (G f a)) (H f a))))) := by apply Eq.refl (@tailadmissible A B P _ _ _)

noncomputable def superadmissible {_138490 _138492 _138498 : Type _} [Nonempty _138490] [Nonempty _138492] [Nonempty _138498] : (_138490 -> _138490 -> Prop) -> ((_138490 -> _138492) -> _138498 -> Prop) -> (_138498 -> _138490) -> ((_138490 -> _138492) -> _138498 -> _138492) -> Prop := fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _ _ _ _ _ _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _ _ _ _103882 _103883 _103884 _103885
theorem superadmissible_def {_138490 _138492 _138498 : Type _} [Nonempty _138490] [Nonempty _138492] [Nonempty _138498] : (@superadmissible _138490 _138492 _138498 _ _ _) = (fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _ _ _ _ _ _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _ _ _ _103882 _103883 _103884 _103885) := by apply Eq.refl (@superadmissible _138490 _138492 _138498 _ _ _)
