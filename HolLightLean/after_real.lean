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

noncomputable def IN {A : Type _} [Nonempty A] : A -> (A -> Prop) -> Prop := fun (a : A) (S : Set A) => a ∈ S
theorem IN_def {A : Type _} [Nonempty A] : (@IN A _) = (fun _32403 : A => fun _32404 : A -> Prop => _32404 _32403) := by apply Eq.refl (@IN A _)

noncomputable def GSPEC {A : Type _} [Nonempty A] : (A -> Prop) -> A -> Prop := id
theorem GSPEC_def {A : Type _} [Nonempty A] : (@GSPEC A _) = (fun _32415 : A -> Prop => _32415) := by apply Eq.refl (@GSPEC A _)

noncomputable def SETSPEC {A : Type _} [Nonempty A] : A -> Prop -> A -> Prop := fun x P => {x' | P ∧ x = x'}
theorem SETSPEC_def {A : Type _} [Nonempty A] : (@SETSPEC A _) = (fun _32420 : A => fun _32421 : Prop => fun _32422 : A => _32421 ∧ (_32420 = _32422)) := by apply Eq.refl (@SETSPEC A _)

noncomputable def EMPTY {A : Type _} [Nonempty A] : A -> Prop := Set.instEmptyCollection.emptyCollection
theorem EMPTY_def {A : Type _} [Nonempty A] : (@EMPTY A _) = (fun x : A => False) := by apply Eq.refl (@EMPTY A _)

noncomputable def INSERT {A : Type _} [Nonempty A] : A -> (A -> Prop) -> A -> Prop := fun a S x => IN x (Set.insert a S)
theorem INSERT_def {A : Type _} [Nonempty A] : (@INSERT A _) = (fun _32459 : A => fun _32460 : A -> Prop => fun y : A => (@IN A _ y _32460) ∨ (y = _32459)) := by
  unfold INSERT IN Set.insert
  grind

elab "two_set_align"  : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
  (try unfold GSPEC);
  (try unfold SETSPEC);
  (try unfold IN);
  (try unfold EMPTY);
  (try unfold id);
  (try unfold INSERT);
  (try unfold Set.insert);
  first
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
    )
  )

noncomputable def UNIV {A : Type _} [Nonempty A] : A -> Prop := Set.univ
theorem UNIV_def {A : Type _} [Nonempty A] : (@UNIV A _) = (fun x : A => True) := by apply Eq.refl (@UNIV A _)

noncomputable def UNION {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun (U V : Set A) => (U ∪ V: Set A)
theorem UNION_def {A : Type _} [Nonempty A] : (@UNION A _) = (fun _32471 : A -> Prop => fun _32472 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_0 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_0 ((@IN A _ x _32471) ∨ (@IN A _ x _32472)) x)) := by
  unfold UNION
  two_set_align

noncomputable def UNIONS {A : Type _} [Nonempty A] : ((A -> Prop) -> Prop) -> A -> Prop := fun F : Set (Set A) => ⋃₀ F

theorem UNIONS_def {A : Type _} [Nonempty A] : (@UNIONS A _) = (fun _32483 : (A -> Prop) -> Prop => @GSPEC A _ (fun GEN_PVAR_1 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_1 (∃ u : A -> Prop, (@IN (A -> Prop) _ u _32483) ∧ (@IN A _ x u)) x)) := by
  unfold UNIONS GSPEC SETSPEC id IN
  funext F x
  apply Eq.propIntro <;> intro h
  · refine ⟨x,⟨?_,rfl⟩⟩
    rw[Set.sUnion_eq_iUnion] at h
    obtain ⟨V,hVx⟩ := Set.mem_iUnion.1 h
    refine ⟨(V : Set A), ⟨?_, hVx⟩⟩
    simp_all only [Set.iUnion_coe_set, Subtype.coe_prop]
  · obtain ⟨x', h'⟩ := h
    rw[h'.2]
    exact h'.1

noncomputable def INTER {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun (U V : Set A) => (U ∩ V : Set A)

theorem INTER_def {A : Type _} [Nonempty A] : (@INTER A _) = (fun _32488 : A -> Prop => fun _32489 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_2 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_2 ((@IN A _ x _32488) ∧ (@IN A _ x _32489)) x)) := by
  unfold INTER ; two_set_align

noncomputable def INTERS {A : Type _} [Nonempty A] : ((A -> Prop) -> Prop) -> A -> Prop := fun F : Set (Set A) => ⋂₀ F

theorem INTERS_def {A : Type _} [Nonempty A] : (@INTERS A _) = (fun _32500 : (A -> Prop) -> Prop => @GSPEC A _ (fun GEN_PVAR_3 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_3 (∀ u : A -> Prop, (@IN (A -> Prop) _ u _32500) -> @IN A _ x u) x)) := by
  unfold INTERS GSPEC SETSPEC id IN
  funext F x
  apply Eq.propIntro <;> intro h
  · refine ⟨x,⟨?_,rfl⟩⟩
    intro a ha
    apply h
    exact ha
  · obtain ⟨x', h'⟩ := h
    rw[h'.2]
    exact h'.1

noncomputable def DIFF {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop := fun (U V : Set A) => U \ V

theorem DIFF_def {A : Type _} [Nonempty A] : (@DIFF A _) = (fun _32505 : A -> Prop => fun _32506 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_4 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_4 ((@IN A _ x _32505) ∧ (¬ (@IN A _ x _32506))) x)) := by
  unfold DIFF
  two_set_align

noncomputable def DELETE {A : Type _} [Nonempty A] : (A -> Prop) -> A -> A -> Prop := fun (S : Set A) (a : A) => S \ ({a} : Set A)
theorem DELETE_def {A : Type _} [Nonempty A] : (@DELETE A _) = (fun _32517 : A -> Prop => fun _32518 : A => @GSPEC A _ (fun GEN_PVAR_6 : A => ∃ y : A, @SETSPEC A _ GEN_PVAR_6 ((@IN A _ y _32517) ∧ (¬ (y = _32518))) y)) := by
  unfold DELETE ; two_set_align

noncomputable def SUBSET {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop := fun (U V : Set A) => U ⊆ V
theorem SUBSET_def {A : Type _} [Nonempty A] : (@SUBSET A _) = (fun _32529 : A -> Prop => fun _32530 : A -> Prop => ∀ x : A, (@IN A _ x _32529) -> @IN A _ x _32530) := by apply Eq.refl (@SUBSET A _)

noncomputable def PSUBSET {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop := fun (U V : Set A) => U ⊂ V
theorem PSUBSET_def {A : Type _} [Nonempty A] : (@PSUBSET A _) = (fun _32541 : A -> Prop => fun _32542 : A -> Prop => (@SUBSET A _ _32541 _32542) ∧ (¬ (_32541 = _32542))) := by
  unfold PSUBSET SUBSET
  two_set_align
  expose_names
  exact Set.ssubset_iff_subset_ne.mpr h

noncomputable def DISJOINT {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop := fun (U V : Set A) => Disjoint U V

theorem DISJOINT_def {A : Type _} [Nonempty A] : (@DISJOINT A _) = (fun _32553 : A -> Prop => fun _32554 : A -> Prop => (@INTER A _ _32553 _32554) = (@EMPTY A _)) := by
  unfold DISJOINT INTER EMPTY; two_set_align <;> expose_names
  · exact Disjoint.inter_eq h
  · exact Set.disjoint_iff_inter_eq_empty.mpr h

noncomputable def SING {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := fun S => ∃ a : A, S = ({a} : Set A)
theorem SING_def {A : Type _} [Nonempty A] : (@SING A _) = (fun _32565 : A -> Prop => ∃ x : A, _32565 = (@INSERT A _ x (@EMPTY A _))) := by
  unfold INSERT EMPTY SING
  two_set_align <;> expose_names <;>
  ( obtain ⟨a, h⟩ := h
    rw[h]
    refine ⟨a, ?_⟩
    funext x ; simp only [Set.mem_empty_iff_false, or_false, Set.setOf_eq_eq_singleton,
      Set.mem_singleton_iff, eq_iff_iff]
    trivial)

noncomputable def FINITE {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := Set.Finite
theorem FINITE_def {A : Type _} [Nonempty A] : (@FINITE A _) = (fun a : A -> Prop => ∀ FINITE' : (A -> Prop) -> Prop, (∀ a' : A -> Prop, ((a' = (@EMPTY A _)) ∨ (∃ x : A, ∃ s : A -> Prop, (a' = (@INSERT A _ x s)) ∧ (FINITE' s))) -> FINITE' a') -> FINITE' a) := by
  unfold FINITE
  two_set_align <;> try unfold IN <;> expose_names
  · intro Fin_HOL h'
    have h'U := h' U
    apply h'
    refine Set.Finite.induction_on U h (Or.inl rfl) ?_
    · intro a S hSa ha hInd
      apply Or.elim hInd <;>
      simp_all only [Set.mem_setOf_eq, forall_eq_or_imp, forall_exists_index, and_imp, insert,
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

noncomputable def INFINITE {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := fun _32574 : A -> Prop => ¬ (@FINITE A _ _32574)
theorem INFINITE_def {A : Type _} [Nonempty A] : (@INFINITE A _) = (fun _32574 : A -> Prop => ¬ (@FINITE A _ _32574)) := by apply Eq.refl (@INFINITE A _)

noncomputable def IMAGE {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> B -> Prop := fun _32579 : A -> B => fun _32580 : A -> Prop => @GSPEC B _ (fun GEN_PVAR_7 : B => ∃ y : B, @SETSPEC B _ GEN_PVAR_7 (∃ x : A, (@IN A _ x _32580) ∧ (y = (_32579 x))) y)
theorem IMAGE_def {A B : Type _} [Nonempty A] [Nonempty B] : (@IMAGE A B _ _) = (fun _32579 : A -> B => fun _32580 : A -> Prop => @GSPEC B _ (fun GEN_PVAR_7 : B => ∃ y : B, @SETSPEC B _ GEN_PVAR_7 (∃ x : A, (@IN A _ x _32580) ∧ (y = (_32579 x))) y)) := by apply Eq.refl (@IMAGE A B _ _)

noncomputable def INJ {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (∀ x : A, (@IN A _ x _32592) -> @IN B _ (_32591 x) _32593) ∧ (∀ x : A, ∀ y : A, ((@IN A _ x _32592) ∧ ((@IN A _ y _32592) ∧ ((_32591 x) = (_32591 y)))) -> x = y)
theorem INJ_def {A B : Type _} [Nonempty A] [Nonempty B] : (@INJ A B _ _) = (fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => (∀ x : A, (@IN A _ x _32592) -> @IN B _ (_32591 x) _32593) ∧ (∀ x : A, ∀ y : A, ((@IN A _ x _32592) ∧ ((@IN A _ y _32592) ∧ ((_32591 x) = (_32591 y)))) -> x = y)) := by apply Eq.refl (@INJ A B _ _)

noncomputable def SURJ {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (∀ x : A, (@IN A _ x _32613) -> @IN B _ (_32612 x) _32614) ∧ (∀ x : B, (@IN B _ x _32614) -> ∃ y : A, (@IN A _ y _32613) ∧ ((_32612 y) = x))
theorem SURJ_def {A B : Type _} [Nonempty A] [Nonempty B] : (@SURJ A B _ _) = (fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => (∀ x : A, (@IN A _ x _32613) -> @IN B _ (_32612 x) _32614) ∧ (∀ x : B, (@IN B _ x _32614) -> ∃ y : A, (@IN A _ y _32613) ∧ ((_32612 y) = x))) := by apply Eq.refl (@SURJ A B _ _)

noncomputable def BIJ {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop := fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _ _ _32633 _32634 _32635) ∧ (@SURJ A B _ _ _32633 _32634 _32635)
theorem BIJ_def {A B : Type _} [Nonempty A] [Nonempty B] : (@BIJ A B _ _) = (fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => (@INJ A B _ _ _32633 _32634 _32635) ∧ (@SURJ A B _ _ _32633 _32634 _32635)) := by apply Eq.refl (@BIJ A B _ _)

noncomputable def CHOICE {A : Type _} [Nonempty A] : (A -> Prop) -> A := fun _32654 : A -> Prop => @Classical.epsilon A _ (fun x : A => @IN A _ x _32654)
theorem CHOICE_def {A : Type _} [Nonempty A] : (@CHOICE A _) = (fun _32654 : A -> Prop => @Classical.epsilon A _ (fun x : A => @IN A _ x _32654)) := by apply Eq.refl (@CHOICE A _)

noncomputable def REST {A : Type _} [Nonempty A] : (A -> Prop) -> A -> Prop := fun _32659 : A -> Prop => @DELETE A _ _32659 (@CHOICE A _ _32659)
theorem REST_def {A : Type _} [Nonempty A] : (@REST A _) = (fun _32659 : A -> Prop => @DELETE A _ _32659 (@CHOICE A _ _32659)) := by apply Eq.refl (@REST A _)

noncomputable def FINREC {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop) _ (fun FINREC' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop => ∀ _42261 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), (∀ f : A -> B -> B, ∀ s : A -> Prop, ∀ a : B, ∀ b : B, (FINREC' _42261 f b s a (NUMERAL Nat.zero)) = ((s = (@EMPTY A _)) ∧ (a = b))) ∧ (∀ b : B, ∀ s : A -> Prop, ∀ n : Nat, ∀ a : B, ∀ f : A -> B -> B, (FINREC' _42261 f b s a (Nat.succ n)) = (∃ x : A, ∃ c : B, (@IN A _ x s) ∧ ((FINREC' _42261 f b (@DELETE A _ s x) c n) ∧ (a = (f x c)))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))
theorem FINREC_def {A B : Type _} [Nonempty A] [Nonempty B] : (@FINREC A B _ _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop) _ (fun FINREC' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> Nat -> Prop => ∀ _42261 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))), (∀ f : A -> B -> B, ∀ s : A -> Prop, ∀ a : B, ∀ b : B, (FINREC' _42261 f b s a (NUMERAL Nat.zero)) = ((s = (@EMPTY A _)) ∧ (a = b))) ∧ (∀ b : B, ∀ s : A -> Prop, ∀ n : Nat, ∀ a : B, ∀ f : A -> B -> B, (FINREC' _42261 f b s a (Nat.succ n)) = (∃ x : A, ∃ c : B, (@IN A _ x s) ∧ ((FINREC' _42261 f b (@DELETE A _ s x) c n) ∧ (a = (f x c)))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))) := by apply Eq.refl (@FINREC A B _ _)

noncomputable def ITSET {A B : Type _} [Nonempty A] [Nonempty B] : (A -> B -> B) -> (A -> Prop) -> B -> B := fun _43111 : A -> B -> B => fun _43112 : A -> Prop => fun _43113 : B => @Classical.epsilon ((A -> Prop) -> B) _ (fun g : (A -> Prop) -> B => ((g (@EMPTY A _)) = _43113) ∧ (∀ x : A, ∀ s : A -> Prop, (@FINITE A _ s) -> (g (@INSERT A _ x s)) = (@COND B _ (@IN A _ x s) (g s) (_43111 x (g s))))) _43112
theorem ITSET_def {A B : Type _} [Nonempty A] [Nonempty B] : (@ITSET A B _ _) = (fun _43111 : A -> B -> B => fun _43112 : A -> Prop => fun _43113 : B => @Classical.epsilon ((A -> Prop) -> B) _ (fun g : (A -> Prop) -> B => ((g (@EMPTY A _)) = _43113) ∧ (∀ x : A, ∀ s : A -> Prop, (@FINITE A _ s) -> (g (@INSERT A _ x s)) = (@COND B _ (@IN A _ x s) (g s) (_43111 x (g s))))) _43112) := by apply Eq.refl (@ITSET A B _ _)

noncomputable def CARD {A : Type _} [Nonempty A] : (A -> Prop) -> Nat := fun _43314 : A -> Prop => @ITSET A Nat _ _ (fun x : A => fun n : Nat => Nat.succ n) _43314 (NUMERAL Nat.zero)
theorem CARD_def {A : Type _} [Nonempty A] : (@CARD A _) = (fun _43314 : A -> Prop => @ITSET A Nat _ _ (fun x : A => fun n : Nat => Nat.succ n) _43314 (NUMERAL Nat.zero)) := by apply Eq.refl (@CARD A _)

noncomputable def HAS_SIZE {A : Type _} [Nonempty A] : (A -> Prop) -> Nat -> Prop := fun _43489 : A -> Prop => fun _43490 : Nat => (@FINITE A _ _43489) ∧ ((@CARD A _ _43489) = _43490)
theorem HAS_SIZE_def {A : Type _} [Nonempty A] : (@HAS_SIZE A _) = (fun _43489 : A -> Prop => fun _43490 : Nat => (@FINITE A _ _43489) ∧ ((@CARD A _ _43489) = _43490)) := by apply Eq.refl (@HAS_SIZE A _)

noncomputable def CROSS {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop := fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) _ (fun GEN_PVAR_132 : prod A B => ∃ x : A, ∃ y : B, @SETSPEC (prod A B) _ GEN_PVAR_132 ((@IN A _ x _47408) ∧ (@IN B _ y _47409)) (@prod_mk A B _ _ x y))
theorem CROSS_def {A B : Type _} [Nonempty A] [Nonempty B] : (@CROSS A B _ _) = (fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) _ (fun GEN_PVAR_132 : prod A B => ∃ x : A, ∃ y : B, @SETSPEC (prod A B) _ GEN_PVAR_132 ((@IN A _ x _47408) ∧ (@IN B _ y _47409)) (@prod_mk A B _ _ x y))) := by apply Eq.refl (@CROSS A B _ _)

noncomputable def ARB {A : Type _} [Nonempty A] : A := @Classical.epsilon A _ (fun x : A => False)
theorem ARB_def {A : Type _} [Nonempty A] : (@ARB A _) = (@Classical.epsilon A _ (fun x : A => False)) := by apply Eq.refl (@ARB A _)

noncomputable def EXTENSIONAL {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (A -> B) -> Prop := fun _48182 : A -> Prop => @GSPEC (A -> B) _ (fun GEN_PVAR_141 : A -> B => ∃ f : A -> B, @SETSPEC (A -> B) _ GEN_PVAR_141 (∀ x : A, (¬ (@IN A _ x _48182)) -> (f x) = (@ARB B _)) f)
theorem EXTENSIONAL_def {A B : Type _} [Nonempty A] [Nonempty B] : (@EXTENSIONAL A B _ _) = (fun _48182 : A -> Prop => @GSPEC (A -> B) _ (fun GEN_PVAR_141 : A -> B => ∃ f : A -> B, @SETSPEC (A -> B) _ GEN_PVAR_141 (∀ x : A, (¬ (@IN A _ x _48182)) -> (f x) = (@ARB B _)) f)) := by apply Eq.refl (@EXTENSIONAL A B _ _)

noncomputable def RESTRICTION {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (A -> B) -> A -> B := fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B _ (@IN A _ _48236 _48234) (_48235 _48236) (@ARB B _)
theorem RESTRICTION_def {A B : Type _} [Nonempty A] [Nonempty B] : (@RESTRICTION A B _ _) = (fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B _ (@IN A _ _48236 _48234) (_48235 _48236) (@ARB B _)) := by apply Eq.refl (@RESTRICTION A B _ _)

noncomputable def cartesian_product {A K : Type _} [Nonempty A] [Nonempty K] : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop := fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) _ (fun GEN_PVAR_142 : K -> A => ∃ f : K -> A, @SETSPEC (K -> A) _ GEN_PVAR_142 ((@EXTENSIONAL K A _ _ _48429 f) ∧ (∀ i : K, (@IN K _ i _48429) -> @IN A _ (f i) (_48430 i))) f)
theorem cartesian_product_def {A K : Type _} [Nonempty A] [Nonempty K] : (@cartesian_product A K _ _) = (fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) _ (fun GEN_PVAR_142 : K -> A => ∃ f : K -> A, @SETSPEC (K -> A) _ GEN_PVAR_142 ((@EXTENSIONAL K A _ _ _48429 f) ∧ (∀ i : K, (@IN K _ i _48429) -> @IN A _ (f i) (_48430 i))) f)) := by apply Eq.refl (@cartesian_product A K _ _)

noncomputable def product_map {A B K : Type _} [Nonempty A] [Nonempty B] [Nonempty K] : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B := fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _ _ _49478 (fun i : K => _49479 i (x i))
theorem product_map_def {A B K : Type _} [Nonempty A] [Nonempty B] [Nonempty K] : (@product_map A B K _ _ _) = (fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _ _ _49478 (fun i : K => _49479 i (x i))) := by apply Eq.refl (@product_map A B K _ _ _)

noncomputable def disjoint_union {A K : Type _} [Nonempty A] [Nonempty K] : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop := fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) _ (fun GEN_PVAR_145 : prod K A => ∃ i : K, ∃ x : A, @SETSPEC (prod K A) _ GEN_PVAR_145 ((@IN K _ i _49614) ∧ (@IN A _ x (_49615 i))) (@prod_mk K A _ _ i x))
theorem disjoint_union_def {A K : Type _} [Nonempty A] [Nonempty K] : (@disjoint_union A K _ _) = (fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) _ (fun GEN_PVAR_145 : prod K A => ∃ i : K, ∃ x : A, @SETSPEC (prod K A) _ GEN_PVAR_145 ((@IN K _ i _49614) ∧ (@IN A _ x (_49615 i))) (@prod_mk K A _ _ i x))) := by apply Eq.refl (@disjoint_union A K _ _)

noncomputable def set_of_list {A : Type _} [Nonempty A] : (List A) -> A -> Prop := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (List A) -> A -> Prop) _ (fun set_of_list' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (List A) -> A -> Prop => ∀ _56511 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))), ((set_of_list' _56511 (@NIL A _)) = (@EMPTY A _)) ∧ (∀ h : A, ∀ t : List A, (set_of_list' _56511 (@CONS A _ h t)) = (@INSERT A _ h (set_of_list' _56511 t)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero))))))))))))))))))
theorem set_of_list_def {A : Type _} [Nonempty A] : (@set_of_list A _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (List A) -> A -> Prop) _ (fun set_of_list' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))))) -> (List A) -> A -> Prop => ∀ _56511 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))), ((set_of_list' _56511 (@NIL A _)) = (@EMPTY A _)) ∧ (∀ h : A, ∀ t : List A, (set_of_list' _56511 (@CONS A _ h t)) = (@INSERT A _ h (set_of_list' _56511 t)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero))))))))))))))))))) := by apply Eq.refl (@set_of_list A _)

noncomputable def list_of_set {A : Type _} [Nonempty A] : (A -> Prop) -> List A := fun _56512 : A -> Prop => @Classical.epsilon (List A) _ (fun l : List A => ((@set_of_list A _ l) = _56512) ∧ ((@LENGTH A _ l) = (@CARD A _ _56512)))
theorem list_of_set_def {A : Type _} [Nonempty A] : (@list_of_set A _) = (fun _56512 : A -> Prop => @Classical.epsilon (List A) _ (fun l : List A => ((@set_of_list A _ l) = _56512) ∧ ((@LENGTH A _ l) = (@CARD A _ _56512)))) := by apply Eq.refl (@list_of_set A _)

noncomputable def pairwise {A : Type _} [Nonempty A] : (A -> A -> Prop) -> (A -> Prop) -> Prop := fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => ∀ x : A, ∀ y : A, ((@IN A _ x _56703) ∧ ((@IN A _ y _56703) ∧ (¬ (x = y)))) -> _56702 x y
theorem pairwise_def {A : Type _} [Nonempty A] : (@pairwise A _) = (fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => ∀ x : A, ∀ y : A, ((@IN A _ x _56703) ∧ ((@IN A _ y _56703) ∧ (¬ (x = y)))) -> _56702 x y) := by apply Eq.refl (@pairwise A _)

noncomputable def UNION_OF {A : Type _} [Nonempty A] : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, (_57415 u) ∧ ((∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57416 c) ∧ ((@UNIONS A _ u) = s))
theorem UNION_OF_def {A : Type _} [Nonempty A] : (@UNION_OF A _) = (fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, (_57415 u) ∧ ((∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57416 c) ∧ ((@UNIONS A _ u) = s))) := by apply Eq.refl (@UNION_OF A _)

noncomputable def INTERSECTION_OF {A : Type _} [Nonempty A] : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop := fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, (_57427 u) ∧ ((∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57428 c) ∧ ((@INTERS A _ u) = s))
theorem INTERSECTION_OF_def {A : Type _} [Nonempty A] : (@INTERSECTION_OF A _) = (fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, (_57427 u) ∧ ((∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57428 c) ∧ ((@INTERS A _ u) = s))) := by apply Eq.refl (@INTERSECTION_OF A _)

noncomputable def ARBITRARY {A : Type _} [Nonempty A] : ((A -> Prop) -> Prop) -> Prop := fun _57563 : (A -> Prop) -> Prop => True
theorem ARBITRARY_def {A : Type _} [Nonempty A] : (@ARBITRARY A _) = (fun _57563 : (A -> Prop) -> Prop => True) := by apply Eq.refl (@ARBITRARY A _)

noncomputable def le_c {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop := fun _64157 : A -> Prop => fun _64158 : B -> Prop => ∃ f : A -> B, (∀ x : A, (@IN A _ x _64157) -> @IN B _ (f x) _64158) ∧ (∀ x : A, ∀ y : A, ((@IN A _ x _64157) ∧ ((@IN A _ y _64157) ∧ ((f x) = (f y)))) -> x = y)
theorem le_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@le_c A B _ _) = (fun _64157 : A -> Prop => fun _64158 : B -> Prop => ∃ f : A -> B, (∀ x : A, (@IN A _ x _64157) -> @IN B _ (f x) _64158) ∧ (∀ x : A, ∀ y : A, ((@IN A _ x _64157) ∧ ((@IN A _ y _64157) ∧ ((f x) = (f y)))) -> x = y)) := by apply Eq.refl (@le_c A B _ _)

noncomputable def lt_c {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop := fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _ _ _64169 _64170) ∧ (¬ (@le_c B A _ _ _64170 _64169))
theorem lt_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@lt_c A B _ _) = (fun _64169 : A -> Prop => fun _64170 : B -> Prop => (@le_c A B _ _ _64169 _64170) ∧ (¬ (@le_c B A _ _ _64170 _64169))) := by apply Eq.refl (@lt_c A B _ _)

noncomputable def eq_c {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop := fun _64181 : A -> Prop => fun _64182 : B -> Prop => ∃ f : A -> B, (∀ x : A, (@IN A _ x _64181) -> @IN B _ (f x) _64182) ∧ (∀ y : B, (@IN B _ y _64182) -> @EXISTSUNIQUE A _ (fun x : A => (@IN A _ x _64181) ∧ ((f x) = y)))
theorem eq_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@eq_c A B _ _) = (fun _64181 : A -> Prop => fun _64182 : B -> Prop => ∃ f : A -> B, (∀ x : A, (@IN A _ x _64181) -> @IN B _ (f x) _64182) ∧ (∀ y : B, (@IN B _ y _64182) -> @EXISTSUNIQUE A _ (fun x : A => (@IN A _ x _64181) ∧ ((f x) = y)))) := by apply Eq.refl (@eq_c A B _ _)

noncomputable def ge_c {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop := fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _ _ _64194 _64193
theorem ge_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@ge_c A B _ _) = (fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _ _ _64194 _64193) := by apply Eq.refl (@ge_c A B _ _)

noncomputable def gt_c {A B : Type _} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop := fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _ _ _64206 _64205
theorem gt_c_def {A B : Type _} [Nonempty A] [Nonempty B] : (@gt_c A B _ _) = (fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _ _ _64206 _64205) := by apply Eq.refl (@gt_c A B _ _)

noncomputable def COUNTABLE {A : Type _} [Nonempty A] : (A -> Prop) -> Prop := fun _64356 : A -> Prop => @ge_c Nat A _ _ (@UNIV Nat _) _64356
theorem COUNTABLE_def {A : Type _} [Nonempty A] : (@COUNTABLE A _) = (fun _64356 : A -> Prop => @ge_c Nat A _ _ (@UNIV Nat _) _64356) := by apply Eq.refl (@COUNTABLE A _)

noncomputable def sup : (Real -> Prop) -> Real := fun _64361 : Real -> Prop => @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x _64361) -> real_le x a) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x _64361) -> real_le x b) -> real_le a b))
theorem sup_def : sup = (fun _64361 : Real -> Prop => @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x _64361) -> real_le x a) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x _64361) -> real_le x b) -> real_le a b))) := by apply Eq.refl sup

noncomputable def inf : (Real -> Prop) -> Real := fun _65220 : Real -> Prop => @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x _65220) -> real_le a x) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x _65220) -> real_le b x) -> real_le b a))
theorem inf_def : inf = (fun _65220 : Real -> Prop => @Classical.epsilon Real _ (fun a : Real => (∀ x : Real, (@IN Real _ x _65220) -> real_le a x) ∧ (∀ b : Real, (∀ x : Real, (@IN Real _ x _65220) -> real_le b x) -> real_le b a))) := by apply Eq.refl inf

noncomputable def has_inf : (Real -> Prop) -> Real -> Prop := fun _66570 : Real -> Prop => fun _66571 : Real => ∀ c : Real, (∀ x : Real, (@IN Real _ x _66570) -> real_le c x) = (real_le c _66571)
theorem has_inf_def : has_inf = (fun _66570 : Real -> Prop => fun _66571 : Real => ∀ c : Real, (∀ x : Real, (@IN Real _ x _66570) -> real_le c x) = (real_le c _66571)) := by apply Eq.refl has_inf

noncomputable def has_sup : (Real -> Prop) -> Real -> Prop := fun _66582 : Real -> Prop => fun _66583 : Real => ∀ c : Real, (∀ x : Real, (@IN Real _ x _66582) -> real_le x c) = (real_le _66583 c)
theorem has_sup_def : has_sup = (fun _66582 : Real -> Prop => fun _66583 : Real => ∀ c : Real, (∀ x : Real, (@IN Real _ x _66582) -> real_le x c) = (real_le _66583 c)) := by apply Eq.refl has_sup

noncomputable def dotdot : Nat -> Nat -> Nat -> Prop := fun _67008 : Nat => fun _67009 : Nat => @GSPEC Nat _ (fun GEN_PVAR_231 : Nat => ∃ x : Nat, @SETSPEC Nat _ GEN_PVAR_231 ((Nat.le _67008 x) ∧ (Nat.le x _67009)) x)
theorem dotdot_def : dotdot = (fun _67008 : Nat => fun _67009 : Nat => @GSPEC Nat _ (fun GEN_PVAR_231 : Nat => ∃ x : Nat, @SETSPEC Nat _ GEN_PVAR_231 ((Nat.le _67008 x) ∧ (Nat.le x _67009)) x)) := by apply Eq.refl dotdot

noncomputable def neutral {A : Type _} [Nonempty A] : (A -> A -> A) -> A := fun _68920 : A -> A -> A => @Classical.epsilon A _ (fun x : A => ∀ y : A, ((_68920 x y) = y) ∧ ((_68920 y x) = y))
theorem neutral_def {A : Type _} [Nonempty A] : (@neutral A _) = (fun _68920 : A -> A -> A => @Classical.epsilon A _ (fun x : A => ∀ y : A, ((_68920 x y) = y) ∧ ((_68920 y x) = y))) := by apply Eq.refl (@neutral A _)

noncomputable def monoidal {A : Type _} [Nonempty A] : (A -> A -> A) -> Prop := fun _68925 : A -> A -> A => (∀ x : A, ∀ y : A, (_68925 x y) = (_68925 y x)) ∧ ((∀ x : A, ∀ y : A, ∀ z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) ∧ (∀ x : A, (_68925 (@neutral A _ _68925) x) = x))
theorem monoidal_def {A : Type _} [Nonempty A] : (@monoidal A _) = (fun _68925 : A -> A -> A => (∀ x : A, ∀ y : A, (_68925 x y) = (_68925 y x)) ∧ ((∀ x : A, ∀ y : A, ∀ z : A, (_68925 x (_68925 y z)) = (_68925 (_68925 x y) z)) ∧ (∀ x : A, (_68925 (@neutral A _ _68925) x) = x))) := by apply Eq.refl (@monoidal A _)

noncomputable def support {A B : Type _} [Nonempty A] [Nonempty B] : (B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop := fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_239 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_239 ((@IN A _ x _69012) ∧ (¬ ((_69011 x) = (@neutral B _ _69010)))) x)
theorem support_def {A B : Type _} [Nonempty A] [Nonempty B] : (@support A B _ _) = (fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_239 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_239 ((@IN A _ x _69012) ∧ (¬ ((_69011 x) = (@neutral B _ _69010)))) x)) := by apply Eq.refl (@support A B _ _)

noncomputable def iterate {A B : Type _} [Nonempty A] [Nonempty B] : (B -> B -> B) -> (A -> Prop) -> (A -> B) -> B := fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B _ (@FINITE A _ (@support A B _ _ _69031 _69033 _69032)) (@ITSET A B _ _ (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _ _ _69031 _69033 _69032) (@neutral B _ _69031)) (@neutral B _ _69031)
theorem iterate_def {A B : Type _} [Nonempty A] [Nonempty B] : (@iterate A B _ _) = (fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B _ (@FINITE A _ (@support A B _ _ _69031 _69033 _69032)) (@ITSET A B _ _ (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _ _ _69031 _69033 _69032) (@neutral B _ _69031)) (@neutral B _ _69031)) := by apply Eq.refl (@iterate A B _ _)

#exit

noncomputable def iterato {A K : Type _} [Nonempty A] [Nonempty K] : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) _ (fun itty : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => ∀ _76787 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∀ dom : A -> Prop, ∀ neut : A, ∀ op : A -> A -> A, ∀ ltle : K -> K -> Prop, ∀ k : K -> Prop, ∀ f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A _ ((@FINITE K _ (@GSPEC K _ (fun GEN_PVAR_265 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_265 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i))) ∧ (¬ ((@GSPEC K _ (fun GEN_PVAR_266 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_266 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i)) = (@EMPTY K _)))) (@LET K A _ _ (fun i : K => @LET_END A _ (op (f i) (itty _76787 dom neut op ltle (@GSPEC K _ (fun GEN_PVAR_267 : K => ∃ j : K, @SETSPEC K _ GEN_PVAR_267 ((@IN K _ j (@DELETE K _ k i)) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) j)) f))) (@COND K _ (∃ i : K, (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i)))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))))) neut)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))))))
theorem iterato_def {A K : Type _} [Nonempty A] [Nonempty K] : (@iterato A K _ _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) _ (fun itty : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => ∀ _76787 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))), ∀ dom : A -> Prop, ∀ neut : A, ∀ op : A -> A -> A, ∀ ltle : K -> K -> Prop, ∀ k : K -> Prop, ∀ f : K -> A, (itty _76787 dom neut op ltle k f) = (@COND A _ ((@FINITE K _ (@GSPEC K _ (fun GEN_PVAR_265 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_265 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i))) ∧ (¬ ((@GSPEC K _ (fun GEN_PVAR_266 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_266 ((@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i)) = (@EMPTY K _)))) (@LET K A _ _ (fun i : K => @LET_END A _ (op (f i) (itty _76787 dom neut op ltle (@GSPEC K _ (fun GEN_PVAR_267 : K => ∃ j : K, @SETSPEC K _ GEN_PVAR_267 ((@IN K _ j (@DELETE K _ k i)) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) j)) f))) (@COND K _ (∃ i : K, (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ ((@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) ∧ (∀ j : K, ((ltle j i) ∧ ((@IN K _ j k) ∧ (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> j = i)))) (@Classical.epsilon K _ (fun i : K => (@IN K _ i k) ∧ (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))))) neut)) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero))))))))))))))) := by apply Eq.refl (@iterato A K _ _)

noncomputable def nproduct {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Nat) -> Nat := @iterate A Nat _ _ Nat.mul
theorem nproduct_def {A : Type _} [Nonempty A] : (@nproduct A _) = (@iterate A Nat _ _ Nat.mul) := by apply Eq.refl (@nproduct A _)

noncomputable def iproduct {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> ℤ) -> ℤ := @iterate A ℤ _ _ int_mul
theorem iproduct_def {A : Type _} [Nonempty A] : (@iproduct A _) = (@iterate A ℤ _ _ int_mul) := by apply Eq.refl (@iproduct A _)

noncomputable def product {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Real) -> Real := @iterate A Real _ _ real_mul
theorem product_def {A : Type _} [Nonempty A] : (@product A _) = (@iterate A Real _ _ real_mul) := by apply Eq.refl (@product A _)

noncomputable def isum {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> ℤ) -> ℤ := @iterate A ℤ _ _ int_add
theorem isum_def {A : Type _} [Nonempty A] : (@isum A _) = (@iterate A ℤ _ _ int_add) := by apply Eq.refl (@isum A _)

noncomputable def nsum {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Nat) -> Nat := @iterate A Nat _ _ Nat.add
theorem nsum_def {A : Type _} [Nonempty A] : (@nsum A _) = (@iterate A Nat _ _ Nat.add) := by apply Eq.refl (@nsum A _)

noncomputable def sum {A : Type _} [Nonempty A] : (A -> Prop) -> (A -> Real) -> Real := @iterate A Real _ _ real_add
theorem sum_def {A : Type _} [Nonempty A] : (@sum A _) = (@iterate A Real _ _ real_add) := by apply Eq.refl (@sum A _)

noncomputable def polynomial_function : (Real -> Real) -> Prop := fun _94200 : Real -> Real => ∃ m : Nat, ∃ c : Nat -> Real, ∀ x : Real, (_94200 x) = (@sum Nat _ (dotdot (NUMERAL Nat.zero) m) (fun i : Nat => real_mul (c i) (real_pow x i)))
theorem polynomial_function_def : polynomial_function = (fun _94200 : Real -> Real => ∃ m : Nat, ∃ c : Nat -> Real, ∀ x : Real, (_94200 x) = (@sum Nat _ (dotdot (NUMERAL Nat.zero) m) (fun i : Nat => real_mul (c i) (real_pow x i)))) := by apply Eq.refl polynomial_function

noncomputable def dimindex {A : Type _} [Nonempty A] : (A -> Prop) -> Nat := fun _94242 : A -> Prop => @COND Nat _ (@FINITE A _ (@UNIV A _)) (@CARD A _ (@UNIV A _)) (NUMERAL (BIT1 Nat.zero))
theorem dimindex_def {A : Type _} [Nonempty A] : (@dimindex A _) = (fun _94242 : A -> Prop => @COND Nat _ (@FINITE A _ (@UNIV A _)) (@CARD A _ (@UNIV A _)) (NUMERAL (BIT1 Nat.zero))) := by apply Eq.refl (@dimindex A _)
axiom finite_index : ∀ {A : Type _} [Nonempty A], Nat -> finite_image A
axiom dest_finite_image : ∀ {A : Type _} [Nonempty A], (finite_image A) -> Nat
axiom mk_cart : ∀ {A B : Type _} [Nonempty A] [Nonempty B], ((finite_image B) -> A) -> cart A B
axiom dest_cart : ∀ {A B : Type _} [Nonempty A] [Nonempty B], (cart A B) -> (finite_image B) -> A

noncomputable def dollar {A N' : Type _} [Nonempty A] [Nonempty N'] : (cart A N') -> Nat -> A := fun _94652 : cart A N' => fun _94653 : Nat => @dest_cart A N' _ _ _94652 (@finite_index N' _ _94653)
theorem dollar_def {A N' : Type _} [Nonempty A] [Nonempty N'] : (@dollar A N' _ _) = (fun _94652 : cart A N' => fun _94653 : Nat => @dest_cart A N' _ _ _94652 (@finite_index N' _ _94653)) := by apply Eq.refl (@dollar A N' _ _)

noncomputable def lambda {A B : Type _} [Nonempty A] [Nonempty B] : (Nat -> A) -> cart A B := fun _94688 : Nat -> A => @Classical.epsilon (cart A B) _ (fun f : cart A B => ∀ i : Nat, ((Nat.le (NUMERAL (BIT1 Nat.zero)) i) ∧ (Nat.le i (@dimindex B _ (@UNIV B _)))) -> (@dollar A B _ _ f i) = (_94688 i))
theorem lambda_def {A B : Type _} [Nonempty A] [Nonempty B] : (@lambda A B _ _) = (fun _94688 : Nat -> A => @Classical.epsilon (cart A B) _ (fun f : cart A B => ∀ i : Nat, ((Nat.le (NUMERAL (BIT1 Nat.zero)) i) ∧ (Nat.le i (@dimindex B _ (@UNIV B _)))) -> (@dollar A B _ _ f i) = (_94688 i))) := by apply Eq.refl (@lambda A B _ _)
axiom mk_finite_sum : ∀ {A B : Type _} [Nonempty A] [Nonempty B], Nat -> finite_sum A B
axiom dest_finite_sum : ∀ {A B : Type _} [Nonempty A] [Nonempty B], (finite_sum A B) -> Nat

noncomputable def pastecart {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A M) -> (cart A N') -> cart A (finite_sum M N') := fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') _ _ (fun i : Nat => @COND A _ (Nat.le i (@dimindex M _ (@UNIV M _))) (@dollar A M _ _ _94979 i) (@dollar A N' _ _ _94980 (Nat.sub i (@dimindex M _ (@UNIV M _)))))
theorem pastecart_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@pastecart A M N' _ _ _) = (fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') _ _ (fun i : Nat => @COND A _ (Nat.le i (@dimindex M _ (@UNIV M _))) (@dollar A M _ _ _94979 i) (@dollar A N' _ _ _94980 (Nat.sub i (@dimindex M _ (@UNIV M _)))))) := by apply Eq.refl (@pastecart A M N' _ _ _)

noncomputable def fstcart {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A (finite_sum M N')) -> cart A M := fun _94991 : cart A (finite_sum M N') => @lambda A M _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94991 i)
theorem fstcart_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@fstcart A M N' _ _ _) = (fun _94991 : cart A (finite_sum M N') => @lambda A M _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94991 i)) := by apply Eq.refl (@fstcart A M N' _ _ _)

noncomputable def sndcart {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A (finite_sum M N')) -> cart A N' := fun _94996 : cart A (finite_sum M N') => @lambda A N' _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94996 (Nat.add i (@dimindex M _ (@UNIV M _))))
theorem sndcart_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@sndcart A M N' _ _ _) = (fun _94996 : cart A (finite_sum M N') => @lambda A N' _ _ (fun i : Nat => @dollar A (finite_sum M N') _ _ _94996 (Nat.add i (@dimindex M _ (@UNIV M _))))) := by apply Eq.refl (@sndcart A M N' _ _ _)
axiom mk_finite_diff : ∀ {A B : Type _} [Nonempty A] [Nonempty B], Nat -> finite_diff A B
axiom dest_finite_diff : ∀ {A B : Type _} [Nonempty A] [Nonempty B], (finite_diff A B) -> Nat
axiom mk_finite_prod : ∀ {A B : Type _} [Nonempty A] [Nonempty B], Nat -> finite_prod A B
axiom dest_finite_prod : ∀ {A B : Type _} [Nonempty A] [Nonempty B], (finite_prod A B) -> Nat
axiom _mk_tybit0 : ∀ {A : Type _} [Nonempty A], (recspace (finite_sum A A)) -> tybit0 A
axiom _dest_tybit0 : ∀ {A : Type _} [Nonempty A], (tybit0 A) -> recspace (finite_sum A A)

noncomputable def _100406 {A : Type _} [Nonempty A] : (finite_sum A A) -> tybit0 A := fun a : finite_sum A A => @_mk_tybit0 A _ ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum A A) _)) a)
theorem _100406_def {A : Type _} [Nonempty A] : (@_100406 A _) = (fun a : finite_sum A A => @_mk_tybit0 A _ ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum A A) _)) a)) := by apply Eq.refl (@_100406 A _)

noncomputable def mktybit0 {A : Type _} [Nonempty A] : (finite_sum A A) -> tybit0 A := @_100406 A _
theorem mktybit0_def {A : Type _} [Nonempty A] : (@mktybit0 A _) = (@_100406 A _) := by apply Eq.refl (@mktybit0 A _)
axiom _mk_tybit1 : ∀ {A : Type _} [Nonempty A], (recspace (finite_sum (finite_sum A A) Unit)) -> tybit1 A
axiom _dest_tybit1 : ∀ {A : Type _} [Nonempty A], (tybit1 A) -> recspace (finite_sum (finite_sum A A) Unit)

noncomputable def _100425 {A : Type _} [Nonempty A] : (finite_sum (finite_sum A A) Unit) -> tybit1 A := fun a : finite_sum (finite_sum A A) Unit => @_mk_tybit1 A _ ((fun a' : finite_sum (finite_sum A A) Unit => @CONSTR (finite_sum (finite_sum A A) Unit) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum (finite_sum A A) Unit) _)) a)
theorem _100425_def {A : Type _} [Nonempty A] : (@_100425 A _) = (fun a : finite_sum (finite_sum A A) Unit => @_mk_tybit1 A _ ((fun a' : finite_sum (finite_sum A A) Unit => @CONSTR (finite_sum (finite_sum A A) Unit) _ (NUMERAL Nat.zero) a' (fun n : Nat => @BOTTOM (finite_sum (finite_sum A A) Unit) _)) a)) := by apply Eq.refl (@_100425 A _)

noncomputable def mktybit1 {A : Type _} [Nonempty A] : (finite_sum (finite_sum A A) Unit) -> tybit1 A := @_100425 A _
theorem mktybit1_def {A : Type _} [Nonempty A] : (@mktybit1 A _) = (@_100425 A _) := by apply Eq.refl (@mktybit1 A _)

noncomputable def vector {A N' : Type _} [Nonempty A] [Nonempty N'] : (List A) -> cart A N' := fun _102119 : List A => @lambda A N' _ _ (fun i : Nat => @EL A _ (Nat.sub i (NUMERAL (BIT1 Nat.zero))) _102119)
theorem vector_def {A N' : Type _} [Nonempty A] [Nonempty N'] : (@vector A N' _ _) = (fun _102119 : List A => @lambda A N' _ _ (fun i : Nat => @EL A _ (Nat.sub i (NUMERAL (BIT1 Nat.zero))) _102119)) := by apply Eq.refl (@vector A N' _ _)

noncomputable def PCROSS {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop := fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) _ (fun GEN_PVAR_363 : cart A (finite_sum M N') => ∃ x : cart A M, ∃ y : cart A N', @SETSPEC (cart A (finite_sum M N')) _ GEN_PVAR_363 ((@IN (cart A M) _ x _102146) ∧ (@IN (cart A N') _ y _102147)) (@pastecart A M N' _ _ _ x y))
theorem PCROSS_def {A M N' : Type _} [Nonempty A] [Nonempty M] [Nonempty N'] : (@PCROSS A M N' _ _ _) = (fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) _ (fun GEN_PVAR_363 : cart A (finite_sum M N') => ∃ x : cart A M, ∃ y : cart A N', @SETSPEC (cart A (finite_sum M N')) _ GEN_PVAR_363 ((@IN (cart A M) _ x _102146) ∧ (@IN (cart A N') _ y _102147)) (@pastecart A M N' _ _ _ x y))) := by apply Eq.refl (@PCROSS A M N' _ _ _)

noncomputable def CASEWISE {_138002 _138038 _138042 _138043 : Type _} [Nonempty _138002] [Nonempty _138038] [Nonempty _138042] [Nonempty _138043] : (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) _ (fun CASEWISE' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => ∀ _102751 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ f : _138043, ∀ x : _138042, (CASEWISE' _102751 (@NIL (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _) f x) = (@Classical.epsilon _138002 _ (fun y : _138002 => True))) ∧ (∀ h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), ∀ t : List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), ∀ f : _138043, ∀ x : _138042, (CASEWISE' _102751 (@CONS (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _ h t) f x) = (@COND _138002 _ (∃ y : _138038, (@prod_fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) = x) (@prod_snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h f (@Classical.epsilon _138038 _ (fun y : _138038 => (@prod_fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) = x))) (CASEWISE' _102751 t f x)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))))
theorem CASEWISE_def {_138002 _138038 _138042 _138043 : Type _} [Nonempty _138002] [Nonempty _138038] [Nonempty _138042] [Nonempty _138043] : (@CASEWISE _138002 _138038 _138042 _138043 _ _ _ _) = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) _ (fun CASEWISE' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> (List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => ∀ _102751 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ f : _138043, ∀ x : _138042, (CASEWISE' _102751 (@NIL (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _) f x) = (@Classical.epsilon _138002 _ (fun y : _138002 => True))) ∧ (∀ h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), ∀ t : List (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), ∀ f : _138043, ∀ x : _138042, (CASEWISE' _102751 (@CONS (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _ h t) f x) = (@COND _138002 _ (∃ y : _138038, (@prod_fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) = x) (@prod_snd (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h f (@Classical.epsilon _138038 _ (fun y : _138038 => (@prod_fst (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) = x))) (CASEWISE' _102751 t f x)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 Nat.zero)))))))))))))))) := by apply Eq.refl (@CASEWISE _138002 _138038 _138042 _138043 _ _ _ _)

noncomputable def admissible {_138333 _138336 _138340 _138341 _138346 : Type _} [Nonempty _138333] [Nonempty _138336] [Nonempty _138340] [Nonempty _138341] [Nonempty _138346] : (_138340 -> _138333 -> Prop) -> ((_138340 -> _138336) -> _138346 -> Prop) -> (_138346 -> _138333) -> ((_138340 -> _138336) -> _138346 -> _138341) -> Prop := fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => ∀ f : _138340 -> _138336, ∀ g : _138340 -> _138336, ∀ a : _138346, ((_103819 f a) ∧ ((_103819 g a) ∧ (∀ z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a)
theorem admissible_def {_138333 _138336 _138340 _138341 _138346 : Type _} [Nonempty _138333] [Nonempty _138336] [Nonempty _138340] [Nonempty _138341] [Nonempty _138346] : (@admissible _138333 _138336 _138340 _138341 _138346 _ _ _ _ _) = (fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => ∀ f : _138340 -> _138336, ∀ g : _138340 -> _138336, ∀ a : _138346, ((_103819 f a) ∧ ((_103819 g a) ∧ (∀ z : _138340, (_103818 z (_103820 a)) -> (f z) = (g z)))) -> (_103821 f a) = (_103821 g a)) := by apply Eq.refl (@admissible _138333 _138336 _138340 _138341 _138346 _ _ _ _ _)

noncomputable def tailadmissible {A B P : Type _} [Nonempty A] [Nonempty B] [Nonempty P] : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop := fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => ∃ P' : (A -> B) -> P -> Prop, ∃ G : (A -> B) -> P -> A, ∃ H : (A -> B) -> P -> B, (∀ f : A -> B, ∀ a : P, ∀ y : A, ((P' f a) ∧ (_103850 y (G f a))) -> _103850 y (_103852 a)) ∧ ((∀ f : A -> B, ∀ g : A -> B, ∀ a : P, (∀ z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) ∧ (((G f a) = (G g a)) ∧ ((H f a) = (H g a)))) ∧ (∀ f : A -> B, ∀ a : P, (_103851 f a) -> (_103853 f a) = (@COND B _ (P' f a) (f (G f a)) (H f a))))
theorem tailadmissible_def {A B P : Type _} [Nonempty A] [Nonempty B] [Nonempty P] : (@tailadmissible A B P _ _ _) = (fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => ∃ P' : (A -> B) -> P -> Prop, ∃ G : (A -> B) -> P -> A, ∃ H : (A -> B) -> P -> B, (∀ f : A -> B, ∀ a : P, ∀ y : A, ((P' f a) ∧ (_103850 y (G f a))) -> _103850 y (_103852 a)) ∧ ((∀ f : A -> B, ∀ g : A -> B, ∀ a : P, (∀ z : A, (_103850 z (_103852 a)) -> (f z) = (g z)) -> ((P' f a) = (P' g a)) ∧ (((G f a) = (G g a)) ∧ ((H f a) = (H g a)))) ∧ (∀ f : A -> B, ∀ a : P, (_103851 f a) -> (_103853 f a) = (@COND B _ (P' f a) (f (G f a)) (H f a))))) := by apply Eq.refl (@tailadmissible A B P _ _ _)

noncomputable def superadmissible {_138490 _138492 _138498 : Type _} [Nonempty _138490] [Nonempty _138492] [Nonempty _138498] : (_138490 -> _138490 -> Prop) -> ((_138490 -> _138492) -> _138498 -> Prop) -> (_138498 -> _138490) -> ((_138490 -> _138492) -> _138498 -> _138492) -> Prop := fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _ _ _ _ _ _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _ _ _ _103882 _103883 _103884 _103885
theorem superadmissible_def {_138490 _138492 _138498 : Type _} [Nonempty _138490] [Nonempty _138492] [Nonempty _138498] : (@superadmissible _138490 _138492 _138498 _ _ _) = (fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _ _ _ _ _ _103882 (fun f : _138490 -> _138492 => fun a : _138498 => True) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _ _ _ _103882 _103883 _103884 _103885) := by apply Eq.refl (@superadmissible _138490 _138492 _138498 _ _ _)
