import HolLightLean.up_to_real

namespace HolLightLean.hol_up_real_terms

set_option linter.style.missingEnd false
set_option linter.unusedVariables false
set_option linter.style.longLine false

open real

@[reducible]
noncomputable def _FALSITY_ : Prop := False
theorem _FALSITY__def : _FALSITY_ = False := by apply Eq.refl _FALSITY_
@[reducible]
noncomputable def o {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (B -> C) -> (A -> B) -> A -> C := fun f : B -> C => fun g : A -> B => fun x : A => f (g x)
theorem o_def {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (@o A B C _ _ _) = (fun f : B -> C => fun g : A -> B => fun x : A => f (g x)) := by apply Eq.refl (@o A B C _ _ _)
@[reducible]
noncomputable def I {A : Type*} [Nonempty A] : A -> A := fun x : A => x
theorem I_def {A : Type*} [Nonempty A] : (@I A _) = (fun x : A => x) := by apply Eq.refl (@I A _)
@[reducible]
noncomputable def hashek : Prop := True
theorem hashek_def : hashek = True := by apply Eq.refl hashek
@[reducible]
noncomputable def LET {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B) -> A -> B := fun f : A -> B => fun x : A => f x
theorem LET_def {A B : Type*} [Nonempty A] [Nonempty B] : (@LET A B _ _) = (fun f : A -> B => fun x : A => f x) := by apply Eq.refl (@LET A B _ _)
@[reducible]
noncomputable def LET_END {A : Type*} [Nonempty A] : A -> A := fun t : A => t
theorem LET_END_def {A : Type*} [Nonempty A] : (@LET_END A _) = (fun t : A => t) := by apply Eq.refl (@LET_END A _)
@[reducible]
noncomputable def GABS {A : Type*} [Nonempty A] : (A -> Prop) -> A := fun P : A -> Prop => @Classical.epsilon A _ P
theorem GABS_def {A : Type*} [Nonempty A] : (@GABS A _) = (fun P : A -> Prop => @Classical.epsilon A _ P) := by apply Eq.refl (@GABS A _)
@[reducible]
noncomputable def _SEQPATTERN {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop := fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) _ (∃ y : B, r x y) (r x) (s x)
theorem _SEQPATTERN_def {A B : Type*} [Nonempty A] [Nonempty B] : (@_SEQPATTERN A B _ _) = (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) _ (∃ y : B, r x y) (r x) (s x)) := by apply Eq.refl (@_SEQPATTERN A B _ _)
@[reducible]
noncomputable def _UNGUARDED_PATTERN : Prop -> Prop -> Prop := fun p : Prop => fun r : Prop => p ∧ r
theorem _UNGUARDED_PATTERN_def : _UNGUARDED_PATTERN = (fun p : Prop => fun r : Prop => p ∧ r) := by apply Eq.refl _UNGUARDED_PATTERN
@[reducible]
noncomputable def _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop := fun p : Prop => fun g : Prop => fun r : Prop => p ∧ (g ∧ r)
theorem _GUARDED_PATTERN_def : _GUARDED_PATTERN = (fun p : Prop => fun g : Prop => fun r : Prop => p ∧ (g ∧ r)) := by apply Eq.refl _GUARDED_PATTERN
@[reducible]
noncomputable def _MATCH {A B : Type*} [Nonempty A] [Nonempty B] : A -> (A -> B -> Prop) -> B := fun e : A => fun r : A -> B -> Prop => @COND B _ (@EXISTSUNIQUE B _ (r e)) (@Classical.epsilon B _ (r e)) (@Classical.epsilon B _ (fun z : B => False))
theorem _MATCH_def {A B : Type*} [Nonempty A] [Nonempty B] : (@_MATCH A B _ _) = (fun e : A => fun r : A -> B -> Prop => @COND B _ (@EXISTSUNIQUE B _ (r e)) (@Classical.epsilon B _ (r e)) (@Classical.epsilon B _ (fun z : B => False))) := by apply Eq.refl (@_MATCH A B _ _)
@[reducible]
noncomputable def _FUNCTION {A B : Type*} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> A -> B := fun r : A -> B -> Prop => fun x : A => @COND B _ (@EXISTSUNIQUE B _ (r x)) (@Classical.epsilon B _ (r x)) (@Classical.epsilon B _ (fun z : B => False))
theorem _FUNCTION_def {A B : Type*} [Nonempty A] [Nonempty B] : (@_FUNCTION A B _ _) = (fun r : A -> B -> Prop => fun x : A => @COND B _ (@EXISTSUNIQUE B _ (r x)) (@Classical.epsilon B _ (r x)) (@Classical.epsilon B _ (fun z : B => False))) := by apply Eq.refl (@_FUNCTION A B _ _)
@[reducible]
noncomputable def CURRY {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : ((prod A B) -> C) -> A -> B -> C := fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@prod_mk A B _ _ _1284 _1285)
theorem CURRY_def {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (@CURRY A B C _ _ _) = (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@prod_mk A B _ _ _1284 _1285)) := by apply Eq.refl (@CURRY A B C _ _ _)
@[reducible]
noncomputable def UNCURRY {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C) -> (prod A B) -> C := fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@prod_fst A B _ _ _1305) (@prod_snd A B _ _ _1305)
theorem UNCURRY_def {A B C : Type*} [Nonempty A] [Nonempty B] [Nonempty C] : (@UNCURRY A B C _ _ _) = (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@prod_fst A B _ _ _1305) (@prod_snd A B _ _ _1305)) := by apply Eq.refl (@UNCURRY A B C _ _ _)
@[reducible]
noncomputable def PASSOC {A B C D : Type*} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D := fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@prod_mk (prod A B) C _ _ (@prod_mk A B _ _ (@prod_fst A (prod B C) _ _ _1322) (@prod_fst B C _ _ (@prod_snd A (prod B C) _ _ _1322))) (@prod_snd B C _ _ (@prod_snd A (prod B C) _ _ _1322)))
theorem PASSOC_def {A B C D : Type*} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] : (@PASSOC A B C D _ _ _ _) = (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@prod_mk (prod A B) C _ _ (@prod_mk A B _ _ (@prod_fst A (prod B C) _ _ _1322) (@prod_fst B C _ _ (@prod_snd A (prod B C) _ _ _1322))) (@prod_snd B C _ _ (@prod_snd A (prod B C) _ _ _1322)))) := by apply Eq.refl (@PASSOC A B C D _ _ _ _)
@[reducible]
noncomputable def minimal : (Nat -> Prop) -> Nat := fun _6536 : Nat -> Prop => @Classical.epsilon Nat _ (fun n : Nat => (_6536 n) ∧ (∀ m : Nat, (Nat.lt m n) -> ¬ (_6536 m)))
theorem minimal_def : minimal = (fun _6536 : Nat -> Prop => @Classical.epsilon Nat _ (fun n : Nat => (_6536 n) ∧ (∀ m : Nat, (Nat.lt m n) -> ¬ (_6536 m)))) := by apply Eq.refl minimal
@[reducible]
noncomputable def MEASURE {A : Type*} [Nonempty A] : (A -> Nat) -> A -> A -> Prop := fun _8094 : A -> Nat => fun x : A => fun y : A => Nat.lt (_8094 x) (_8094 y)
theorem MEASURE_def {A : Type*} [Nonempty A] : (@MEASURE A _) = (fun _8094 : A -> Nat => fun x : A => fun y : A => Nat.lt (_8094 x) (_8094 y)) := by apply Eq.refl (@MEASURE A _)
axiom _mk_char : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> CHAR
axiom _dest_char : CHAR -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))
@[reducible]
noncomputable def _22943 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> CHAR := fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _ (NUMERAL Nat.zero) (@prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) _ _ a0' (@prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) _ _ a1' (@prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) _ _ a2' (@prod_mk Prop (prod Prop (prod Prop (prod Prop Prop))) _ _ a3' (@prod_mk Prop (prod Prop (prod Prop Prop)) _ _ a4' (@prod_mk Prop (prod Prop Prop) _ _ a5' (@prod_mk Prop Prop _ _ a6' a7'))))))) (fun n : Nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _)) a0 a1 a2 a3 a4 a5 a6 a7)
theorem _22943_def : _22943 = (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _ (NUMERAL Nat.zero) (@prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) _ _ a0' (@prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) _ _ a1' (@prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) _ _ a2' (@prod_mk Prop (prod Prop (prod Prop (prod Prop Prop))) _ _ a3' (@prod_mk Prop (prod Prop (prod Prop Prop)) _ _ a4' (@prod_mk Prop (prod Prop Prop) _ _ a5' (@prod_mk Prop Prop _ _ a6' a7'))))))) (fun n : Nat => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _)) a0 a1 a2 a3 a4 a5 a6 a7)) := by apply Eq.refl _22943
@[reducible]
noncomputable def ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> CHAR := _22943
theorem ASCII_def : ASCII = _22943 := by apply Eq.refl ASCII
@[reducible]
noncomputable def real_of_num : Nat -> real := fun m : Nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)
theorem real_of_num_def : real_of_num = (fun m : Nat => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u)) := by apply Eq.refl real_of_num
@[reducible]
noncomputable def real_neg : real -> real := fun x1 : real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) ∧ (dest_real x1 x1'))
theorem real_neg_def : real_neg = (fun x1 : real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, (treal_eq (treal_neg x1') u) ∧ (dest_real x1 x1'))) := by apply Eq.refl real_neg
@[reducible]
noncomputable def real_add : real -> real -> real := fun x1 : real => fun y1 : real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))
theorem real_add_def : real_add = (fun x1 : real => fun y1 : real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, (treal_eq (treal_add x1' y1') u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))) := by apply Eq.refl real_add
@[reducible]
noncomputable def real_mul : real -> real -> real := fun x1 : real => fun y1 : real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))
theorem real_mul_def : real_mul = (fun x1 : real => fun y1 : real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, (treal_eq (treal_mul x1' y1') u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))) := by apply Eq.refl real_mul
@[reducible]
noncomputable def real_le : real -> real -> Prop := fun x1 : real => fun y1 : real => @Classical.epsilon Prop _ (fun u : Prop => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, ((treal_le x1' y1') = u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))
theorem real_le_def : real_le = (fun x1 : real => fun y1 : real => @Classical.epsilon Prop _ (fun u : Prop => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, ((treal_le x1' y1') = u) ∧ ((dest_real x1 x1') ∧ (dest_real y1 y1')))) := by apply Eq.refl real_le
@[reducible]
noncomputable def real_inv : real -> real := fun x : real => mk_real (fun u : prod hreal hreal => ∃ x' : prod hreal hreal, (treal_eq (treal_inv x') u) ∧ (dest_real x x'))
theorem real_inv_def : real_inv = (fun x : real => mk_real (fun u : prod hreal hreal => ∃ x' : prod hreal hreal, (treal_eq (treal_inv x') u) ∧ (dest_real x x'))) := by apply Eq.refl real_inv
@[reducible]
noncomputable def real_sub : real -> real -> real := fun _24112 : real => fun _24113 : real => real_add _24112 (real_neg _24113)
theorem real_sub_def : real_sub = (fun _24112 : real => fun _24113 : real => real_add _24112 (real_neg _24113)) := by apply Eq.refl real_sub
@[reducible]
noncomputable def real_lt : real -> real -> Prop := fun _24124 : real => fun _24125 : real => ¬ (real_le _24125 _24124)
theorem real_lt_def : real_lt = (fun _24124 : real => fun _24125 : real => ¬ (real_le _24125 _24124)) := by apply Eq.refl real_lt
@[reducible]
noncomputable def real_ge : real -> real -> Prop := fun _24136 : real => fun _24137 : real => real_le _24137 _24136
theorem real_ge_def : real_ge = (fun _24136 : real => fun _24137 : real => real_le _24137 _24136) := by apply Eq.refl real_ge
@[reducible]
noncomputable def real_gt : real -> real -> Prop := fun _24148 : real => fun _24149 : real => real_lt _24149 _24148
theorem real_gt_def : real_gt = (fun _24148 : real => fun _24149 : real => real_lt _24149 _24148) := by apply Eq.refl real_gt
@[reducible]
noncomputable def real_abs : real -> real := fun _24160 : real => @COND real _ (real_le (real_of_num (NUMERAL Nat.zero)) _24160) _24160 (real_neg _24160)
theorem real_abs_def : real_abs = (fun _24160 : real => @COND real _ (real_le (real_of_num (NUMERAL Nat.zero)) _24160) _24160 (real_neg _24160)) := by apply Eq.refl real_abs
@[reducible]
noncomputable def real_pow : real -> Nat -> real := @Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> real -> Nat -> real) _ (fun real_pow' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> real -> Nat -> real => ∀ _24171 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ x : real, (real_pow' _24171 x (NUMERAL Nat.zero)) = (real_of_num (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : real, ∀ n : Nat, (real_pow' _24171 x (Nat.succ n)) = (real_mul x (real_pow' _24171 x n)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))))))))))
theorem real_pow_def : real_pow = (@Classical.epsilon ((prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> real -> Nat -> real) _ (fun real_pow' : (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))))) -> real -> Nat -> real => ∀ _24171 : prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))), (∀ x : real, (real_pow' _24171 x (NUMERAL Nat.zero)) = (real_of_num (NUMERAL (BIT1 Nat.zero)))) ∧ (∀ x : real, ∀ n : Nat, (real_pow' _24171 x (Nat.succ n)) = (real_mul x (real_pow' _24171 x n)))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat (prod Nat Nat)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat (prod Nat Nat))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat (prod Nat Nat)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 Nat.zero)))))))) (@prod_mk Nat (prod Nat Nat) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))) (@prod_mk Nat Nat _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 Nat.zero)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 Nat.zero)))))))))))))))) := by apply Eq.refl real_pow
@[reducible]
noncomputable def real_div : real -> real -> real := fun _24172 : real => fun _24173 : real => real_mul _24172 (real_inv _24173)
theorem real_div_def : real_div = (fun _24172 : real => fun _24173 : real => real_mul _24172 (real_inv _24173)) := by apply Eq.refl real_div
@[reducible]
noncomputable def real_max : real -> real -> real := fun _24184 : real => fun _24185 : real => @COND real _ (real_le _24184 _24185) _24185 _24184
theorem real_max_def : real_max = (fun _24184 : real => fun _24185 : real => @COND real _ (real_le _24184 _24185) _24185 _24184) := by apply Eq.refl real_max
@[reducible]
noncomputable def real_min : real -> real -> real := fun _24196 : real => fun _24197 : real => @COND real _ (real_le _24196 _24197) _24196 _24197
theorem real_min_def : real_min = (fun _24196 : real => fun _24197 : real => @COND real _ (real_le _24196 _24197) _24196 _24197) := by apply Eq.refl real_min
@[reducible]
noncomputable def real_sgn : real -> real := fun _26684 : real => @COND real _ (real_lt (real_of_num (NUMERAL Nat.zero)) _26684) (real_of_num (NUMERAL (BIT1 Nat.zero))) (@COND real _ (real_lt _26684 (real_of_num (NUMERAL Nat.zero))) (real_neg (real_of_num (NUMERAL (BIT1 Nat.zero)))) (real_of_num (NUMERAL Nat.zero)))
theorem real_sgn_def : real_sgn = (fun _26684 : real => @COND real _ (real_lt (real_of_num (NUMERAL Nat.zero)) _26684) (real_of_num (NUMERAL (BIT1 Nat.zero))) (@COND real _ (real_lt _26684 (real_of_num (NUMERAL Nat.zero))) (real_neg (real_of_num (NUMERAL (BIT1 Nat.zero)))) (real_of_num (NUMERAL Nat.zero)))) := by apply Eq.refl real_sgn
@[reducible]
noncomputable def SQRT : real -> real := fun _27235 : real => @Classical.epsilon real _ (fun y : real => ((real_sgn y) = (real_sgn _27235)) ∧ ((real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero)))) = (real_abs _27235)))
theorem SQRT_def : SQRT = (fun _27235 : real => @Classical.epsilon real _ (fun y : real => ((real_sgn y) = (real_sgn _27235)) ∧ ((real_pow y (NUMERAL (BIT0 (BIT1 Nat.zero)))) = (real_abs _27235)))) := by apply Eq.refl SQRT
