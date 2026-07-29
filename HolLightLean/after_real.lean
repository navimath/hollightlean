import HolLightLean.real_align
import HolLightLean.hol_up_real_opam
import HolLightLean.hol_up_real_terms
open HolLightLean.hol_up_real_opam
-- open HolLightLean.hol_up_real_terms

/- noncomputable def DECIMAL : Nat -> Nat -> Real := fun _27914 : Nat => fun _27915 : Nat => real_div (real_of_num _27914) (real_of_num _27915)
theorem DECIMAL_def : DECIMAL = (fun _27914 : Nat => fun _27915 : Nat => real_div (real_of_num _27914) (real_of_num _27915)) := by apply Eq.refl DECIMAL

noncomputable def integer : Real -> Prop := fun _28801 : Real => ∃ n : Nat, (real_abs _28801) = (real_of_num n)
theorem integer_def : integer = (fun _28801 : Real => ∃ n : Nat, (real_abs _28801) = (real_of_num n)) := by apply Eq.refl integer
 -/
