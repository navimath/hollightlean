import HolLightLean.hol_opam

set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.nameCheck false
                

attribute [local instance 10000] Classical.propDecidable

theorem hol_T_DEF : 
  True = Eq (α := Set Prop) (fun (p : Prop) ↦ p) fun (p : Prop) ↦ p := @HolLightLean.hol_opam.thm_T_DEF holTheoryInst

theorem hol_AND_DEF : 
  And = fun (p q : Prop) ↦
    Eq (α := Set (Prop → Prop → Prop)) (fun (f : Prop → Prop → Prop) ↦ f p q) fun (f : Prop → Prop → Prop) ↦ f True True := @HolLightLean.hol_opam.thm_AND_DEF holTheoryInst

theorem hol_IMP_DEF : 
  HOLTheory.imp = fun (p q : Prop) ↦ (p ∧ q) = p := @HolLightLean.hol_opam.thm_IMP_DEF holTheoryInst

theorem hol_FORALL_DEF : 
  ∀ {A : Type} [inst : Nonempty A], Eq (α := Set (Set A)) HOLTheory.FORALL fun (P : Set A) ↦ P = fun (x : A) ↦ True := @HolLightLean.hol_opam.thm_FORALL_DEF holTheoryInst

theorem hol_EXISTS_DEF : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set (Set A)) HOLTheory.EXISTS fun (P : Set A) ↦ ∀ (q : Prop), (∀ (x : A), P x → q) → q := @HolLightLean.hol_opam.thm_EXISTS_DEF holTheoryInst

theorem hol_OR_DEF : 
  Or = fun (p q : Prop) ↦ ∀ (r : Prop), (p → r) → (q → r) → r := @HolLightLean.hol_opam.thm_OR_DEF holTheoryInst

theorem hol_F_DEF : 
  False = ∀ (p : Prop), p := @HolLightLean.hol_opam.thm_F_DEF holTheoryInst

theorem hol_NOT_DEF : 
  Not = fun (p : Prop) ↦ p → False := @HolLightLean.hol_opam.thm_NOT_DEF holTheoryInst

theorem hol_EXISTS_UNIQUE_DEF : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set (Set A)) ExistsUnique fun (P : Set A) ↦ HOLTheory.EXISTS P ∧ ∀ (x y : A), P x ∧ P y → x = y := @HolLightLean.hol_opam.thm_EXISTS_UNIQUE_DEF holTheoryInst

theorem hol__FALSITY_ : 
  False = False := @HolLightLean.hol_opam.thm__FALSITY_ holTheoryInst

theorem hol_EQ_REFL : 
  ∀ {A : Type} [Nonempty A] (x : A), x = x := @HolLightLean.hol_opam.thm_EQ_REFL holTheoryInst

theorem hol_REFL_CLAUSE : 
  ∀ {A : Type} [Nonempty A] (x : A), (x = x) = True := @HolLightLean.hol_opam.thm_REFL_CLAUSE holTheoryInst

theorem hol_EQ_SYM : 
  ∀ {A : Type} [Nonempty A] (x y : A), x = y → y = x := @HolLightLean.hol_opam.thm_EQ_SYM holTheoryInst

theorem hol_EQ_SYM_EQ : 
  ∀ {A : Type} [Nonempty A] (x y : A), (x = y) = (y = x) := @HolLightLean.hol_opam.thm_EQ_SYM_EQ holTheoryInst

theorem hol_EQ_TRANS : 
  ∀ {A : Type} [Nonempty A] (x y z : A), x = y ∧ y = z → x = z := @HolLightLean.hol_opam.thm_EQ_TRANS holTheoryInst

theorem hol_BETA_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (y : A), (fun (x : A) ↦ f x) y = f y := @HolLightLean.hol_opam.thm_BETA_THM holTheoryInst

theorem hol_ABS_SIMP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t1 : A) (t2 : B), (fun (x : B) ↦ t1) t2 = t1 := @HolLightLean.hol_opam.thm_ABS_SIMP holTheoryInst

theorem hol_CONJ_ASSOC : 
  ∀ (t1 t2 t3 : Prop), (t1 ∧ t2 ∧ t3) = ((t1 ∧ t2) ∧ t3) := @HolLightLean.hol_opam.thm_CONJ_ASSOC holTheoryInst

theorem hol_CONJ_SYM : 
  ∀ (t1 t2 : Prop), (t1 ∧ t2) = (t2 ∧ t1) := @HolLightLean.hol_opam.thm_CONJ_SYM holTheoryInst

theorem hol_CONJ_ACI : 
  ∀ (r p q : Prop),
    (p ∧ q) = (q ∧ p) ∧ ((p ∧ q) ∧ r) = (p ∧ q ∧ r) ∧ (p ∧ q ∧ r) = (q ∧ p ∧ r) ∧ (p ∧ p) = p ∧ (p ∧ p ∧ q) = (p ∧ q) := @HolLightLean.hol_opam.thm_CONJ_ACI holTheoryInst

theorem hol_DISJ_ASSOC : 
  ∀ (t1 t2 t3 : Prop), (t1 ∨ t2 ∨ t3) = ((t1 ∨ t2) ∨ t3) := @HolLightLean.hol_opam.thm_DISJ_ASSOC holTheoryInst

theorem hol_DISJ_SYM : 
  ∀ (t1 t2 : Prop), (t1 ∨ t2) = (t2 ∨ t1) := @HolLightLean.hol_opam.thm_DISJ_SYM holTheoryInst

theorem hol_DISJ_ACI : 
  ∀ (r p q : Prop),
    (p ∨ q) = (q ∨ p) ∧ ((p ∨ q) ∨ r) = (p ∨ q ∨ r) ∧ (p ∨ q ∨ r) = (q ∨ p ∨ r) ∧ (p ∨ p) = p ∧ (p ∨ p ∨ q) = (p ∨ q) := @HolLightLean.hol_opam.thm_DISJ_ACI holTheoryInst

theorem hol_IMP_CONJ : 
  ∀ (p q r : Prop), Eq (α := Prop) (p ∧ q → r) (p → q → r) := @HolLightLean.hol_opam.thm_IMP_CONJ holTheoryInst

theorem hol_IMP_CONJ_ALT : 
  ∀ (q p r : Prop), Eq (α := Prop) (p ∧ q → r) (q → p → r) := @HolLightLean.hol_opam.thm_IMP_CONJ_ALT holTheoryInst

theorem hol_LEFT_OR_DISTRIB : 
  ∀ (p q r : Prop), (p ∧ (q ∨ r)) = (p ∧ q ∨ p ∧ r) := @HolLightLean.hol_opam.thm_LEFT_OR_DISTRIB holTheoryInst

theorem hol_RIGHT_OR_DISTRIB : 
  ∀ (p q r : Prop), ((p ∨ q) ∧ r) = (p ∧ r ∨ q ∧ r) := @HolLightLean.hol_opam.thm_RIGHT_OR_DISTRIB holTheoryInst

theorem hol_FORALL_SIMP : 
  ∀ {A : Type} [Nonempty A] (t : Prop), (∀ (x : A), t) = t := @HolLightLean.hol_opam.thm_FORALL_SIMP holTheoryInst

theorem hol_EXISTS_SIMP : 
  ∀ {A : Type} [Nonempty A] (t : Prop), (∃ (x : A), t) = t := @HolLightLean.hol_opam.thm_EXISTS_SIMP holTheoryInst

theorem hol_EQ_CLAUSES : 
  ∀ (t : Prop), (True = t) = t ∧ (t = True) = t ∧ (False = t) = ¬t ∧ (t = False) = ¬t := @HolLightLean.hol_opam.thm_EQ_CLAUSES holTheoryInst

theorem hol_NOT_CLAUSES_WEAK : 
  (¬True) = False ∧ (¬False) = True := @HolLightLean.hol_opam.thm_NOT_CLAUSES_WEAK holTheoryInst

theorem hol_AND_CLAUSES : 
  ∀ (t : Prop), (True ∧ t) = t ∧ (t ∧ True) = t ∧ (False ∧ t) = False ∧ (t ∧ False) = False ∧ (t ∧ t) = t := @HolLightLean.hol_opam.thm_AND_CLAUSES holTheoryInst

theorem hol_OR_CLAUSES : 
  ∀ (t : Prop), (True ∨ t) = True ∧ (t ∨ True) = True ∧ (False ∨ t) = t ∧ (t ∨ False) = t ∧ (t ∨ t) = t := @HolLightLean.hol_opam.thm_OR_CLAUSES holTheoryInst

theorem hol_IMP_CLAUSES : 
  ∀ (t : Prop), (True → t) = t ∧ (t → True) = True ∧ (False → t) = True ∧ (t → t) = True ∧ (t → False) = ¬t := @HolLightLean.hol_opam.thm_IMP_CLAUSES holTheoryInst

theorem hol_EXISTS_UNIQUE_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (∃! x : A, P x) = ((∃ (x : A), P x) ∧ ∀ (x x' : A), P x ∧ P x' → x = x') := @HolLightLean.hol_opam.thm_EXISTS_UNIQUE_THM holTheoryInst

theorem hol_EXISTS_REFL : 
  ∀ {A : Type} [Nonempty A] (a : A), ∃ (x : A), x = a := @HolLightLean.hol_opam.thm_EXISTS_REFL holTheoryInst

theorem hol_EXISTS_UNIQUE_REFL : 
  ∀ {A : Type} [Nonempty A] (a : A), ∃! x : A, x = a := @HolLightLean.hol_opam.thm_EXISTS_UNIQUE_REFL holTheoryInst

theorem hol_UNWIND_THM1 : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (a : A), (∃ (x : A), a = x ∧ P x) = P a := @HolLightLean.hol_opam.thm_UNWIND_THM1 holTheoryInst

theorem hol_UNWIND_THM2 : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (a : A), (∃ (x : A), x = a ∧ P x) = P a := @HolLightLean.hol_opam.thm_UNWIND_THM2 holTheoryInst

theorem hol_FORALL_UNWIND_THM2 : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (a : A), (∀ (x : A), x = a → P x) = P a := @HolLightLean.hol_opam.thm_FORALL_UNWIND_THM2 holTheoryInst

theorem hol_FORALL_UNWIND_THM1 : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (a : A), (∀ (x : A), a = x → P x) = P a := @HolLightLean.hol_opam.thm_FORALL_UNWIND_THM1 holTheoryInst

theorem hol_SWAP_FORALL_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop),
    Eq (α := Prop) (∀ (x : A) (y : B), P x y) (∀ (y : B) (x : A), P x y) := @HolLightLean.hol_opam.thm_SWAP_FORALL_THM holTheoryInst

theorem hol_SWAP_EXISTS_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop), (∃ (x : A) (y : B), P x y) = ∃ (y : B) (x : A), P x y := @HolLightLean.hol_opam.thm_SWAP_EXISTS_THM holTheoryInst

theorem hol_FORALL_AND_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Set A), (∀ (x : A), P x ∧ Q x) = ((∀ (x : A), P x) ∧ ∀ (x : A), Q x) := @HolLightLean.hol_opam.thm_FORALL_AND_THM holTheoryInst

theorem hol_AND_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Set A), ((∀ (x : A), P x) ∧ ∀ (x : A), Q x) = ∀ (x : A), P x ∧ Q x := @HolLightLean.hol_opam.thm_AND_FORALL_THM holTheoryInst

theorem hol_LEFT_AND_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), ((∀ (x : A), P x) ∧ Q) = ∀ (x : A), P x ∧ Q := @HolLightLean.hol_opam.thm_LEFT_AND_FORALL_THM holTheoryInst

theorem hol_RIGHT_AND_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (P ∧ ∀ (x : A), Q x) = ∀ (x : A), P ∧ Q x := @HolLightLean.hol_opam.thm_RIGHT_AND_FORALL_THM holTheoryInst

theorem hol_EXISTS_OR_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Set A), (∃ (x : A), P x ∨ Q x) = ((∃ (x : A), P x) ∨ ∃ (x : A), Q x) := @HolLightLean.hol_opam.thm_EXISTS_OR_THM holTheoryInst

theorem hol_OR_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Set A), ((∃ (x : A), P x) ∨ ∃ (x : A), Q x) = ∃ (x : A), P x ∨ Q x := @HolLightLean.hol_opam.thm_OR_EXISTS_THM holTheoryInst

theorem hol_LEFT_OR_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), ((∃ (x : A), P x) ∨ Q) = ∃ (x : A), P x ∨ Q := @HolLightLean.hol_opam.thm_LEFT_OR_EXISTS_THM holTheoryInst

theorem hol_RIGHT_OR_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (P ∨ ∃ (x : A), Q x) = ∃ (x : A), P ∨ Q x := @HolLightLean.hol_opam.thm_RIGHT_OR_EXISTS_THM holTheoryInst

theorem hol_LEFT_EXISTS_AND_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), (∃ (x : A), P x ∧ Q) = ((∃ (x : A), P x) ∧ Q) := @HolLightLean.hol_opam.thm_LEFT_EXISTS_AND_THM holTheoryInst

theorem hol_RIGHT_EXISTS_AND_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (∃ (x : A), P ∧ Q x) = (P ∧ ∃ (x : A), Q x) := @HolLightLean.hol_opam.thm_RIGHT_EXISTS_AND_THM holTheoryInst

theorem hol_TRIV_EXISTS_AND_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Prop), (∃ (x : A), P ∧ Q) = ((∃ (x : A), P) ∧ ∃ (x : A), Q) := @HolLightLean.hol_opam.thm_TRIV_EXISTS_AND_THM holTheoryInst

theorem hol_LEFT_AND_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), ((∃ (x : A), P x) ∧ Q) = ∃ (x : A), P x ∧ Q := @HolLightLean.hol_opam.thm_LEFT_AND_EXISTS_THM holTheoryInst

theorem hol_RIGHT_AND_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (P ∧ ∃ (x : A), Q x) = ∃ (x : A), P ∧ Q x := @HolLightLean.hol_opam.thm_RIGHT_AND_EXISTS_THM holTheoryInst

theorem hol_TRIV_AND_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Prop), ((∃ (x : A), P) ∧ ∃ (x : A), Q) = ∃ (x : A), P ∧ Q := @HolLightLean.hol_opam.thm_TRIV_AND_EXISTS_THM holTheoryInst

theorem hol_TRIV_FORALL_OR_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Prop), (∀ (x : A), P ∨ Q) = ((∀ (x : A), P) ∨ ∀ (x : A), Q) := @HolLightLean.hol_opam.thm_TRIV_FORALL_OR_THM holTheoryInst

theorem hol_TRIV_OR_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Prop), ((∀ (x : A), P) ∨ ∀ (x : A), Q) = ∀ (x : A), P ∨ Q := @HolLightLean.hol_opam.thm_TRIV_OR_FORALL_THM holTheoryInst

theorem hol_RIGHT_IMP_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), Eq (α := Prop) (P → ∀ (x : A), Q x) (∀ (x : A), P → Q x) := @HolLightLean.hol_opam.thm_RIGHT_IMP_FORALL_THM holTheoryInst

theorem hol_RIGHT_FORALL_IMP_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), Eq (α := Prop) (∀ (x : A), P → Q x) (P → ∀ (x : A), Q x) := @HolLightLean.hol_opam.thm_RIGHT_FORALL_IMP_THM holTheoryInst

theorem hol_LEFT_IMP_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), Eq (α := Prop) ((∃ (x : A), P x) → Q) (∀ (x : A), P x → Q) := @HolLightLean.hol_opam.thm_LEFT_IMP_EXISTS_THM holTheoryInst

theorem hol_LEFT_FORALL_IMP_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), Eq (α := Prop) (∀ (x : A), P x → Q) ((∃ (x : A), P x) → Q) := @HolLightLean.hol_opam.thm_LEFT_FORALL_IMP_THM holTheoryInst

theorem hol_TRIV_FORALL_IMP_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Prop), Eq (α := Prop) (∀ (x : A), P → Q) ((∃ (x : A), P) → ∀ (x : A), Q) := @HolLightLean.hol_opam.thm_TRIV_FORALL_IMP_THM holTheoryInst

theorem hol_TRIV_EXISTS_IMP_THM : 
  ∀ {A : Type} [Nonempty A] (P Q : Prop), (∃ (x : A), P → Q) = ((∀ (x : A), P) → ∃ (x : A), Q) := @HolLightLean.hol_opam.thm_TRIV_EXISTS_IMP_THM holTheoryInst

theorem hol_MONO_FORALL : 
  ∀ {A : Type} [Nonempty A] (P Q : Set A), (∀ (x : A), P x → Q x) → (∀ (x : A), P x) → ∀ (x : A), Q x := @HolLightLean.hol_opam.thm_MONO_FORALL holTheoryInst

theorem hol_MONO_EXISTS : 
  ∀ {A : Type} [Nonempty A] (P Q : Set A), (∀ (x : A), P x → Q x) → (∃ (x : A), P x) → ∃ (x : A), Q x := @HolLightLean.hol_opam.thm_MONO_EXISTS holTheoryInst

theorem hol_WLOG_RELATION : 
  ∀ {A : Type} [Nonempty A] (R' P : A → A → Prop),
    ((∀ (x y : A), P x y → P y x) ∧ (∀ (x y : A), R' x y ∨ R' y x) ∧ ∀ (x y : A), R' x y → P x y) → ∀ (x y : A), P x y := @HolLightLean.hol_opam.thm_WLOG_RELATION holTheoryInst

theorem hol_EXISTS_UNIQUE_ALT : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (∃! x : A, P x) = ∃ (x : A), ∀ (y : A), P y = (x = y) := @HolLightLean.hol_opam.thm_EXISTS_UNIQUE_ALT holTheoryInst

theorem hol_EXISTS_UNIQUE : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (∃! x : A, P x) = ∃ (x : A), P x ∧ ∀ (y : A), P y → y = x := @HolLightLean.hol_opam.thm_EXISTS_UNIQUE holTheoryInst

theorem hol_ETA_AX : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : A → B), (fun (x : A) ↦ t x) = t := @HolLightLean.hol_opam.thm_ETA_AX holTheoryInst

theorem hol_EQ_EXT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f g : A → B), (∀ (x : A), f x = g x) → f = g := @HolLightLean.hol_opam.thm_EQ_EXT holTheoryInst

theorem hol_FUN_EQ_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f g : A → B), (f = g) = ∀ (x : A), f x = g x := @HolLightLean.hol_opam.thm_FUN_EQ_THM holTheoryInst

theorem hol_SELECT_AX : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (x : A), P x → P (Classical.epsilon P) := @HolLightLean.hol_opam.thm_SELECT_AX holTheoryInst

theorem hol_EXISTS_THM : 
  ∀ {A : Type} [inst : Nonempty A], Eq (α := Set (Set A)) HOLTheory.EXISTS fun (P : Set A) ↦ P (Classical.epsilon P) := @HolLightLean.hol_opam.thm_EXISTS_THM holTheoryInst

theorem hol_SELECT_REFL : 
  ∀ {A : Type} [inst : Nonempty A] (x : A), (Classical.epsilon fun (y : A) ↦ y = x) = x := @HolLightLean.hol_opam.thm_SELECT_REFL holTheoryInst

theorem hol_SELECT_UNIQUE : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (x : A), (∀ (y : A), P y = (y = x)) → Classical.epsilon P = x := @HolLightLean.hol_opam.thm_SELECT_UNIQUE holTheoryInst

theorem hol_EXCLUDED_MIDDLE : 
  ∀ (t : Prop), t ∨ ¬t := @HolLightLean.hol_opam.thm_EXCLUDED_MIDDLE holTheoryInst

theorem hol_BOOL_CASES_AX : 
  ∀ (t : Prop), t = True ∨ t = False := @HolLightLean.hol_opam.thm_BOOL_CASES_AX holTheoryInst

theorem hol_DE_MORGAN_THM : 
  ∀ (t1 t2 : Prop), (¬(t1 ∧ t2)) = (¬t1 ∨ ¬t2) ∧ (¬(t1 ∨ t2)) = (¬t1 ∧ ¬t2) := @HolLightLean.hol_opam.thm_DE_MORGAN_THM holTheoryInst

theorem hol_NOT_CLAUSES : 
  (∀ (t : Prop), (¬¬t) = t) ∧ (¬True) = False ∧ (¬False) = True := @HolLightLean.hol_opam.thm_NOT_CLAUSES holTheoryInst

theorem hol_NOT_IMP : 
  ∀ (t1 t2 : Prop), (¬(t1 → t2)) = (t1 ∧ ¬t2) := @HolLightLean.hol_opam.thm_NOT_IMP holTheoryInst

theorem hol_CONTRAPOS_THM : 
  ∀ (t1 t2 : Prop), Eq (α := Prop) (¬t1 → ¬t2) (t2 → t1) := @HolLightLean.hol_opam.thm_CONTRAPOS_THM holTheoryInst

theorem hol_NOT_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (¬∃ (x : A), P x) = ∀ (x : A), ¬P x := @HolLightLean.hol_opam.thm_NOT_EXISTS_THM holTheoryInst

theorem hol_EXISTS_NOT_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (∃ (x : A), ¬P x) = ¬∀ (x : A), P x := @HolLightLean.hol_opam.thm_EXISTS_NOT_THM holTheoryInst

theorem hol_NOT_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (¬∀ (x : A), P x) = ∃ (x : A), ¬P x := @HolLightLean.hol_opam.thm_NOT_FORALL_THM holTheoryInst

theorem hol_FORALL_NOT_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A), (∀ (x : A), ¬P x) = ¬∃ (x : A), P x := @HolLightLean.hol_opam.thm_FORALL_NOT_THM holTheoryInst

theorem hol_FORALL_BOOL_THM : 
  ∀ (P : Set Prop), (∀ (b : Prop), P b) = (P True ∧ P False) := @HolLightLean.hol_opam.thm_FORALL_BOOL_THM holTheoryInst

theorem hol_EXISTS_BOOL_THM : 
  ∀ (P : Set Prop), (∃ (b : Prop), P b) = (P True ∨ P False) := @HolLightLean.hol_opam.thm_EXISTS_BOOL_THM holTheoryInst

theorem hol_LEFT_FORALL_OR_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), (∀ (x : A), P x ∨ Q) = ((∀ (x : A), P x) ∨ Q) := @HolLightLean.hol_opam.thm_LEFT_FORALL_OR_THM holTheoryInst

theorem hol_RIGHT_FORALL_OR_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (∀ (x : A), P ∨ Q x) = (P ∨ ∀ (x : A), Q x) := @HolLightLean.hol_opam.thm_RIGHT_FORALL_OR_THM holTheoryInst

theorem hol_LEFT_OR_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), ((∀ (x : A), P x) ∨ Q) = ∀ (x : A), P x ∨ Q := @HolLightLean.hol_opam.thm_LEFT_OR_FORALL_THM holTheoryInst

theorem hol_RIGHT_OR_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (P ∨ ∀ (x : A), Q x) = ∀ (x : A), P ∨ Q x := @HolLightLean.hol_opam.thm_RIGHT_OR_FORALL_THM holTheoryInst

theorem hol_LEFT_IMP_FORALL_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), ((∀ (x : A), P x) → Q) = ∃ (x : A), P x → Q := @HolLightLean.hol_opam.thm_LEFT_IMP_FORALL_THM holTheoryInst

theorem hol_LEFT_EXISTS_IMP_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (Q : Prop), (∃ (x : A), P x → Q) = ((∀ (x : A), P x) → Q) := @HolLightLean.hol_opam.thm_LEFT_EXISTS_IMP_THM holTheoryInst

theorem hol_RIGHT_IMP_EXISTS_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (P → ∃ (x : A), Q x) = ∃ (x : A), P → Q x := @HolLightLean.hol_opam.thm_RIGHT_IMP_EXISTS_THM holTheoryInst

theorem hol_RIGHT_EXISTS_IMP_THM : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (Q : Set A), (∃ (x : A), P → Q x) = (P → ∃ (x : A), Q x) := @HolLightLean.hol_opam.thm_RIGHT_EXISTS_IMP_THM holTheoryInst

theorem hol_COND_DEF : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Prop → A → A → A) (fun (P : Prop) (x y : A) ↦ if P then x else y) fun (t : Prop) (t1 t2 : A) ↦
      Classical.epsilon fun (x : A) ↦ (t = True → x = t1) ∧ (t = False → x = t2) := @HolLightLean.hol_opam.thm_COND_DEF holTheoryInst

theorem hol_COND_CLAUSES : 
  ∀ {A : Type} [Nonempty A] (t1 t2 : A), (if True then t1 else t2) = t1 ∧ (if False then t1 else t2) = t2 := @HolLightLean.hol_opam.thm_COND_CLAUSES holTheoryInst

theorem hol_COND_EXPAND : 
  ∀ (b t1 t2 : Prop), (if b then t1 else t2) = ((¬b ∨ t1) ∧ (b ∨ t2)) := @HolLightLean.hol_opam.thm_COND_EXPAND holTheoryInst

theorem hol_COND_ID : 
  ∀ {A : Type} [Nonempty A] (b : Prop) (t : A), (if b then t else t) = t := @HolLightLean.hol_opam.thm_COND_ID holTheoryInst

theorem hol_COND_RAND : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (b : Prop) (f : A → B) (x y : A),
    f (if b then x else y) = if b then f x else f y := @HolLightLean.hol_opam.thm_COND_RAND holTheoryInst

theorem hol_COND_RATOR : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (b : Prop) (f g : A → B) (x : A),
    (if b then f else g) x = if b then f x else g x := @HolLightLean.hol_opam.thm_COND_RATOR holTheoryInst

theorem hol_COND_ABS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (b : Prop) (f g : A → B),
    (fun (x : A) ↦ if b then f x else g x) = if b then f else g := @HolLightLean.hol_opam.thm_COND_ABS holTheoryInst

theorem hol_COND_SWAP : 
  ∀ {A : Type} [Nonempty A] (p : Prop) (x y : A), (if ¬p then x else y) = if p then y else x := @HolLightLean.hol_opam.thm_COND_SWAP holTheoryInst

theorem hol_MONO_COND : 
  ∀ (A C b B D : Prop), (A → B) ∧ (C → D) → (if b then A else C) → if b then B else D := @HolLightLean.hol_opam.thm_MONO_COND holTheoryInst

theorem hol_COND_ELIM_THM : 
  ∀ {A : Type} [Nonempty A] (x : A) (c : Prop) (P : Set A) (y : A), P (if c then x else y) = ((c → P x) ∧ (¬c → P y)) := @HolLightLean.hol_opam.thm_COND_ELIM_THM holTheoryInst

theorem hol_SKOLEM_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop),
    (∀ (x : A), ∃ (y : B), P x y) = ∃ (y : A → B), ∀ (x : A), P x (y x) := @HolLightLean.hol_opam.thm_SKOLEM_THM holTheoryInst

theorem hol_SKOLEM_THM_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set A) (R' : A → B → Prop),
    (∀ (x : A), P x → ∃ (y : B), R' x y) = ∃ (f : A → B), ∀ (x : A), P x → R' x (f x) := @HolLightLean.hol_opam.thm_SKOLEM_THM_GEN holTheoryInst

theorem hol_UNIQUE_SKOLEM_ALT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop),
    (∀ (x : A), ∃! y : B, P x y) = ∃ (f : A → B), ∀ (x : A) (y : B), P x y = (f x = y) := @HolLightLean.hol_opam.thm_UNIQUE_SKOLEM_ALT holTheoryInst

theorem hol_UNIQUE_SKOLEM_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop),
    (∀ (x : A), ∃! y : B, P x y) = ∃! f : A → B, ∀ (x : A), P x (f x) := @HolLightLean.hol_opam.thm_UNIQUE_SKOLEM_THM holTheoryInst

theorem hol_bool_INDUCT : 
  ∀ (P : Set Prop), P False ∧ P True → ∀ (x : Prop), P x := @HolLightLean.hol_opam.thm_bool_INDUCT holTheoryInst

theorem hol_bool_RECURSION : 
  ∀ {A : Type} [Nonempty A] (a b : A), ∃ (f : Prop → A), f False = a ∧ f True = b := @HolLightLean.hol_opam.thm_bool_RECURSION holTheoryInst

theorem hol_o_DEF : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : B → C) (g : A → B), f ∘ g = fun (x : A) ↦ f (g x) := @HolLightLean.hol_opam.thm_o_DEF holTheoryInst

theorem hol_I_DEF : 
  ∀ {A : Type} [Nonempty A], Eq (α := A → A) id fun (x : A) ↦ x := @HolLightLean.hol_opam.thm_I_DEF holTheoryInst

theorem hol_o_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : B → C) (g : A → B) (x : A), (f ∘ g) x = f (g x) := @HolLightLean.hol_opam.thm_o_THM holTheoryInst

theorem hol_o_ASSOC : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (f : C → D) (g : B → C) (h : A → B),
    f ∘ g ∘ h = (f ∘ g) ∘ h := @HolLightLean.hol_opam.thm_o_ASSOC holTheoryInst

theorem hol_I_THM : 
  ∀ {A : Type} [Nonempty A] (x : A), id x = x := @HolLightLean.hol_opam.thm_I_THM holTheoryInst

theorem hol_I_O_ID : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B), id ∘ f = f ∧ f ∘ id = f := @HolLightLean.hol_opam.thm_I_O_ID holTheoryInst

theorem hol_EXISTS_ONE_REP : 
  ∃ (b : Prop), b := @HolLightLean.hol_opam.thm_EXISTS_ONE_REP holTheoryInst

theorem hol_one_DEF : 
  () = Classical.epsilon fun (x : Unit) ↦ True := @HolLightLean.hol_opam.thm_one_DEF holTheoryInst

theorem hol_one : 
  ∀ (v : Unit), v = () := @HolLightLean.hol_opam.thm_one holTheoryInst

theorem hol_one_axiom : 
  ∀ {A : Type} [Nonempty A] (f g : A → Unit), f = g := @HolLightLean.hol_opam.thm_one_axiom holTheoryInst

theorem hol_one_INDUCT : 
  ∀ (P : Set Unit), P () → ∀ (x : Unit), P x := @HolLightLean.hol_opam.thm_one_INDUCT holTheoryInst

theorem hol_one_RECURSION : 
  ∀ {A : Type} [Nonempty A] (e : A), ∃ (fn : Unit → A), fn () = e := @HolLightLean.hol_opam.thm_one_RECURSION holTheoryInst

theorem hol_one_Axiom : 
  ∀ {A : Type} [Nonempty A] (e : A), ∃! fn : Unit → A, fn () = e := @HolLightLean.hol_opam.thm_one_Axiom holTheoryInst

theorem hol_FORALL_ONE_THM : 
  ∀ (P : Set Unit), (∀ (x : Unit), P x) = P () := @HolLightLean.hol_opam.thm_FORALL_ONE_THM holTheoryInst

theorem hol_EXISTS_ONE_THM : 
  ∀ (P : Set Unit), (∃ (x : Unit), P x) = P () := @HolLightLean.hol_opam.thm_EXISTS_ONE_THM holTheoryInst

theorem hol_ETA_ONE : 
  ∀ {A : Type} [Nonempty A] (f : Unit → A), (fun (x : Unit) ↦ f ()) = f := @HolLightLean.hol_opam.thm_ETA_ONE holTheoryInst

theorem hol_LET_DEF : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (x : A), f x = f x := @HolLightLean.hol_opam.thm_LET_DEF holTheoryInst

theorem hol_LET_END_DEF : 
  ∀ {A : Type} [Nonempty A] (t : A), id t = t := @HolLightLean.hol_opam.thm_LET_END_DEF holTheoryInst

theorem hol_GABS_DEF : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A), Classical.epsilon P = Classical.epsilon P := @HolLightLean.hol_opam.thm_GABS_DEF holTheoryInst

theorem hol_GEQ_DEF : 
  ∀ {A : Type} [Nonempty A] (a b : A), (a = b) = (a = b) := @HolLightLean.hol_opam.thm_GEQ_DEF holTheoryInst

theorem hol__SEQPATTERN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Eq (α := (A → B → Prop) → (A → B → Prop) → A → B → Prop) _SEQPATTERN fun (r s : A → B → Prop) (x : A) ↦
      if ∃ (y : B), r x y then r x else s x := @HolLightLean.hol_opam.thm__SEQPATTERN holTheoryInst

theorem hol__UNGUARDED_PATTERN : 
  Eq (α := Prop → Prop → Prop) (fun (p r : Prop) ↦ p ∧ r) fun (p r : Prop) ↦ p ∧ r := @HolLightLean.hol_opam.thm__UNGUARDED_PATTERN holTheoryInst

theorem hol__GUARDED_PATTERN : 
  Eq (α := Prop → Prop → Prop → Prop) (fun (p g r : Prop) ↦ p ∧ g ∧ r) fun (p g r : Prop) ↦ p ∧ g ∧ r := @HolLightLean.hol_opam.thm__GUARDED_PATTERN holTheoryInst

theorem hol__MATCH : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Eq (α := A → (A → B → Prop) → B) _MATCH fun (e : A) (r : A → B → Prop) ↦
      if ExistsUnique (r e) then Classical.epsilon (r e) else Classical.epsilon fun (z : B) ↦ False := @HolLightLean.hol_opam.thm__MATCH holTheoryInst

theorem hol__FUNCTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Eq (α := (A → B → Prop) → A → B) _FUNCTION fun (r : A → B → Prop) (x : A) ↦
      if ExistsUnique (r x) then Classical.epsilon (r x) else Classical.epsilon fun (z : B) ↦ False := @HolLightLean.hol_opam.thm__FUNCTION holTheoryInst

theorem hol_mk_pair_def : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (x : A) (y : B),
    mk_pair x y = fun (a : A) (b : B) ↦ a = x ∧ b = y := @HolLightLean.hol_opam.thm_mk_pair_def holTheoryInst

theorem hol_PAIR_EXISTS_THM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B], ∃ (x : A → B → Prop) (a : A) (b : B), x = mk_pair a b := @HolLightLean.hol_opam.thm_PAIR_EXISTS_THM holTheoryInst

theorem hol_REP_ABS_PAIR : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (x : A) (y : B),
    REP_prod (ABS_prod (mk_pair x y)) = mk_pair x y := @HolLightLean.hol_opam.thm_REP_ABS_PAIR holTheoryInst

theorem hol_COMMA_DEF : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (x : A) (y : B), (x, y) = ABS_prod (mk_pair x y) := @HolLightLean.hol_opam.thm_COMMA_DEF holTheoryInst

theorem hol_FST_DEF : 
  ∀ {A B : Type} [inst : Nonempty A] [Nonempty B] (p : A × B),
    p.1 = Classical.epsilon fun (x : A) ↦ ∃ (y : B), p = (x, y) := @HolLightLean.hol_opam.thm_FST_DEF holTheoryInst

theorem hol_SND_DEF : 
  ∀ {A B : Type} [Nonempty A] [inst : Nonempty B] (p : A × B),
    p.2 = Classical.epsilon fun (y : B) ↦ ∃ (x : A), p = (x, y) := @HolLightLean.hol_opam.thm_SND_DEF holTheoryInst

theorem hol_PAIR_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A) (y : B) (a : A) (b : B), ((x, y) = (a, b)) = (x = a ∧ y = b) := @HolLightLean.hol_opam.thm_PAIR_EQ holTheoryInst

theorem hol_PAIR_SURJECTIVE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (p : A × B), ∃ (x : A) (y : B), p = (x, y) := @HolLightLean.hol_opam.thm_PAIR_SURJECTIVE holTheoryInst

theorem hol_FST : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A) (y : B), (x, y).1 = x := @HolLightLean.hol_opam.thm_FST holTheoryInst

theorem hol_SND : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A) (y : B), (x, y).2 = y := @HolLightLean.hol_opam.thm_SND holTheoryInst

theorem hol_PAIR : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A × B), (x.1, x.2) = x := @HolLightLean.hol_opam.thm_PAIR holTheoryInst

theorem hol_pair_INDUCT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A × B)), (∀ (x : A) (y : B), P (x, y)) → ∀ (p : A × B), P p := @HolLightLean.hol_opam.thm_pair_INDUCT holTheoryInst

theorem hol_pair_RECURSION : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (PAIR' : A → B → C),
    ∃ (fn : A × B → C), ∀ (a0 : A) (a1 : B), fn (a0, a1) = PAIR' a0 a1 := @HolLightLean.hol_opam.thm_pair_RECURSION holTheoryInst

theorem hol_CURRY_DEF : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A × B → C) (x : A) (y : B), f (x, y) = f (x, y) := @HolLightLean.hol_opam.thm_CURRY_DEF holTheoryInst

theorem hol_UNCURRY_DEF : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A → B → C) (x : A) (y : B), f (x, y).1 (x, y).2 = f x y := @HolLightLean.hol_opam.thm_UNCURRY_DEF holTheoryInst

theorem hol_PASSOC_DEF : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (f : (A × B) × C → D) (x : A) (y : B) (z : C),
    f (((x, y, z).1, (x, y, z).2.1), (x, y, z).2.2) = f ((x, y), z) := @HolLightLean.hol_opam.thm_PASSOC_DEF holTheoryInst

theorem hol_FORALL_PAIR_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A × B)),
    Eq (α := Prop) (∀ (p : A × B), P p) (∀ (p1 : A) (p2 : B), P (p1, p2)) := @HolLightLean.hol_opam.thm_FORALL_PAIR_THM holTheoryInst

theorem hol_EXISTS_PAIR_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A × B)), (∃ (p : A × B), P p) = ∃ (p1 : A) (p2 : B), P (p1, p2) := @HolLightLean.hol_opam.thm_EXISTS_PAIR_THM holTheoryInst

theorem hol_LAMBDA_PAIR_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [inst : Nonempty C] (t : A × B → C),
    Eq (α := A × B → C) (fun (p : A × B) ↦ t p)
      (Classical.epsilon fun (f : A × B → C) ↦ ∀ (x : A) (y : B), f (x, y) = t (x, y)) := @HolLightLean.hol_opam.thm_LAMBDA_PAIR_THM holTheoryInst

theorem hol_LAMBDA_PAIR : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [inst : Nonempty C] (f : A → B → C),
    Eq (α := A × B → C) (Classical.epsilon fun (f' : A × B → C) ↦ ∀ (x : A) (y : B), f' (x, y) = f x y)
      fun (p : A × B) ↦ f p.1 p.2 := @HolLightLean.hol_opam.thm_LAMBDA_PAIR holTheoryInst

theorem hol_LAMBDA_TRIPLE_THM : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [inst : Nonempty D] (f : A × B × C → D),
    Eq (α := A × B × C → D) (fun (t : A × B × C) ↦ f t)
      (Classical.epsilon fun (f' : A × B × C → D) ↦ ∀ (x : A) (y : B) (z : C), f' (x, y, z) = f (x, y, z)) := @HolLightLean.hol_opam.thm_LAMBDA_TRIPLE_THM holTheoryInst

theorem hol_LAMBDA_TRIPLE : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [inst : Nonempty D] (f : A → B → C → D),
    Eq (α := A × B × C → D)
      (Classical.epsilon fun (f' : A × B × C → D) ↦ ∀ (x : A) (y : B) (z : C), f' (x, y, z) = f x y z)
      fun (t : A × B × C) ↦ f t.1 t.2.1 t.2.2 := @HolLightLean.hol_opam.thm_LAMBDA_TRIPLE holTheoryInst

theorem hol_PAIRED_ETA_THM : 
  ∀ {A B C D E : Type} [Nonempty A] [Nonempty B] [inst : Nonempty C] [inst_1 : Nonempty D] [inst_2 : Nonempty E],
    (∀ (f : A × B → C), (Classical.epsilon fun (f' : A × B → C) ↦ ∀ (x : A) (y : B), f' (x, y) = f (x, y)) = f) ∧
      (∀ (f : A × B × C → D),
          (Classical.epsilon fun (f' : A × B × C → D) ↦ ∀ (x : A) (y : B) (z : C), f' (x, y, z) = f (x, y, z)) = f) ∧
        ∀ (f : A × B × C × D → E),
          (Classical.epsilon fun (f' : A × B × C × D → E) ↦
              ∀ (w : A) (x : B) (y : C) (z : D), f' (w, x, y, z) = f (w, x, y, z)) =
            f := @HolLightLean.hol_opam.thm_PAIRED_ETA_THM holTheoryInst

theorem hol_FORALL_UNCURRY : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set (A → B → C)),
    Eq (α := Prop) (∀ (f : A → B → C), P f) (∀ (f : A × B → C), P fun (a : A) (b : B) ↦ f (a, b)) := @HolLightLean.hol_opam.thm_FORALL_UNCURRY holTheoryInst

theorem hol_EXISTS_UNCURRY : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set (A → B → C)),
    (∃ (f : A → B → C), P f) = ∃ (f : A × B → C), P fun (a : A) (b : B) ↦ f (a, b) := @HolLightLean.hol_opam.thm_EXISTS_UNCURRY holTheoryInst

theorem hol_EXISTS_CURRY : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [inst : Nonempty C] (P : Set (A × B → C)),
    (∃ (f : A × B → C), P f) =
      ∃ (f : A → B → C), P (Classical.epsilon fun (f' : A × B → C) ↦ ∀ (a : A) (b : B), f' (a, b) = f a b) := @HolLightLean.hol_opam.thm_EXISTS_CURRY holTheoryInst

theorem hol_FORALL_CURRY : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [inst : Nonempty C] (P : Set (A × B → C)),
    Eq (α := Prop) (∀ (f : A × B → C), P f)
      (∀ (f : A → B → C), P (Classical.epsilon fun (f' : A × B → C) ↦ ∀ (a : A) (b : B), f' (a, b) = f a b)) := @HolLightLean.hol_opam.thm_FORALL_CURRY holTheoryInst

theorem hol_FORALL_UNPAIR_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop),
    Eq (α := Prop) (∀ (x : A) (y : B), P x y) (∀ (z : A × B), P z.1 z.2) := @HolLightLean.hol_opam.thm_FORALL_UNPAIR_THM holTheoryInst

theorem hol_EXISTS_UNPAIR_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop), (∃ (x : A) (y : B), P x y) = ∃ (z : A × B), P z.1 z.2 := @HolLightLean.hol_opam.thm_EXISTS_UNPAIR_THM holTheoryInst

theorem hol_FORALL_PAIR_FUN_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set (A → B × C)),
    Eq (α := Prop) (∀ (f : A → B × C), P f) (∀ (g : A → B) (h : A → C), P fun (a : A) ↦ (g a, h a)) := @HolLightLean.hol_opam.thm_FORALL_PAIR_FUN_THM holTheoryInst

theorem hol_EXISTS_PAIR_FUN_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set (A → B × C)),
    (∃ (f : A → B × C), P f) = ∃ (g : A → B) (h : A → C), P fun (a : A) ↦ (g a, h a) := @HolLightLean.hol_opam.thm_EXISTS_PAIR_FUN_THM holTheoryInst

theorem hol_FORALL_UNPAIR_FUN_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : (A → B) → (A → C) → Prop),
    Eq (α := Prop) (∀ (f : A → B) (g : A → C), P f g) (∀ (h : A → B × C), P (Prod.fst ∘ h) (Prod.snd ∘ h)) := @HolLightLean.hol_opam.thm_FORALL_UNPAIR_FUN_THM holTheoryInst

theorem hol_EXISTS_UNPAIR_FUN_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : (A → B) → (A → C) → Prop),
    (∃ (f : A → B) (g : A → C), P f g) = ∃ (h : A → B × C), P (Prod.fst ∘ h) (Prod.snd ∘ h) := @HolLightLean.hol_opam.thm_EXISTS_UNPAIR_FUN_THM holTheoryInst

theorem hol_EXISTS_SWAP_FUN_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set (A → B → C)),
    (∃ (f : A → B → C), P f) = ∃ (f : B → A → C), P fun (a : A) (b : B) ↦ f b a := @HolLightLean.hol_opam.thm_EXISTS_SWAP_FUN_THM holTheoryInst

theorem hol_FORALL_PAIRED_THM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : A → B → Prop),
    HOLTheory.FORALL (A := A × B) (Classical.epsilon fun (f : Set (A × B)) ↦ ∀ (x : A) (y : B), f (x, y) = P x y) =
      ∀ (x : A) (y : B), P x y := @HolLightLean.hol_opam.thm_FORALL_PAIRED_THM holTheoryInst

theorem hol_EXISTS_PAIRED_THM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : A → B → Prop),
    HOLTheory.EXISTS (A := A × B) (Classical.epsilon fun (f : Set (A × B)) ↦ ∀ (x : A) (y : B), f (x, y) = P x y) =
      ∃ (x : A) (y : B), P x y := @HolLightLean.hol_opam.thm_EXISTS_PAIRED_THM holTheoryInst

theorem hol_FORALL_TRIPLED_THM : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (P : A → B → C → Prop),
    HOLTheory.FORALL (A := A × B × C)
        (Classical.epsilon fun (f : Set (A × B × C)) ↦ ∀ (x : A) (y : B) (z : C), f (x, y, z) = P x y z) =
      ∀ (x : A) (y : B) (z : C), P x y z := @HolLightLean.hol_opam.thm_FORALL_TRIPLED_THM holTheoryInst

theorem hol_EXISTS_TRIPLED_THM : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (P : A → B → C → Prop),
    HOLTheory.EXISTS (A := A × B × C)
        (Classical.epsilon fun (f : Set (A × B × C)) ↦ ∀ (x : A) (y : B) (z : C), f (x, y, z) = P x y z) =
      ∃ (x : A) (y : B) (z : C), P x y z := @HolLightLean.hol_opam.thm_EXISTS_TRIPLED_THM holTheoryInst

theorem hol_CHOICE_UNPAIR_THM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : A → B → Prop),
    Eq (α := A × B) (Classical.epsilon (Classical.epsilon fun (f : Set (A × B)) ↦ ∀ (x : A) (y : B), f (x, y) = P x y))
      (Classical.epsilon fun (p : A × B) ↦ P p.1 p.2) := @HolLightLean.hol_opam.thm_CHOICE_UNPAIR_THM holTheoryInst

theorem hol_CHOICE_PAIRED_THM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : A → B → Prop) (Q : Set (A × B)),
    ((∃ (x : A) (y : B), P x y) ∧ ∀ (x : A) (y : B), P x y → Q (x, y)) →
      Q (Classical.epsilon (Classical.epsilon fun (f : Set (A × B)) ↦ ∀ (x : A) (y : B), f (x, y) = P x y)) := @HolLightLean.hol_opam.thm_CHOICE_PAIRED_THM holTheoryInst

theorem hol_ONE_ONE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B), Function.Injective f = ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2 := @HolLightLean.hol_opam.thm_ONE_ONE holTheoryInst

theorem hol_ONTO : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (y : B), ∃ (x : A), y = f x) (∀ (y : B), ∃ (x : A), y = f x) := @HolLightLean.hol_opam.thm_ONTO holTheoryInst

theorem hol_INFINITY_AX : 
  ∃ (f : ℕ → ℕ), Function.Injective f ∧ ¬∀ (y : ℕ), ∃ (x : ℕ), y = f x := @HolLightLean.hol_opam.thm_INFINITY_AX holTheoryInst

theorem hol_IND_SUC_0_EXISTS : 
  ∃ (f : ℕ → ℕ) (z : ℕ), (∀ (x1 x2 : ℕ), (f x1 = f x2) = (x1 = x2)) ∧ ∀ (x : ℕ), ¬f x = z := @HolLightLean.hol_opam.thm_IND_SUC_0_EXISTS holTheoryInst

theorem hol_NUM_REP_RULES : 
  NUM_REP IND_0 ∧ ∀ (i : ℕ), NUM_REP i → NUM_REP (IND_SUC i) := @HolLightLean.hol_opam.thm_NUM_REP_RULES holTheoryInst

theorem hol_NUM_REP_CASES : 
  ∀ (a : ℕ), NUM_REP a = (a = IND_0 ∨ ∃ (i : ℕ), a = IND_SUC i ∧ NUM_REP i) := @HolLightLean.hol_opam.thm_NUM_REP_CASES holTheoryInst

theorem hol_NUM_REP_INDUCT : 
  ∀ (NUM_REP' : Set ℕ),
    (NUM_REP' IND_0 ∧ ∀ (i : ℕ), NUM_REP' i → NUM_REP' (IND_SUC i)) → ∀ (a : ℕ), NUM_REP a → NUM_REP' a := @HolLightLean.hol_opam.thm_NUM_REP_INDUCT holTheoryInst

theorem hol_ZERO_DEF : 
  (0 : ℕ) = mk_num IND_0 := @HolLightLean.hol_opam.thm_ZERO_DEF holTheoryInst

theorem hol_SUC_DEF : 
  ∀ (n : ℕ), n + (1 : ℕ) = mk_num (IND_SUC (dest_num n)) := @HolLightLean.hol_opam.thm_SUC_DEF holTheoryInst

theorem hol_SUC_INJ : 
  ∀ (m n : ℕ), (m + (1 : ℕ) = n + (1 : ℕ)) = (m = n) := @HolLightLean.hol_opam.thm_SUC_INJ holTheoryInst

theorem hol_NOT_SUC : 
  ∀ (n : ℕ), ¬n + (1 : ℕ) = (0 : ℕ) := @HolLightLean.hol_opam.thm_NOT_SUC holTheoryInst

theorem hol_num_INDUCTION : 
  ∀ (P : Set ℕ), (P (0 : ℕ) ∧ ∀ (n : ℕ), P n → P (n + (1 : ℕ))) → ∀ (n : ℕ), P n := @HolLightLean.hol_opam.thm_num_INDUCTION holTheoryInst

theorem hol_num_Axiom : 
  ∀ {A : Type} [Nonempty A] (e : A) (f : A → ℕ → A),
    ∃! fn : ℕ → A, fn (0 : ℕ) = e ∧ ∀ (n : ℕ), fn (n + (1 : ℕ)) = f (fn n) n := @HolLightLean.hol_opam.thm_num_Axiom holTheoryInst

theorem hol_num_CASES : 
  ∀ (m : ℕ), m = (0 : ℕ) ∨ ∃ (n : ℕ), m = n + (1 : ℕ) := @HolLightLean.hol_opam.thm_num_CASES holTheoryInst

theorem hol_PRE : 
  (0 : ℕ) - (1 : ℕ) = (0 : ℕ) ∧ ∀ (n : ℕ), n + (1 : ℕ) - (1 : ℕ) = n := @HolLightLean.hol_opam.thm_PRE holTheoryInst

theorem hol_ADD : 
  (∀ (n : ℕ), (0 : ℕ) + n = n) ∧ ∀ (m n : ℕ), m + (1 : ℕ) + n = m + n + (1 : ℕ) := @HolLightLean.hol_opam.thm_ADD holTheoryInst

theorem hol_ADD_0 : 
  ∀ (m : ℕ), m + (0 : ℕ) = m := @HolLightLean.hol_opam.thm_ADD_0 holTheoryInst

theorem hol_ADD_SUC : 
  ∀ (m n : ℕ), m + (n + (1 : ℕ)) = m + n + (1 : ℕ) := @HolLightLean.hol_opam.thm_ADD_SUC holTheoryInst

theorem hol_ADD_CLAUSES : 
  (∀ (n : ℕ), (0 : ℕ) + n = n) ∧
    (∀ (m : ℕ), m + (0 : ℕ) = m) ∧
      (∀ (m n : ℕ), m + (1 : ℕ) + n = m + n + (1 : ℕ)) ∧ ∀ (m n : ℕ), m + (n + (1 : ℕ)) = m + n + (1 : ℕ) := @HolLightLean.hol_opam.thm_ADD_CLAUSES holTheoryInst

theorem hol_ADD_SYM : 
  ∀ (m n : ℕ), m + n = n + m := @HolLightLean.hol_opam.thm_ADD_SYM holTheoryInst

theorem hol_ADD_ASSOC : 
  ∀ (m n p : ℕ), m + (n + p) = m + n + p := @HolLightLean.hol_opam.thm_ADD_ASSOC holTheoryInst

theorem hol_ADD_AC : 
  ∀ (n m p : ℕ), m + n = n + m ∧ m + n + p = m + (n + p) ∧ m + (n + p) = n + (m + p) := @HolLightLean.hol_opam.thm_ADD_AC holTheoryInst

theorem hol_ADD_EQ_0 : 
  ∀ (m n : ℕ), (m + n = (0 : ℕ)) = (m = (0 : ℕ) ∧ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_ADD_EQ_0 holTheoryInst

theorem hol_EQ_ADD_LCANCEL : 
  ∀ (m n p : ℕ), (m + n = m + p) = (n = p) := @HolLightLean.hol_opam.thm_EQ_ADD_LCANCEL holTheoryInst

theorem hol_EQ_ADD_RCANCEL : 
  ∀ (m n p : ℕ), (m + p = n + p) = (m = n) := @HolLightLean.hol_opam.thm_EQ_ADD_RCANCEL holTheoryInst

theorem hol_EQ_ADD_LCANCEL_0 : 
  ∀ (m n : ℕ), (m + n = m) = (n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EQ_ADD_LCANCEL_0 holTheoryInst

theorem hol_EQ_ADD_RCANCEL_0 : 
  ∀ (m n : ℕ), (m + n = n) = (m = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EQ_ADD_RCANCEL_0 holTheoryInst

theorem hol_BIT0 : 
  ∀ (n : ℕ), n + n = n + n := @HolLightLean.hol_opam.thm_BIT0 holTheoryInst

theorem hol_BIT1 : 
  ∀ (n : ℕ), n + n + (1 : ℕ) = n + n + (1 : ℕ) := @HolLightLean.hol_opam.thm_BIT1 holTheoryInst

theorem hol_BIT0_THM : 
  ∀ (n : ℕ), n + n = n + n := @HolLightLean.hol_opam.thm_BIT0_THM holTheoryInst

theorem hol_BIT1_THM : 
  ∀ (n : ℕ), n + n + (1 : ℕ) = n + n + (1 : ℕ) := @HolLightLean.hol_opam.thm_BIT1_THM holTheoryInst

theorem hol_ONE : 
  (0 : ℕ) + (0 : ℕ) + (1 : ℕ) = (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_ONE holTheoryInst

theorem hol_TWO : 
  (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_TWO holTheoryInst

theorem hol_ADD1 : 
  ∀ (m : ℕ), m + (1 : ℕ) = m + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_ADD1 holTheoryInst

theorem hol_MULT : 
  (∀ (n : ℕ), (0 : ℕ) * n = (0 : ℕ)) ∧ ∀ (m n : ℕ), (m + (1 : ℕ)) * n = m * n + n := @HolLightLean.hol_opam.thm_MULT holTheoryInst

theorem hol_MULT_0 : 
  ∀ (m : ℕ), m * (0 : ℕ) = (0 : ℕ) := @HolLightLean.hol_opam.thm_MULT_0 holTheoryInst

theorem hol_MULT_SUC : 
  ∀ (m n : ℕ), m * (n + (1 : ℕ)) = m + m * n := @HolLightLean.hol_opam.thm_MULT_SUC holTheoryInst

theorem hol_MULT_CLAUSES : 
  (∀ (n : ℕ), (0 : ℕ) * n = (0 : ℕ)) ∧
    (∀ (m : ℕ), m * (0 : ℕ) = (0 : ℕ)) ∧
      (∀ (n : ℕ), ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * n = n) ∧
        (∀ (m : ℕ), m * ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = m) ∧
          (∀ (m n : ℕ), (m + (1 : ℕ)) * n = m * n + n) ∧ ∀ (m n : ℕ), m * (n + (1 : ℕ)) = m + m * n := @HolLightLean.hol_opam.thm_MULT_CLAUSES holTheoryInst

theorem hol_MULT_SYM : 
  ∀ (m n : ℕ), m * n = n * m := @HolLightLean.hol_opam.thm_MULT_SYM holTheoryInst

theorem hol_LEFT_ADD_DISTRIB : 
  ∀ (m n p : ℕ), m * (n + p) = m * n + m * p := @HolLightLean.hol_opam.thm_LEFT_ADD_DISTRIB holTheoryInst

theorem hol_RIGHT_ADD_DISTRIB : 
  ∀ (m n p : ℕ), (m + n) * p = m * p + n * p := @HolLightLean.hol_opam.thm_RIGHT_ADD_DISTRIB holTheoryInst

theorem hol_MULT_ASSOC : 
  ∀ (m n p : ℕ), m * (n * p) = m * n * p := @HolLightLean.hol_opam.thm_MULT_ASSOC holTheoryInst

theorem hol_MULT_AC : 
  ∀ (n m p : ℕ), m * n = n * m ∧ m * n * p = m * (n * p) ∧ m * (n * p) = n * (m * p) := @HolLightLean.hol_opam.thm_MULT_AC holTheoryInst

theorem hol_MULT_EQ_0 : 
  ∀ (m n : ℕ), (m * n = (0 : ℕ)) = (m = (0 : ℕ) ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_MULT_EQ_0 holTheoryInst

theorem hol_EQ_MULT_LCANCEL : 
  ∀ (m n p : ℕ), (m * n = m * p) = (m = (0 : ℕ) ∨ n = p) := @HolLightLean.hol_opam.thm_EQ_MULT_LCANCEL holTheoryInst

theorem hol_EQ_MULT_RCANCEL : 
  ∀ (m n p : ℕ), (m * p = n * p) = (m = n ∨ p = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EQ_MULT_RCANCEL holTheoryInst

theorem hol_MULT_2 : 
  ∀ (n : ℕ), ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n = n + n := @HolLightLean.hol_opam.thm_MULT_2 holTheoryInst

theorem hol_MULT_EQ_1 : 
  ∀ (m n : ℕ),
    (m * n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = (m = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∧ n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_MULT_EQ_1 holTheoryInst

theorem hol_EXP : 
  (∀ (m : ℕ), m ^ (0 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ ∀ (m n : ℕ), m ^ (n + (1 : ℕ)) = m * m ^ n := @HolLightLean.hol_opam.thm_EXP holTheoryInst

theorem hol_EXP_EQ_0 : 
  ∀ (m n : ℕ), (m ^ n = (0 : ℕ)) = (m = (0 : ℕ) ∧ ¬n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EXP_EQ_0 holTheoryInst

theorem hol_EXP_EQ_1 : 
  ∀ (x n : ℕ), (x ^ n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = (x = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EXP_EQ_1 holTheoryInst

theorem hol_EXP_ZERO : 
  ∀ (n : ℕ), (0 : ℕ) ^ n = if n = (0 : ℕ) then (0 : ℕ) + (0 : ℕ) + (1 : ℕ) else (0 : ℕ) := @HolLightLean.hol_opam.thm_EXP_ZERO holTheoryInst

theorem hol_EXP_ADD : 
  ∀ (m n p : ℕ), m ^ (n + p) = m ^ n * m ^ p := @HolLightLean.hol_opam.thm_EXP_ADD holTheoryInst

theorem hol_EXP_ONE : 
  ∀ (n : ℕ), ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ^ n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_EXP_ONE holTheoryInst

theorem hol_EXP_1 : 
  ∀ (n : ℕ), n ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = n := @HolLightLean.hol_opam.thm_EXP_1 holTheoryInst

theorem hol_EXP_2 : 
  ∀ (n : ℕ), n ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = n * n := @HolLightLean.hol_opam.thm_EXP_2 holTheoryInst

theorem hol_MULT_EXP : 
  ∀ (p m n : ℕ), (m * n) ^ p = m ^ p * n ^ p := @HolLightLean.hol_opam.thm_MULT_EXP holTheoryInst

theorem hol_EXP_MULT : 
  ∀ (m n p : ℕ), m ^ (n * p) = (m ^ n) ^ p := @HolLightLean.hol_opam.thm_EXP_MULT holTheoryInst

theorem hol_EXP_EXP : 
  ∀ (x m n : ℕ), (x ^ m) ^ n = x ^ (m * n) := @HolLightLean.hol_opam.thm_EXP_EXP holTheoryInst

theorem hol_LE : 
  (∀ (m : ℕ), (m ≤ (0 : ℕ)) = (m = (0 : ℕ))) ∧ ∀ (m n : ℕ), (m ≤ n + (1 : ℕ)) = (m = n + (1 : ℕ) ∨ m ≤ n) := @HolLightLean.hol_opam.thm_LE holTheoryInst

theorem hol_LT : 
  (∀ (m : ℕ), (m < (0 : ℕ)) = False) ∧ ∀ (m n : ℕ), (m < n + (1 : ℕ)) = (m = n ∨ m < n) := @HolLightLean.hol_opam.thm_LT holTheoryInst

theorem hol_GE : 
  ∀ (n m : ℕ), (m ≥ n) = (n ≤ m) := @HolLightLean.hol_opam.thm_GE holTheoryInst

theorem hol_GT : 
  ∀ (n m : ℕ), (m > n) = (n < m) := @HolLightLean.hol_opam.thm_GT holTheoryInst

theorem hol_MAX : 
  ∀ (m n : ℕ), max m n = if m ≤ n then n else m := @HolLightLean.hol_opam.thm_MAX holTheoryInst

theorem hol_MIN : 
  ∀ (m n : ℕ), min m n = if m ≤ n then m else n := @HolLightLean.hol_opam.thm_MIN holTheoryInst

theorem hol_LE_SUC_LT : 
  ∀ (m n : ℕ), (m + (1 : ℕ) ≤ n) = (m < n) := @HolLightLean.hol_opam.thm_LE_SUC_LT holTheoryInst

theorem hol_LT_SUC_LE : 
  ∀ (m n : ℕ), (m < n + (1 : ℕ)) = (m ≤ n) := @HolLightLean.hol_opam.thm_LT_SUC_LE holTheoryInst

theorem hol_LE_SUC : 
  ∀ (m n : ℕ), (m + (1 : ℕ) ≤ n + (1 : ℕ)) = (m ≤ n) := @HolLightLean.hol_opam.thm_LE_SUC holTheoryInst

theorem hol_LT_SUC : 
  ∀ (m n : ℕ), (m + (1 : ℕ) < n + (1 : ℕ)) = (m < n) := @HolLightLean.hol_opam.thm_LT_SUC holTheoryInst

theorem hol_LE_0 : 
  ∀ (n : ℕ), (0 : ℕ) ≤ n := @HolLightLean.hol_opam.thm_LE_0 holTheoryInst

theorem hol_LT_0 : 
  ∀ (n : ℕ), (0 : ℕ) < n + (1 : ℕ) := @HolLightLean.hol_opam.thm_LT_0 holTheoryInst

theorem hol_LE_REFL : 
  ∀ (n : ℕ), n ≤ n := @HolLightLean.hol_opam.thm_LE_REFL holTheoryInst

theorem hol_LT_REFL : 
  ∀ (n : ℕ), ¬n < n := @HolLightLean.hol_opam.thm_LT_REFL holTheoryInst

theorem hol_LT_IMP_NE : 
  ∀ (m n : ℕ), m < n → ¬m = n := @HolLightLean.hol_opam.thm_LT_IMP_NE holTheoryInst

theorem hol_LE_ANTISYM : 
  ∀ (m n : ℕ), (m ≤ n ∧ n ≤ m) = (m = n) := @HolLightLean.hol_opam.thm_LE_ANTISYM holTheoryInst

theorem hol_LT_ANTISYM : 
  ∀ (m n : ℕ), ¬(m < n ∧ n < m) := @HolLightLean.hol_opam.thm_LT_ANTISYM holTheoryInst

theorem hol_LET_ANTISYM : 
  ∀ (m n : ℕ), ¬(m ≤ n ∧ n < m) := @HolLightLean.hol_opam.thm_LET_ANTISYM holTheoryInst

theorem hol_LTE_ANTISYM : 
  ∀ (m n : ℕ), ¬(m < n ∧ n ≤ m) := @HolLightLean.hol_opam.thm_LTE_ANTISYM holTheoryInst

theorem hol_LE_TRANS : 
  ∀ (m n p : ℕ), m ≤ n ∧ n ≤ p → m ≤ p := @HolLightLean.hol_opam.thm_LE_TRANS holTheoryInst

theorem hol_LT_TRANS : 
  ∀ (m n p : ℕ), m < n ∧ n < p → m < p := @HolLightLean.hol_opam.thm_LT_TRANS holTheoryInst

theorem hol_LET_TRANS : 
  ∀ (m n p : ℕ), m ≤ n ∧ n < p → m < p := @HolLightLean.hol_opam.thm_LET_TRANS holTheoryInst

theorem hol_LTE_TRANS : 
  ∀ (m n p : ℕ), m < n ∧ n ≤ p → m < p := @HolLightLean.hol_opam.thm_LTE_TRANS holTheoryInst

theorem hol_LE_CASES : 
  ∀ (m n : ℕ), m ≤ n ∨ n ≤ m := @HolLightLean.hol_opam.thm_LE_CASES holTheoryInst

theorem hol_LT_CASES : 
  ∀ (m n : ℕ), m < n ∨ n < m ∨ m = n := @HolLightLean.hol_opam.thm_LT_CASES holTheoryInst

theorem hol_LET_CASES : 
  ∀ (m n : ℕ), m ≤ n ∨ n < m := @HolLightLean.hol_opam.thm_LET_CASES holTheoryInst

theorem hol_LTE_CASES : 
  ∀ (m n : ℕ), m < n ∨ n ≤ m := @HolLightLean.hol_opam.thm_LTE_CASES holTheoryInst

theorem hol_LE_LT : 
  ∀ (m n : ℕ), (m ≤ n) = (m < n ∨ m = n) := @HolLightLean.hol_opam.thm_LE_LT holTheoryInst

theorem hol_LT_LE : 
  ∀ (m n : ℕ), (m < n) = (m ≤ n ∧ ¬m = n) := @HolLightLean.hol_opam.thm_LT_LE holTheoryInst

theorem hol_NOT_LE : 
  ∀ (m n : ℕ), (¬m ≤ n) = (n < m) := @HolLightLean.hol_opam.thm_NOT_LE holTheoryInst

theorem hol_NOT_LT : 
  ∀ (m n : ℕ), (¬m < n) = (n ≤ m) := @HolLightLean.hol_opam.thm_NOT_LT holTheoryInst

theorem hol_LT_IMP_LE : 
  ∀ (m n : ℕ), m < n → m ≤ n := @HolLightLean.hol_opam.thm_LT_IMP_LE holTheoryInst

theorem hol_EQ_IMP_LE : 
  ∀ (m n : ℕ), m = n → m ≤ n := @HolLightLean.hol_opam.thm_EQ_IMP_LE holTheoryInst

theorem hol_LT_NZ : 
  ∀ (n : ℕ), ((0 : ℕ) < n) = ¬n = (0 : ℕ) := @HolLightLean.hol_opam.thm_LT_NZ holTheoryInst

theorem hol_LE_1 : 
  (∀ (n : ℕ), ¬n = (0 : ℕ) → (0 : ℕ) < n) ∧
    (∀ (n : ℕ), ¬n = (0 : ℕ) → (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n) ∧
      (∀ (n : ℕ), (0 : ℕ) < n → ¬n = (0 : ℕ)) ∧
        (∀ (n : ℕ), (0 : ℕ) < n → (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n) ∧
          (∀ (n : ℕ), (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n → (0 : ℕ) < n) ∧
            ∀ (n : ℕ), (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n → ¬n = (0 : ℕ) := @HolLightLean.hol_opam.thm_LE_1 holTheoryInst

theorem hol_LE_EXISTS : 
  ∀ (m n : ℕ), (m ≤ n) = ∃ (d : ℕ), n = m + d := @HolLightLean.hol_opam.thm_LE_EXISTS holTheoryInst

theorem hol_LT_EXISTS : 
  ∀ (m n : ℕ), (m < n) = ∃ (d : ℕ), n = m + (d + (1 : ℕ)) := @HolLightLean.hol_opam.thm_LT_EXISTS holTheoryInst

theorem hol_LE_ADD : 
  ∀ (m n : ℕ), m ≤ m + n := @HolLightLean.hol_opam.thm_LE_ADD holTheoryInst

theorem hol_LE_ADDR : 
  ∀ (m n : ℕ), n ≤ m + n := @HolLightLean.hol_opam.thm_LE_ADDR holTheoryInst

theorem hol_LT_ADD : 
  ∀ (m n : ℕ), (m < m + n) = ((0 : ℕ) < n) := @HolLightLean.hol_opam.thm_LT_ADD holTheoryInst

theorem hol_LT_ADDR : 
  ∀ (m n : ℕ), (n < m + n) = ((0 : ℕ) < m) := @HolLightLean.hol_opam.thm_LT_ADDR holTheoryInst

theorem hol_LE_ADD_LCANCEL : 
  ∀ (m n p : ℕ), (m + n ≤ m + p) = (n ≤ p) := @HolLightLean.hol_opam.thm_LE_ADD_LCANCEL holTheoryInst

theorem hol_LE_ADD_RCANCEL : 
  ∀ (m n p : ℕ), (m + p ≤ n + p) = (m ≤ n) := @HolLightLean.hol_opam.thm_LE_ADD_RCANCEL holTheoryInst

theorem hol_LT_ADD_LCANCEL : 
  ∀ (m n p : ℕ), (m + n < m + p) = (n < p) := @HolLightLean.hol_opam.thm_LT_ADD_LCANCEL holTheoryInst

theorem hol_LT_ADD_RCANCEL : 
  ∀ (m n p : ℕ), (m + p < n + p) = (m < n) := @HolLightLean.hol_opam.thm_LT_ADD_RCANCEL holTheoryInst

theorem hol_LE_ADD2 : 
  ∀ (m n p q : ℕ), m ≤ p ∧ n ≤ q → m + n ≤ p + q := @HolLightLean.hol_opam.thm_LE_ADD2 holTheoryInst

theorem hol_LET_ADD2 : 
  ∀ (m n p q : ℕ), m ≤ p ∧ n < q → m + n < p + q := @HolLightLean.hol_opam.thm_LET_ADD2 holTheoryInst

theorem hol_LTE_ADD2 : 
  ∀ (m n p q : ℕ), m < p ∧ n ≤ q → m + n < p + q := @HolLightLean.hol_opam.thm_LTE_ADD2 holTheoryInst

theorem hol_LT_ADD2 : 
  ∀ (m n p q : ℕ), m < p ∧ n < q → m + n < p + q := @HolLightLean.hol_opam.thm_LT_ADD2 holTheoryInst

theorem hol_LT_MULT : 
  ∀ (m n : ℕ), ((0 : ℕ) < m * n) = ((0 : ℕ) < m ∧ (0 : ℕ) < n) := @HolLightLean.hol_opam.thm_LT_MULT holTheoryInst

theorem hol_LE_MULT2 : 
  ∀ (m n p q : ℕ), m ≤ n ∧ p ≤ q → m * p ≤ n * q := @HolLightLean.hol_opam.thm_LE_MULT2 holTheoryInst

theorem hol_LT_LMULT : 
  ∀ (m n p : ℕ), ¬m = (0 : ℕ) ∧ n < p → m * n < m * p := @HolLightLean.hol_opam.thm_LT_LMULT holTheoryInst

theorem hol_LE_MULT_LCANCEL : 
  ∀ (m n p : ℕ), (m * n ≤ m * p) = (m = (0 : ℕ) ∨ n ≤ p) := @HolLightLean.hol_opam.thm_LE_MULT_LCANCEL holTheoryInst

theorem hol_LE_MULT_RCANCEL : 
  ∀ (m n p : ℕ), (m * p ≤ n * p) = (m ≤ n ∨ p = (0 : ℕ)) := @HolLightLean.hol_opam.thm_LE_MULT_RCANCEL holTheoryInst

theorem hol_LT_MULT_LCANCEL : 
  ∀ (m n p : ℕ), (m * n < m * p) = (¬m = (0 : ℕ) ∧ n < p) := @HolLightLean.hol_opam.thm_LT_MULT_LCANCEL holTheoryInst

theorem hol_LT_MULT_RCANCEL : 
  ∀ (m n p : ℕ), (m * p < n * p) = (m < n ∧ ¬p = (0 : ℕ)) := @HolLightLean.hol_opam.thm_LT_MULT_RCANCEL holTheoryInst

theorem hol_LT_MULT2 : 
  ∀ (m n p q : ℕ), m < n ∧ p < q → m * p < n * q := @HolLightLean.hol_opam.thm_LT_MULT2 holTheoryInst

theorem hol_LE_SQUARE_REFL : 
  ∀ (n : ℕ), n ≤ n * n := @HolLightLean.hol_opam.thm_LE_SQUARE_REFL holTheoryInst

theorem hol_LT_POW2_REFL : 
  ∀ (n : ℕ), n < ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ^ n := @HolLightLean.hol_opam.thm_LT_POW2_REFL holTheoryInst

theorem hol_WLOG_LE : 
  ∀ (P : ℕ → ℕ → Prop), ((∀ (m n : ℕ), P m n = P n m) ∧ ∀ (m n : ℕ), m ≤ n → P m n) → ∀ (m n : ℕ), P m n := @HolLightLean.hol_opam.thm_WLOG_LE holTheoryInst

theorem hol_WLOG_LT : 
  ∀ (P : ℕ → ℕ → Prop),
    ((∀ (m : ℕ), P m m) ∧ (∀ (m n : ℕ), P m n = P n m) ∧ ∀ (m n : ℕ), m < n → P m n) → ∀ (m y : ℕ), P m y := @HolLightLean.hol_opam.thm_WLOG_LT holTheoryInst

theorem hol_WLOG_LE_3 : 
  ∀ (P : ℕ → ℕ → ℕ → Prop),
    ((∀ (x y z : ℕ), P x y z → P y x z ∧ P x z y) ∧ ∀ (x y z : ℕ), x ≤ y ∧ y ≤ z → P x y z) → ∀ (x y z : ℕ), P x y z := @HolLightLean.hol_opam.thm_WLOG_LE_3 holTheoryInst

theorem hol_num_WF : 
  ∀ (P : Set ℕ), (∀ (n : ℕ), (∀ m < n, P m) → P n) → ∀ (n : ℕ), P n := @HolLightLean.hol_opam.thm_num_WF holTheoryInst

theorem hol_num_WOP : 
  ∀ (P : Set ℕ), (∃ (n : ℕ), P n) = ∃ (n : ℕ), P n ∧ ∀ m < n, ¬P m := @HolLightLean.hol_opam.thm_num_WOP holTheoryInst

theorem hol_num_MAX : 
  ∀ (P : Set ℕ), ((∃ (x : ℕ), P x) ∧ ∃ (M : ℕ), ∀ (x : ℕ), P x → x ≤ M) = ∃ (m : ℕ), P m ∧ ∀ (x : ℕ), P x → x ≤ m := @HolLightLean.hol_opam.thm_num_MAX holTheoryInst

theorem hol_LE_INDUCT : 
  ∀ (P : ℕ → ℕ → Prop),
    ((∀ (m : ℕ), P m m) ∧ ∀ (m n : ℕ), m ≤ n ∧ P m n → P m (n + (1 : ℕ))) → ∀ (m n : ℕ), m ≤ n → P m n := @HolLightLean.hol_opam.thm_LE_INDUCT holTheoryInst

theorem hol_num_INDUCTION_DOWN : 
  ∀ (P : Set ℕ) (m : ℕ),
    ((∀ (n : ℕ), m ≤ n → P n) ∧ ∀ (n : ℕ), n < m ∧ P (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) → P n) → ∀ (n : ℕ), P n := @HolLightLean.hol_opam.thm_num_INDUCTION_DOWN holTheoryInst

theorem hol_EVEN : 
  Even (0 : ℕ) = True ∧ ∀ (n : ℕ), Even (n + (1 : ℕ)) = ¬Even n := @HolLightLean.hol_opam.thm_EVEN holTheoryInst

theorem hol_ODD : 
  Odd (0 : ℕ) = False ∧ ∀ (n : ℕ), Odd (n + (1 : ℕ)) = ¬Odd n := @HolLightLean.hol_opam.thm_ODD holTheoryInst

theorem hol_NOT_EVEN : 
  ∀ (n : ℕ), (¬Even n) = Odd n := @HolLightLean.hol_opam.thm_NOT_EVEN holTheoryInst

theorem hol_NOT_ODD : 
  ∀ (n : ℕ), (¬Odd n) = Even n := @HolLightLean.hol_opam.thm_NOT_ODD holTheoryInst

theorem hol_EVEN_OR_ODD : 
  ∀ (n : ℕ), Even n ∨ Odd n := @HolLightLean.hol_opam.thm_EVEN_OR_ODD holTheoryInst

theorem hol_EVEN_AND_ODD : 
  ∀ (n : ℕ), ¬(Even n ∧ Odd n) := @HolLightLean.hol_opam.thm_EVEN_AND_ODD holTheoryInst

theorem hol_EVEN_ADD : 
  ∀ (m n : ℕ), Even (m + n) = (Even m = Even n) := @HolLightLean.hol_opam.thm_EVEN_ADD holTheoryInst

theorem hol_EVEN_MULT : 
  ∀ (m n : ℕ), Even (m * n) = (Even m ∨ Even n) := @HolLightLean.hol_opam.thm_EVEN_MULT holTheoryInst

theorem hol_EVEN_EXP : 
  ∀ (m n : ℕ), Even (m ^ n) = (Even m ∧ ¬n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EVEN_EXP holTheoryInst

theorem hol_ODD_ADD : 
  ∀ (m n : ℕ), Odd (m + n) = ¬Odd m = Odd n := @HolLightLean.hol_opam.thm_ODD_ADD holTheoryInst

theorem hol_ODD_MULT : 
  ∀ (m n : ℕ), Odd (m * n) = (Odd m ∧ Odd n) := @HolLightLean.hol_opam.thm_ODD_MULT holTheoryInst

theorem hol_ODD_EXP : 
  ∀ (m n : ℕ), Odd (m ^ n) = (Odd m ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_ODD_EXP holTheoryInst

theorem hol_EVEN_DOUBLE : 
  ∀ (n : ℕ), Even (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n) := @HolLightLean.hol_opam.thm_EVEN_DOUBLE holTheoryInst

theorem hol_ODD_DOUBLE : 
  ∀ (n : ℕ), Odd (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n + (1 : ℕ)) := @HolLightLean.hol_opam.thm_ODD_DOUBLE holTheoryInst

theorem hol_EVEN_EXISTS_LEMMA : 
  ∀ (n : ℕ),
    (Even n → ∃ (m : ℕ), n = ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m) ∧
      (¬Even n → ∃ (m : ℕ), n = ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m + (1 : ℕ)) := @HolLightLean.hol_opam.thm_EVEN_EXISTS_LEMMA holTheoryInst

theorem hol_EVEN_EXISTS : 
  ∀ (n : ℕ), Even n = ∃ (m : ℕ), n = ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m := @HolLightLean.hol_opam.thm_EVEN_EXISTS holTheoryInst

theorem hol_ODD_EXISTS : 
  ∀ (n : ℕ), Odd n = ∃ (m : ℕ), n = ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m + (1 : ℕ) := @HolLightLean.hol_opam.thm_ODD_EXISTS holTheoryInst

theorem hol_EVEN_ODD_DECOMPOSITION : 
  ∀ (n : ℕ),
    (∃ (k : ℕ) (m : ℕ), Odd m ∧ n = ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ^ k * m) =
      ¬n = (0 : ℕ) := @HolLightLean.hol_opam.thm_EVEN_ODD_DECOMPOSITION holTheoryInst

theorem hol_SUB : 
  (∀ (m : ℕ), m - (0 : ℕ) = m) ∧ ∀ (m n : ℕ), m - (n + (1 : ℕ)) = m - n - (1 : ℕ) := @HolLightLean.hol_opam.thm_SUB holTheoryInst

theorem hol_SUB_0 : 
  ∀ (m : ℕ), (0 : ℕ) - m = (0 : ℕ) ∧ m - (0 : ℕ) = m := @HolLightLean.hol_opam.thm_SUB_0 holTheoryInst

theorem hol_SUB_PRESUC : 
  ∀ (m n : ℕ), m + (1 : ℕ) - n - (1 : ℕ) = m - n := @HolLightLean.hol_opam.thm_SUB_PRESUC holTheoryInst

theorem hol_SUB_SUC : 
  ∀ (m n : ℕ), m + (1 : ℕ) - (n + (1 : ℕ)) = m - n := @HolLightLean.hol_opam.thm_SUB_SUC holTheoryInst

theorem hol_SUB_REFL : 
  ∀ (n : ℕ), n - n = (0 : ℕ) := @HolLightLean.hol_opam.thm_SUB_REFL holTheoryInst

theorem hol_ADD_SUB : 
  ∀ (m n : ℕ), m + n - n = m := @HolLightLean.hol_opam.thm_ADD_SUB holTheoryInst

theorem hol_ADD_SUB2 : 
  ∀ (m n : ℕ), m + n - m = n := @HolLightLean.hol_opam.thm_ADD_SUB2 holTheoryInst

theorem hol_SUB_EQ_0 : 
  ∀ (m n : ℕ), (m - n = (0 : ℕ)) = (m ≤ n) := @HolLightLean.hol_opam.thm_SUB_EQ_0 holTheoryInst

theorem hol_ADD_SUBR2 : 
  ∀ (m n : ℕ), m - (m + n) = (0 : ℕ) := @HolLightLean.hol_opam.thm_ADD_SUBR2 holTheoryInst

theorem hol_ADD_SUBR : 
  ∀ (m n : ℕ), n - (m + n) = (0 : ℕ) := @HolLightLean.hol_opam.thm_ADD_SUBR holTheoryInst

theorem hol_SUB_ADD : 
  ∀ (m n : ℕ), n ≤ m → m - n + n = m := @HolLightLean.hol_opam.thm_SUB_ADD holTheoryInst

theorem hol_SUB_ADD_LCANCEL : 
  ∀ (m n p : ℕ), m + n - (m + p) = n - p := @HolLightLean.hol_opam.thm_SUB_ADD_LCANCEL holTheoryInst

theorem hol_SUB_ADD_RCANCEL : 
  ∀ (m n p : ℕ), m + p - (n + p) = m - n := @HolLightLean.hol_opam.thm_SUB_ADD_RCANCEL holTheoryInst

theorem hol_LEFT_SUB_DISTRIB : 
  ∀ (m n p : ℕ), m * (n - p) = m * n - m * p := @HolLightLean.hol_opam.thm_LEFT_SUB_DISTRIB holTheoryInst

theorem hol_RIGHT_SUB_DISTRIB : 
  ∀ (m n p : ℕ), (m - n) * p = m * p - n * p := @HolLightLean.hol_opam.thm_RIGHT_SUB_DISTRIB holTheoryInst

theorem hol_SUC_SUB1 : 
  ∀ (n : ℕ), n + (1 : ℕ) - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = n := @HolLightLean.hol_opam.thm_SUC_SUB1 holTheoryInst

theorem hol_EVEN_SUB : 
  ∀ (m n : ℕ), Even (m - n) = (m ≤ n ∨ Even m = Even n) := @HolLightLean.hol_opam.thm_EVEN_SUB holTheoryInst

theorem hol_ODD_SUB : 
  ∀ (m n : ℕ), Odd (m - n) = (n < m ∧ ¬Odd m = Odd n) := @HolLightLean.hol_opam.thm_ODD_SUB holTheoryInst

theorem hol_FACT : 
  Nat.factorial (0 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∧ ∀ (n : ℕ), (n + (1 : ℕ)).factorial = (n + (1 : ℕ)) * n.factorial := @HolLightLean.hol_opam.thm_FACT holTheoryInst

theorem hol_FACT_LT : 
  ∀ (n : ℕ), (0 : ℕ) < n.factorial := @HolLightLean.hol_opam.thm_FACT_LT holTheoryInst

theorem hol_FACT_LE : 
  ∀ (n : ℕ), (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n.factorial := @HolLightLean.hol_opam.thm_FACT_LE holTheoryInst

theorem hol_FACT_NZ : 
  ∀ (n : ℕ), ¬n.factorial = (0 : ℕ) := @HolLightLean.hol_opam.thm_FACT_NZ holTheoryInst

theorem hol_FACT_MONO : 
  ∀ (m n : ℕ), m ≤ n → m.factorial ≤ n.factorial := @HolLightLean.hol_opam.thm_FACT_MONO holTheoryInst

theorem hol_EXP_LT_0 : 
  ∀ (n x : ℕ), ((0 : ℕ) < x ^ n) = (¬x = (0 : ℕ) ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EXP_LT_0 holTheoryInst

theorem hol_LT_EXP : 
  ∀ (x m n : ℕ),
    (x ^ m < x ^ n) =
      ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x ∧ m < n ∨
        x = (0 : ℕ) ∧ ¬m = (0 : ℕ) ∧ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_LT_EXP holTheoryInst

theorem hol_LE_EXP : 
  ∀ (x m n : ℕ),
    (x ^ m ≤ x ^ n) = if x = (0 : ℕ) then m = (0 : ℕ) → n = (0 : ℕ) else x = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ m ≤ n := @HolLightLean.hol_opam.thm_LE_EXP holTheoryInst

theorem hol_EQ_EXP : 
  ∀ (x m n : ℕ),
    (x ^ m = x ^ n) = if x = (0 : ℕ) then (m = (0 : ℕ)) = (n = (0 : ℕ)) else x = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ m = n := @HolLightLean.hol_opam.thm_EQ_EXP holTheoryInst

theorem hol_EXP_MONO_LE_IMP : 
  ∀ (x y n : ℕ), x ≤ y → x ^ n ≤ y ^ n := @HolLightLean.hol_opam.thm_EXP_MONO_LE_IMP holTheoryInst

theorem hol_EXP_MONO_LT_IMP : 
  ∀ (x y n : ℕ), x < y ∧ ¬n = (0 : ℕ) → x ^ n < y ^ n := @HolLightLean.hol_opam.thm_EXP_MONO_LT_IMP holTheoryInst

theorem hol_EXP_MONO_LE : 
  ∀ (x y n : ℕ), (x ^ n ≤ y ^ n) = (x ≤ y ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EXP_MONO_LE holTheoryInst

theorem hol_EXP_MONO_LT : 
  ∀ (x y n : ℕ), (x ^ n < y ^ n) = (x < y ∧ ¬n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EXP_MONO_LT holTheoryInst

theorem hol_EXP_MONO_EQ : 
  ∀ (x y n : ℕ), (x ^ n = y ^ n) = (x = y ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EXP_MONO_EQ holTheoryInst

theorem hol_DIVMOD_EXIST : 
  ∀ (m n : ℕ), ¬n = (0 : ℕ) → ∃ (q : ℕ) (r : ℕ), m = q * n + r ∧ r < n := @HolLightLean.hol_opam.thm_DIVMOD_EXIST holTheoryInst

theorem hol_DIVMOD_EXIST_0 : 
  ∀ (m n : ℕ), ∃ (q : ℕ) (r : ℕ), if n = (0 : ℕ) then q = (0 : ℕ) ∧ r = m else m = q * n + r ∧ r < n := @HolLightLean.hol_opam.thm_DIVMOD_EXIST_0 holTheoryInst

theorem hol_DIVISION : 
  ∀ (m n : ℕ), ¬n = (0 : ℕ) → m = m / n * n + m % n ∧ m % n < n := @HolLightLean.hol_opam.thm_DIVISION holTheoryInst

theorem hol_DIV_ZERO : 
  ∀ (n : ℕ), n / (0 : ℕ) = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIV_ZERO holTheoryInst

theorem hol_MOD_ZERO : 
  ∀ (n : ℕ), n % (0 : ℕ) = n := @HolLightLean.hol_opam.thm_MOD_ZERO holTheoryInst

theorem hol_DIVISION_SIMP : 
  (∀ (m n : ℕ), m / n * n + m % n = m) ∧ ∀ (m n : ℕ), n * (m / n) + m % n = m := @HolLightLean.hol_opam.thm_DIVISION_SIMP holTheoryInst

theorem hol_EQ_DIVMOD : 
  ∀ (p m n : ℕ), (m / p = n / p ∧ m % p = n % p) = (m = n) := @HolLightLean.hol_opam.thm_EQ_DIVMOD holTheoryInst

theorem hol_MOD_LT_EQ : 
  ∀ (m n : ℕ), (m % n < n) = ¬n = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_LT_EQ holTheoryInst

theorem hol_MOD_LT_EQ_LT : 
  ∀ (m n : ℕ), (m % n < n) = ((0 : ℕ) < n) := @HolLightLean.hol_opam.thm_MOD_LT_EQ_LT holTheoryInst

theorem hol_DIVMOD_UNIQ_LEMMA : 
  ∀ (m n q1 r1 q2 r2 : ℕ), (m = q1 * n + r1 ∧ r1 < n) ∧ m = q2 * n + r2 ∧ r2 < n → q1 = q2 ∧ r1 = r2 := @HolLightLean.hol_opam.thm_DIVMOD_UNIQ_LEMMA holTheoryInst

theorem hol_DIVMOD_UNIQ : 
  ∀ (m n q r : ℕ), m = q * n + r ∧ r < n → m / n = q ∧ m % n = r := @HolLightLean.hol_opam.thm_DIVMOD_UNIQ holTheoryInst

theorem hol_MOD_UNIQ : 
  ∀ (m n q r : ℕ), m = q * n + r ∧ r < n → m % n = r := @HolLightLean.hol_opam.thm_MOD_UNIQ holTheoryInst

theorem hol_DIV_UNIQ : 
  ∀ (m n q r : ℕ), m = q * n + r ∧ r < n → m / n = q := @HolLightLean.hol_opam.thm_DIV_UNIQ holTheoryInst

theorem hol_MOD_0 : 
  ∀ (n : ℕ), (0 : ℕ) % n = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_0 holTheoryInst

theorem hol_DIV_0 : 
  ∀ (n : ℕ), (0 : ℕ) / n = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIV_0 holTheoryInst

theorem hol_MOD_MULT : 
  ∀ (m n : ℕ), m * n % m = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_MULT holTheoryInst

theorem hol_DIV_MULT : 
  ∀ (m n : ℕ), ¬m = (0 : ℕ) → m * n / m = n := @HolLightLean.hol_opam.thm_DIV_MULT holTheoryInst

theorem hol_MOD_LT : 
  ∀ (m n : ℕ), m < n → m % n = m := @HolLightLean.hol_opam.thm_MOD_LT holTheoryInst

theorem hol_MOD_EQ_SELF : 
  ∀ (m n : ℕ), (m % n = m) = (n = (0 : ℕ) ∨ m < n) := @HolLightLean.hol_opam.thm_MOD_EQ_SELF holTheoryInst

theorem hol_MOD_CASES : 
  ∀ (n p : ℕ),
    n < ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * p → n % p = if n < p then n else n - p := @HolLightLean.hol_opam.thm_MOD_CASES holTheoryInst

theorem hol_MOD_ADD_CASES : 
  ∀ (m n p : ℕ), m < p ∧ n < p → (m + n) % p = if m + n < p then m + n else m + n - p := @HolLightLean.hol_opam.thm_MOD_ADD_CASES holTheoryInst

theorem hol_MOD_EQ : 
  ∀ (m n p q : ℕ), m = n + q * p → m % p = n % p := @HolLightLean.hol_opam.thm_MOD_EQ holTheoryInst

theorem hol_DIV_LE : 
  ∀ (m n : ℕ), m / n ≤ m := @HolLightLean.hol_opam.thm_DIV_LE holTheoryInst

theorem hol_DIV_MUL_LE : 
  ∀ (m n : ℕ), n * (m / n) ≤ m := @HolLightLean.hol_opam.thm_DIV_MUL_LE holTheoryInst

theorem hol_MOD_LE_TWICE : 
  ∀ (m n : ℕ), (0 : ℕ) < m ∧ m ≤ n → ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * (n % m) ≤ n := @HolLightLean.hol_opam.thm_MOD_LE_TWICE holTheoryInst

theorem hol_MOD_1 : 
  ∀ (n : ℕ), n % ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_1 holTheoryInst

theorem hol_DIV_1 : 
  ∀ (n : ℕ), n / ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = n := @HolLightLean.hol_opam.thm_DIV_1 holTheoryInst

theorem hol_DIV_LT : 
  ∀ (m n : ℕ), m < n → m / n = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIV_LT holTheoryInst

theorem hol_MOD_MOD : 
  ∀ (m n p : ℕ), m % (n * p) % n = m % n := @HolLightLean.hol_opam.thm_MOD_MOD holTheoryInst

theorem hol_MOD_MOD_REFL : 
  ∀ (m n : ℕ), m % n % n = m % n := @HolLightLean.hol_opam.thm_MOD_MOD_REFL holTheoryInst

theorem hol_MOD_MOD_LE : 
  ∀ (m n p : ℕ), ¬n = (0 : ℕ) ∧ n ≤ p → m % n % p = m % n := @HolLightLean.hol_opam.thm_MOD_MOD_LE holTheoryInst

theorem hol_MOD_EVEN_2 : 
  ∀ (m n : ℕ),
    Even n →
      m % n % ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        m % ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_MOD_EVEN_2 holTheoryInst

theorem hol_DIV_MULT2 : 
  ∀ (m n p : ℕ), ¬m = (0 : ℕ) → m * n / (m * p) = n / p := @HolLightLean.hol_opam.thm_DIV_MULT2 holTheoryInst

theorem hol_MOD_MULT2 : 
  ∀ (m n p : ℕ), m * n % (m * p) = m * (n % p) := @HolLightLean.hol_opam.thm_MOD_MULT2 holTheoryInst

theorem hol_MOD_EXISTS : 
  ∀ (m n : ℕ), (∃ (q : ℕ), m = n * q) = if n = (0 : ℕ) then m = (0 : ℕ) else m % n = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_EXISTS holTheoryInst

theorem hol_LE_RDIV_EQ : 
  ∀ (a b n : ℕ), ¬a = (0 : ℕ) → (n ≤ b / a) = (a * n ≤ b) := @HolLightLean.hol_opam.thm_LE_RDIV_EQ holTheoryInst

theorem hol_RDIV_LT_EQ : 
  ∀ (a b n : ℕ), ¬a = (0 : ℕ) → (b / a < n) = (b < a * n) := @HolLightLean.hol_opam.thm_RDIV_LT_EQ holTheoryInst

theorem hol_LE_LDIV_EQ : 
  ∀ (a b n : ℕ), ¬a = (0 : ℕ) → (b / a ≤ n) = (b < a * (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_LE_LDIV_EQ holTheoryInst

theorem hol_LDIV_LT_EQ : 
  ∀ (a b n : ℕ), ¬a = (0 : ℕ) → (n < b / a) = (a * (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ≤ b) := @HolLightLean.hol_opam.thm_LDIV_LT_EQ holTheoryInst

theorem hol_LE_LDIV : 
  ∀ (a b n : ℕ), ¬a = (0 : ℕ) ∧ b ≤ a * n → b / a ≤ n := @HolLightLean.hol_opam.thm_LE_LDIV holTheoryInst

theorem hol_DIV_MONO : 
  ∀ (m n p : ℕ), m ≤ n → m / p ≤ n / p := @HolLightLean.hol_opam.thm_DIV_MONO holTheoryInst

theorem hol_DIV_MONO_LT : 
  ∀ (m n p : ℕ), ¬p = (0 : ℕ) ∧ m + p ≤ n → m / p < n / p := @HolLightLean.hol_opam.thm_DIV_MONO_LT holTheoryInst

theorem hol_DIV_EQ_0 : 
  ∀ (m n : ℕ), ¬n = (0 : ℕ) → (m / n = (0 : ℕ)) = (m < n) := @HolLightLean.hol_opam.thm_DIV_EQ_0 holTheoryInst

theorem hol_MOD_DIV_EQ_0 : 
  ∀ (m n : ℕ), ¬n = (0 : ℕ) → m % n / n = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_DIV_EQ_0 holTheoryInst

theorem hol_MOD_EQ_0 : 
  ∀ (m n : ℕ), (m % n = (0 : ℕ)) = ∃ (q : ℕ), m = q * n := @HolLightLean.hol_opam.thm_MOD_EQ_0 holTheoryInst

theorem hol_DIV_EQ_SELF : 
  ∀ (m n : ℕ), (m / n = m) = (m = (0 : ℕ) ∨ n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_DIV_EQ_SELF holTheoryInst

theorem hol_MOD_REFL : 
  ∀ (n : ℕ), n % n = (0 : ℕ) := @HolLightLean.hol_opam.thm_MOD_REFL holTheoryInst

theorem hol_EVEN_MOD : 
  ∀ (n : ℕ), Even n = (n % ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (0 : ℕ)) := @HolLightLean.hol_opam.thm_EVEN_MOD holTheoryInst

theorem hol_ODD_MOD : 
  ∀ (n : ℕ), Odd n = (n % ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_ODD_MOD holTheoryInst

theorem hol_MOD_2_CASES : 
  ∀ (n : ℕ),
    n % ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      if Even n then (0 : ℕ) else (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_MOD_2_CASES holTheoryInst

theorem hol_EVEN_MOD_EVEN : 
  ∀ (m n : ℕ), Even n → Even (m % n) = Even m := @HolLightLean.hol_opam.thm_EVEN_MOD_EVEN holTheoryInst

theorem hol_ODD_MOD_EVEN : 
  ∀ (m n : ℕ), Even n → Odd (m % n) = Odd m := @HolLightLean.hol_opam.thm_ODD_MOD_EVEN holTheoryInst

theorem hol_HALF_DOUBLE : 
  (∀ (n : ℕ),
      ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n /
          ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        n) ∧
    ∀ (n : ℕ),
      n * ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) /
          ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        n := @HolLightLean.hol_opam.thm_HALF_DOUBLE holTheoryInst

theorem hol_DOUBLE_HALF : 
  (∀ (n : ℕ),
      Even n →
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) *
            (n / ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) =
          n) ∧
    ∀ (n : ℕ),
      Even n →
        n / ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) *
            ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
          n := @HolLightLean.hol_opam.thm_DOUBLE_HALF holTheoryInst

theorem hol_MOD_MULT_RMOD : 
  ∀ (m n p : ℕ), m * (p % n) % n = m * p % n := @HolLightLean.hol_opam.thm_MOD_MULT_RMOD holTheoryInst

theorem hol_MOD_MULT_LMOD : 
  ∀ (m n p : ℕ), m % n * p % n = m * p % n := @HolLightLean.hol_opam.thm_MOD_MULT_LMOD holTheoryInst

theorem hol_MOD_MULT_MOD2 : 
  ∀ (m n p : ℕ), m % n * (p % n) % n = m * p % n := @HolLightLean.hol_opam.thm_MOD_MULT_MOD2 holTheoryInst

theorem hol_MOD_EXP_MOD : 
  ∀ (m n p : ℕ), (m % n) ^ p % n = m ^ p % n := @HolLightLean.hol_opam.thm_MOD_EXP_MOD holTheoryInst

theorem hol_MOD_MULT_ADD : 
  (∀ (m n p : ℕ), (m * n + p) % n = p % n) ∧
    (∀ (m n p : ℕ), (n * m + p) % n = p % n) ∧
      (∀ (m n p : ℕ), (p + m * n) % n = p % n) ∧ ∀ (m n p : ℕ), (p + n * m) % n = p % n := @HolLightLean.hol_opam.thm_MOD_MULT_ADD holTheoryInst

theorem hol_DIV_MULT_ADD : 
  (∀ (a b n : ℕ), ¬n = (0 : ℕ) → (a * n + b) / n = a + b / n) ∧
    (∀ (a b n : ℕ), ¬n = (0 : ℕ) → (n * a + b) / n = a + b / n) ∧
      (∀ (a b n : ℕ), ¬n = (0 : ℕ) → (b + a * n) / n = b / n + a) ∧
        ∀ (a b n : ℕ), ¬n = (0 : ℕ) → (b + n * a) / n = b / n + a := @HolLightLean.hol_opam.thm_DIV_MULT_ADD holTheoryInst

theorem hol_MOD_ADD_MOD : 
  ∀ (a b n : ℕ), (a % n + b % n) % n = (a + b) % n := @HolLightLean.hol_opam.thm_MOD_ADD_MOD holTheoryInst

theorem hol_DIV_ADD_MOD : 
  ∀ (a b n : ℕ), ¬n = (0 : ℕ) → ((a + b) % n = a % n + b % n) = ((a + b) / n = a / n + b / n) := @HolLightLean.hol_opam.thm_DIV_ADD_MOD holTheoryInst

theorem hol_MOD_ADD_EQ_EQ : 
  ∀ (n x y : ℕ), ((x + y) % n = x % n + y % n) = (n = (0 : ℕ) ∨ x % n + y % n < n) := @HolLightLean.hol_opam.thm_MOD_ADD_EQ_EQ holTheoryInst

theorem hol_DIV_ADD_EQ_EQ : 
  ∀ (n x y : ℕ), ((x + y) / n = x / n + y / n) = (n = (0 : ℕ) ∨ x % n + y % n < n) := @HolLightLean.hol_opam.thm_DIV_ADD_EQ_EQ holTheoryInst

theorem hol_DIV_ADD_EQ : 
  ∀ (n x y : ℕ), x % n + y % n < n → (x + y) / n = x / n + y / n := @HolLightLean.hol_opam.thm_DIV_ADD_EQ holTheoryInst

theorem hol_MOD_ADD_EQ : 
  ∀ (n x y : ℕ), x % n + y % n < n → (x + y) % n = x % n + y % n := @HolLightLean.hol_opam.thm_MOD_ADD_EQ holTheoryInst

theorem hol_DIV_REFL : 
  ∀ (n : ℕ), ¬n = (0 : ℕ) → n / n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_DIV_REFL holTheoryInst

theorem hol_MOD_LE : 
  ∀ (m n : ℕ), m % n ≤ m := @HolLightLean.hol_opam.thm_MOD_LE holTheoryInst

theorem hol_DIV_MONO2 : 
  ∀ (m n p : ℕ), ¬p = (0 : ℕ) ∧ p ≤ m → n / m ≤ n / p := @HolLightLean.hol_opam.thm_DIV_MONO2 holTheoryInst

theorem hol_DIV_LE_EXCLUSION : 
  ∀ (a b c d : ℕ), ¬b = (0 : ℕ) ∧ b * c < (a + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * d → c / d ≤ a / b := @HolLightLean.hol_opam.thm_DIV_LE_EXCLUSION holTheoryInst

theorem hol_DIV_EQ_EXCLUSION : 
  ∀ (a b c d : ℕ),
    b * c < (a + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * d ∧ a * d < (c + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * b → a / b = c / d := @HolLightLean.hol_opam.thm_DIV_EQ_EXCLUSION holTheoryInst

theorem hol_MULT_DIV_LE : 
  ∀ (m n p : ℕ), m * (n / p) ≤ m * n / p := @HolLightLean.hol_opam.thm_MULT_DIV_LE holTheoryInst

theorem hol_DIV_DIV : 
  ∀ (m n p : ℕ), m / n / p = m / (n * p) := @HolLightLean.hol_opam.thm_DIV_DIV holTheoryInst

theorem hol_DIV_MOD : 
  ∀ (m n p : ℕ), m / n % p = m % (n * p) / n := @HolLightLean.hol_opam.thm_DIV_MOD holTheoryInst

theorem hol_MOD_MULT_MOD : 
  ∀ (m n p : ℕ), m % (n * p) = n * (m / n % p) + m % n := @HolLightLean.hol_opam.thm_MOD_MULT_MOD holTheoryInst

theorem hol_MOD_MOD_EXP_MIN : 
  ∀ (x p m n : ℕ), x % p ^ m % p ^ n = x % p ^ min m n := @HolLightLean.hol_opam.thm_MOD_MOD_EXP_MIN holTheoryInst

theorem hol_MOD_EXP : 
  ∀ (m n p : ℕ), ¬m = (0 : ℕ) → m ^ n % m ^ p = if p ≤ n ∨ m = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) then (0 : ℕ) else m ^ n := @HolLightLean.hol_opam.thm_MOD_EXP holTheoryInst

theorem hol_DIV_EXP : 
  ∀ (m n p : ℕ),
    ¬m = (0 : ℕ) →
      m ^ n / m ^ p =
        if p ≤ n then m ^ (n - p) else if m = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) then (0 : ℕ) + (0 : ℕ) + (1 : ℕ) else (0 : ℕ) := @HolLightLean.hol_opam.thm_DIV_EXP holTheoryInst

theorem hol_FORALL_LT_MOD_THM : 
  ∀ (P : Set ℕ) (n : ℕ), (∀ a < n, P a) = (n = (0 : ℕ) ∨ ∀ (a : ℕ), P (a % n)) := @HolLightLean.hol_opam.thm_FORALL_LT_MOD_THM holTheoryInst

theorem hol_FORALL_MOD_THM : 
  ∀ (P : Set ℕ) (n : ℕ), ¬n = (0 : ℕ) → Eq (α := Prop) (∀ (a : ℕ), P (a % n)) (∀ a < n, P a) := @HolLightLean.hol_opam.thm_FORALL_MOD_THM holTheoryInst

theorem hol_EXISTS_LT_MOD_THM : 
  ∀ (P : Set ℕ) (n : ℕ), (∃ a < n, P a) = (¬n = (0 : ℕ) ∧ ∃ (a : ℕ), P (a % n)) := @HolLightLean.hol_opam.thm_EXISTS_LT_MOD_THM holTheoryInst

theorem hol_EXISTS_MOD_THM : 
  ∀ (P : Set ℕ) (n : ℕ), ¬n = (0 : ℕ) → (∃ (a : ℕ), P (a % n)) = ∃ a < n, P a := @HolLightLean.hol_opam.thm_EXISTS_MOD_THM holTheoryInst

theorem hol_PRE_ELIM_THM : 
  ∀ (n : ℕ) (P : Set ℕ), P (n - (1 : ℕ)) = ∀ (m : ℕ), n = m + (1 : ℕ) ∨ m = (0 : ℕ) ∧ n = (0 : ℕ) → P m := @HolLightLean.hol_opam.thm_PRE_ELIM_THM holTheoryInst

theorem hol_SUB_ELIM_THM : 
  ∀ (a b : ℕ) (P : Set ℕ), P (a - b) = ∀ (d : ℕ), a = b + d ∨ a < b ∧ d = (0 : ℕ) → P d := @HolLightLean.hol_opam.thm_SUB_ELIM_THM holTheoryInst

theorem hol_DIVMOD_ELIM_THM : 
  ∀ (m n : ℕ) (P : ℕ → ℕ → Prop),
    P (m / n) (m % n) = ∀ (q r : ℕ), n = (0 : ℕ) ∧ q = (0 : ℕ) ∧ r = m ∨ m = q * n + r ∧ r < n → P q r := @HolLightLean.hol_opam.thm_DIVMOD_ELIM_THM holTheoryInst

theorem hol_minimal : 
  ∀ (P : Set ℕ), HolLightLean.hol_up_real_terms.minimal P = Classical.epsilon fun (n : ℕ) ↦ P n ∧ ∀ m < n, ¬P m := @HolLightLean.hol_opam.thm_minimal holTheoryInst

theorem hol_MINIMAL : 
  ∀ (P : Set ℕ),
    (∃ (n : ℕ), P n) =
      (P (HolLightLean.hol_up_real_terms.minimal P) ∧ ∀ m < HolLightLean.hol_up_real_terms.minimal P, ¬P m) := @HolLightLean.hol_opam.thm_MINIMAL holTheoryInst

theorem hol_MINIMAL_UNIQUE : 
  ∀ (P : Set ℕ) (n : ℕ), (P n ∧ ∀ m < n, ¬P m) → HolLightLean.hol_up_real_terms.minimal P = n := @HolLightLean.hol_opam.thm_MINIMAL_UNIQUE holTheoryInst

theorem hol_LE_MINIMAL : 
  ∀ (P : Set ℕ) (n : ℕ), (∃ (r : ℕ), P r) → (n ≤ HolLightLean.hol_up_real_terms.minimal P) = ∀ (i : ℕ), P i → n ≤ i := @HolLightLean.hol_opam.thm_LE_MINIMAL holTheoryInst

theorem hol_MINIMAL_LE : 
  ∀ (P : Set ℕ) (n : ℕ), (∃ (r : ℕ), P r) → (HolLightLean.hol_up_real_terms.minimal P ≤ n) = ∃ i ≤ n, P i := @HolLightLean.hol_opam.thm_MINIMAL_LE holTheoryInst

theorem hol_MINIMAL_UBOUND : 
  ∀ (P : Set ℕ) (n : ℕ), P n → HolLightLean.hol_up_real_terms.minimal P ≤ n := @HolLightLean.hol_opam.thm_MINIMAL_UBOUND holTheoryInst

theorem hol_MINIMAL_LBOUND : 
  ∀ (P : Set ℕ) (n : ℕ), ((∃ (r : ℕ), P r) ∧ ∀ m < n, ¬P m) → n ≤ HolLightLean.hol_up_real_terms.minimal P := @HolLightLean.hol_opam.thm_MINIMAL_LBOUND holTheoryInst

theorem hol_MINIMAL_MONO : 
  ∀ (P Q : Set ℕ),
    ((∃ (n : ℕ), P n) ∧ ∀ (n : ℕ), P n → Q n) →
      HolLightLean.hol_up_real_terms.minimal Q ≤ HolLightLean.hol_up_real_terms.minimal P := @HolLightLean.hol_opam.thm_MINIMAL_MONO holTheoryInst

theorem hol_TRANSITIVE_STEPWISE_LT_EQ : 
  ∀ (R' : ℕ → ℕ → Prop),
    (∀ (x y z : ℕ), R' x y ∧ R' y z → R' x z) →
      Eq (α := Prop) (∀ (m n : ℕ), m < n → R' m n) (∀ (n : ℕ), R' n (n + (1 : ℕ))) := @HolLightLean.hol_opam.thm_TRANSITIVE_STEPWISE_LT_EQ holTheoryInst

theorem hol_TRANSITIVE_STEPWISE_LT : 
  ∀ (R' : ℕ → ℕ → Prop),
    ((∀ (x y z : ℕ), R' x y ∧ R' y z → R' x z) ∧ ∀ (n : ℕ), R' n (n + (1 : ℕ))) → ∀ (m n : ℕ), m < n → R' m n := @HolLightLean.hol_opam.thm_TRANSITIVE_STEPWISE_LT holTheoryInst

theorem hol_TRANSITIVE_STEPWISE_LE_EQ : 
  ∀ (R' : ℕ → ℕ → Prop),
    ((∀ (x : ℕ), R' x x) ∧ ∀ (x y z : ℕ), R' x y ∧ R' y z → R' x z) →
      Eq (α := Prop) (∀ (m n : ℕ), m ≤ n → R' m n) (∀ (n : ℕ), R' n (n + (1 : ℕ))) := @HolLightLean.hol_opam.thm_TRANSITIVE_STEPWISE_LE_EQ holTheoryInst

theorem hol_TRANSITIVE_STEPWISE_LE : 
  ∀ (R' : ℕ → ℕ → Prop),
    ((∀ (x : ℕ), R' x x) ∧ (∀ (x y z : ℕ), R' x y ∧ R' y z → R' x z) ∧ ∀ (n : ℕ), R' n (n + (1 : ℕ))) →
      ∀ (m n : ℕ), m ≤ n → R' m n := @HolLightLean.hol_opam.thm_TRANSITIVE_STEPWISE_LE holTheoryInst

theorem hol_DEPENDENT_CHOICE_FIXED : 
  ∀ {A : Type} [Nonempty A] (P : ℕ → A → Prop) (R' : ℕ → A → A → Prop) (a : A),
    (P (0 : ℕ) a ∧ ∀ (n : ℕ) (x : A), P n x → ∃ (y : A), P (n + (1 : ℕ)) y ∧ R' n x y) →
      ∃ (f : ℕ → A), f (0 : ℕ) = a ∧ (∀ (n : ℕ), P n (f n)) ∧ ∀ (n : ℕ), R' n (f n) (f (n + (1 : ℕ))) := @HolLightLean.hol_opam.thm_DEPENDENT_CHOICE_FIXED holTheoryInst

theorem hol_DEPENDENT_CHOICE : 
  ∀ {A : Type} [Nonempty A] (P : ℕ → A → Prop) (R' : ℕ → A → A → Prop),
    ((∃ (a : A), P (0 : ℕ) a) ∧ ∀ (n : ℕ) (x : A), P n x → ∃ (y : A), P (n + (1 : ℕ)) y ∧ R' n x y) →
      ∃ (f : ℕ → A), (∀ (n : ℕ), P n (f n)) ∧ ∀ (n : ℕ), R' n (f n) (f (n + (1 : ℕ))) := @HolLightLean.hol_opam.thm_DEPENDENT_CHOICE holTheoryInst

theorem hol_WF : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    WellFounded lt2 = ∀ (P : Set A), (∃ (x : A), P x) → ∃ (x : A), P x ∧ ∀ (y : A), lt2 y x → ¬P y := @HolLightLean.hol_opam.thm_WF holTheoryInst

theorem hol_WF_EQ : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    WellFounded lt2 = ∀ (P : Set A), (∃ (x : A), P x) = ∃ (x : A), P x ∧ ∀ (y : A), lt2 y x → ¬P y := @HolLightLean.hol_opam.thm_WF_EQ holTheoryInst

theorem hol_WF_IND : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    WellFounded lt2 = ∀ (P : Set A), (∀ (x : A), (∀ (y : A), lt2 y x → P y) → P x) → ∀ (x : A), P x := @HolLightLean.hol_opam.thm_WF_IND holTheoryInst

theorem hol_WF_DCHAIN : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    WellFounded lt2 = ¬∃ (s : ℕ → A), ∀ (n : ℕ), lt2 (s (n + (1 : ℕ))) (s n) := @HolLightLean.hol_opam.thm_WF_DCHAIN holTheoryInst

theorem hol_WF_DHAIN_TRANSITIVE : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    (∀ (x y z : A), lt2 x y ∧ lt2 y z → lt2 x z) →
      WellFounded lt2 = ¬∃ (s : ℕ → A), ∀ (i j : ℕ), i < j → lt2 (s j) (s i) := @HolLightLean.hol_opam.thm_WF_DHAIN_TRANSITIVE holTheoryInst

theorem hol_WF_UREC : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop),
    WellFounded lt2 →
      ∀ (H : (A → B) → A → B),
        (∀ (f g : A → B) (x : A), (∀ (z : A), lt2 z x → f z = g z) → H f x = H g x) →
          ∀ (f g : A → B), ((∀ (x : A), f x = H f x) ∧ ∀ (x : A), g x = H g x) → f = g := @HolLightLean.hol_opam.thm_WF_UREC holTheoryInst

theorem hol_WF_UREC_WF : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    (∀ (H : Set A → A → Prop),
        (∀ (f g : Set A) (x : A), (∀ (z : A), lt2 z x → f z = g z) → H f x = H g x) →
          ∀ (f g : Set A), ((∀ (x : A), f x = H f x) ∧ ∀ (x : A), g x = H g x) → f = g) →
      WellFounded lt2 := @HolLightLean.hol_opam.thm_WF_UREC_WF holTheoryInst

theorem hol_WF_REC_INVARIANT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop),
    WellFounded lt2 →
      ∀ (H : (A → B) → A → B) (S' : A → B → Prop),
        (∀ (f g : A → B) (x : A), (∀ (z : A), lt2 z x → f z = g z ∧ S' z (f z)) → H f x = H g x ∧ S' x (H f x)) →
          ∃ (f : A → B), ∀ (x : A), f x = H f x := @HolLightLean.hol_opam.thm_WF_REC_INVARIANT holTheoryInst

theorem hol_WF_REC : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop),
    WellFounded lt2 →
      ∀ (H : (A → B) → A → B),
        (∀ (f g : A → B) (x : A), (∀ (z : A), lt2 z x → f z = g z) → H f x = H g x) →
          ∃ (f : A → B), ∀ (x : A), f x = H f x := @HolLightLean.hol_opam.thm_WF_REC holTheoryInst

theorem hol_WF_REC_WF : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    (∀ (H : (A → ℕ) → A → ℕ),
        (∀ (f g : A → ℕ) (x : A), (∀ (z : A), lt2 z x → f z = g z) → H f x = H g x) →
          ∃ (f : A → ℕ), ∀ (x : A), f x = H f x) →
      WellFounded lt2 := @HolLightLean.hol_opam.thm_WF_REC_WF holTheoryInst

theorem hol_WF_EREC : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop),
    WellFounded lt2 →
      ∀ (H : (A → B) → A → B),
        (∀ (f g : A → B) (x : A), (∀ (z : A), lt2 z x → f z = g z) → H f x = H g x) →
          ∃! f : A → B, ∀ (x : A), f x = H f x := @HolLightLean.hol_opam.thm_WF_EREC holTheoryInst

theorem hol_WF_REC_EXISTS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop),
    WellFounded lt2 →
      ∀ (P : (A → B) → A → B → Prop),
        ((∀ (f g : A → B) (x : A) (y : B), (∀ (z : A), lt2 z x → f z = g z) → P f x y = P g x y) ∧
            ∀ (f : A → B) (x : A), (∀ (z : A), lt2 z x → P f z (f z)) → ∃ (y : B), P f x y) →
          ∃ (f : A → B), ∀ (x : A), P f x (f x) := @HolLightLean.hol_opam.thm_WF_REC_EXISTS holTheoryInst

theorem hol_WF_SUBSET : 
  ∀ {A : Type} [Nonempty A] (lt2 lt3 : A → A → Prop),
    (∀ (x y : A), lt2 x y → lt3 x y) ∧ WellFounded lt3 → WellFounded lt2 := @HolLightLean.hol_opam.thm_WF_SUBSET holTheoryInst

theorem hol_WF_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop) (P : Set A),
    WellFounded lt2 → WellFounded fun (x y : A) ↦ P x ∧ P y ∧ lt2 x y := @HolLightLean.hol_opam.thm_WF_RESTRICT holTheoryInst

theorem hol_WF_MEASURE_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : B → B → Prop) (m : A → B),
    WellFounded lt2 → WellFounded fun (x x' : A) ↦ lt2 (m x) (m x') := @HolLightLean.hol_opam.thm_WF_MEASURE_GEN holTheoryInst

theorem hol_WF_LEX_DEPENDENT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : A → A → Prop) (S' : A → B → B → Prop),
    (WellFounded R' ∧ ∀ (a : A), WellFounded (S' a)) →
      WellFounded (α := A × B)
        (Classical.epsilon fun (f : A × B → A × B → Prop) ↦
          ∀ (r1 : A) (s1 : B),
            f (r1, s1) =
              Classical.epsilon fun (f' : Set (A × B)) ↦
                ∀ (r2 : A) (s2 : B), f' (r2, s2) = (R' r1 r2 ∨ r1 = r2 ∧ S' r1 s1 s2)) := @HolLightLean.hol_opam.thm_WF_LEX_DEPENDENT holTheoryInst

theorem hol_WF_LEX : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : A → A → Prop) (S' : B → B → Prop),
    WellFounded R' ∧ WellFounded S' →
      WellFounded (α := A × B)
        (Classical.epsilon fun (f : A × B → A × B → Prop) ↦
          ∀ (r1 : A) (s1 : B),
            f (r1, s1) =
              Classical.epsilon fun (f' : Set (A × B)) ↦
                ∀ (r2 : A) (s2 : B), f' (r2, s2) = (R' r1 r2 ∨ r1 = r2 ∧ S' s1 s2)) := @HolLightLean.hol_opam.thm_WF_LEX holTheoryInst

theorem hol_WF_POINTWISE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop) (lt3 : B → B → Prop),
    WellFounded lt2 ∧ WellFounded lt3 →
      WellFounded (α := A × B)
        (Classical.epsilon fun (f : A × B → A × B → Prop) ↦
          ∀ (x1 : A) (y1 : B),
            f (x1, y1) =
              Classical.epsilon fun (f' : Set (A × B)) ↦ ∀ (x2 : A) (y2 : B), f' (x2, y2) = (lt2 x1 x2 ∧ lt3 y1 y2)) := @HolLightLean.hol_opam.thm_WF_POINTWISE holTheoryInst

theorem hol_WF_num : 
  WellFounded fun (x1 x2 : ℕ) ↦ x1 < x2 := @HolLightLean.hol_opam.thm_WF_num holTheoryInst

theorem hol_WF_REC_num : 
  ∀ {A : Type} [Nonempty A] (H : (ℕ → A) → ℕ → A),
    (∀ (f g : ℕ → A) (n : ℕ), (∀ m < n, f m = g m) → H f n = H g n) → ∃ (f : ℕ → A), ∀ (n : ℕ), f n = H f n := @HolLightLean.hol_opam.thm_WF_REC_num holTheoryInst

theorem hol_MEASURE : 
  ∀ {A : Type} [Nonempty A] (m : A → ℕ), Eq (α := A → A → Prop) (fun (x y : A) ↦ m x < m y) fun (x y : A) ↦ m x < m y := @HolLightLean.hol_opam.thm_MEASURE holTheoryInst

theorem hol_WF_MEASURE : 
  ∀ {A : Type} [Nonempty A] (m : A → ℕ), WellFounded fun (x y : A) ↦ m x < m y := @HolLightLean.hol_opam.thm_WF_MEASURE holTheoryInst

theorem hol_MEASURE_LE : 
  ∀ {A : Type} [Nonempty A] (a b : A) (m : A → ℕ), (∀ (y : A), m y < m a → m y < m b) = (m a ≤ m b) := @HolLightLean.hol_opam.thm_MEASURE_LE holTheoryInst

theorem hol_WF_ANTISYM : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop) (x y : A), WellFounded lt2 → ¬(lt2 x y ∧ lt2 y x) := @HolLightLean.hol_opam.thm_WF_ANTISYM holTheoryInst

theorem hol_WF_REFL : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop) (x : A), WellFounded lt2 → ¬lt2 x x := @HolLightLean.hol_opam.thm_WF_REFL holTheoryInst

theorem hol_WF_FALSE : 
  ∀ {A : Type} [Nonempty A], WellFounded fun (x y : A) ↦ False := @HolLightLean.hol_opam.thm_WF_FALSE holTheoryInst

theorem hol_MINIMAL_BAD_SEQUENCE : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop) (bad : Set (ℕ → A)),
    (WellFounded lt2 ∧
        (∀ (x : ℕ → A), ¬bad x → ∃ (n : ℕ), ∀ (y : ℕ → A), (∀ k < n, y k = x k) → ¬bad y) ∧ ∃ (x : ℕ → A), bad x) →
      ∃ (y : ℕ → A), bad y ∧ ∀ (z : ℕ → A) (n : ℕ), (bad z ∧ ∀ k < n, z k = y k) → ¬lt2 (z n) (y n) := @HolLightLean.hol_opam.thm_MINIMAL_BAD_SEQUENCE holTheoryInst

theorem hol_WF_REC_TAIL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set A) (g : A → A) (h : A → B),
    ∃ (f : A → B), ∀ (x : A), f x = if P x then f (g x) else h x := @HolLightLean.hol_opam.thm_WF_REC_TAIL holTheoryInst

theorem hol_WF_REC_TAIL_GENERAL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (lt2 : A → A → Prop) (P : (A → B) → A → Prop) (G : (A → B) → A → A)
    (H : (A → B) → A → B),
    (WellFounded lt2 ∧
        (∀ (f g : A → B) (x : A), (∀ (z : A), lt2 z x → f z = g z) → P f x = P g x ∧ G f x = G g x ∧ H f x = H g x) ∧
          (∀ (f g : A → B) (x : A), (∀ (z : A), lt2 z x → f z = g z) → H f x = H g x) ∧
            ∀ (f : A → B) (x y : A), P f x ∧ lt2 y (G f x) → lt2 y x) →
      ∃ (f : A → B), ∀ (x : A), f x = if P f x then f (G f x) else H f x := @HolLightLean.hol_opam.thm_WF_REC_TAIL_GENERAL holTheoryInst

theorem hol_ARITH_ZERO : 
  (0 : ℕ) = (0 : ℕ) ∧ (0 : ℕ) + (0 : ℕ) = (0 : ℕ) := @HolLightLean.hol_opam.thm_ARITH_ZERO holTheoryInst

theorem hol_BIT0_0 : 
  (0 : ℕ) + (0 : ℕ) = (0 : ℕ) := @HolLightLean.hol_opam.thm_BIT0_0 holTheoryInst

theorem hol_BIT1_0 : 
  (0 : ℕ) + (0 : ℕ) + (1 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_BIT1_0 holTheoryInst

theorem hol_ARITH_SUC : 
  (∀ (n : ℕ), n + (1 : ℕ) = n + (1 : ℕ)) ∧
    (0 : ℕ) + (1 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∧
      (∀ (n : ℕ), n + n + (1 : ℕ) = n + n + (1 : ℕ)) ∧
        ∀ (n : ℕ), n + n + (1 : ℕ) + (1 : ℕ) = n + (1 : ℕ) + (n + (1 : ℕ)) := @HolLightLean.hol_opam.thm_ARITH_SUC holTheoryInst

theorem hol_ARITH_PRE : 
  (∀ (n : ℕ), n - (1 : ℕ) = n - (1 : ℕ)) ∧
    (0 : ℕ) - (1 : ℕ) = (0 : ℕ) ∧
      (∀ (n : ℕ), n + n - (1 : ℕ) = if n = (0 : ℕ) then (0 : ℕ) else n - (1 : ℕ) + (n - (1 : ℕ)) + (1 : ℕ)) ∧
        ∀ (n : ℕ), n + n + (1 : ℕ) - (1 : ℕ) = n + n := @HolLightLean.hol_opam.thm_ARITH_PRE holTheoryInst

theorem hol_ARITH_ADD : 
  (∀ (m n : ℕ), m + n = m + n) ∧
    (0 : ℕ) + (0 : ℕ) = (0 : ℕ) ∧
      (∀ (n : ℕ), (0 : ℕ) + (n + n) = n + n) ∧
        (∀ (n : ℕ), (0 : ℕ) + (n + n + (1 : ℕ)) = n + n + (1 : ℕ)) ∧
          (∀ (n : ℕ), n + n + (0 : ℕ) = n + n) ∧
            (∀ (n : ℕ), n + n + (1 : ℕ) + (0 : ℕ) = n + n + (1 : ℕ)) ∧
              (∀ (m n : ℕ), m + m + (n + n) = m + n + (m + n)) ∧
                (∀ (m n : ℕ), m + m + (n + n + (1 : ℕ)) = m + n + (m + n) + (1 : ℕ)) ∧
                  (∀ (m n : ℕ), m + m + (1 : ℕ) + (n + n) = m + n + (m + n) + (1 : ℕ)) ∧
                    ∀ (m n : ℕ), m + m + (1 : ℕ) + (n + n + (1 : ℕ)) = m + n + (1 : ℕ) + (m + n + (1 : ℕ)) := @HolLightLean.hol_opam.thm_ARITH_ADD holTheoryInst

theorem hol_ARITH_MULT : 
  (∀ (m n : ℕ), m * n = m * n) ∧
    (0 : ℕ) * (0 : ℕ) = (0 : ℕ) ∧
      (∀ (n : ℕ), (0 : ℕ) * (n + n) = (0 : ℕ)) ∧
        (∀ (n : ℕ), (0 : ℕ) * (n + n + (1 : ℕ)) = (0 : ℕ)) ∧
          (∀ (n : ℕ), (n + n) * (0 : ℕ) = (0 : ℕ)) ∧
            (∀ (n : ℕ), (n + n + (1 : ℕ)) * (0 : ℕ) = (0 : ℕ)) ∧
              (∀ (m n : ℕ), (m + m) * (n + n) = m * n + m * n + (m * n + m * n)) ∧
                (∀ (m n : ℕ), (m + m) * (n + n + (1 : ℕ)) = m + m + (m * n + m * n + (m * n + m * n))) ∧
                  (∀ (m n : ℕ), (m + m + (1 : ℕ)) * (n + n) = n + n + (m * n + m * n + (m * n + m * n))) ∧
                    ∀ (m n : ℕ),
                      (m + m + (1 : ℕ)) * (n + n + (1 : ℕ)) =
                        m + m + (1 : ℕ) + (n + n + (m * n + m * n + (m * n + m * n))) := @HolLightLean.hol_opam.thm_ARITH_MULT holTheoryInst

theorem hol_ARITH_EXP : 
  (∀ (m n : ℕ), m ^ n = m ^ n) ∧
    (0 : ℕ) ^ (0 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∧
      (∀ (m : ℕ), (m + m) ^ (0 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧
        (∀ (m : ℕ), (m + m + (1 : ℕ)) ^ (0 : ℕ) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧
          (∀ (n : ℕ), (0 : ℕ) ^ (n + n) = (0 : ℕ) ^ n * (0 : ℕ) ^ n) ∧
            (∀ (m n : ℕ), (m + m) ^ (n + n) = (m + m) ^ n * (m + m) ^ n) ∧
              (∀ (m n : ℕ), (m + m + (1 : ℕ)) ^ (n + n) = (m + m + (1 : ℕ)) ^ n * (m + m + (1 : ℕ)) ^ n) ∧
                (∀ (n : ℕ), (0 : ℕ) ^ (n + n + (1 : ℕ)) = (0 : ℕ)) ∧
                  (∀ (m n : ℕ), (m + m) ^ (n + n + (1 : ℕ)) = (m + m) * ((m + m) ^ n * (m + m) ^ n)) ∧
                    ∀ (m n : ℕ),
                      (m + m + (1 : ℕ)) ^ (n + n + (1 : ℕ)) =
                        (m + m + (1 : ℕ)) * ((m + m + (1 : ℕ)) ^ n * (m + m + (1 : ℕ)) ^ n) := @HolLightLean.hol_opam.thm_ARITH_EXP holTheoryInst

theorem hol_ARITH_EVEN : 
  (∀ (n : ℕ), Even n = Even n) ∧
    Even (0 : ℕ) = True ∧ (∀ (n : ℕ), Even (n + n) = True) ∧ ∀ (n : ℕ), Even (n + n + (1 : ℕ)) = False := @HolLightLean.hol_opam.thm_ARITH_EVEN holTheoryInst

theorem hol_ARITH_ODD : 
  (∀ (n : ℕ), Odd n = Odd n) ∧
    Odd (0 : ℕ) = False ∧ (∀ (n : ℕ), Odd (n + n) = False) ∧ ∀ (n : ℕ), Odd (n + n + (1 : ℕ)) = True := @HolLightLean.hol_opam.thm_ARITH_ODD holTheoryInst

theorem hol_ARITH_LE : 
  (∀ (m n : ℕ), (m ≤ n) = (m ≤ n)) ∧
    ((0 : ℕ) ≤ (0 : ℕ)) = True ∧
      (∀ (n : ℕ), (n + n ≤ (0 : ℕ)) = (n ≤ (0 : ℕ))) ∧
        (∀ (n : ℕ), (n + n + (1 : ℕ) ≤ (0 : ℕ)) = False) ∧
          (∀ (n : ℕ), ((0 : ℕ) ≤ n + n) = True) ∧
            (∀ (n : ℕ), ((0 : ℕ) ≤ n + n + (1 : ℕ)) = True) ∧
              (∀ (m n : ℕ), (m + m ≤ n + n) = (m ≤ n)) ∧
                (∀ (m n : ℕ), (m + m ≤ n + n + (1 : ℕ)) = (m ≤ n)) ∧
                  (∀ (m n : ℕ), (m + m + (1 : ℕ) ≤ n + n) = (m < n)) ∧
                    ∀ (m n : ℕ), (m + m + (1 : ℕ) ≤ n + n + (1 : ℕ)) = (m ≤ n) := @HolLightLean.hol_opam.thm_ARITH_LE holTheoryInst

theorem hol_ARITH_LT : 
  (∀ (m n : ℕ), (m < n) = (m < n)) ∧
    ((0 : ℕ) < (0 : ℕ)) = False ∧
      (∀ (n : ℕ), (n + n < (0 : ℕ)) = False) ∧
        (∀ (n : ℕ), (n + n + (1 : ℕ) < (0 : ℕ)) = False) ∧
          (∀ (n : ℕ), ((0 : ℕ) < n + n) = ((0 : ℕ) < n)) ∧
            (∀ (n : ℕ), ((0 : ℕ) < n + n + (1 : ℕ)) = True) ∧
              (∀ (m n : ℕ), (m + m < n + n) = (m < n)) ∧
                (∀ (m n : ℕ), (m + m < n + n + (1 : ℕ)) = (m ≤ n)) ∧
                  (∀ (m n : ℕ), (m + m + (1 : ℕ) < n + n) = (m < n)) ∧
                    ∀ (m n : ℕ), (m + m + (1 : ℕ) < n + n + (1 : ℕ)) = (m < n) := @HolLightLean.hol_opam.thm_ARITH_LT holTheoryInst

theorem hol_ARITH_EQ : 
  (∀ (m n : ℕ), (m = n) = (m = n)) ∧
    ((0 : ℕ) = (0 : ℕ)) = True ∧
      (∀ (n : ℕ), (n + n = (0 : ℕ)) = (n = (0 : ℕ))) ∧
        (∀ (n : ℕ), (n + n + (1 : ℕ) = (0 : ℕ)) = False) ∧
          (∀ (n : ℕ), ((0 : ℕ) = n + n) = ((0 : ℕ) = n)) ∧
            (∀ (n : ℕ), ((0 : ℕ) = n + n + (1 : ℕ)) = False) ∧
              (∀ (m n : ℕ), (m + m = n + n) = (m = n)) ∧
                (∀ (m n : ℕ), (m + m = n + n + (1 : ℕ)) = False) ∧
                  (∀ (m n : ℕ), (m + m + (1 : ℕ) = n + n) = False) ∧
                    ∀ (m n : ℕ), (m + m + (1 : ℕ) = n + n + (1 : ℕ)) = (m = n) := @HolLightLean.hol_opam.thm_ARITH_EQ holTheoryInst

theorem hol_ARITH_SUB : 
  (∀ (m n : ℕ), m - n = m - n) ∧
    (0 : ℕ) - (0 : ℕ) = (0 : ℕ) ∧
      (∀ (n : ℕ), (0 : ℕ) - (n + n) = (0 : ℕ)) ∧
        (∀ (n : ℕ), (0 : ℕ) - (n + n + (1 : ℕ)) = (0 : ℕ)) ∧
          (∀ (n : ℕ), n + n - (0 : ℕ) = n + n) ∧
            (∀ (n : ℕ), n + n + (1 : ℕ) - (0 : ℕ) = n + n + (1 : ℕ)) ∧
              (∀ (m n : ℕ), m + m - (n + n) = m - n + (m - n)) ∧
                (∀ (m n : ℕ), m + m - (n + n + (1 : ℕ)) = m - n + (m - n) - (1 : ℕ)) ∧
                  (∀ (m n : ℕ), m + m + (1 : ℕ) - (n + n) = if n ≤ m then m - n + (m - n) + (1 : ℕ) else (0 : ℕ)) ∧
                    ∀ (m n : ℕ), m + m + (1 : ℕ) - (n + n + (1 : ℕ)) = m - n + (m - n) := @HolLightLean.hol_opam.thm_ARITH_SUB holTheoryInst

theorem hol_EXP_2_NE_0 : 
  ∀ (n : ℕ), ¬((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ^ n = (0 : ℕ) := @HolLightLean.hol_opam.thm_EXP_2_NE_0 holTheoryInst

theorem hol_INJ_INVERSE2 : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : A → B → C),
    (∀ (x1 : A) (y1 : B) (x2 : A) (y2 : B), (P x1 y1 = P x2 y2) = (x1 = x2 ∧ y1 = y2)) →
      ∃ (X : C → A) (Y : C → B), ∀ (x : A) (y : B), X (P x y) = x ∧ Y (P x y) = y := @HolLightLean.hol_opam.thm_INJ_INVERSE2 holTheoryInst

theorem hol_NUMPAIR : 
  ∀ (x y : ℕ),
    NUMPAIR x y =
      ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ^ x *
        (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * y + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_NUMPAIR holTheoryInst

theorem hol_NUMPAIR_INJ_LEMMA : 
  ∀ (x1 y1 x2 y2 : ℕ), NUMPAIR x1 y1 = NUMPAIR x2 y2 → x1 = x2 := @HolLightLean.hol_opam.thm_NUMPAIR_INJ_LEMMA holTheoryInst

theorem hol_NUMPAIR_INJ : 
  ∀ (x1 y1 x2 y2 : ℕ), (NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 ∧ y1 = y2) := @HolLightLean.hol_opam.thm_NUMPAIR_INJ holTheoryInst

theorem hol_NUMSUM : 
  ∀ (b : Prop) (x : ℕ),
    NUMSUM b x =
      if b then ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * x + (1 : ℕ)
      else ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * x := @HolLightLean.hol_opam.thm_NUMSUM holTheoryInst

theorem hol_NUMSUM_INJ : 
  ∀ (b1 : Prop) (x1 : ℕ) (b2 : Prop) (x2 : ℕ), (NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 ∧ x1 = x2) := @HolLightLean.hol_opam.thm_NUMSUM_INJ holTheoryInst

theorem hol_INJN : 
  ∀ {A : Type} [inst : Nonempty A] (m : ℕ), Eq (α := ℕ → A → Prop) (INJN m) fun (n : ℕ) (a : A) ↦ n = m := @HolLightLean.hol_opam.thm_INJN holTheoryInst

theorem hol_INJN_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (n1 n2 : ℕ), Eq (α := ℕ → A → Prop) (INJN n1) (INJN n2) = (n1 = n2) := @HolLightLean.hol_opam.thm_INJN_INJ holTheoryInst

theorem hol_INJA : 
  ∀ {A : Type} [inst : Nonempty A] (a : A), INJA a = fun (n : ℕ) (b : A) ↦ b = a := @HolLightLean.hol_opam.thm_INJA holTheoryInst

theorem hol_INJA_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (a1 a2 : A), (INJA a1 = INJA a2) = (a1 = a2) := @HolLightLean.hol_opam.thm_INJA_INJ holTheoryInst

theorem hol_INJF : 
  ∀ {A : Type} [inst : Nonempty A] (f : ℕ → ℕ → A → Prop), INJF f = fun (n : ℕ) ↦ f (NUMFST n) (NUMSND n) := @HolLightLean.hol_opam.thm_INJF holTheoryInst

theorem hol_INJF_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (f1 f2 : ℕ → ℕ → A → Prop), (INJF f1 = INJF f2) = (f1 = f2) := @HolLightLean.hol_opam.thm_INJF_INJ holTheoryInst

theorem hol_INJP : 
  ∀ {A : Type} [inst : Nonempty A] (f1 f2 : ℕ → A → Prop),
    INJP f1 f2 = fun (n : ℕ) (a : A) ↦ if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a := @HolLightLean.hol_opam.thm_INJP holTheoryInst

theorem hol_INJP_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (f1 f1' f2 f2' : ℕ → A → Prop), (INJP f1 f2 = INJP f1' f2') = (f1 = f1' ∧ f2 = f2') := @HolLightLean.hol_opam.thm_INJP_INJ holTheoryInst

theorem hol_ZCONSTR : 
  ∀ {A : Type} [inst : Nonempty A] (c : ℕ) (i : A) (r : ℕ → ℕ → A → Prop),
    ZCONSTR c i r = INJP (INJN (c + (1 : ℕ))) (INJP (INJA i) (INJF r)) := @HolLightLean.hol_opam.thm_ZCONSTR holTheoryInst

theorem hol_ZBOT : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := ℕ → A → Prop) ZBOT (INJP (INJN (0 : ℕ)) (Classical.epsilon fun (z : ℕ → A → Prop) ↦ True)) := @HolLightLean.hol_opam.thm_ZBOT holTheoryInst

theorem hol_ZCONSTR_ZBOT : 
  ∀ {A : Type} [inst : Nonempty A] (c : ℕ) (i : A) (r : ℕ → ℕ → A → Prop), ¬ZCONSTR c i r = ZBOT := @HolLightLean.hol_opam.thm_ZCONSTR_ZBOT holTheoryInst

theorem hol_ZRECSPACE_RULES : 
  ∀ {A : Type} [inst : Nonempty A],
    ZRECSPACE (α := A) ZBOT ∧
      ∀ (c : ℕ) (i : A) (r : ℕ → ℕ → A → Prop), (∀ (n : ℕ), ZRECSPACE (r n)) → ZRECSPACE (ZCONSTR c i r) := @HolLightLean.hol_opam.thm_ZRECSPACE_RULES holTheoryInst

theorem hol_ZRECSPACE_CASES : 
  ∀ {A : Type} [inst : Nonempty A] (a : ℕ → A → Prop),
    ZRECSPACE a = (a = ZBOT ∨ ∃ (c : ℕ) (i : A) (r : ℕ → ℕ → A → Prop), a = ZCONSTR c i r ∧ ∀ (n : ℕ), ZRECSPACE (r n)) := @HolLightLean.hol_opam.thm_ZRECSPACE_CASES holTheoryInst

theorem hol_ZRECSPACE_INDUCT : 
  ∀ {A : Type} [inst : Nonempty A] (ZRECSPACE' : Set (ℕ → A → Prop)),
    (ZRECSPACE' ZBOT ∧
        ∀ (c : ℕ) (i : A) (r : ℕ → ℕ → A → Prop), (∀ (n : ℕ), ZRECSPACE' (r n)) → ZRECSPACE' (ZCONSTR c i r)) →
      ∀ (a : ℕ → A → Prop), ZRECSPACE a → ZRECSPACE' a := @HolLightLean.hol_opam.thm_ZRECSPACE_INDUCT holTheoryInst

theorem hol_BOTTOM : 
  ∀ {A : Type} [inst : Nonempty A], Eq (α := recspace A) BOTTOM (_mk_rec ZBOT) := @HolLightLean.hol_opam.thm_BOTTOM holTheoryInst

theorem hol_CONSTR : 
  ∀ {A : Type} [inst : Nonempty A] (c : ℕ) (i : A) (r : ℕ → recspace A),
    CONSTR c i r = _mk_rec (ZCONSTR c i fun (n : ℕ) ↦ _dest_rec (r n)) := @HolLightLean.hol_opam.thm_CONSTR holTheoryInst

theorem hol_MK_REC_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (x y : ℕ → A → Prop),
    Eq (α := recspace A) (_mk_rec x) (_mk_rec y) → ZRECSPACE x ∧ ZRECSPACE y → x = y := @HolLightLean.hol_opam.thm_MK_REC_INJ holTheoryInst

theorem hol_DEST_REC_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (x y : recspace A), (_dest_rec x = _dest_rec y) = (x = y) := @HolLightLean.hol_opam.thm_DEST_REC_INJ holTheoryInst

theorem hol_CONSTR_BOT : 
  ∀ {A : Type} [inst : Nonempty A] (c : ℕ) (i : A) (r : ℕ → recspace A), ¬CONSTR c i r = BOTTOM := @HolLightLean.hol_opam.thm_CONSTR_BOT holTheoryInst

theorem hol_CONSTR_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (c1 : ℕ) (i1 : A) (r1 : ℕ → recspace A) (c2 : ℕ) (i2 : A) (r2 : ℕ → recspace A),
    (CONSTR c1 i1 r1 = CONSTR c2 i2 r2) = (c1 = c2 ∧ i1 = i2 ∧ r1 = r2) := @HolLightLean.hol_opam.thm_CONSTR_INJ holTheoryInst

theorem hol_CONSTR_IND : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set (recspace A)),
    (P BOTTOM ∧ ∀ (c : ℕ) (i : A) (r : ℕ → recspace A), (∀ (n : ℕ), P (r n)) → P (CONSTR c i r)) →
      ∀ (x : recspace A), P x := @HolLightLean.hol_opam.thm_CONSTR_IND holTheoryInst

theorem hol_CONSTR_REC : 
  ∀ {A B : Type} [inst : Nonempty A] [Nonempty B] (Fn : ℕ → A → (ℕ → recspace A) → (ℕ → B) → B),
    ∃ (f : recspace A → B), ∀ (c : ℕ) (i : A) (r : ℕ → recspace A), f (CONSTR c i r) = Fn c i r fun (n : ℕ) ↦ f (r n) := @HolLightLean.hol_opam.thm_CONSTR_REC holTheoryInst

theorem hol_FCONS : 
  ∀ {A : Type} [inst : Nonempty A],
    (∀ (a : A) (f : ℕ → A), FCONS a f (0 : ℕ) = a) ∧ ∀ (a : A) (f : ℕ → A) (n : ℕ), FCONS a f (n + (1 : ℕ)) = f n := @HolLightLean.hol_opam.thm_FCONS holTheoryInst

theorem hol_FCONS_UNDO : 
  ∀ {A : Type} [inst : Nonempty A] (f : ℕ → A), f = FCONS (f (0 : ℕ)) (f ∘ fun (x : ℕ) ↦ x + (1 : ℕ)) := @HolLightLean.hol_opam.thm_FCONS_UNDO holTheoryInst

theorem hol_FNIL : 
  ∀ {A : Type} [inst : Nonempty A] (n : ℕ), Eq (α := A) (FNIL n) (Classical.epsilon fun (x : A) ↦ True) := @HolLightLean.hol_opam.thm_FNIL holTheoryInst

theorem hol_sum_INDUCT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A ⊕ B)),
    ((∀ (a : A), P (Sum.inl a)) ∧ ∀ (a : B), P (Sum.inr a)) → ∀ (x : A ⊕ B), P x := @HolLightLean.hol_opam.thm_sum_INDUCT holTheoryInst

theorem hol_sum_RECURSION : 
  ∀ {A B Z' : Type} [Nonempty A] [Nonempty B] [Nonempty Z'] (INL' : A → Z') (INR' : B → Z'),
    ∃ (fn : A ⊕ B → Z'), (∀ (a : A), fn (Sum.inl a) = INL' a) ∧ ∀ (a : B), fn (Sum.inr a) = INR' a := @HolLightLean.hol_opam.thm_sum_RECURSION holTheoryInst

theorem hol_OUTL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (x : A), OUTL (B := B) (Sum.inl x) = x := @HolLightLean.hol_opam.thm_OUTL holTheoryInst

theorem hol_OUTR : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (y : B), OUTR (A := A) (Sum.inr y) = y := @HolLightLean.hol_opam.thm_OUTR holTheoryInst

theorem hol_option_INDUCT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Option A)), (P none ∧ ∀ (a : A), P (some a)) → ∀ (x : Option A), P x := @HolLightLean.hol_opam.thm_option_INDUCT holTheoryInst

theorem hol_option_RECURSION : 
  ∀ {A Z' : Type} [Nonempty A] [Nonempty Z'] (NONE' : Z') (SOME' : A → Z'),
    ∃ (fn : Option A → Z'), fn none = NONE' ∧ ∀ (a : A), fn (some a) = SOME' a := @HolLightLean.hol_opam.thm_option_RECURSION holTheoryInst

theorem hol_list_INDUCT : 
  ∀ {A : Type} [Nonempty A] (P : Set (List A)),
    (P [] ∧ ∀ (a0 : A) (a1 : List A), P a1 → P (a0 :: a1)) → ∀ (x : List A), P x := @HolLightLean.hol_opam.thm_list_INDUCT holTheoryInst

theorem hol_list_RECURSION : 
  ∀ {A Z' : Type} [Nonempty A] [Nonempty Z'] (NIL' : Z') (CONS' : A → List A → Z' → Z'),
    ∃ (fn : List A → Z'), fn [] = NIL' ∧ ∀ (a0 : A) (a1 : List A), fn (a0 :: a1) = CONS' a0 a1 (fn a1) := @HolLightLean.hol_opam.thm_list_RECURSION holTheoryInst

theorem hol_FORALL_OPTION_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set (Option A)), (∀ (x : Option A), P x) = (P none ∧ ∀ (a : A), P (some a)) := @HolLightLean.hol_opam.thm_FORALL_OPTION_THM holTheoryInst

theorem hol_EXISTS_OPTION_THM : 
  ∀ {A : Type} [Nonempty A] (P : Set (Option A)), (∃ (x : Option A), P x) = (P none ∨ ∃ (a : A), P (some a)) := @HolLightLean.hol_opam.thm_EXISTS_OPTION_THM holTheoryInst

theorem hol_option_DISTINCT : 
  ∀ {A : Type} [Nonempty A] (a : A), ¬some a = none := @HolLightLean.hol_opam.thm_option_DISTINCT holTheoryInst

theorem hol_option_INJ : 
  ∀ {A : Type} [Nonempty A] (a b : A), (some a = some b) = (a = b) := @HolLightLean.hol_opam.thm_option_INJ holTheoryInst

theorem hol_ISO : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (g : B → A) (f : A → B),
    ISO f g = ((∀ (x : B), f (g x) = x) ∧ ∀ (y : A), g (f y) = y) := @HolLightLean.hol_opam.thm_ISO holTheoryInst

theorem hol_ISO_REFL : 
  ∀ {A : Type} [inst : Nonempty A], ISO (fun (x : A) ↦ x) fun (x : A) ↦ x := @HolLightLean.hol_opam.thm_ISO_REFL holTheoryInst

theorem hol_ISO_FUN : 
  ∀ {A A' B B' : Type} [inst : Nonempty A] [inst_1 : Nonempty A'] [inst_2 : Nonempty B] [inst_3 : Nonempty B']
    (g : B → B') (f' : A' → A) (g' : B' → B) (f : A → A'),
    ISO f f' ∧ ISO g g' → ISO (fun (h : A → B) (a' : A') ↦ g (h (f' a'))) fun (h : A' → B') (a : A) ↦ g' (h (f a)) := @HolLightLean.hol_opam.thm_ISO_FUN holTheoryInst

theorem hol_ISO_USAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (g : B → A) (f : A → B),
    ISO f g →
      (∀ (P : Set A), Eq (α := Prop) (∀ (x : A), P x) (∀ (x : B), P (g x))) ∧
        (∀ (P : Set A), (∃ (x : A), P x) = ∃ (x : B), P (g x)) ∧ ∀ (a : A) (b : B), (a = g b) = (f a = b) := @HolLightLean.hol_opam.thm_ISO_USAGE holTheoryInst

theorem hol_HD : 
  ∀ {A : Type} [inst : Nonempty A] (t : List A) (h : A), HD (h :: t) = h := @HolLightLean.hol_opam.thm_HD holTheoryInst

theorem hol_TL : 
  ∀ {A : Type} [inst : Nonempty A] (h : A) (t : List A), TL (h :: t) = t := @HolLightLean.hol_opam.thm_TL holTheoryInst

theorem hol_APPEND : 
  ∀ {A : Type} [Nonempty A],
    (∀ (l : List A), List.append [] l = l) ∧ ∀ (h : A) (t l : List A), (h :: t).append l = h :: t.append l := @HolLightLean.hol_opam.thm_APPEND holTheoryInst

theorem hol_REVERSE : 
  ∀ {A : Type} [Nonempty A] (l : List A) (x : A),
    Eq (α := List A) (List.reverse []) [] ∧ (x :: l).reverse = l.reverse.append [x] := @HolLightLean.hol_opam.thm_REVERSE holTheoryInst

theorem hol_LENGTH : 
  ∀ {A : Type} [Nonempty A],
    List.length (α := A) [] = (0 : ℕ) ∧ ∀ (h : A) (t : List A), (h :: t).length = t.length + (1 : ℕ) := @HolLightLean.hol_opam.thm_LENGTH holTheoryInst

theorem hol_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → B), List.map f [] = []) ∧ ∀ (f : A → B) (h : A) (t : List A), List.map f (h :: t) = f h :: List.map f t := @HolLightLean.hol_opam.thm_MAP holTheoryInst

theorem hol_LAST : 
  ∀ {A : Type} [inst : Nonempty A] (h : A) (t : List A), LAST (h :: t) = if t = [] then h else LAST t := @HolLightLean.hol_opam.thm_LAST holTheoryInst

theorem hol_BUTLAST : 
  ∀ {A : Type} [Nonempty A] (h : A) (t : List A),
    Eq (α := List A) (List.dropLast []) [] ∧ (h :: t).dropLast = if t = [] then [] else h :: t.dropLast := @HolLightLean.hol_opam.thm_BUTLAST holTheoryInst

theorem hol_REPLICATE : 
  ∀ {A : Type} [Nonempty A] (n : ℕ) (x : A),
    List.replicate (0 : ℕ) x = [] ∧ List.replicate (n + (1 : ℕ)) x = x :: List.replicate n x := @HolLightLean.hol_opam.thm_REPLICATE holTheoryInst

theorem hol_NULL : 
  ∀ {A : Type} [Nonempty A] (h : A) (t : List A),
    (List.isEmpty (α := A) [] = true) = True ∧ ((h :: t).isEmpty = true) = False := @HolLightLean.hol_opam.thm_NULL holTheoryInst

theorem hol_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (h : A) (P : Set A) (t : List A), ALL P [] = True ∧ ALL P (h :: t) = (P h ∧ ALL P t) := @HolLightLean.hol_opam.thm_ALL holTheoryInst

theorem hol_EX : 
  ∀ {A : Type} [inst : Nonempty A] (h : A) (P : Set A) (t : List A), EX P [] = False ∧ EX P (h :: t) = (P h ∨ EX P t) := @HolLightLean.hol_opam.thm_EX holTheoryInst

theorem hol_ITLIST : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (h : A) (f : A → B → B) (t : List A) (b : B),
    List.foldr f b [] = b ∧ List.foldr f b (h :: t) = f h (List.foldr f b t) := @HolLightLean.hol_opam.thm_ITLIST holTheoryInst

theorem hol_MEM : 
  ∀ {A : Type} [Nonempty A] (h x : A) (t : List A),
    Membership.mem (γ := List A) [] x = False ∧ (x ∈ h :: t) = (x = h ∨ x ∈ t) := @HolLightLean.hol_opam.thm_MEM holTheoryInst

theorem hol_ALL2_DEF : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (h1' : A) (P : A → B → Prop) (t1 : List A) (l2 : List B),
    ALL2 P [] l2 = (l2 = []) ∧ ALL2 P (h1' :: t1) l2 = if l2 = [] then False else P h1' (HD l2) ∧ ALL2 P t1 (TL l2) := @HolLightLean.hol_opam.thm_ALL2_DEF holTheoryInst

theorem hol_ALL2 : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (h1' : A) (h2' : B) (P : A → B → Prop) (t1 : List A)
    (t2 : List B),
    ALL2 P [] [] = True ∧
      ALL2 P (h1' :: t1) [] = False ∧
        ALL2 P [] (h2' :: t2) = False ∧ ALL2 P (h1' :: t1) (h2' :: t2) = (P h1' h2' ∧ ALL2 P t1 t2) := @HolLightLean.hol_opam.thm_ALL2 holTheoryInst

theorem hol_MAP2_DEF : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (h1' : A) (f : A → B → C)
    (t1 : List A) (l : List B), MAP2 f [] l = [] ∧ MAP2 f (h1' :: t1) l = f h1' (HD l) :: MAP2 f t1 (TL l) := @HolLightLean.hol_opam.thm_MAP2_DEF holTheoryInst

theorem hol_MAP2 : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (h1' : A) (h2' : B) (f : A → B → C)
    (t1 : List A) (t2 : List B), MAP2 f [] [] = [] ∧ MAP2 f (h1' :: t1) (h2' :: t2) = f h1' h2' :: MAP2 f t1 t2 := @HolLightLean.hol_opam.thm_MAP2 holTheoryInst

theorem hol_EL : 
  ∀ {A : Type} [inst : Nonempty A] (n : ℕ) (l : List A), EL (0 : ℕ) l = HD l ∧ EL (n + (1 : ℕ)) l = EL n (TL l) := @HolLightLean.hol_opam.thm_EL holTheoryInst

theorem hol_FILTER : 
  ∀ {A : Type} [inst : Nonempty A] (h : A) (P : Set A) (t : List A),
    FILTER P [] = [] ∧ FILTER P (h :: t) = if P h then h :: FILTER P t else FILTER P t := @HolLightLean.hol_opam.thm_FILTER holTheoryInst

theorem hol_ASSOC : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (h : A × B) (a : A) (t : List (A × B)),
    ASSOC a (h :: t) = if h.1 = a then h.2 else ASSOC a t := @HolLightLean.hol_opam.thm_ASSOC holTheoryInst

theorem hol_ITLIST2_DEF : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (h1' : A) (f : A → B → C → C)
    (t1 : List A) (l2 : List B) (b : C),
    ITLIST2 f [] l2 b = b ∧ ITLIST2 f (h1' :: t1) l2 b = f h1' (HD l2) (ITLIST2 f t1 (TL l2) b) := @HolLightLean.hol_opam.thm_ITLIST2_DEF holTheoryInst

theorem hol_ITLIST2 : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (h1' : A) (h2' : B)
    (f : A → B → C → C) (t1 : List A) (t2 : List B) (b : C),
    ITLIST2 f [] [] b = b ∧ ITLIST2 f (h1' :: t1) (h2' :: t2) b = f h1' h2' (ITLIST2 f t1 t2 b) := @HolLightLean.hol_opam.thm_ITLIST2 holTheoryInst

theorem hol_ZIP_DEF : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (h1' : A) (t1 : List A) (l2 : List B),
    Eq (α := List (A × B)) (ZIP [] l2 : List (prod A B)) [] ∧ ZIP (h1' :: t1) l2 = (h1', HD l2) :: ZIP t1 (TL l2) := @HolLightLean.hol_opam.thm_ZIP_DEF holTheoryInst

theorem hol_ZIP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (h1' : A) (h2' : B) (t1 : List A) (t2 : List B),
    Eq (α := List (A × B)) (ZIP [] [] : List (prod A B)) [] ∧ ZIP (h1' :: t1) (h2' :: t2) = (h1', h2') :: ZIP t1 t2 := @HolLightLean.hol_opam.thm_ZIP holTheoryInst

theorem hol_ALLPAIRS : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (h : A) (f : A → B → Prop) (t : List A) (l : List B),
    ALLPAIRS f [] l = True ∧ ALLPAIRS f (h :: t) l = (ALL (f h) l ∧ ALLPAIRS f t l) := @HolLightLean.hol_opam.thm_ALLPAIRS holTheoryInst

theorem hol_PAIRWISE : 
  ∀ {A : Type} [inst : Nonempty A] (h : A) (r : A → A → Prop) (t : List A),
    List.Pairwise r [] = True ∧ List.Pairwise r (h :: t) = (ALL (r h) t ∧ List.Pairwise r t) := @HolLightLean.hol_opam.thm_PAIRWISE holTheoryInst

theorem hol_list_of_seq : 
  ∀ {A : Type} [Nonempty A] (s : ℕ → A) (n : ℕ),
    Eq (α := List A) (List.ofFn (n := (0 : ℕ)) fun (i : Fin (0 : ℕ)) ↦ s ↑i) [] ∧
      (List.ofFn (n := n + (1 : ℕ)) fun (i : Fin (n + (1 : ℕ))) ↦ s ↑i) =
        List.append (List.ofFn (n := n) fun (i : Fin n) ↦ s ↑i) [s n] := @HolLightLean.hol_opam.thm_list_of_seq holTheoryInst

theorem hol_NOT_CONS_NIL : 
  ∀ {A : Type} [Nonempty A] (h : A) (t : List A), ¬h :: t = [] := @HolLightLean.hol_opam.thm_NOT_CONS_NIL holTheoryInst

theorem hol_LAST_CLAUSES : 
  ∀ {A : Type} [inst : Nonempty A] (h k : A) (t : List A), LAST [h] = h ∧ LAST (h :: k :: t) = LAST (k :: t) := @HolLightLean.hol_opam.thm_LAST_CLAUSES holTheoryInst

theorem hol_APPEND_NIL : 
  ∀ {A : Type} [Nonempty A] (l : List A), l.append [] = l := @HolLightLean.hol_opam.thm_APPEND_NIL holTheoryInst

theorem hol_APPEND_ASSOC : 
  ∀ {A : Type} [Nonempty A] (l m n : List A), l.append (m.append n) = (l.append m).append n := @HolLightLean.hol_opam.thm_APPEND_ASSOC holTheoryInst

theorem hol_REVERSE_APPEND : 
  ∀ {A : Type} [Nonempty A] (l m : List A), (l.append m).reverse = m.reverse.append l.reverse := @HolLightLean.hol_opam.thm_REVERSE_APPEND holTheoryInst

theorem hol_REVERSE_REVERSE : 
  ∀ {A : Type} [Nonempty A] (l : List A), l.reverse.reverse = l := @HolLightLean.hol_opam.thm_REVERSE_REVERSE holTheoryInst

theorem hol_REVERSE_EQ_EMPTY : 
  ∀ {A : Type} [Nonempty A] (l : List A), (l.reverse = []) = (l = []) := @HolLightLean.hol_opam.thm_REVERSE_EQ_EMPTY holTheoryInst

theorem hol_CONS_11 : 
  ∀ {A : Type} [Nonempty A] (h1' h2' : A) (t1 t2 : List A), (h1' :: t1 = h2' :: t2) = (h1' = h2' ∧ t1 = t2) := @HolLightLean.hol_opam.thm_CONS_11 holTheoryInst

theorem hol_list_CASES : 
  ∀ {A : Type} [Nonempty A] (l : List A), l = [] ∨ ∃ (h : A) (t : List A), l = h :: t := @HolLightLean.hol_opam.thm_list_CASES holTheoryInst

theorem hol_LIST_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (l1 l2 : List A),
    (l1 = l2) = (l1.length = l2.length ∧ ∀ n < l2.length, EL n l1 = EL n l2) := @HolLightLean.hol_opam.thm_LIST_EQ holTheoryInst

theorem hol_LENGTH_APPEND : 
  ∀ {A : Type} [Nonempty A] (l m : List A), (l.append m).length = l.length + m.length := @HolLightLean.hol_opam.thm_LENGTH_APPEND holTheoryInst

theorem hol_MAP_APPEND : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (l1 l2 : List A),
    List.map f (l1.append l2) = (List.map f l1).append (List.map f l2) := @HolLightLean.hol_opam.thm_MAP_APPEND holTheoryInst

theorem hol_LENGTH_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (l : List A) (f : A → B), (List.map f l).length = l.length := @HolLightLean.hol_opam.thm_LENGTH_MAP holTheoryInst

theorem hol_LENGTH_EQ_NIL : 
  ∀ {A : Type} [Nonempty A] (l : List A), (l.length = (0 : ℕ)) = (l = []) := @HolLightLean.hol_opam.thm_LENGTH_EQ_NIL holTheoryInst

theorem hol_LENGTH_EQ_CONS : 
  ∀ {A : Type} [Nonempty A] (l : List A) (n : ℕ),
    (l.length = n + (1 : ℕ)) = ∃ (h : A) (t : List A), l = h :: t ∧ t.length = n := @HolLightLean.hol_opam.thm_LENGTH_EQ_CONS holTheoryInst

theorem hol_LENGTH_REVERSE : 
  ∀ {A : Type} [Nonempty A] (l : List A), l.reverse.length = l.length := @HolLightLean.hol_opam.thm_LENGTH_REVERSE holTheoryInst

theorem hol_MAP_o : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A → B) (g : B → C) (l : List A),
    List.map (g ∘ f) l = List.map g (List.map f l) := @HolLightLean.hol_opam.thm_MAP_o holTheoryInst

theorem hol_MAP_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [Nonempty B] (f g : A → B) (l : List A),
    ALL (fun (x : A) ↦ f x = g x) l → List.map f l = List.map g l := @HolLightLean.hol_opam.thm_MAP_EQ holTheoryInst

theorem hol_ALL_IMP : 
  ∀ {A : Type} [inst : Nonempty A] (P Q : Set A) (l : List A), (∀ (x : A), x ∈ l ∧ P x → Q x) ∧ ALL P l → ALL Q l := @HolLightLean.hol_opam.thm_ALL_IMP holTheoryInst

theorem hol_NOT_EX : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A), (¬EX P l) = ALL (fun (x : A) ↦ ¬P x) l := @HolLightLean.hol_opam.thm_NOT_EX holTheoryInst

theorem hol_NOT_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A), (¬ALL P l) = EX (fun (x : A) ↦ ¬P x) l := @HolLightLean.hol_opam.thm_NOT_ALL holTheoryInst

theorem hol_ALL_MAP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set B) (f : A → B) (l : List A),
    ALL P (List.map f l) = ALL (P ∘ f) l := @HolLightLean.hol_opam.thm_ALL_MAP holTheoryInst

theorem hol_ALL_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (R' P Q : Set A) (l : List A),
    (ALL R' l ∧ ∀ (x : A), R' x → P x = Q x) → ALL P l = ALL Q l := @HolLightLean.hol_opam.thm_ALL_EQ holTheoryInst

theorem hol_ALL_T : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ALL (fun (x : A) ↦ True) l := @HolLightLean.hol_opam.thm_ALL_T holTheoryInst

theorem hol_MAP_EQ_ALL2 : 
  ∀ {A B : Type} [inst : Nonempty A] [Nonempty B] (f : A → B) (l m : List A),
    ALL2 (fun (x y : A) ↦ f x = f y) l m → List.map f l = List.map f m := @HolLightLean.hol_opam.thm_MAP_EQ_ALL2 holTheoryInst

theorem hol_ALL2_MAP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : B → A → Prop) (f : A → B) (l : List A),
    ALL2 P (List.map f l) l = ALL (fun (a : A) ↦ P (f a) a) l := @HolLightLean.hol_opam.thm_ALL2_MAP holTheoryInst

theorem hol_MAP_EQ_DEGEN : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A) (f : A → A), ALL (fun (x : A) ↦ f x = x) l → List.map f l = l := @HolLightLean.hol_opam.thm_MAP_EQ_DEGEN holTheoryInst

theorem hol_ALL2_AND_RIGHT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (l : List A) (m : List B) (P : Set A) (Q : A → B → Prop),
    ALL2 (fun (x : A) (y : B) ↦ P x ∧ Q x y) l m = (ALL P l ∧ ALL2 Q l m) := @HolLightLean.hol_opam.thm_ALL2_AND_RIGHT holTheoryInst

theorem hol_ITLIST_APPEND : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → B) (a : B) (l1 l2 : List A),
    List.foldr f a (l1.append l2) = List.foldr f (List.foldr f a l2) l1 := @HolLightLean.hol_opam.thm_ITLIST_APPEND holTheoryInst

theorem hol_ITLIST_EXTRA : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : A) (b : B) (f : A → B → B) (l : List A),
    List.foldr f b (l.append [a]) = List.foldr f (f a b) l := @HolLightLean.hol_opam.thm_ITLIST_EXTRA holTheoryInst

theorem hol_ALL_MP : 
  ∀ {A : Type} [inst : Nonempty A] (P Q : Set A) (l : List A), ALL (fun (x : A) ↦ P x → Q x) l ∧ ALL P l → ALL Q l := @HolLightLean.hol_opam.thm_ALL_MP holTheoryInst

theorem hol_AND_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (P Q : Set A) (l : List A), (ALL P l ∧ ALL Q l) = ALL (fun (x : A) ↦ P x ∧ Q x) l := @HolLightLean.hol_opam.thm_AND_ALL holTheoryInst

theorem hol_EX_IMP : 
  ∀ {A : Type} [inst : Nonempty A] (P Q : Set A) (l : List A), (∀ (x : A), x ∈ l ∧ P x → Q x) ∧ EX P l → EX Q l := @HolLightLean.hol_opam.thm_EX_IMP holTheoryInst

theorem hol_ALL_MEM : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A), (∀ x ∈ l, P x) = ALL P l := @HolLightLean.hol_opam.thm_ALL_MEM holTheoryInst

theorem hol_LENGTH_REPLICATE : 
  ∀ {A : Type} [Nonempty A] (n : ℕ) (x : A), (List.replicate n x).length = n := @HolLightLean.hol_opam.thm_LENGTH_REPLICATE holTheoryInst

theorem hol_MEM_REPLICATE : 
  ∀ {A : Type} [Nonempty A] (n : ℕ) (x y : A), (x ∈ List.replicate n y) = (x = y ∧ ¬n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_MEM_REPLICATE holTheoryInst

theorem hol_EX_MAP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set B) (f : A → B) (l : List A),
    EX P (List.map f l) = EX (P ∘ f) l := @HolLightLean.hol_opam.thm_EX_MAP holTheoryInst

theorem hol_EXISTS_EX : 
  ∀ {A B : Type} [Nonempty A] [inst : Nonempty B] (P : A → B → Prop) (l : List B),
    (∃ (x : A), EX (P x) l) = EX (fun (s : B) ↦ ∃ (x : A), P x s) l := @HolLightLean.hol_opam.thm_EXISTS_EX holTheoryInst

theorem hol_FORALL_ALL : 
  ∀ {A B : Type} [Nonempty A] [inst : Nonempty B] (P : A → B → Prop) (l : List B),
    (∀ (x : A), ALL (P x) l) = ALL (fun (s : B) ↦ ∀ (x : A), P x s) l := @HolLightLean.hol_opam.thm_FORALL_ALL holTheoryInst

theorem hol_MEM_APPEND : 
  ∀ {A : Type} [Nonempty A] (x : A) (l1 l2 : List A), (x ∈ l1.append l2) = (x ∈ l1 ∨ x ∈ l2) := @HolLightLean.hol_opam.thm_MEM_APPEND holTheoryInst

theorem hol_MEM_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (y : B) (l : List A), (y ∈ List.map f l) = ∃ x ∈ l, y = f x := @HolLightLean.hol_opam.thm_MEM_MAP holTheoryInst

theorem hol_FILTER_APPEND : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l1 l2 : List A),
    FILTER P (l1.append l2) = (FILTER P l1).append (FILTER P l2) := @HolLightLean.hol_opam.thm_FILTER_APPEND holTheoryInst

theorem hol_FILTER_MAP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set B) (f : A → B) (l : List A),
    FILTER P (List.map f l) = List.map f (FILTER (P ∘ f) l) := @HolLightLean.hol_opam.thm_FILTER_MAP holTheoryInst

theorem hol_MEM_FILTER : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A) (x : A), (x ∈ FILTER P l) = (P x ∧ x ∈ l) := @HolLightLean.hol_opam.thm_MEM_FILTER holTheoryInst

theorem hol_LENGTH_FILTER : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A), (FILTER P l).length ≤ l.length := @HolLightLean.hol_opam.thm_LENGTH_FILTER holTheoryInst

theorem hol_EX_MEM : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A), (∃ (x : A), P x ∧ x ∈ l) = EX P l := @HolLightLean.hol_opam.thm_EX_MEM holTheoryInst

theorem hol_MAP_FST_ZIP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (l1 : List A) (l2 : List B),
    l1.length = l2.length → List.map Prod.fst (ZIP l1 l2) = l1 := @HolLightLean.hol_opam.thm_MAP_FST_ZIP holTheoryInst

theorem hol_MAP_SND_ZIP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (l1 : List A) (l2 : List B),
    l1.length = l2.length → List.map Prod.snd (ZIP l1 l2) = l2 := @HolLightLean.hol_opam.thm_MAP_SND_ZIP holTheoryInst

theorem hol_LENGTH_ZIP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (l1 : List A) (l2 : List B),
    l1.length = l2.length → List.length (α := A × B) (ZIP l1 l2 : List (prod A B)) = l2.length := @HolLightLean.hol_opam.thm_LENGTH_ZIP holTheoryInst

theorem hol_MEM_ASSOC : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (l : List (A × B)) (x : A),
    ((x, ASSOC x l) ∈ l) = (x ∈ List.map Prod.fst l) := @HolLightLean.hol_opam.thm_MEM_ASSOC holTheoryInst

theorem hol_ALL_APPEND : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l1 l2 : List A), ALL P (l1.append l2) = (ALL P l1 ∧ ALL P l2) := @HolLightLean.hol_opam.thm_ALL_APPEND holTheoryInst

theorem hol_MEM_EL : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ∀ n < l.length, EL n l ∈ l := @HolLightLean.hol_opam.thm_MEM_EL holTheoryInst

theorem hol_MEM_EXISTS_EL : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A) (x : A), (x ∈ l) = ∃ i < l.length, x = EL i l := @HolLightLean.hol_opam.thm_MEM_EXISTS_EL holTheoryInst

theorem hol_ALL_EL : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set A) (l : List A), (∀ i < l.length, P (EL i l)) = ALL P l := @HolLightLean.hol_opam.thm_ALL_EL holTheoryInst

theorem hol_ALL2_MAP2 : 
  ∀ {A B C D : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty D]
    (P : B → D → Prop) (f : A → B) (g : C → D) (l : List A) (m : List C),
    ALL2 P (List.map f l) (List.map g m) = ALL2 (fun (x : A) (y : C) ↦ P (f x) (g y)) l m := @HolLightLean.hol_opam.thm_ALL2_MAP2 holTheoryInst

theorem hol_AND_ALL2 : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P Q : A → B → Prop) (l : List A) (m : List B),
    (ALL2 P l m ∧ ALL2 Q l m) = ALL2 (fun (x : A) (y : B) ↦ P x y ∧ Q x y) l m := @HolLightLean.hol_opam.thm_AND_ALL2 holTheoryInst

theorem hol_ALLPAIRS_SYM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : A → B → Prop) (l : List A) (m : List B),
    ALLPAIRS P l m = ALLPAIRS (fun (x : B) (y : A) ↦ P y x) m l := @HolLightLean.hol_opam.thm_ALLPAIRS_SYM holTheoryInst

theorem hol_ALLPAIRS_MEM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : A → B → Prop) (l : List A) (m : List B),
    (∀ (x : A) (y : B), x ∈ l ∧ y ∈ m → P x y) = ALLPAIRS P l m := @HolLightLean.hol_opam.thm_ALLPAIRS_MEM holTheoryInst

theorem hol_ALLPAIRS_MAP : 
  ∀ {A B C D : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty D]
    (P : B → D → Prop) (f : A → B) (g : C → D) (l : List A) (m : List C),
    ALLPAIRS P (List.map f l) (List.map g m) = ALLPAIRS (fun (x : A) (y : C) ↦ P (f x) (g y)) l m := @HolLightLean.hol_opam.thm_ALLPAIRS_MAP holTheoryInst

theorem hol_ALLPAIRS_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (R' R'' : A → B → Prop) (l : List A) (m : List B) (P : Set A)
    (Q : Set B),
    (ALL P l ∧ ALL Q m ∧ ∀ (p : A) (q : B), P p ∧ Q q → R' p q = R'' p q) → ALLPAIRS R' l m = ALLPAIRS R'' l m := @HolLightLean.hol_opam.thm_ALLPAIRS_EQ holTheoryInst

theorem hol_ALL2_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (P : A → A → Prop) (l : List A), ALL2 P l l = ALL (fun (x : A) ↦ P x x) l := @HolLightLean.hol_opam.thm_ALL2_ALL holTheoryInst

theorem hol_APPEND_EQ_NIL : 
  ∀ {A : Type} [Nonempty A] (l m : List A), (l.append m = []) = (l = [] ∧ m = []) := @HolLightLean.hol_opam.thm_APPEND_EQ_NIL holTheoryInst

theorem hol_APPEND_LCANCEL : 
  ∀ {A : Type} [Nonempty A] (l1 l2 l3 : List A), (l1.append l2 = l1.append l3) = (l2 = l3) := @HolLightLean.hol_opam.thm_APPEND_LCANCEL holTheoryInst

theorem hol_APPEND_RCANCEL : 
  ∀ {A : Type} [Nonempty A] (l1 l2 l3 : List A), (l1.append l3 = l2.append l3) = (l1 = l2) := @HolLightLean.hol_opam.thm_APPEND_RCANCEL holTheoryInst

theorem hol_LENGTH_MAP2 : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (f : A → B → C) (l : List A)
    (m : List B), l.length = m.length → (MAP2 f l m).length = m.length := @HolLightLean.hol_opam.thm_LENGTH_MAP2 holTheoryInst

theorem hol_EL_MAP2 : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (f : A → B → C) (l : List A)
    (m : List B) (k : ℕ), k < l.length ∧ k < m.length → EL k (MAP2 f l m) = f (EL k l) (EL k m) := @HolLightLean.hol_opam.thm_EL_MAP2 holTheoryInst

theorem hol_MAP_EQ_NIL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (l : List A), (List.map f l = []) = (l = []) := @HolLightLean.hol_opam.thm_MAP_EQ_NIL holTheoryInst

theorem hol_INJECTIVE_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (l m : List A), List.map f l = List.map f m → l = m) (∀ (x y : A), f x = f y → x = y) := @HolLightLean.hol_opam.thm_INJECTIVE_MAP holTheoryInst

theorem hol_SURJECTIVE_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (m : List B), ∃ (l : List A), List.map f l = m) (∀ (y : B), ∃ (x : A), f x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_MAP holTheoryInst

theorem hol_MAP_ID : 
  ∀ {A : Type} [Nonempty A] (l : List A), List.map (fun (x : A) ↦ x) l = l := @HolLightLean.hol_opam.thm_MAP_ID holTheoryInst

theorem hol_MAP_I : 
  ∀ {A : Type} [Nonempty A], Eq (α := List A → List A) (List.map id) id := @HolLightLean.hol_opam.thm_MAP_I holTheoryInst

theorem hol_BUTLAST_CLAUSES : 
  ∀ {A : Type} [Nonempty A],
    Eq (α := List A) (List.dropLast []) [] ∧
      (∀ (a : A), [a].dropLast = []) ∧ ∀ (a h : A) (t : List A), (a :: h :: t).dropLast = a :: (h :: t).dropLast := @HolLightLean.hol_opam.thm_BUTLAST_CLAUSES holTheoryInst

theorem hol_BUTLAST_APPEND : 
  ∀ {A : Type} [Nonempty A] (l m : List A), (l.append m).dropLast = if m = [] then l.dropLast else l.append m.dropLast := @HolLightLean.hol_opam.thm_BUTLAST_APPEND holTheoryInst

theorem hol_APPEND_BUTLAST_LAST : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ¬l = [] → l.dropLast.append [LAST l] = l := @HolLightLean.hol_opam.thm_APPEND_BUTLAST_LAST holTheoryInst

theorem hol_LAST_APPEND : 
  ∀ {A : Type} [inst : Nonempty A] (p q : List A), LAST (p.append q) = if q = [] then LAST p else LAST q := @HolLightLean.hol_opam.thm_LAST_APPEND holTheoryInst

theorem hol_LENGTH_TL : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ¬l = [] → (TL l).length = l.length - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_LENGTH_TL holTheoryInst

theorem hol_LAST_REVERSE : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ¬l = [] → LAST l.reverse = HD l := @HolLightLean.hol_opam.thm_LAST_REVERSE holTheoryInst

theorem hol_HD_REVERSE : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ¬l = [] → HD l.reverse = LAST l := @HolLightLean.hol_opam.thm_HD_REVERSE holTheoryInst

theorem hol_EL_APPEND : 
  ∀ {A : Type} [inst : Nonempty A] (k : ℕ) (l m : List A),
    EL k (l.append m) = if k < l.length then EL k l else EL (k - l.length) m := @HolLightLean.hol_opam.thm_EL_APPEND holTheoryInst

theorem hol_EL_TL : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A) (n : ℕ), EL n (TL l) = EL (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) l := @HolLightLean.hol_opam.thm_EL_TL holTheoryInst

theorem hol_EL_CONS : 
  ∀ {A : Type} [inst : Nonempty A] (n : ℕ) (h : A) (t : List A),
    EL n (h :: t) = if n = (0 : ℕ) then h else EL (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) t := @HolLightLean.hol_opam.thm_EL_CONS holTheoryInst

theorem hol_LAST_EL : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ¬l = [] → LAST l = EL (l.length - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) l := @HolLightLean.hol_opam.thm_LAST_EL holTheoryInst

theorem hol_HD_APPEND : 
  ∀ {A : Type} [inst : Nonempty A] (l m : List A), HD (l.append m) = if l = [] then HD m else HD l := @HolLightLean.hol_opam.thm_HD_APPEND holTheoryInst

theorem hol_CONS_HD_TL : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A), ¬l = [] → l = HD l :: TL l := @HolLightLean.hol_opam.thm_CONS_HD_TL holTheoryInst

theorem hol_EL_MAP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (n : ℕ) (l : List A),
    n < l.length → EL n (List.map f l) = f (EL n l) := @HolLightLean.hol_opam.thm_EL_MAP holTheoryInst

theorem hol_MAP_REVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (l : List A), (List.map f l).reverse = List.map f l.reverse := @HolLightLean.hol_opam.thm_MAP_REVERSE holTheoryInst

theorem hol_ALL_FILTER : 
  ∀ {A : Type} [inst : Nonempty A] (P Q : Set A) (l : List A), ALL P (FILTER Q l) = ALL (fun (x : A) ↦ Q x → P x) l := @HolLightLean.hol_opam.thm_ALL_FILTER holTheoryInst

theorem hol_APPEND_SING : 
  ∀ {A : Type} [Nonempty A] (h : A) (t : List A), [h].append t = h :: t := @HolLightLean.hol_opam.thm_APPEND_SING holTheoryInst

theorem hol_MEM_APPEND_DECOMPOSE_LEFT : 
  ∀ {A : Type} [Nonempty A] (x : A) (l : List A),
    (x ∈ l) = ∃ (l1 : List A) (l2 : List A), x ∉ l1 ∧ l = l1.append (x :: l2) := @HolLightLean.hol_opam.thm_MEM_APPEND_DECOMPOSE_LEFT holTheoryInst

theorem hol_MEM_APPEND_DECOMPOSE : 
  ∀ {A : Type} [Nonempty A] (x : A) (l : List A), (x ∈ l) = ∃ (l1 : List A) (l2 : List A), l = l1.append (x :: l2) := @HolLightLean.hol_opam.thm_MEM_APPEND_DECOMPOSE holTheoryInst

theorem hol_PAIRWISE_APPEND : 
  ∀ {A : Type} [Nonempty A] (R' : A → A → Prop) (l m : List A),
    List.Pairwise R' (l.append m) = (List.Pairwise R' l ∧ List.Pairwise R' m ∧ ∀ (x y : A), x ∈ l ∧ y ∈ m → R' x y) := @HolLightLean.hol_opam.thm_PAIRWISE_APPEND holTheoryInst

theorem hol_PAIRWISE_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : B → B → Prop) (f : A → B) (l : List A),
    List.Pairwise R' (List.map f l) = List.Pairwise (fun (x y : A) ↦ R' (f x) (f y)) l := @HolLightLean.hol_opam.thm_PAIRWISE_MAP holTheoryInst

theorem hol_PAIRWISE_IMPLIES : 
  ∀ {A : Type} [Nonempty A] (R' R'' : A → A → Prop) (l : List A),
    (List.Pairwise R' l ∧ ∀ (x y : A), x ∈ l ∧ y ∈ l ∧ R' x y → R'' x y) → List.Pairwise R'' l := @HolLightLean.hol_opam.thm_PAIRWISE_IMPLIES holTheoryInst

theorem hol_PAIRWISE_TRANSITIVE : 
  ∀ {A : Type} [Nonempty A] (R' : A → A → Prop) (x y : A) (l : List A),
    (∀ (x' y' z : A), R' x' y' ∧ R' y' z → R' x' z) →
      List.Pairwise R' (x :: y :: l) = (R' x y ∧ List.Pairwise R' (y :: l)) := @HolLightLean.hol_opam.thm_PAIRWISE_TRANSITIVE holTheoryInst

theorem hol_LENGTH_LIST_OF_SEQ : 
  ∀ {A : Type} [Nonempty A] (s : ℕ → A) (n : ℕ), List.length (α := A) (List.ofFn (n := n) fun (i : Fin n) ↦ s ↑i) = n := @HolLightLean.hol_opam.thm_LENGTH_LIST_OF_SEQ holTheoryInst

theorem hol_EL_LIST_OF_SEQ : 
  ∀ {A : Type} [inst : Nonempty A] (s : ℕ → A) (m n : ℕ), m < n → EL m (List.ofFn (n := n) fun (i : Fin n) ↦ s ↑i) = s m := @HolLightLean.hol_opam.thm_EL_LIST_OF_SEQ holTheoryInst

theorem hol_LIST_OF_SEQ_EQ_NIL : 
  ∀ {A : Type} [Nonempty A] (s : ℕ → A) (n : ℕ),
    Eq (α := List A) (List.ofFn (n := n) fun (i : Fin n) ↦ s ↑i) [] = (n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_LIST_OF_SEQ_EQ_NIL holTheoryInst

theorem hol_LIST_OF_SEQ_EQ_SELF : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A),
    (List.ofFn (n := l.length) fun (i : Fin l.length) ↦ (fun (i : ℕ) ↦ EL i l) ↑i) = l := @HolLightLean.hol_opam.thm_LIST_OF_SEQ_EQ_SELF holTheoryInst

theorem hol_LENGTH_EQ_LIST_OF_SEQ : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A) (n : ℕ),
    (l.length = n) = (l = List.ofFn (n := n) fun (i : Fin n) ↦ (fun (i : ℕ) ↦ EL i l) ↑i) := @HolLightLean.hol_opam.thm_LENGTH_EQ_LIST_OF_SEQ holTheoryInst

theorem hol_MAP_LIST_OF_SEQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : ℕ → A) (g : A → B) (n : ℕ),
    List.map g (List.ofFn (n := n) fun (i : Fin n) ↦ f ↑i) = List.ofFn (n := n) fun (i : Fin n) ↦ (g ∘ f) ↑i := @HolLightLean.hol_opam.thm_MAP_LIST_OF_SEQ holTheoryInst

theorem hol_LIST_OF_SEQ : 
  ∀ {A : Type} [Nonempty A],
    (∀ (f : ℕ → A), Eq (α := List A) (List.ofFn (n := (0 : ℕ)) fun (i : Fin (0 : ℕ)) ↦ f ↑i) []) ∧
      ∀ (f : ℕ → A) (n : ℕ),
        (List.ofFn (n := n + (1 : ℕ)) fun (i : Fin (n + (1 : ℕ))) ↦ f ↑i) =
          f (0 : ℕ) :: List.ofFn (n := n) fun (i : Fin n) ↦ (f ∘ fun (x : ℕ) ↦ x + (1 : ℕ)) ↑i := @HolLightLean.hol_opam.thm_LIST_OF_SEQ holTheoryInst

theorem hol_MONO_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (P Q : Set A) (l : List A), (∀ (x : A), P x → Q x) → ALL P l → ALL Q l := @HolLightLean.hol_opam.thm_MONO_ALL holTheoryInst

theorem hol_MONO_ALL2 : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P Q : A → B → Prop) (l : List A) (l' : List B),
    (∀ (x : A) (y : B), P x y → Q x y) → ALL2 P l l' → ALL2 Q l l' := @HolLightLean.hol_opam.thm_MONO_ALL2 holTheoryInst

theorem hol_char_INDUCT : 
  ∀ (P : Set CHAR),
    (∀ (a0 a1 a2 a3 a4 a5 a6 a7 : Prop),
        P
          (_mk_char
            ((fun (a0' a1' a2' a3' a4' a5' a6' a7' : Prop) ↦
                (CONSTR (NUMERAL Nat.zero)
                    (prod_mk a0'
                      (prod_mk a1' (prod_mk a2' (prod_mk a3' (prod_mk a4' (prod_mk a5' (prod_mk a6' a7')))))))
                    fun (n : ℕ) ↦ BOTTOM :
                  recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))
              a0 a1 a2 a3 a4 a5 a6 a7))) →
      ∀ (x : CHAR), P x := @HolLightLean.hol_opam.thm_char_INDUCT holTheoryInst

theorem hol_char_RECURSION : 
  ∀ {Z' : Type} [Nonempty Z'] (f : Prop → Prop → Prop → Prop → Prop → Prop → Prop → Prop → Z'),
    ∃ (fn : CHAR → Z'),
      ∀ (a0 a1 a2 a3 a4 a5 a6 a7 : Prop),
        fn
            (_mk_char
              ((fun (a0' a1' a2' a3' a4' a5' a6' a7' : Prop) ↦
                  (CONSTR (NUMERAL Nat.zero)
                      (prod_mk a0'
                        (prod_mk a1' (prod_mk a2' (prod_mk a3' (prod_mk a4' (prod_mk a5' (prod_mk a6' a7')))))))
                      fun (n : ℕ) ↦ BOTTOM :
                    recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))
                a0 a1 a2 a3 a4 a5 a6 a7)) =
          f a0 a1 a2 a3 a4 a5 a6 a7 := @HolLightLean.hol_opam.thm_char_RECURSION holTheoryInst

theorem hol_dist : 
  ∀ (n m : ℕ), (m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1) = m - n + (n - m) := @HolLightLean.hol_opam.thm_dist holTheoryInst

theorem hol_DIST_REFL : 
  ∀ (n : ℕ), (n, n).1 - (n, n).2 + ((n, n).2 - (n, n).1) = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIST_REFL holTheoryInst

theorem hol_DIST_LZERO : 
  ∀ (n : ℕ), ((0 : ℕ), n).1 - ((0 : ℕ), n).2 + (((0 : ℕ), n).2 - ((0 : ℕ), n).1) = n := @HolLightLean.hol_opam.thm_DIST_LZERO holTheoryInst

theorem hol_DIST_RZERO : 
  ∀ (n : ℕ), (n, (0 : ℕ)).1 - (n, (0 : ℕ)).2 + ((n, (0 : ℕ)).2 - (n, (0 : ℕ)).1) = n := @HolLightLean.hol_opam.thm_DIST_RZERO holTheoryInst

theorem hol_DIST_SYM : 
  ∀ (m n : ℕ), (m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1) = (n, m).1 - (n, m).2 + ((n, m).2 - (n, m).1) := @HolLightLean.hol_opam.thm_DIST_SYM holTheoryInst

theorem hol_DIST_LADD : 
  ∀ (m p n : ℕ),
    (m + n, m + p).1 - (m + n, m + p).2 + ((m + n, m + p).2 - (m + n, m + p).1) =
      (n, p).1 - (n, p).2 + ((n, p).2 - (n, p).1) := @HolLightLean.hol_opam.thm_DIST_LADD holTheoryInst

theorem hol_DIST_RADD : 
  ∀ (m p n : ℕ),
    (m + p, n + p).1 - (m + p, n + p).2 + ((m + p, n + p).2 - (m + p, n + p).1) =
      (m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1) := @HolLightLean.hol_opam.thm_DIST_RADD holTheoryInst

theorem hol_DIST_LADD_0 : 
  ∀ (m n : ℕ), (m + n, m).1 - (m + n, m).2 + ((m + n, m).2 - (m + n, m).1) = n := @HolLightLean.hol_opam.thm_DIST_LADD_0 holTheoryInst

theorem hol_DIST_RADD_0 : 
  ∀ (m n : ℕ), (m, m + n).1 - (m, m + n).2 + ((m, m + n).2 - (m, m + n).1) = n := @HolLightLean.hol_opam.thm_DIST_RADD_0 holTheoryInst

theorem hol_DIST_LMUL : 
  ∀ (m n p : ℕ),
    m * ((n, p).1 - (n, p).2 + ((n, p).2 - (n, p).1)) =
      (m * n, m * p).1 - (m * n, m * p).2 + ((m * n, m * p).2 - (m * n, m * p).1) := @HolLightLean.hol_opam.thm_DIST_LMUL holTheoryInst

theorem hol_DIST_RMUL : 
  ∀ (m n p : ℕ),
    ((m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1)) * p =
      (m * p, n * p).1 - (m * p, n * p).2 + ((m * p, n * p).2 - (m * p, n * p).1) := @HolLightLean.hol_opam.thm_DIST_RMUL holTheoryInst

theorem hol_DIST_EQ_0 : 
  ∀ (m n : ℕ), ((m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1) = (0 : ℕ)) = (m = n) := @HolLightLean.hol_opam.thm_DIST_EQ_0 holTheoryInst

theorem hol_DIST_ELIM_THM : 
  ∀ (y x : ℕ) (P : Set ℕ),
    P ((x, y).1 - (x, y).2 + ((x, y).2 - (x, y).1)) = ∀ (d : ℕ), (x = y + d → P d) ∧ (y = x + d → P d) := @HolLightLean.hol_opam.thm_DIST_ELIM_THM holTheoryInst

theorem hol_DIST_TRIANGLE_LE : 
  ∀ (m n p q : ℕ),
    (m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1) + ((n, p).1 - (n, p).2 + ((n, p).2 - (n, p).1)) ≤ q →
      (m, p).1 - (m, p).2 + ((m, p).2 - (m, p).1) ≤ q := @HolLightLean.hol_opam.thm_DIST_TRIANGLE_LE holTheoryInst

theorem hol_DIST_TRIANGLES_LE : 
  ∀ (m n p q r s : ℕ),
    (m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1) ≤ r ∧ (p, q).1 - (p, q).2 + ((p, q).2 - (p, q).1) ≤ s →
      (m, p).1 - (m, p).2 + ((m, p).2 - (m, p).1) ≤ (n, q).1 - (n, q).2 + ((n, q).2 - (n, q).1) + (r + s) := @HolLightLean.hol_opam.thm_DIST_TRIANGLES_LE holTheoryInst

theorem hol_BOUNDS_LINEAR : 
  ∀ (A B C : ℕ), (∀ (n : ℕ), A * n ≤ B * n + C) = (A ≤ B) := @HolLightLean.hol_opam.thm_BOUNDS_LINEAR holTheoryInst

theorem hol_BOUNDS_LINEAR_0 : 
  ∀ (A B : ℕ), (∀ (n : ℕ), A * n ≤ B) = (A = (0 : ℕ)) := @HolLightLean.hol_opam.thm_BOUNDS_LINEAR_0 holTheoryInst

theorem hol_BOUNDS_DIVIDED : 
  ∀ (P : ℕ → ℕ), (∃ (B : ℕ), ∀ (n : ℕ), P n ≤ B) = ∃ (A : ℕ) (B : ℕ), ∀ (n : ℕ), n * P n ≤ A * n + B := @HolLightLean.hol_opam.thm_BOUNDS_DIVIDED holTheoryInst

theorem hol_BOUNDS_NOTZERO : 
  ∀ (P : ℕ → ℕ → ℕ) (A B : ℕ),
    (P (0 : ℕ) (0 : ℕ) = (0 : ℕ) ∧ ∀ (m n : ℕ), P m n ≤ A * (m + n) + B) → ∃ (B' : ℕ), ∀ (m n : ℕ), P m n ≤ B' * (m + n) := @HolLightLean.hol_opam.thm_BOUNDS_NOTZERO holTheoryInst

theorem hol_BOUNDS_IGNORE : 
  ∀ (P Q : ℕ → ℕ), (∃ (B : ℕ), ∀ (i : ℕ), P i ≤ Q i + B) = ∃ (B : ℕ) (N' : ℕ), ∀ (i : ℕ), N' ≤ i → P i ≤ Q i + B := @HolLightLean.hol_opam.thm_BOUNDS_IGNORE holTheoryInst

theorem hol_is_nadd : 
  ∀ (x : ℕ → ℕ),
    is_nadd x =
      ∃ (B : ℕ),
        ∀ (m n : ℕ),
          (m * x n, n * x m).1 - (m * x n, n * x m).2 + ((m * x n, n * x m).2 - (m * x n, n * x m).1) ≤ B * (m + n) := @HolLightLean.hol_opam.thm_is_nadd holTheoryInst

theorem hol_is_nadd_0 : 
  is_nadd fun (n : ℕ) ↦ (0 : ℕ) := @HolLightLean.hol_opam.thm_is_nadd_0 holTheoryInst

theorem hol_NADD_CAUCHY : 
  ∀ (x : nadd),
    ∃ (B : ℕ),
      ∀ (m n : ℕ),
        (m * dest_nadd x n, n * dest_nadd x m).1 - (m * dest_nadd x n, n * dest_nadd x m).2 +
            ((m * dest_nadd x n, n * dest_nadd x m).2 - (m * dest_nadd x n, n * dest_nadd x m).1) ≤
          B * (m + n) := @HolLightLean.hol_opam.thm_NADD_CAUCHY holTheoryInst

theorem hol_NADD_BOUND : 
  ∀ (x : nadd), ∃ (A : ℕ) (B : ℕ), ∀ (n : ℕ), dest_nadd x n ≤ A * n + B := @HolLightLean.hol_opam.thm_NADD_BOUND holTheoryInst

theorem hol_NADD_MULTIPLICATIVE : 
  ∀ (x : nadd),
    ∃ (B : ℕ),
      ∀ (m n : ℕ),
        (dest_nadd x (m * n), m * dest_nadd x n).1 - (dest_nadd x (m * n), m * dest_nadd x n).2 +
            ((dest_nadd x (m * n), m * dest_nadd x n).2 - (dest_nadd x (m * n), m * dest_nadd x n).1) ≤
          B * m + B := @HolLightLean.hol_opam.thm_NADD_MULTIPLICATIVE holTheoryInst

theorem hol_NADD_ADDITIVE : 
  ∀ (x : nadd),
    ∃ (B : ℕ),
      ∀ (m n : ℕ),
        (dest_nadd x (m + n), dest_nadd x m + dest_nadd x n).1 -
              (dest_nadd x (m + n), dest_nadd x m + dest_nadd x n).2 +
            ((dest_nadd x (m + n), dest_nadd x m + dest_nadd x n).2 -
              (dest_nadd x (m + n), dest_nadd x m + dest_nadd x n).1) ≤
          B := @HolLightLean.hol_opam.thm_NADD_ADDITIVE holTheoryInst

theorem hol_NADD_SUC : 
  ∀ (x : nadd),
    ∃ (B : ℕ),
      ∀ (n : ℕ),
        (dest_nadd x (n + (1 : ℕ)), dest_nadd x n).1 - (dest_nadd x (n + (1 : ℕ)), dest_nadd x n).2 +
            ((dest_nadd x (n + (1 : ℕ)), dest_nadd x n).2 - (dest_nadd x (n + (1 : ℕ)), dest_nadd x n).1) ≤
          B := @HolLightLean.hol_opam.thm_NADD_SUC holTheoryInst

theorem hol_NADD_DIST_LEMMA : 
  ∀ (x : nadd),
    ∃ (B : ℕ),
      ∀ (m n : ℕ),
        (dest_nadd x (m + n), dest_nadd x m).1 - (dest_nadd x (m + n), dest_nadd x m).2 +
            ((dest_nadd x (m + n), dest_nadd x m).2 - (dest_nadd x (m + n), dest_nadd x m).1) ≤
          B * n := @HolLightLean.hol_opam.thm_NADD_DIST_LEMMA holTheoryInst

theorem hol_NADD_DIST : 
  ∀ (x : nadd),
    ∃ (B : ℕ),
      ∀ (m n : ℕ),
        (dest_nadd x m, dest_nadd x n).1 - (dest_nadd x m, dest_nadd x n).2 +
            ((dest_nadd x m, dest_nadd x n).2 - (dest_nadd x m, dest_nadd x n).1) ≤
          B * ((m, n).1 - (m, n).2 + ((m, n).2 - (m, n).1)) := @HolLightLean.hol_opam.thm_NADD_DIST holTheoryInst

theorem hol_NADD_ALTMUL : 
  ∀ (x y : nadd),
    ∃ (A : ℕ) (B : ℕ),
      ∀ (n : ℕ),
        (n * dest_nadd x (dest_nadd y n), dest_nadd x n * dest_nadd y n).1 -
              (n * dest_nadd x (dest_nadd y n), dest_nadd x n * dest_nadd y n).2 +
            ((n * dest_nadd x (dest_nadd y n), dest_nadd x n * dest_nadd y n).2 -
              (n * dest_nadd x (dest_nadd y n), dest_nadd x n * dest_nadd y n).1) ≤
          A * n + B := @HolLightLean.hol_opam.thm_NADD_ALTMUL holTheoryInst

theorem hol_nadd_eq : 
  ∀ (x y : nadd),
    nadd_eq x y =
      ∃ (B : ℕ),
        ∀ (n : ℕ),
          (dest_nadd x n, dest_nadd y n).1 - (dest_nadd x n, dest_nadd y n).2 +
              ((dest_nadd x n, dest_nadd y n).2 - (dest_nadd x n, dest_nadd y n).1) ≤
            B := @HolLightLean.hol_opam.thm_nadd_eq holTheoryInst

theorem hol_NADD_EQ_REFL : 
  ∀ (x : nadd), nadd_eq x x := @HolLightLean.hol_opam.thm_NADD_EQ_REFL holTheoryInst

theorem hol_NADD_EQ_SYM : 
  ∀ (x y : nadd), nadd_eq x y = nadd_eq y x := @HolLightLean.hol_opam.thm_NADD_EQ_SYM holTheoryInst

theorem hol_NADD_EQ_TRANS : 
  ∀ (x y z : nadd), nadd_eq x y ∧ nadd_eq y z → nadd_eq x z := @HolLightLean.hol_opam.thm_NADD_EQ_TRANS holTheoryInst

theorem hol_nadd_of_num : 
  ∀ (k : ℕ), nadd_of_num k = mk_nadd fun (n : ℕ) ↦ k * n := @HolLightLean.hol_opam.thm_nadd_of_num holTheoryInst

theorem hol_NADD_OF_NUM : 
  ∀ (k : ℕ), dest_nadd (nadd_of_num k) = fun (n : ℕ) ↦ k * n := @HolLightLean.hol_opam.thm_NADD_OF_NUM holTheoryInst

theorem hol_NADD_OF_NUM_WELLDEF : 
  ∀ (m n : ℕ), m = n → nadd_eq (nadd_of_num m) (nadd_of_num n) := @HolLightLean.hol_opam.thm_NADD_OF_NUM_WELLDEF holTheoryInst

theorem hol_NADD_OF_NUM_EQ : 
  ∀ (m n : ℕ), nadd_eq (nadd_of_num m) (nadd_of_num n) = (m = n) := @HolLightLean.hol_opam.thm_NADD_OF_NUM_EQ holTheoryInst

theorem hol_nadd_le : 
  ∀ (x y : nadd), nadd_le x y = ∃ (B : ℕ), ∀ (n : ℕ), dest_nadd x n ≤ dest_nadd y n + B := @HolLightLean.hol_opam.thm_nadd_le holTheoryInst

theorem hol_NADD_LE_WELLDEF_LEMMA : 
  ∀ (x x' y y' : nadd), nadd_eq x x' ∧ nadd_eq y y' ∧ nadd_le x y → nadd_le x' y' := @HolLightLean.hol_opam.thm_NADD_LE_WELLDEF_LEMMA holTheoryInst

theorem hol_NADD_LE_WELLDEF : 
  ∀ (x x' y y' : nadd), nadd_eq x x' ∧ nadd_eq y y' → nadd_le x y = nadd_le x' y' := @HolLightLean.hol_opam.thm_NADD_LE_WELLDEF holTheoryInst

theorem hol_NADD_LE_REFL : 
  ∀ (x : nadd), nadd_le x x := @HolLightLean.hol_opam.thm_NADD_LE_REFL holTheoryInst

theorem hol_NADD_LE_TRANS : 
  ∀ (x y z : nadd), nadd_le x y ∧ nadd_le y z → nadd_le x z := @HolLightLean.hol_opam.thm_NADD_LE_TRANS holTheoryInst

theorem hol_NADD_LE_ANTISYM : 
  ∀ (x y : nadd), (nadd_le x y ∧ nadd_le y x) = nadd_eq x y := @HolLightLean.hol_opam.thm_NADD_LE_ANTISYM holTheoryInst

theorem hol_NADD_LE_TOTAL_LEMMA : 
  ∀ (x y : nadd), ¬nadd_le x y → ∀ (B : ℕ), ∃ (n : ℕ), ¬n = (0 : ℕ) ∧ dest_nadd y n + B < dest_nadd x n := @HolLightLean.hol_opam.thm_NADD_LE_TOTAL_LEMMA holTheoryInst

theorem hol_NADD_LE_TOTAL : 
  ∀ (x y : nadd), nadd_le x y ∨ nadd_le y x := @HolLightLean.hol_opam.thm_NADD_LE_TOTAL holTheoryInst

theorem hol_NADD_ARCH : 
  ∀ (x : nadd), ∃ (n : ℕ), nadd_le x (nadd_of_num n) := @HolLightLean.hol_opam.thm_NADD_ARCH holTheoryInst

theorem hol_NADD_OF_NUM_LE : 
  ∀ (m n : ℕ), nadd_le (nadd_of_num m) (nadd_of_num n) = (m ≤ n) := @HolLightLean.hol_opam.thm_NADD_OF_NUM_LE holTheoryInst

theorem hol_nadd_add : 
  ∀ (x y : nadd), nadd_add x y = mk_nadd fun (n : ℕ) ↦ dest_nadd x n + dest_nadd y n := @HolLightLean.hol_opam.thm_nadd_add holTheoryInst

theorem hol_NADD_ADD : 
  ∀ (x y : nadd), dest_nadd (nadd_add x y) = fun (n : ℕ) ↦ dest_nadd x n + dest_nadd y n := @HolLightLean.hol_opam.thm_NADD_ADD holTheoryInst

theorem hol_NADD_ADD_WELLDEF : 
  ∀ (x x' y y' : nadd), nadd_eq x x' ∧ nadd_eq y y' → nadd_eq (nadd_add x y) (nadd_add x' y') := @HolLightLean.hol_opam.thm_NADD_ADD_WELLDEF holTheoryInst

theorem hol_NADD_ADD_SYM : 
  ∀ (x y : nadd), nadd_eq (nadd_add x y) (nadd_add y x) := @HolLightLean.hol_opam.thm_NADD_ADD_SYM holTheoryInst

theorem hol_NADD_ADD_ASSOC : 
  ∀ (x y z : nadd), nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z) := @HolLightLean.hol_opam.thm_NADD_ADD_ASSOC holTheoryInst

theorem hol_NADD_ADD_LID : 
  ∀ (x : nadd), nadd_eq (nadd_add (nadd_of_num (0 : ℕ)) x) x := @HolLightLean.hol_opam.thm_NADD_ADD_LID holTheoryInst

theorem hol_NADD_ADD_LCANCEL : 
  ∀ (x y z : nadd), nadd_eq (nadd_add x y) (nadd_add x z) → nadd_eq y z := @HolLightLean.hol_opam.thm_NADD_ADD_LCANCEL holTheoryInst

theorem hol_NADD_LE_ADD : 
  ∀ (x y : nadd), nadd_le x (nadd_add x y) := @HolLightLean.hol_opam.thm_NADD_LE_ADD holTheoryInst

theorem hol_NADD_LE_EXISTS : 
  ∀ (x y : nadd), nadd_le x y → ∃ (d : nadd), nadd_eq y (nadd_add x d) := @HolLightLean.hol_opam.thm_NADD_LE_EXISTS holTheoryInst

theorem hol_NADD_OF_NUM_ADD : 
  ∀ (m n : ℕ), nadd_eq (nadd_add (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (m + n)) := @HolLightLean.hol_opam.thm_NADD_OF_NUM_ADD holTheoryInst

theorem hol_nadd_mul : 
  ∀ (x y : nadd), nadd_mul x y = mk_nadd fun (n : ℕ) ↦ dest_nadd x (dest_nadd y n) := @HolLightLean.hol_opam.thm_nadd_mul holTheoryInst

theorem hol_NADD_MUL : 
  ∀ (x y : nadd), dest_nadd (nadd_mul x y) = fun (n : ℕ) ↦ dest_nadd x (dest_nadd y n) := @HolLightLean.hol_opam.thm_NADD_MUL holTheoryInst

theorem hol_NADD_MUL_SYM : 
  ∀ (x y : nadd), nadd_eq (nadd_mul x y) (nadd_mul y x) := @HolLightLean.hol_opam.thm_NADD_MUL_SYM holTheoryInst

theorem hol_NADD_MUL_ASSOC : 
  ∀ (x y z : nadd), nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z) := @HolLightLean.hol_opam.thm_NADD_MUL_ASSOC holTheoryInst

theorem hol_NADD_MUL_LID : 
  ∀ (x : nadd), nadd_eq (nadd_mul (nadd_of_num ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) x) x := @HolLightLean.hol_opam.thm_NADD_MUL_LID holTheoryInst

theorem hol_NADD_LDISTRIB : 
  ∀ (x y z : nadd), nadd_eq (nadd_mul x (nadd_add y z)) (nadd_add (nadd_mul x y) (nadd_mul x z)) := @HolLightLean.hol_opam.thm_NADD_LDISTRIB holTheoryInst

theorem hol_NADD_MUL_WELLDEF_LEMMA : 
  ∀ (x y y' : nadd), nadd_eq y y' → nadd_eq (nadd_mul x y) (nadd_mul x y') := @HolLightLean.hol_opam.thm_NADD_MUL_WELLDEF_LEMMA holTheoryInst

theorem hol_NADD_MUL_WELLDEF : 
  ∀ (x x' y y' : nadd), nadd_eq x x' ∧ nadd_eq y y' → nadd_eq (nadd_mul x y) (nadd_mul x' y') := @HolLightLean.hol_opam.thm_NADD_MUL_WELLDEF holTheoryInst

theorem hol_NADD_OF_NUM_MUL : 
  ∀ (m n : ℕ), nadd_eq (nadd_mul (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (m * n)) := @HolLightLean.hol_opam.thm_NADD_OF_NUM_MUL holTheoryInst

theorem hol_NADD_LE_0 : 
  ∀ (x : nadd), nadd_le (nadd_of_num (0 : ℕ)) x := @HolLightLean.hol_opam.thm_NADD_LE_0 holTheoryInst

theorem hol_NADD_EQ_IMP_LE : 
  ∀ (x y : nadd), nadd_eq x y → nadd_le x y := @HolLightLean.hol_opam.thm_NADD_EQ_IMP_LE holTheoryInst

theorem hol_NADD_LE_LMUL : 
  ∀ (x y z : nadd), nadd_le y z → nadd_le (nadd_mul x y) (nadd_mul x z) := @HolLightLean.hol_opam.thm_NADD_LE_LMUL holTheoryInst

theorem hol_NADD_LE_RMUL : 
  ∀ (x y z : nadd), nadd_le x y → nadd_le (nadd_mul x z) (nadd_mul y z) := @HolLightLean.hol_opam.thm_NADD_LE_RMUL holTheoryInst

theorem hol_NADD_LE_RADD : 
  ∀ (x y z : nadd), nadd_le (nadd_add x z) (nadd_add y z) = nadd_le x y := @HolLightLean.hol_opam.thm_NADD_LE_RADD holTheoryInst

theorem hol_NADD_LE_LADD : 
  ∀ (x y z : nadd), nadd_le (nadd_add x y) (nadd_add x z) = nadd_le y z := @HolLightLean.hol_opam.thm_NADD_LE_LADD holTheoryInst

theorem hol_NADD_RDISTRIB : 
  ∀ (x y z : nadd), nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z)) := @HolLightLean.hol_opam.thm_NADD_RDISTRIB holTheoryInst

theorem hol_NADD_ARCH_MULT : 
  ∀ (x : nadd) (k : ℕ),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) → ∃ (N' : ℕ), nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N') x) := @HolLightLean.hol_opam.thm_NADD_ARCH_MULT holTheoryInst

theorem hol_NADD_ARCH_ZERO : 
  ∀ (x k : nadd), (∀ (n : ℕ), nadd_le (nadd_mul (nadd_of_num n) x) k) → nadd_eq x (nadd_of_num (0 : ℕ)) := @HolLightLean.hol_opam.thm_NADD_ARCH_ZERO holTheoryInst

theorem hol_NADD_ARCH_LEMMA : 
  ∀ (x y z : nadd),
    (∀ (n : ℕ), nadd_le (nadd_mul (nadd_of_num n) x) (nadd_add (nadd_mul (nadd_of_num n) y) z)) → nadd_le x y := @HolLightLean.hol_opam.thm_NADD_ARCH_LEMMA holTheoryInst

theorem hol_NADD_COMPLETE : 
  ∀ (P : Set nadd),
    ((∃ (x : nadd), P x) ∧ ∃ (M : nadd), ∀ (x : nadd), P x → nadd_le x M) →
      ∃ (M : nadd), (∀ (x : nadd), P x → nadd_le x M) ∧ ∀ (M' : nadd), (∀ (x : nadd), P x → nadd_le x M') → nadd_le M M' := @HolLightLean.hol_opam.thm_NADD_COMPLETE holTheoryInst

theorem hol_NADD_UBOUND : 
  ∀ (x : nadd), ∃ (B : ℕ) (N' : ℕ), ∀ (n : ℕ), N' ≤ n → dest_nadd x n ≤ B * n := @HolLightLean.hol_opam.thm_NADD_UBOUND holTheoryInst

theorem hol_NADD_NONZERO : 
  ∀ (x : nadd), ¬nadd_eq x (nadd_of_num (0 : ℕ)) → ∃ (N' : ℕ), ∀ (n : ℕ), N' ≤ n → ¬dest_nadd x n = (0 : ℕ) := @HolLightLean.hol_opam.thm_NADD_NONZERO holTheoryInst

theorem hol_NADD_LBOUND : 
  ∀ (x : nadd), ¬nadd_eq x (nadd_of_num (0 : ℕ)) → ∃ (A : ℕ) (N' : ℕ), ∀ (n : ℕ), N' ≤ n → n ≤ A * dest_nadd x n := @HolLightLean.hol_opam.thm_NADD_LBOUND holTheoryInst

theorem hol_nadd_rinv : 
  ∀ (x : nadd), nadd_rinv x = fun (n : ℕ) ↦ n * n / dest_nadd x n := @HolLightLean.hol_opam.thm_nadd_rinv holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA0 : 
  ∀ (x : nadd), ¬nadd_eq x (nadd_of_num (0 : ℕ)) → ∃ (A : ℕ) (B : ℕ), ∀ (n : ℕ), nadd_rinv x n ≤ A * n + B := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA0 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA1 : 
  ∀ (x : nadd) (n : ℕ),
    ¬dest_nadd x n = (0 : ℕ) →
      (dest_nadd x n * nadd_rinv x n, n * n).1 - (dest_nadd x n * nadd_rinv x n, n * n).2 +
          ((dest_nadd x n * nadd_rinv x n, n * n).2 - (dest_nadd x n * nadd_rinv x n, n * n).1) ≤
        dest_nadd x n := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA1 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA2 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (N' : ℕ),
        ∀ (n : ℕ),
          N' ≤ n →
            (dest_nadd x n * nadd_rinv x n, n * n).1 - (dest_nadd x n * nadd_rinv x n, n * n).2 +
                ((dest_nadd x n * nadd_rinv x n, n * n).2 - (dest_nadd x n * nadd_rinv x n, n * n).1) ≤
              dest_nadd x n := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA2 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA3 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (N' : ℕ),
        ∀ (m n : ℕ),
          N' ≤ n →
            (m * (dest_nadd x m * (dest_nadd x n * nadd_rinv x n)), m * (dest_nadd x m * (n * n))).1 -
                  (m * (dest_nadd x m * (dest_nadd x n * nadd_rinv x n)), m * (dest_nadd x m * (n * n))).2 +
                ((m * (dest_nadd x m * (dest_nadd x n * nadd_rinv x n)), m * (dest_nadd x m * (n * n))).2 -
                  (m * (dest_nadd x m * (dest_nadd x n * nadd_rinv x n)), m * (dest_nadd x m * (n * n))).1) ≤
              m * (dest_nadd x m * dest_nadd x n) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA3 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA4 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (N' : ℕ),
        ∀ (m n : ℕ),
          N' ≤ m ∧ N' ≤ n →
            dest_nadd x m * dest_nadd x n *
                ((m * nadd_rinv x n, n * nadd_rinv x m).1 - (m * nadd_rinv x n, n * nadd_rinv x m).2 +
                  ((m * nadd_rinv x n, n * nadd_rinv x m).2 - (m * nadd_rinv x n, n * nadd_rinv x m).1)) ≤
              m * n *
                  ((m * dest_nadd x n, n * dest_nadd x m).1 - (m * dest_nadd x n, n * dest_nadd x m).2 +
                    ((m * dest_nadd x n, n * dest_nadd x m).2 - (m * dest_nadd x n, n * dest_nadd x m).1)) +
                dest_nadd x m * dest_nadd x n * (m + n) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA4 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA5 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (B : ℕ) (N' : ℕ),
        ∀ (m n : ℕ),
          N' ≤ m ∧ N' ≤ n →
            dest_nadd x m * dest_nadd x n *
                ((m * nadd_rinv x n, n * nadd_rinv x m).1 - (m * nadd_rinv x n, n * nadd_rinv x m).2 +
                  ((m * nadd_rinv x n, n * nadd_rinv x m).2 - (m * nadd_rinv x n, n * nadd_rinv x m).1)) ≤
              B * (m * n * (m + n)) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA5 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA6 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (B : ℕ) (N' : ℕ),
        ∀ (m n : ℕ),
          N' ≤ m ∧ N' ≤ n →
            m * n *
                ((m * nadd_rinv x n, n * nadd_rinv x m).1 - (m * nadd_rinv x n, n * nadd_rinv x m).2 +
                  ((m * nadd_rinv x n, n * nadd_rinv x m).2 - (m * nadd_rinv x n, n * nadd_rinv x m).1)) ≤
              B * (m * n * (m + n)) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA6 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA7 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (B : ℕ) (N' : ℕ),
        ∀ (m n : ℕ),
          N' ≤ m ∧ N' ≤ n →
            (m * nadd_rinv x n, n * nadd_rinv x m).1 - (m * nadd_rinv x n, n * nadd_rinv x m).2 +
                ((m * nadd_rinv x n, n * nadd_rinv x m).2 - (m * nadd_rinv x n, n * nadd_rinv x m).1) ≤
              B * (m + n) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA7 holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA7a : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∀ (N' : ℕ),
        ∃ (A : ℕ) (B : ℕ),
          ∀ (m n : ℕ),
            m ≤ N' →
              (m * nadd_rinv x n, n * nadd_rinv x m).1 - (m * nadd_rinv x n, n * nadd_rinv x m).2 +
                  ((m * nadd_rinv x n, n * nadd_rinv x m).2 - (m * nadd_rinv x n, n * nadd_rinv x m).1) ≤
                A * n + B := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA7a holTheoryInst

theorem hol_NADD_MUL_LINV_LEMMA8 : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) →
      ∃ (B : ℕ),
        ∀ (m n : ℕ),
          (m * nadd_rinv x n, n * nadd_rinv x m).1 - (m * nadd_rinv x n, n * nadd_rinv x m).2 +
              ((m * nadd_rinv x n, n * nadd_rinv x m).2 - (m * nadd_rinv x n, n * nadd_rinv x m).1) ≤
            B * (m + n) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV_LEMMA8 holTheoryInst

theorem hol_nadd_inv : 
  ∀ (x : nadd), nadd_inv x = if nadd_eq x (nadd_of_num (0 : ℕ)) then nadd_of_num (0 : ℕ) else mk_nadd (nadd_rinv x) := @HolLightLean.hol_opam.thm_nadd_inv holTheoryInst

theorem hol_NADD_INV : 
  ∀ (x : nadd), dest_nadd (nadd_inv x) = if nadd_eq x (nadd_of_num (0 : ℕ)) then fun (n : ℕ) ↦ (0 : ℕ) else nadd_rinv x := @HolLightLean.hol_opam.thm_NADD_INV holTheoryInst

theorem hol_NADD_MUL_LINV : 
  ∀ (x : nadd),
    ¬nadd_eq x (nadd_of_num (0 : ℕ)) → nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_NADD_MUL_LINV holTheoryInst

theorem hol_NADD_INV_0 : 
  nadd_eq (nadd_inv (nadd_of_num (0 : ℕ))) (nadd_of_num (0 : ℕ)) := @HolLightLean.hol_opam.thm_NADD_INV_0 holTheoryInst

theorem hol_NADD_INV_WELLDEF : 
  ∀ (x y : nadd), nadd_eq x y → nadd_eq (nadd_inv x) (nadd_inv y) := @HolLightLean.hol_opam.thm_NADD_INV_WELLDEF holTheoryInst

theorem hol_HREAL_OF_NUM_EQ : 
  ∀ (m n : ℕ), (hreal_of_num m = hreal_of_num n) = (m = n) := @HolLightLean.hol_opam.thm_HREAL_OF_NUM_EQ holTheoryInst

theorem hol_HREAL_OF_NUM_LE : 
  ∀ (m n : ℕ), hreal_le (hreal_of_num m) (hreal_of_num n) = (m ≤ n) := @HolLightLean.hol_opam.thm_HREAL_OF_NUM_LE holTheoryInst

theorem hol_HREAL_OF_NUM_ADD : 
  ∀ (m n : ℕ), hreal_add (hreal_of_num m) (hreal_of_num n) = hreal_of_num (m + n) := @HolLightLean.hol_opam.thm_HREAL_OF_NUM_ADD holTheoryInst

theorem hol_HREAL_OF_NUM_MUL : 
  ∀ (m n : ℕ), hreal_mul (hreal_of_num m) (hreal_of_num n) = hreal_of_num (m * n) := @HolLightLean.hol_opam.thm_HREAL_OF_NUM_MUL holTheoryInst

theorem hol_HREAL_LE_REFL : 
  ∀ (x : hreal), hreal_le x x := @HolLightLean.hol_opam.thm_HREAL_LE_REFL holTheoryInst

theorem hol_HREAL_LE_TRANS : 
  ∀ (x y z : hreal), hreal_le x y ∧ hreal_le y z → hreal_le x z := @HolLightLean.hol_opam.thm_HREAL_LE_TRANS holTheoryInst

theorem hol_HREAL_LE_ANTISYM : 
  ∀ (x y : hreal), (hreal_le x y ∧ hreal_le y x) = (x = y) := @HolLightLean.hol_opam.thm_HREAL_LE_ANTISYM holTheoryInst

theorem hol_HREAL_LE_TOTAL : 
  ∀ (x y : hreal), hreal_le x y ∨ hreal_le y x := @HolLightLean.hol_opam.thm_HREAL_LE_TOTAL holTheoryInst

theorem hol_HREAL_LE_ADD : 
  ∀ (x y : hreal), hreal_le x (hreal_add x y) := @HolLightLean.hol_opam.thm_HREAL_LE_ADD holTheoryInst

theorem hol_HREAL_LE_EXISTS : 
  ∀ (x y : hreal), hreal_le x y → ∃ (d : hreal), y = hreal_add x d := @HolLightLean.hol_opam.thm_HREAL_LE_EXISTS holTheoryInst

theorem hol_HREAL_ARCH : 
  ∀ (x : hreal), ∃ (n : ℕ), hreal_le x (hreal_of_num n) := @HolLightLean.hol_opam.thm_HREAL_ARCH holTheoryInst

theorem hol_HREAL_ADD_SYM : 
  ∀ (x y : hreal), hreal_add x y = hreal_add y x := @HolLightLean.hol_opam.thm_HREAL_ADD_SYM holTheoryInst

theorem hol_HREAL_ADD_ASSOC : 
  ∀ (x y z : hreal), hreal_add x (hreal_add y z) = hreal_add (hreal_add x y) z := @HolLightLean.hol_opam.thm_HREAL_ADD_ASSOC holTheoryInst

theorem hol_HREAL_ADD_LID : 
  ∀ (x : hreal), hreal_add (hreal_of_num (0 : ℕ)) x = x := @HolLightLean.hol_opam.thm_HREAL_ADD_LID holTheoryInst

theorem hol_HREAL_ADD_LCANCEL : 
  ∀ (x y z : hreal), hreal_add x y = hreal_add x z → y = z := @HolLightLean.hol_opam.thm_HREAL_ADD_LCANCEL holTheoryInst

theorem hol_HREAL_MUL_SYM : 
  ∀ (x y : hreal), hreal_mul x y = hreal_mul y x := @HolLightLean.hol_opam.thm_HREAL_MUL_SYM holTheoryInst

theorem hol_HREAL_MUL_ASSOC : 
  ∀ (x y z : hreal), hreal_mul x (hreal_mul y z) = hreal_mul (hreal_mul x y) z := @HolLightLean.hol_opam.thm_HREAL_MUL_ASSOC holTheoryInst

theorem hol_HREAL_MUL_LID : 
  ∀ (x : hreal), hreal_mul (hreal_of_num ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) x = x := @HolLightLean.hol_opam.thm_HREAL_MUL_LID holTheoryInst

theorem hol_HREAL_ADD_LDISTRIB : 
  ∀ (x y z : hreal), hreal_mul x (hreal_add y z) = hreal_add (hreal_mul x y) (hreal_mul x z) := @HolLightLean.hol_opam.thm_HREAL_ADD_LDISTRIB holTheoryInst

theorem hol_HREAL_MUL_LINV : 
  ∀ (x : hreal), ¬x = hreal_of_num (0 : ℕ) → hreal_mul (hreal_inv x) x = hreal_of_num ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_HREAL_MUL_LINV holTheoryInst

theorem hol_HREAL_INV_0 : 
  hreal_inv (hreal_of_num (0 : ℕ)) = hreal_of_num (0 : ℕ) := @HolLightLean.hol_opam.thm_HREAL_INV_0 holTheoryInst

theorem hol_HREAL_LE_EXISTS_DEF : 
  ∀ (m n : hreal), hreal_le m n = ∃ (d : hreal), n = hreal_add m d := @HolLightLean.hol_opam.thm_HREAL_LE_EXISTS_DEF holTheoryInst

theorem hol_HREAL_EQ_ADD_LCANCEL : 
  ∀ (m n p : hreal), (hreal_add m n = hreal_add m p) = (n = p) := @HolLightLean.hol_opam.thm_HREAL_EQ_ADD_LCANCEL holTheoryInst

theorem hol_HREAL_EQ_ADD_RCANCEL : 
  ∀ (m n p : hreal), (hreal_add m p = hreal_add n p) = (m = n) := @HolLightLean.hol_opam.thm_HREAL_EQ_ADD_RCANCEL holTheoryInst

theorem hol_HREAL_LE_ADD_LCANCEL : 
  ∀ (m n p : hreal), hreal_le (hreal_add m n) (hreal_add m p) = hreal_le n p := @HolLightLean.hol_opam.thm_HREAL_LE_ADD_LCANCEL holTheoryInst

theorem hol_HREAL_LE_ADD_RCANCEL : 
  ∀ (m n p : hreal), hreal_le (hreal_add m p) (hreal_add n p) = hreal_le m n := @HolLightLean.hol_opam.thm_HREAL_LE_ADD_RCANCEL holTheoryInst

theorem hol_HREAL_ADD_RID : 
  ∀ (n : hreal), hreal_add n (hreal_of_num (0 : ℕ)) = n := @HolLightLean.hol_opam.thm_HREAL_ADD_RID holTheoryInst

theorem hol_HREAL_ADD_RDISTRIB : 
  ∀ (m n p : hreal), hreal_mul (hreal_add m n) p = hreal_add (hreal_mul m p) (hreal_mul n p) := @HolLightLean.hol_opam.thm_HREAL_ADD_RDISTRIB holTheoryInst

theorem hol_HREAL_MUL_LZERO : 
  ∀ (m : hreal), hreal_mul (hreal_of_num (0 : ℕ)) m = hreal_of_num (0 : ℕ) := @HolLightLean.hol_opam.thm_HREAL_MUL_LZERO holTheoryInst

theorem hol_HREAL_MUL_RZERO : 
  ∀ (m : hreal), hreal_mul m (hreal_of_num (0 : ℕ)) = hreal_of_num (0 : ℕ) := @HolLightLean.hol_opam.thm_HREAL_MUL_RZERO holTheoryInst

theorem hol_HREAL_ADD_AC : 
  ∀ (n m p : hreal),
    hreal_add m n = hreal_add n m ∧
      hreal_add (hreal_add m n) p = hreal_add m (hreal_add n p) ∧
        hreal_add m (hreal_add n p) = hreal_add n (hreal_add m p) := @HolLightLean.hol_opam.thm_HREAL_ADD_AC holTheoryInst

theorem hol_HREAL_LE_ADD2 : 
  ∀ (a b c d : hreal), hreal_le a b ∧ hreal_le c d → hreal_le (hreal_add a c) (hreal_add b d) := @HolLightLean.hol_opam.thm_HREAL_LE_ADD2 holTheoryInst

theorem hol_HREAL_LE_MUL_RCANCEL_IMP : 
  ∀ (a b c : hreal), hreal_le a b → hreal_le (hreal_mul a c) (hreal_mul b c) := @HolLightLean.hol_opam.thm_HREAL_LE_MUL_RCANCEL_IMP holTheoryInst

theorem hol_treal_of_num : 
  ∀ (n : ℕ), treal_of_num n = (hreal_of_num n, hreal_of_num (0 : ℕ)) := @HolLightLean.hol_opam.thm_treal_of_num holTheoryInst

theorem hol_treal_neg : 
  ∀ (y x : hreal), treal_neg (x, y) = (y, x) := @HolLightLean.hol_opam.thm_treal_neg holTheoryInst

theorem hol_treal_add : 
  ∀ (x1 x2 y1 y2 : hreal), treal_add (x1, y1) (x2, y2) = (hreal_add x1 x2, hreal_add y1 y2) := @HolLightLean.hol_opam.thm_treal_add holTheoryInst

theorem hol_treal_mul : 
  ∀ (x1 y2 y1 x2 : hreal),
    treal_mul (x1, y1) (x2, y2) =
      (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2), hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2)) := @HolLightLean.hol_opam.thm_treal_mul holTheoryInst

theorem hol_treal_le : 
  ∀ (x1 y2 x2 y1 : hreal), treal_le (x1, y1) (x2, y2) = hreal_le (hreal_add x1 y2) (hreal_add x2 y1) := @HolLightLean.hol_opam.thm_treal_le holTheoryInst

theorem hol_treal_inv : 
  ∀ (y x : hreal),
    treal_inv (x, y) =
      if x = y then (hreal_of_num (0 : ℕ), hreal_of_num (0 : ℕ))
      else
        if hreal_le y x then (hreal_inv (Classical.epsilon fun (d : hreal) ↦ x = hreal_add y d), hreal_of_num (0 : ℕ))
        else (hreal_of_num (0 : ℕ), hreal_inv (Classical.epsilon fun (d : hreal) ↦ y = hreal_add x d)) := @HolLightLean.hol_opam.thm_treal_inv holTheoryInst

theorem hol_treal_eq : 
  ∀ (x1 y2 x2 y1 : hreal), treal_eq (x1, y1) (x2, y2) = (hreal_add x1 y2 = hreal_add x2 y1) := @HolLightLean.hol_opam.thm_treal_eq holTheoryInst

theorem hol_TREAL_EQ_REFL : 
  ∀ (x : hreal × hreal), treal_eq x x := @HolLightLean.hol_opam.thm_TREAL_EQ_REFL holTheoryInst

theorem hol_TREAL_EQ_SYM : 
  ∀ (x y : hreal × hreal), treal_eq x y = treal_eq y x := @HolLightLean.hol_opam.thm_TREAL_EQ_SYM holTheoryInst

theorem hol_TREAL_EQ_TRANS : 
  ∀ (x y z : hreal × hreal), treal_eq x y ∧ treal_eq y z → treal_eq x z := @HolLightLean.hol_opam.thm_TREAL_EQ_TRANS holTheoryInst

theorem hol_TREAL_EQ_AP : 
  ∀ (x y : hreal × hreal), x = y → treal_eq x y := @HolLightLean.hol_opam.thm_TREAL_EQ_AP holTheoryInst

theorem hol_TREAL_OF_NUM_EQ : 
  ∀ (m n : ℕ), treal_eq (treal_of_num m) (treal_of_num n) = (m = n) := @HolLightLean.hol_opam.thm_TREAL_OF_NUM_EQ holTheoryInst

theorem hol_TREAL_OF_NUM_LE : 
  ∀ (m n : ℕ), treal_le (treal_of_num m) (treal_of_num n) = (m ≤ n) := @HolLightLean.hol_opam.thm_TREAL_OF_NUM_LE holTheoryInst

theorem hol_TREAL_OF_NUM_ADD : 
  ∀ (m n : ℕ), treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (m + n)) := @HolLightLean.hol_opam.thm_TREAL_OF_NUM_ADD holTheoryInst

theorem hol_TREAL_OF_NUM_MUL : 
  ∀ (m n : ℕ), treal_eq (treal_mul (treal_of_num m) (treal_of_num n)) (treal_of_num (m * n)) := @HolLightLean.hol_opam.thm_TREAL_OF_NUM_MUL holTheoryInst

theorem hol_TREAL_ADD_SYM_EQ : 
  ∀ (x y : hreal × hreal), treal_add x y = treal_add y x := @HolLightLean.hol_opam.thm_TREAL_ADD_SYM_EQ holTheoryInst

theorem hol_TREAL_MUL_SYM_EQ : 
  ∀ (x y : hreal × hreal), treal_mul x y = treal_mul y x := @HolLightLean.hol_opam.thm_TREAL_MUL_SYM_EQ holTheoryInst

theorem hol_TREAL_ADD_SYM : 
  ∀ (x y : hreal × hreal), treal_eq (treal_add x y) (treal_add y x) := @HolLightLean.hol_opam.thm_TREAL_ADD_SYM holTheoryInst

theorem hol_TREAL_ADD_ASSOC : 
  ∀ (x y z : hreal × hreal), treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z) := @HolLightLean.hol_opam.thm_TREAL_ADD_ASSOC holTheoryInst

theorem hol_TREAL_ADD_LID : 
  ∀ (x : hreal × hreal), treal_eq (treal_add (treal_of_num (0 : ℕ)) x) x := @HolLightLean.hol_opam.thm_TREAL_ADD_LID holTheoryInst

theorem hol_TREAL_ADD_LINV : 
  ∀ (x : hreal × hreal), treal_eq (treal_add (treal_neg x) x) (treal_of_num (0 : ℕ)) := @HolLightLean.hol_opam.thm_TREAL_ADD_LINV holTheoryInst

theorem hol_TREAL_MUL_SYM : 
  ∀ (x y : hreal × hreal), treal_eq (treal_mul x y) (treal_mul y x) := @HolLightLean.hol_opam.thm_TREAL_MUL_SYM holTheoryInst

theorem hol_TREAL_MUL_ASSOC : 
  ∀ (x y z : hreal × hreal), treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z) := @HolLightLean.hol_opam.thm_TREAL_MUL_ASSOC holTheoryInst

theorem hol_TREAL_MUL_LID : 
  ∀ (x : hreal × hreal), treal_eq (treal_mul (treal_of_num ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) x) x := @HolLightLean.hol_opam.thm_TREAL_MUL_LID holTheoryInst

theorem hol_TREAL_ADD_LDISTRIB : 
  ∀ (x y z : hreal × hreal), treal_eq (treal_mul x (treal_add y z)) (treal_add (treal_mul x y) (treal_mul x z)) := @HolLightLean.hol_opam.thm_TREAL_ADD_LDISTRIB holTheoryInst

theorem hol_TREAL_LE_REFL : 
  ∀ (x : hreal × hreal), treal_le x x := @HolLightLean.hol_opam.thm_TREAL_LE_REFL holTheoryInst

theorem hol_TREAL_LE_ANTISYM : 
  ∀ (x y : hreal × hreal), (treal_le x y ∧ treal_le y x) = treal_eq x y := @HolLightLean.hol_opam.thm_TREAL_LE_ANTISYM holTheoryInst

theorem hol_TREAL_LE_TRANS : 
  ∀ (x y z : hreal × hreal), treal_le x y ∧ treal_le y z → treal_le x z := @HolLightLean.hol_opam.thm_TREAL_LE_TRANS holTheoryInst

theorem hol_TREAL_LE_TOTAL : 
  ∀ (x y : hreal × hreal), treal_le x y ∨ treal_le y x := @HolLightLean.hol_opam.thm_TREAL_LE_TOTAL holTheoryInst

theorem hol_TREAL_LE_LADD_IMP : 
  ∀ (x y z : hreal × hreal), treal_le y z → treal_le (treal_add x y) (treal_add x z) := @HolLightLean.hol_opam.thm_TREAL_LE_LADD_IMP holTheoryInst

theorem hol_TREAL_LE_MUL : 
  ∀ (x y : hreal × hreal),
    treal_le (treal_of_num (0 : ℕ)) x ∧ treal_le (treal_of_num (0 : ℕ)) y →
      treal_le (treal_of_num (0 : ℕ)) (treal_mul x y) := @HolLightLean.hol_opam.thm_TREAL_LE_MUL holTheoryInst

theorem hol_TREAL_INV_0 : 
  treal_eq (treal_inv (treal_of_num (0 : ℕ))) (treal_of_num (0 : ℕ)) := @HolLightLean.hol_opam.thm_TREAL_INV_0 holTheoryInst

theorem hol_TREAL_MUL_LINV : 
  ∀ (x : hreal × hreal),
    ¬treal_eq x (treal_of_num (0 : ℕ)) →
      treal_eq (treal_mul (treal_inv x) x) (treal_of_num ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_TREAL_MUL_LINV holTheoryInst

theorem hol_TREAL_OF_NUM_WELLDEF : 
  ∀ (m n : ℕ), m = n → treal_eq (treal_of_num m) (treal_of_num n) := @HolLightLean.hol_opam.thm_TREAL_OF_NUM_WELLDEF holTheoryInst

theorem hol_TREAL_NEG_WELLDEF : 
  ∀ (x1 x2 : hreal × hreal), treal_eq x1 x2 → treal_eq (treal_neg x1) (treal_neg x2) := @HolLightLean.hol_opam.thm_TREAL_NEG_WELLDEF holTheoryInst

theorem hol_TREAL_ADD_WELLDEFR : 
  ∀ (x1 x2 y : hreal × hreal), treal_eq x1 x2 → treal_eq (treal_add x1 y) (treal_add x2 y) := @HolLightLean.hol_opam.thm_TREAL_ADD_WELLDEFR holTheoryInst

theorem hol_TREAL_ADD_WELLDEF : 
  ∀ (x1 x2 y1 y2 : hreal × hreal), treal_eq x1 x2 ∧ treal_eq y1 y2 → treal_eq (treal_add x1 y1) (treal_add x2 y2) := @HolLightLean.hol_opam.thm_TREAL_ADD_WELLDEF holTheoryInst

theorem hol_TREAL_MUL_WELLDEFR : 
  ∀ (x1 x2 y : hreal × hreal), treal_eq x1 x2 → treal_eq (treal_mul x1 y) (treal_mul x2 y) := @HolLightLean.hol_opam.thm_TREAL_MUL_WELLDEFR holTheoryInst

theorem hol_TREAL_MUL_WELLDEF : 
  ∀ (x1 x2 y1 y2 : hreal × hreal), treal_eq x1 x2 ∧ treal_eq y1 y2 → treal_eq (treal_mul x1 y1) (treal_mul x2 y2) := @HolLightLean.hol_opam.thm_TREAL_MUL_WELLDEF holTheoryInst

theorem hol_TREAL_EQ_IMP_LE : 
  ∀ (x y : hreal × hreal), treal_eq x y → treal_le x y := @HolLightLean.hol_opam.thm_TREAL_EQ_IMP_LE holTheoryInst

theorem hol_TREAL_LE_WELLDEF : 
  ∀ (x1 x2 y1 y2 : hreal × hreal), treal_eq x1 x2 ∧ treal_eq y1 y2 → treal_le x1 y1 = treal_le x2 y2 := @HolLightLean.hol_opam.thm_TREAL_LE_WELLDEF holTheoryInst

theorem hol_TREAL_INV_WELLDEF : 
  ∀ (x y : hreal × hreal), treal_eq x y → treal_eq (treal_inv x) (treal_inv y) := @HolLightLean.hol_opam.thm_TREAL_INV_WELLDEF holTheoryInst

theorem hol_REAL_ADD_SYM : 
  ∀ (x y : ℝ), x + y = y + x := @HolLightLean.hol_opam.thm_REAL_ADD_SYM holTheoryInst

theorem hol_REAL_ADD_ASSOC : 
  ∀ (x y z : ℝ), x + (y + z) = x + y + z := @HolLightLean.hol_opam.thm_REAL_ADD_ASSOC holTheoryInst

theorem hol_REAL_ADD_LID : 
  ∀ (x : ℝ), ↑(0 : ℕ) + x = x := @HolLightLean.hol_opam.thm_REAL_ADD_LID holTheoryInst

theorem hol_REAL_ADD_LINV : 
  ∀ (x : ℝ), -x + x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_ADD_LINV holTheoryInst

theorem hol_REAL_MUL_SYM : 
  ∀ (x y : ℝ), x * y = y * x := @HolLightLean.hol_opam.thm_REAL_MUL_SYM holTheoryInst

theorem hol_REAL_MUL_ASSOC : 
  ∀ (x y z : ℝ), x * (y * z) = x * y * z := @HolLightLean.hol_opam.thm_REAL_MUL_ASSOC holTheoryInst

theorem hol_REAL_MUL_LID : 
  ∀ (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * x = x := @HolLightLean.hol_opam.thm_REAL_MUL_LID holTheoryInst

theorem hol_REAL_ADD_LDISTRIB : 
  ∀ (x y z : ℝ), x * (y + z) = x * y + x * z := @HolLightLean.hol_opam.thm_REAL_ADD_LDISTRIB holTheoryInst

theorem hol_REAL_LE_REFL : 
  ∀ (x : ℝ), x ≤ x := @HolLightLean.hol_opam.thm_REAL_LE_REFL holTheoryInst

theorem hol_REAL_LE_ANTISYM : 
  ∀ (x y : ℝ), (x ≤ y ∧ y ≤ x) = (x = y) := @HolLightLean.hol_opam.thm_REAL_LE_ANTISYM holTheoryInst

theorem hol_REAL_LE_TRANS : 
  ∀ (x y z : ℝ), x ≤ y ∧ y ≤ z → x ≤ z := @HolLightLean.hol_opam.thm_REAL_LE_TRANS holTheoryInst

theorem hol_REAL_LE_TOTAL : 
  ∀ (x y : ℝ), x ≤ y ∨ y ≤ x := @HolLightLean.hol_opam.thm_REAL_LE_TOTAL holTheoryInst

theorem hol_REAL_LE_LADD_IMP : 
  ∀ (x y z : ℝ), y ≤ z → x + y ≤ x + z := @HolLightLean.hol_opam.thm_REAL_LE_LADD_IMP holTheoryInst

theorem hol_REAL_LE_MUL : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) ≤ x * y := @HolLightLean.hol_opam.thm_REAL_LE_MUL holTheoryInst

theorem hol_REAL_INV_0 : 
  Eq (α := ℝ) (↑(0 : ℕ))⁻¹ ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_INV_0 holTheoryInst

theorem hol_REAL_MUL_LINV : 
  ∀ (x : ℝ), ¬x = ↑(0 : ℕ) → x⁻¹ * x = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_MUL_LINV holTheoryInst

theorem hol_REAL_OF_NUM_EQ : 
  ∀ (m n : ℕ), Eq (α := ℝ) ↑m ↑n = (m = n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_EQ holTheoryInst

theorem hol_REAL_OF_NUM_LE : 
  ∀ (m n : ℕ), LE.le (α := ℝ) ↑m ↑n = (m ≤ n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_LE holTheoryInst

theorem hol_REAL_OF_NUM_ADD : 
  ∀ (m n : ℕ), HAdd.hAdd (α := ℝ) ↑m ↑n = ↑(m + n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_ADD holTheoryInst

theorem hol_REAL_OF_NUM_MUL : 
  ∀ (m n : ℕ), HMul.hMul (α := ℝ) ↑m ↑n = ↑(m * n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_MUL holTheoryInst

theorem hol_real_sub : 
  ∀ (x y : ℝ), x - y = x + -y := @HolLightLean.hol_opam.thm_real_sub holTheoryInst

theorem hol_real_lt : 
  ∀ (y x : ℝ), (x < y) = ¬y ≤ x := @HolLightLean.hol_opam.thm_real_lt holTheoryInst

theorem hol_real_ge : 
  ∀ (y x : ℝ), (x ≥ y) = (y ≤ x) := @HolLightLean.hol_opam.thm_real_ge holTheoryInst

theorem hol_real_gt : 
  ∀ (y x : ℝ), (x > y) = (y < x) := @HolLightLean.hol_opam.thm_real_gt holTheoryInst

theorem hol_real_abs : 
  ∀ (x : ℝ), |x| = if ↑(0 : ℕ) ≤ x then x else -x := @HolLightLean.hol_opam.thm_real_abs holTheoryInst

theorem hol_real_pow : 
  ∀ (x : ℝ), x ^ (0 : ℕ) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ ∀ (n : ℕ), x ^ (n + (1 : ℕ)) = x * x ^ n := @HolLightLean.hol_opam.thm_real_pow holTheoryInst

theorem hol_real_div : 
  ∀ (x y : ℝ), x / y = x * y⁻¹ := @HolLightLean.hol_opam.thm_real_div holTheoryInst

theorem hol_real_max : 
  ∀ (n m : ℝ), max m n = if m ≤ n then n else m := @HolLightLean.hol_opam.thm_real_max holTheoryInst

theorem hol_real_min : 
  ∀ (m n : ℝ), min m n = if m ≤ n then m else n := @HolLightLean.hol_opam.thm_real_min holTheoryInst

theorem hol_REAL_HREAL_LEMMA1 : 
  ∃ (r : hreal → ℝ), (∀ (x : ℝ), (↑(0 : ℕ) ≤ x) = ∃ (y : hreal), x = r y) ∧ ∀ (y z : hreal), hreal_le y z = (r y ≤ r z) := @HolLightLean.hol_opam.thm_REAL_HREAL_LEMMA1 holTheoryInst

theorem hol_REAL_HREAL_LEMMA2 : 
  ∃ (h : ℝ → hreal) (r : hreal → ℝ),
    (∀ (x : hreal), h (r x) = x) ∧
      (∀ (x : ℝ), ↑(0 : ℕ) ≤ x → r (h x) = x) ∧
        (∀ (x : hreal), ↑(0 : ℕ) ≤ r x) ∧ ∀ (x y : hreal), hreal_le x y = (r x ≤ r y) := @HolLightLean.hol_opam.thm_REAL_HREAL_LEMMA2 holTheoryInst

theorem hol_REAL_COMPLETE_SOMEPOS : 
  ∀ (P : Set ℝ),
    ((∃ (x : ℝ), P x ∧ ↑(0 : ℕ) ≤ x) ∧ ∃ (M : ℝ), ∀ (x : ℝ), P x → x ≤ M) →
      ∃ (M : ℝ), (∀ (x : ℝ), P x → x ≤ M) ∧ ∀ (M' : ℝ), (∀ (x : ℝ), P x → x ≤ M') → M ≤ M' := @HolLightLean.hol_opam.thm_REAL_COMPLETE_SOMEPOS holTheoryInst

theorem hol_REAL_COMPLETE : 
  ∀ (P : Set ℝ),
    ((∃ (x : ℝ), P x) ∧ ∃ (M : ℝ), ∀ (x : ℝ), P x → x ≤ M) →
      ∃ (M : ℝ), (∀ (x : ℝ), P x → x ≤ M) ∧ ∀ (M' : ℝ), (∀ (x : ℝ), P x → x ≤ M') → M ≤ M' := @HolLightLean.hol_opam.thm_REAL_COMPLETE holTheoryInst

theorem hol_REAL_ADD_AC : 
  ∀ (n m p : ℝ), m + n = n + m ∧ m + n + p = m + (n + p) ∧ m + (n + p) = n + (m + p) := @HolLightLean.hol_opam.thm_REAL_ADD_AC holTheoryInst

theorem hol_REAL_ADD_RINV : 
  ∀ (x : ℝ), x + -x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_ADD_RINV holTheoryInst

theorem hol_REAL_EQ_ADD_LCANCEL : 
  ∀ (x y z : ℝ), (x + y = x + z) = (y = z) := @HolLightLean.hol_opam.thm_REAL_EQ_ADD_LCANCEL holTheoryInst

theorem hol_REAL_EQ_ADD_RCANCEL : 
  ∀ (x y z : ℝ), (x + z = y + z) = (x = y) := @HolLightLean.hol_opam.thm_REAL_EQ_ADD_RCANCEL holTheoryInst

theorem hol_REAL_MUL_RZERO : 
  ∀ (x : ℝ), x * ↑(0 : ℕ) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_MUL_RZERO holTheoryInst

theorem hol_REAL_MUL_LZERO : 
  ∀ (x : ℝ), ↑(0 : ℕ) * x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_MUL_LZERO holTheoryInst

theorem hol_REAL_NEG_NEG : 
  ∀ (x : ℝ), - -x = x := @HolLightLean.hol_opam.thm_REAL_NEG_NEG holTheoryInst

theorem hol_REAL_MUL_RNEG : 
  ∀ (x y : ℝ), x * -y = -(x * y) := @HolLightLean.hol_opam.thm_REAL_MUL_RNEG holTheoryInst

theorem hol_REAL_MUL_LNEG : 
  ∀ (x y : ℝ), -x * y = -(x * y) := @HolLightLean.hol_opam.thm_REAL_MUL_LNEG holTheoryInst

theorem hol_REAL_NEG_ADD : 
  ∀ (x y : ℝ), -(x + y) = -x + -y := @HolLightLean.hol_opam.thm_REAL_NEG_ADD holTheoryInst

theorem hol_REAL_ADD_RID : 
  ∀ (x : ℝ), x + ↑(0 : ℕ) = x := @HolLightLean.hol_opam.thm_REAL_ADD_RID holTheoryInst

theorem hol_REAL_NEG_0 : 
  Eq (α := ℝ) (-↑(0 : ℕ)) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_NEG_0 holTheoryInst

theorem hol_REAL_LE_LNEG : 
  ∀ (x y : ℝ), (-x ≤ y) = (↑(0 : ℕ) ≤ x + y) := @HolLightLean.hol_opam.thm_REAL_LE_LNEG holTheoryInst

theorem hol_REAL_LE_NEG2 : 
  ∀ (x y : ℝ), (-x ≤ -y) = (y ≤ x) := @HolLightLean.hol_opam.thm_REAL_LE_NEG2 holTheoryInst

theorem hol_REAL_LE_RNEG : 
  ∀ (x y : ℝ), (x ≤ -y) = (x + y ≤ ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_LE_RNEG holTheoryInst

theorem hol_REAL_OF_NUM_POW : 
  ∀ (x n : ℕ), HPow.hPow (α := ℝ) (↑x) n = ↑(x ^ n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_POW holTheoryInst

theorem hol_REAL_POW_NEG : 
  ∀ (x : ℝ) (n : ℕ), (-x) ^ n = if Even n then x ^ n else -x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_NEG holTheoryInst

theorem hol_REAL_ABS_NUM : 
  ∀ (n : ℕ), Eq (α := ℝ) |↑n| ↑n := @HolLightLean.hol_opam.thm_REAL_ABS_NUM holTheoryInst

theorem hol_REAL_ABS_NEG : 
  ∀ (x : ℝ), |(-x)| = |x| := @HolLightLean.hol_opam.thm_REAL_ABS_NEG holTheoryInst

theorem hol_REAL_LTE_TOTAL : 
  ∀ (x y : ℝ), x < y ∨ y ≤ x := @HolLightLean.hol_opam.thm_REAL_LTE_TOTAL holTheoryInst

theorem hol_REAL_LET_TOTAL : 
  ∀ (x y : ℝ), x ≤ y ∨ y < x := @HolLightLean.hol_opam.thm_REAL_LET_TOTAL holTheoryInst

theorem hol_REAL_LT_IMP_LE : 
  ∀ (x y : ℝ), x < y → x ≤ y := @HolLightLean.hol_opam.thm_REAL_LT_IMP_LE holTheoryInst

theorem hol_REAL_LTE_TRANS : 
  ∀ (x y z : ℝ), x < y ∧ y ≤ z → x < z := @HolLightLean.hol_opam.thm_REAL_LTE_TRANS holTheoryInst

theorem hol_REAL_LET_TRANS : 
  ∀ (x y z : ℝ), x ≤ y ∧ y < z → x < z := @HolLightLean.hol_opam.thm_REAL_LET_TRANS holTheoryInst

theorem hol_REAL_LT_TRANS : 
  ∀ (x y z : ℝ), x < y ∧ y < z → x < z := @HolLightLean.hol_opam.thm_REAL_LT_TRANS holTheoryInst

theorem hol_REAL_LE_ADD : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) ≤ x + y := @HolLightLean.hol_opam.thm_REAL_LE_ADD holTheoryInst

theorem hol_REAL_LTE_ANTISYM : 
  ∀ (x y : ℝ), ¬(x < y ∧ y ≤ x) := @HolLightLean.hol_opam.thm_REAL_LTE_ANTISYM holTheoryInst

theorem hol_REAL_SUB_LE : 
  ∀ (x y : ℝ), (↑(0 : ℕ) ≤ x - y) = (y ≤ x) := @HolLightLean.hol_opam.thm_REAL_SUB_LE holTheoryInst

theorem hol_REAL_NEG_SUB : 
  ∀ (x y : ℝ), -(x - y) = y - x := @HolLightLean.hol_opam.thm_REAL_NEG_SUB holTheoryInst

theorem hol_REAL_LE_LT : 
  ∀ (x y : ℝ), (x ≤ y) = (x < y ∨ x = y) := @HolLightLean.hol_opam.thm_REAL_LE_LT holTheoryInst

theorem hol_REAL_SUB_LT : 
  ∀ (x y : ℝ), (↑(0 : ℕ) < x - y) = (y < x) := @HolLightLean.hol_opam.thm_REAL_SUB_LT holTheoryInst

theorem hol_REAL_NOT_LT : 
  ∀ (x y : ℝ), (¬x < y) = (y ≤ x) := @HolLightLean.hol_opam.thm_REAL_NOT_LT holTheoryInst

theorem hol_REAL_SUB_0 : 
  ∀ (x y : ℝ), (x - y = ↑(0 : ℕ)) = (x = y) := @HolLightLean.hol_opam.thm_REAL_SUB_0 holTheoryInst

theorem hol_REAL_LT_LE : 
  ∀ (x y : ℝ), (x < y) = (x ≤ y ∧ ¬x = y) := @HolLightLean.hol_opam.thm_REAL_LT_LE holTheoryInst

theorem hol_REAL_LT_REFL : 
  ∀ (x : ℝ), ¬x < x := @HolLightLean.hol_opam.thm_REAL_LT_REFL holTheoryInst

theorem hol_REAL_LTE_ADD : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) < x + y := @HolLightLean.hol_opam.thm_REAL_LTE_ADD holTheoryInst

theorem hol_REAL_LET_ADD : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x + y := @HolLightLean.hol_opam.thm_REAL_LET_ADD holTheoryInst

theorem hol_REAL_LT_ADD : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x + y := @HolLightLean.hol_opam.thm_REAL_LT_ADD holTheoryInst

theorem hol_REAL_ENTIRE : 
  ∀ (x y : ℝ), (x * y = ↑(0 : ℕ)) = (x = ↑(0 : ℕ) ∨ y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_ENTIRE holTheoryInst

theorem hol_REAL_LE_NEGTOTAL : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x ∨ ↑(0 : ℕ) ≤ -x := @HolLightLean.hol_opam.thm_REAL_LE_NEGTOTAL holTheoryInst

theorem hol_REAL_LE_SQUARE : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x * x := @HolLightLean.hol_opam.thm_REAL_LE_SQUARE holTheoryInst

theorem hol_REAL_MUL_RID : 
  ∀ (x : ℝ), x * ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = x := @HolLightLean.hol_opam.thm_REAL_MUL_RID holTheoryInst

theorem hol_REAL_POW_2 : 
  ∀ (x : ℝ), x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x * x := @HolLightLean.hol_opam.thm_REAL_POW_2 holTheoryInst

theorem hol_REAL_POLY_CLAUSES : 
  (∀ (x y z : ℝ), x + (y + z) = x + y + z) ∧
    (∀ (x y : ℝ), x + y = y + x) ∧
      (∀ (x : ℝ), ↑(0 : ℕ) + x = x) ∧
        (∀ (x y z : ℝ), x * (y * z) = x * y * z) ∧
          (∀ (x y : ℝ), x * y = y * x) ∧
            (∀ (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * x = x) ∧
              (∀ (x : ℝ), ↑(0 : ℕ) * x = ↑(0 : ℕ)) ∧
                (∀ (x y z : ℝ), x * (y + z) = x * y + x * z) ∧
                  (∀ (x : ℝ), x ^ (0 : ℕ) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∧
                    ∀ (x : ℝ) (n : ℕ), x ^ (n + (1 : ℕ)) = x * x ^ n := @HolLightLean.hol_opam.thm_REAL_POLY_CLAUSES holTheoryInst

theorem hol_REAL_POLY_NEG_CLAUSES : 
  (∀ (x : ℝ), -x = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * x) ∧ ∀ (x y : ℝ), x - y = x + -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * y := @HolLightLean.hol_opam.thm_REAL_POLY_NEG_CLAUSES holTheoryInst

theorem hol_REAL_POS : 
  ∀ (n : ℕ), LE.le (α := ℝ) ↑(0 : ℕ) ↑n := @HolLightLean.hol_opam.thm_REAL_POS holTheoryInst

theorem hol_REAL_LT_NZ : 
  ∀ (n : ℕ), (¬Eq (α := ℝ) ↑n ↑(0 : ℕ)) = LT.lt (α := ℝ) ↑(0 : ℕ) ↑n := @HolLightLean.hol_opam.thm_REAL_LT_NZ holTheoryInst

theorem hol_REAL_POS_LT : 
  ∀ (n : ℕ), LT.lt (α := ℝ) ↑(0 : ℕ) ↑(n + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POS_LT holTheoryInst

theorem hol_REAL_OF_NUM_LT : 
  ∀ (m n : ℕ), LT.lt (α := ℝ) ↑m ↑n = (m < n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_LT holTheoryInst

theorem hol_REAL_OF_NUM_GE : 
  ∀ (m n : ℕ), GE.ge (α := ℝ) ↑m ↑n = (m ≥ n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_GE holTheoryInst

theorem hol_REAL_OF_NUM_GT : 
  ∀ (m n : ℕ), GT.gt (α := ℝ) ↑m ↑n = (m > n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_GT holTheoryInst

theorem hol_REAL_OF_NUM_MAX : 
  ∀ (m n : ℕ), Eq (α := ℝ) (max ↑m ↑n) ↑(max m n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_MAX holTheoryInst

theorem hol_REAL_OF_NUM_MIN : 
  ∀ (m n : ℕ), Eq (α := ℝ) (min ↑m ↑n) ↑(min m n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_MIN holTheoryInst

theorem hol_REAL_OF_NUM_SUC : 
  ∀ (n : ℕ), HAdd.hAdd (α := ℝ) ↑n ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = ↑(n + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_SUC holTheoryInst

theorem hol_REAL_OF_NUM_SUB : 
  ∀ (m n : ℕ), m ≤ n → HSub.hSub (α := ℝ) ↑n ↑m = ↑(n - m) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_SUB holTheoryInst

theorem hol_REAL_OF_NUM_SUB_CASES : 
  ∀ (m n : ℕ), HSub.hSub (α := ℝ) ↑m ↑n = if n ≤ m then ↑(m - n) else -↑(n - m) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_SUB_CASES holTheoryInst

theorem hol_REAL_OF_NUM_CLAUSES : 
  (∀ (m n : ℕ), Eq (α := ℝ) ↑m ↑n = (m = n)) ∧
    (∀ (m n : ℕ), GE.ge (α := ℝ) ↑m ↑n = (m ≥ n)) ∧
      (∀ (m n : ℕ), GT.gt (α := ℝ) ↑m ↑n = (m > n)) ∧
        (∀ (m n : ℕ), LE.le (α := ℝ) ↑m ↑n = (m ≤ n)) ∧
          (∀ (m n : ℕ), LT.lt (α := ℝ) ↑m ↑n = (m < n)) ∧
            (∀ (m n : ℕ), Eq (α := ℝ) (max ↑m ↑n) ↑(max m n)) ∧
              (∀ (m n : ℕ), Eq (α := ℝ) (min ↑m ↑n) ↑(min m n)) ∧
                (∀ (m n : ℕ), HAdd.hAdd (α := ℝ) ↑m ↑n = ↑(m + n)) ∧
                  (∀ (m n : ℕ), HMul.hMul (α := ℝ) ↑m ↑n = ↑(m * n)) ∧ ∀ (x n : ℕ), HPow.hPow (α := ℝ) (↑x) n = ↑(x ^ n) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_CLAUSES holTheoryInst

theorem hol_REAL_MUL_AC : 
  ∀ (n m p : ℝ), m * n = n * m ∧ m * n * p = m * (n * p) ∧ m * (n * p) = n * (m * p) := @HolLightLean.hol_opam.thm_REAL_MUL_AC holTheoryInst

theorem hol_REAL_ADD_RDISTRIB : 
  ∀ (x y z : ℝ), (x + y) * z = x * z + y * z := @HolLightLean.hol_opam.thm_REAL_ADD_RDISTRIB holTheoryInst

theorem hol_REAL_LT_LADD_IMP : 
  ∀ (x y z : ℝ), y < z → x + y < x + z := @HolLightLean.hol_opam.thm_REAL_LT_LADD_IMP holTheoryInst

theorem hol_REAL_LT_MUL : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x * y := @HolLightLean.hol_opam.thm_REAL_LT_MUL holTheoryInst

theorem hol_REAL_EQ_ADD_LCANCEL_0 : 
  ∀ (x y : ℝ), (x + y = x) = (y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_EQ_ADD_LCANCEL_0 holTheoryInst

theorem hol_REAL_EQ_ADD_RCANCEL_0 : 
  ∀ (x y : ℝ), (x + y = y) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_EQ_ADD_RCANCEL_0 holTheoryInst

theorem hol_REAL_LNEG_UNIQ : 
  ∀ (x y : ℝ), (x + y = ↑(0 : ℕ)) = (x = -y) := @HolLightLean.hol_opam.thm_REAL_LNEG_UNIQ holTheoryInst

theorem hol_REAL_RNEG_UNIQ : 
  ∀ (x y : ℝ), (x + y = ↑(0 : ℕ)) = (y = -x) := @HolLightLean.hol_opam.thm_REAL_RNEG_UNIQ holTheoryInst

theorem hol_REAL_NEG_LMUL : 
  ∀ (x y : ℝ), -(x * y) = -x * y := @HolLightLean.hol_opam.thm_REAL_NEG_LMUL holTheoryInst

theorem hol_REAL_NEG_RMUL : 
  ∀ (x y : ℝ), -(x * y) = x * -y := @HolLightLean.hol_opam.thm_REAL_NEG_RMUL holTheoryInst

theorem hol_REAL_NEG_MUL2 : 
  ∀ (x y : ℝ), -x * -y = x * y := @HolLightLean.hol_opam.thm_REAL_NEG_MUL2 holTheoryInst

theorem hol_REAL_LT_LADD : 
  ∀ (x y z : ℝ), (x + y < x + z) = (y < z) := @HolLightLean.hol_opam.thm_REAL_LT_LADD holTheoryInst

theorem hol_REAL_LT_RADD : 
  ∀ (x y z : ℝ), (x + z < y + z) = (x < y) := @HolLightLean.hol_opam.thm_REAL_LT_RADD holTheoryInst

theorem hol_REAL_LT_ANTISYM : 
  ∀ (x y : ℝ), ¬(x < y ∧ y < x) := @HolLightLean.hol_opam.thm_REAL_LT_ANTISYM holTheoryInst

theorem hol_REAL_LT_GT : 
  ∀ (x y : ℝ), x < y → ¬y < x := @HolLightLean.hol_opam.thm_REAL_LT_GT holTheoryInst

theorem hol_REAL_NOT_EQ : 
  ∀ (x y : ℝ), (¬x = y) = (x < y ∨ y < x) := @HolLightLean.hol_opam.thm_REAL_NOT_EQ holTheoryInst

theorem hol_REAL_NOT_LE : 
  ∀ (x y : ℝ), (¬x ≤ y) = (y < x) := @HolLightLean.hol_opam.thm_REAL_NOT_LE holTheoryInst

theorem hol_REAL_LET_ANTISYM : 
  ∀ (x y : ℝ), ¬(x ≤ y ∧ y < x) := @HolLightLean.hol_opam.thm_REAL_LET_ANTISYM holTheoryInst

theorem hol_REAL_NEG_LT0 : 
  ∀ (x : ℝ), (-x < ↑(0 : ℕ)) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_REAL_NEG_LT0 holTheoryInst

theorem hol_REAL_NEG_GT0 : 
  ∀ (x : ℝ), (↑(0 : ℕ) < -x) = (x < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_NEG_GT0 holTheoryInst

theorem hol_REAL_NEG_LE0 : 
  ∀ (x : ℝ), (-x ≤ ↑(0 : ℕ)) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_NEG_LE0 holTheoryInst

theorem hol_REAL_NEG_GE0 : 
  ∀ (x : ℝ), (↑(0 : ℕ) ≤ -x) = (x ≤ ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_NEG_GE0 holTheoryInst

theorem hol_REAL_LT_TOTAL : 
  ∀ (x y : ℝ), x = y ∨ x < y ∨ y < x := @HolLightLean.hol_opam.thm_REAL_LT_TOTAL holTheoryInst

theorem hol_REAL_LT_NEGTOTAL : 
  ∀ (x : ℝ), x = ↑(0 : ℕ) ∨ ↑(0 : ℕ) < x ∨ ↑(0 : ℕ) < -x := @HolLightLean.hol_opam.thm_REAL_LT_NEGTOTAL holTheoryInst

theorem hol_REAL_LE_01 : 
  LE.le (α := ℝ) ↑(0 : ℕ) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_LE_01 holTheoryInst

theorem hol_REAL_LT_01 : 
  LT.lt (α := ℝ) ↑(0 : ℕ) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_LT_01 holTheoryInst

theorem hol_REAL_LE_LADD : 
  ∀ (x y z : ℝ), (x + y ≤ x + z) = (y ≤ z) := @HolLightLean.hol_opam.thm_REAL_LE_LADD holTheoryInst

theorem hol_REAL_LE_RADD : 
  ∀ (x y z : ℝ), (x + z ≤ y + z) = (x ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_RADD holTheoryInst

theorem hol_REAL_LT_ADD2 : 
  ∀ (w x y z : ℝ), w < x ∧ y < z → w + y < x + z := @HolLightLean.hol_opam.thm_REAL_LT_ADD2 holTheoryInst

theorem hol_REAL_LE_ADD2 : 
  ∀ (w x y z : ℝ), w ≤ x ∧ y ≤ z → w + y ≤ x + z := @HolLightLean.hol_opam.thm_REAL_LE_ADD2 holTheoryInst

theorem hol_REAL_LT_LNEG : 
  ∀ (x y : ℝ), (-x < y) = (↑(0 : ℕ) < x + y) := @HolLightLean.hol_opam.thm_REAL_LT_LNEG holTheoryInst

theorem hol_REAL_LT_RNEG : 
  ∀ (x y : ℝ), (x < -y) = (x + y < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_LT_RNEG holTheoryInst

theorem hol_REAL_LT_ADDNEG : 
  ∀ (x y z : ℝ), (y < x + -z) = (y + z < x) := @HolLightLean.hol_opam.thm_REAL_LT_ADDNEG holTheoryInst

theorem hol_REAL_LT_ADDNEG2 : 
  ∀ (x y z : ℝ), (x + -y < z) = (x < z + y) := @HolLightLean.hol_opam.thm_REAL_LT_ADDNEG2 holTheoryInst

theorem hol_REAL_LT_ADD1 : 
  ∀ (x y : ℝ), x ≤ y → x < y + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_LT_ADD1 holTheoryInst

theorem hol_REAL_SUB_ADD : 
  ∀ (x y : ℝ), x - y + y = x := @HolLightLean.hol_opam.thm_REAL_SUB_ADD holTheoryInst

theorem hol_REAL_SUB_ADD2 : 
  ∀ (x y : ℝ), y + (x - y) = x := @HolLightLean.hol_opam.thm_REAL_SUB_ADD2 holTheoryInst

theorem hol_REAL_SUB_REFL : 
  ∀ (x : ℝ), x - x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_SUB_REFL holTheoryInst

theorem hol_REAL_LE_DOUBLE : 
  ∀ (x : ℝ), (↑(0 : ℕ) ≤ x + x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_LE_DOUBLE holTheoryInst

theorem hol_REAL_LE_NEGL : 
  ∀ (x : ℝ), (-x ≤ x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_LE_NEGL holTheoryInst

theorem hol_REAL_LE_NEGR : 
  ∀ (x : ℝ), (x ≤ -x) = (x ≤ ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_LE_NEGR holTheoryInst

theorem hol_REAL_NEG_EQ_0 : 
  ∀ (x : ℝ), (-x = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_NEG_EQ_0 holTheoryInst

theorem hol_REAL_ADD_SUB : 
  ∀ (x y : ℝ), x + y - x = y := @HolLightLean.hol_opam.thm_REAL_ADD_SUB holTheoryInst

theorem hol_REAL_NEG_EQ : 
  ∀ (x y : ℝ), (-x = y) = (x = -y) := @HolLightLean.hol_opam.thm_REAL_NEG_EQ holTheoryInst

theorem hol_REAL_NEG_MINUS1 : 
  ∀ (x : ℝ), -x = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * x := @HolLightLean.hol_opam.thm_REAL_NEG_MINUS1 holTheoryInst

theorem hol_REAL_LT_IMP_NE : 
  ∀ (x y : ℝ), x < y → ¬x = y := @HolLightLean.hol_opam.thm_REAL_LT_IMP_NE holTheoryInst

theorem hol_REAL_LE_ADDR : 
  ∀ (x y : ℝ), (x ≤ x + y) = (↑(0 : ℕ) ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_ADDR holTheoryInst

theorem hol_REAL_LE_ADDL : 
  ∀ (x y : ℝ), (y ≤ x + y) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_LE_ADDL holTheoryInst

theorem hol_REAL_LT_ADDR : 
  ∀ (x y : ℝ), (x < x + y) = (↑(0 : ℕ) < y) := @HolLightLean.hol_opam.thm_REAL_LT_ADDR holTheoryInst

theorem hol_REAL_LT_ADDL : 
  ∀ (x y : ℝ), (y < x + y) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_REAL_LT_ADDL holTheoryInst

theorem hol_REAL_SUB_SUB : 
  ∀ (x y : ℝ), x - y - x = -y := @HolLightLean.hol_opam.thm_REAL_SUB_SUB holTheoryInst

theorem hol_REAL_LT_ADD_SUB : 
  ∀ (x y z : ℝ), (x + y < z) = (x < z - y) := @HolLightLean.hol_opam.thm_REAL_LT_ADD_SUB holTheoryInst

theorem hol_REAL_LT_SUB_RADD : 
  ∀ (x y z : ℝ), (x - y < z) = (x < z + y) := @HolLightLean.hol_opam.thm_REAL_LT_SUB_RADD holTheoryInst

theorem hol_REAL_LT_SUB_LADD : 
  ∀ (x y z : ℝ), (x < y - z) = (x + z < y) := @HolLightLean.hol_opam.thm_REAL_LT_SUB_LADD holTheoryInst

theorem hol_REAL_LE_SUB_LADD : 
  ∀ (x y z : ℝ), (x ≤ y - z) = (x + z ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_SUB_LADD holTheoryInst

theorem hol_REAL_LE_SUB_RADD : 
  ∀ (x y z : ℝ), (x - y ≤ z) = (x ≤ z + y) := @HolLightLean.hol_opam.thm_REAL_LE_SUB_RADD holTheoryInst

theorem hol_REAL_ADD2_SUB2 : 
  ∀ (a b c d : ℝ), a + b - (c + d) = a - c + (b - d) := @HolLightLean.hol_opam.thm_REAL_ADD2_SUB2 holTheoryInst

theorem hol_REAL_SUB_LZERO : 
  ∀ (x : ℝ), ↑(0 : ℕ) - x = -x := @HolLightLean.hol_opam.thm_REAL_SUB_LZERO holTheoryInst

theorem hol_REAL_SUB_RZERO : 
  ∀ (x : ℝ), x - ↑(0 : ℕ) = x := @HolLightLean.hol_opam.thm_REAL_SUB_RZERO holTheoryInst

theorem hol_REAL_LET_ADD2 : 
  ∀ (w x y z : ℝ), w ≤ x ∧ y < z → w + y < x + z := @HolLightLean.hol_opam.thm_REAL_LET_ADD2 holTheoryInst

theorem hol_REAL_LTE_ADD2 : 
  ∀ (w x y z : ℝ), w < x ∧ y ≤ z → w + y < x + z := @HolLightLean.hol_opam.thm_REAL_LTE_ADD2 holTheoryInst

theorem hol_REAL_SUB_LNEG : 
  ∀ (x y : ℝ), -x - y = -(x + y) := @HolLightLean.hol_opam.thm_REAL_SUB_LNEG holTheoryInst

theorem hol_REAL_SUB_RNEG : 
  ∀ (x y : ℝ), x - -y = x + y := @HolLightLean.hol_opam.thm_REAL_SUB_RNEG holTheoryInst

theorem hol_REAL_SUB_NEG2 : 
  ∀ (x y : ℝ), -x - -y = y - x := @HolLightLean.hol_opam.thm_REAL_SUB_NEG2 holTheoryInst

theorem hol_REAL_SUB_TRIANGLE : 
  ∀ (a b c : ℝ), a - b + (b - c) = a - c := @HolLightLean.hol_opam.thm_REAL_SUB_TRIANGLE holTheoryInst

theorem hol_REAL_EQ_SUB_LADD : 
  ∀ (x y z : ℝ), (x = y - z) = (x + z = y) := @HolLightLean.hol_opam.thm_REAL_EQ_SUB_LADD holTheoryInst

theorem hol_REAL_EQ_SUB_RADD : 
  ∀ (x y z : ℝ), (x - y = z) = (x = z + y) := @HolLightLean.hol_opam.thm_REAL_EQ_SUB_RADD holTheoryInst

theorem hol_REAL_SUB_SUB2 : 
  ∀ (x y : ℝ), x - (x - y) = y := @HolLightLean.hol_opam.thm_REAL_SUB_SUB2 holTheoryInst

theorem hol_REAL_ADD_SUB2 : 
  ∀ (x y : ℝ), x - (x + y) = -y := @HolLightLean.hol_opam.thm_REAL_ADD_SUB2 holTheoryInst

theorem hol_REAL_EQ_IMP_LE : 
  ∀ (x y : ℝ), x = y → x ≤ y := @HolLightLean.hol_opam.thm_REAL_EQ_IMP_LE holTheoryInst

theorem hol_REAL_LT_IMP_NZ : 
  ∀ (x : ℝ), ↑(0 : ℕ) < x → ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_LT_IMP_NZ holTheoryInst

theorem hol_REAL_DIFFSQ : 
  ∀ (x y : ℝ), (x + y) * (x - y) = x * x - y * y := @HolLightLean.hol_opam.thm_REAL_DIFFSQ holTheoryInst

theorem hol_REAL_EQ_NEG2 : 
  ∀ (x y : ℝ), (-x = -y) = (x = y) := @HolLightLean.hol_opam.thm_REAL_EQ_NEG2 holTheoryInst

theorem hol_REAL_LT_NEG2 : 
  ∀ (x y : ℝ), (-x < -y) = (y < x) := @HolLightLean.hol_opam.thm_REAL_LT_NEG2 holTheoryInst

theorem hol_REAL_SUB_LDISTRIB : 
  ∀ (x y z : ℝ), x * (y - z) = x * y - x * z := @HolLightLean.hol_opam.thm_REAL_SUB_LDISTRIB holTheoryInst

theorem hol_REAL_SUB_RDISTRIB : 
  ∀ (x y z : ℝ), (x - y) * z = x * z - y * z := @HolLightLean.hol_opam.thm_REAL_SUB_RDISTRIB holTheoryInst

theorem hol_REAL_ABS_ZERO : 
  ∀ (x : ℝ), (|x| = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_ABS_ZERO holTheoryInst

theorem hol_REAL_ABS_0 : 
  Eq (α := ℝ) |↑(0 : ℕ)| ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_ABS_0 holTheoryInst

theorem hol_REAL_ABS_1 : 
  Eq (α := ℝ) |↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))| ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_ABS_1 holTheoryInst

theorem hol_REAL_ABS_TRIANGLE : 
  ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := @HolLightLean.hol_opam.thm_REAL_ABS_TRIANGLE holTheoryInst

theorem hol_REAL_ABS_TRIANGLE_LE : 
  ∀ (x y z : ℝ), |x| + |y - x| ≤ z → |y| ≤ z := @HolLightLean.hol_opam.thm_REAL_ABS_TRIANGLE_LE holTheoryInst

theorem hol_REAL_ABS_TRIANGLE_LT : 
  ∀ (x y z : ℝ), |x| + |y - x| < z → |y| < z := @HolLightLean.hol_opam.thm_REAL_ABS_TRIANGLE_LT holTheoryInst

theorem hol_REAL_ABS_POS : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ |x| := @HolLightLean.hol_opam.thm_REAL_ABS_POS holTheoryInst

theorem hol_REAL_ABS_SUB : 
  ∀ (x y : ℝ), |x - y| = |y - x| := @HolLightLean.hol_opam.thm_REAL_ABS_SUB holTheoryInst

theorem hol_REAL_ABS_NZ : 
  ∀ (x : ℝ), (¬x = ↑(0 : ℕ)) = (↑(0 : ℕ) < |x|) := @HolLightLean.hol_opam.thm_REAL_ABS_NZ holTheoryInst

theorem hol_REAL_ABS_ABS : 
  ∀ (x : ℝ), |(|x|)| = |x| := @HolLightLean.hol_opam.thm_REAL_ABS_ABS holTheoryInst

theorem hol_REAL_ABS_LE : 
  ∀ (x : ℝ), x ≤ |x| := @HolLightLean.hol_opam.thm_REAL_ABS_LE holTheoryInst

theorem hol_REAL_ABS_REFL : 
  ∀ (x : ℝ), (|x| = x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_ABS_REFL holTheoryInst

theorem hol_REAL_ABS_BETWEEN : 
  ∀ (x y d : ℝ), (↑(0 : ℕ) < d ∧ x - d < y ∧ y < x + d) = (|y - x| < d) := @HolLightLean.hol_opam.thm_REAL_ABS_BETWEEN holTheoryInst

theorem hol_REAL_ABS_BOUND : 
  ∀ (x y d : ℝ), |x - y| < d → y < x + d := @HolLightLean.hol_opam.thm_REAL_ABS_BOUND holTheoryInst

theorem hol_REAL_ABS_STILLNZ : 
  ∀ (x y : ℝ), |x - y| < |y| → ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_ABS_STILLNZ holTheoryInst

theorem hol_REAL_ABS_CASES : 
  ∀ (x : ℝ), x = ↑(0 : ℕ) ∨ ↑(0 : ℕ) < |x| := @HolLightLean.hol_opam.thm_REAL_ABS_CASES holTheoryInst

theorem hol_REAL_ABS_BETWEEN1 : 
  ∀ (x y z : ℝ), x < z ∧ |y - x| < z - x → y < z := @HolLightLean.hol_opam.thm_REAL_ABS_BETWEEN1 holTheoryInst

theorem hol_REAL_ABS_SIGN : 
  ∀ (x y : ℝ), |x - y| < y → ↑(0 : ℕ) < x := @HolLightLean.hol_opam.thm_REAL_ABS_SIGN holTheoryInst

theorem hol_REAL_ABS_SIGN2 : 
  ∀ (x y : ℝ), |x - y| < -y → x < ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_ABS_SIGN2 holTheoryInst

theorem hol_REAL_ABS_CIRCLE : 
  ∀ (x y h : ℝ), |h| < |y| - |x| → |x + h| < |y| := @HolLightLean.hol_opam.thm_REAL_ABS_CIRCLE holTheoryInst

theorem hol_REAL_SUB_ABS : 
  ∀ (x y : ℝ), |x| - |y| ≤ |x - y| := @HolLightLean.hol_opam.thm_REAL_SUB_ABS holTheoryInst

theorem hol_REAL_ABS_SUB_ABS : 
  ∀ (x y : Real),
    @LE.le Real Real.instLE
      (@abs Real Real.lattice Real.instAddGroup
        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@abs Real Real.lattice Real.instAddGroup x)
          (@abs Real Real.lattice Real.instAddGroup y)))
      (@abs Real Real.lattice Real.instAddGroup (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) x y)) := @HolLightLean.hol_opam.thm_REAL_ABS_SUB_ABS holTheoryInst

theorem hol_REAL_ABS_BETWEEN2 : 
  ∀ (x0 x y0 y : ℝ),
    x0 < y0 ∧
        ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * |x - x0| < y0 - x0 ∧
          ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * |y - y0| < y0 - x0 →
      x < y := @HolLightLean.hol_opam.thm_REAL_ABS_BETWEEN2 holTheoryInst

theorem hol_REAL_ABS_BOUNDS : 
  ∀ (x k : ℝ), (|x| ≤ k) = (-k ≤ x ∧ x ≤ k) := @HolLightLean.hol_opam.thm_REAL_ABS_BOUNDS holTheoryInst

theorem hol_REAL_BOUNDS_LE : 
  ∀ (x k : ℝ), (-k ≤ x ∧ x ≤ k) = (|x| ≤ k) := @HolLightLean.hol_opam.thm_REAL_BOUNDS_LE holTheoryInst

theorem hol_REAL_BOUNDS_LT : 
  ∀ (x k : ℝ), (-k < x ∧ x < k) = (|x| < k) := @HolLightLean.hol_opam.thm_REAL_BOUNDS_LT holTheoryInst

theorem hol_REAL_MIN_MAX : 
  ∀ (x y : ℝ), min x y = -max (-x) (-y) := @HolLightLean.hol_opam.thm_REAL_MIN_MAX holTheoryInst

theorem hol_REAL_MAX_MIN : 
  ∀ (x y : ℝ), max x y = -min (-x) (-y) := @HolLightLean.hol_opam.thm_REAL_MAX_MIN holTheoryInst

theorem hol_REAL_MAX_MAX : 
  ∀ (x y : ℝ), x ≤ max x y ∧ y ≤ max x y := @HolLightLean.hol_opam.thm_REAL_MAX_MAX holTheoryInst

theorem hol_REAL_MIN_MIN : 
  ∀ (x y : ℝ), min x y ≤ x ∧ min x y ≤ y := @HolLightLean.hol_opam.thm_REAL_MIN_MIN holTheoryInst

theorem hol_REAL_MAX_SYM : 
  ∀ (x y : ℝ), max x y = max y x := @HolLightLean.hol_opam.thm_REAL_MAX_SYM holTheoryInst

theorem hol_REAL_MIN_SYM : 
  ∀ (x y : ℝ), min x y = min y x := @HolLightLean.hol_opam.thm_REAL_MIN_SYM holTheoryInst

theorem hol_REAL_LE_MAX : 
  ∀ (x y z : ℝ), (z ≤ max x y) = (z ≤ x ∨ z ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_MAX holTheoryInst

theorem hol_REAL_LE_MIN : 
  ∀ (x y z : ℝ), (z ≤ min x y) = (z ≤ x ∧ z ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_MIN holTheoryInst

theorem hol_REAL_LT_MAX : 
  ∀ (x y z : ℝ), (z < max x y) = (z < x ∨ z < y) := @HolLightLean.hol_opam.thm_REAL_LT_MAX holTheoryInst

theorem hol_REAL_LT_MIN : 
  ∀ (x y z : ℝ), (z < min x y) = (z < x ∧ z < y) := @HolLightLean.hol_opam.thm_REAL_LT_MIN holTheoryInst

theorem hol_REAL_MAX_LE : 
  ∀ (x y z : ℝ), (max x y ≤ z) = (x ≤ z ∧ y ≤ z) := @HolLightLean.hol_opam.thm_REAL_MAX_LE holTheoryInst

theorem hol_REAL_MIN_LE : 
  ∀ (x y z : ℝ), (min x y ≤ z) = (x ≤ z ∨ y ≤ z) := @HolLightLean.hol_opam.thm_REAL_MIN_LE holTheoryInst

theorem hol_REAL_MAX_LT : 
  ∀ (x y z : ℝ), (max x y < z) = (x < z ∧ y < z) := @HolLightLean.hol_opam.thm_REAL_MAX_LT holTheoryInst

theorem hol_REAL_MIN_LT : 
  ∀ (x y z : ℝ), (min x y < z) = (x < z ∨ y < z) := @HolLightLean.hol_opam.thm_REAL_MIN_LT holTheoryInst

theorem hol_REAL_MAX_ASSOC : 
  ∀ (x y z : ℝ), max x (max y z) = max (max x y) z := @HolLightLean.hol_opam.thm_REAL_MAX_ASSOC holTheoryInst

theorem hol_REAL_MIN_ASSOC : 
  ∀ (x y z : ℝ), min x (min y z) = min (min x y) z := @HolLightLean.hol_opam.thm_REAL_MIN_ASSOC holTheoryInst

theorem hol_REAL_MAX_ACI : 
  ∀ (z x y : ℝ),
    max x y = max y x ∧
      max (max x y) z = max x (max y z) ∧ max x (max y z) = max y (max x z) ∧ max x x = x ∧ max x (max x y) = max x y := @HolLightLean.hol_opam.thm_REAL_MAX_ACI holTheoryInst

theorem hol_REAL_MIN_ACI : 
  ∀ (z x y : ℝ),
    min x y = min y x ∧
      min (min x y) z = min x (min y z) ∧ min x (min y z) = min y (min x z) ∧ min x x = x ∧ min x (min x y) = min x y := @HolLightLean.hol_opam.thm_REAL_MIN_ACI holTheoryInst

theorem hol_REAL_ABS_MUL : 
  ∀ (x y : ℝ), |x * y| = |x| * |y| := @HolLightLean.hol_opam.thm_REAL_ABS_MUL holTheoryInst

theorem hol_REAL_POW_LE : 
  ∀ (x : ℝ) (n : ℕ), ↑(0 : ℕ) ≤ x → ↑(0 : ℕ) ≤ x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LE holTheoryInst

theorem hol_REAL_POW_LT : 
  ∀ (x : ℝ) (n : ℕ), ↑(0 : ℕ) < x → ↑(0 : ℕ) < x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LT holTheoryInst

theorem hol_REAL_ABS_POW : 
  ∀ (x : ℝ) (n : ℕ), |x ^ n| = |x| ^ n := @HolLightLean.hol_opam.thm_REAL_ABS_POW holTheoryInst

theorem hol_REAL_LE_LMUL : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) ≤ x ∧ y ≤ z → x * y ≤ x * z := @HolLightLean.hol_opam.thm_REAL_LE_LMUL holTheoryInst

theorem hol_REAL_LE_RMUL : 
  ∀ (x y z : ℝ), x ≤ y ∧ ↑(0 : ℕ) ≤ z → x * z ≤ y * z := @HolLightLean.hol_opam.thm_REAL_LE_RMUL holTheoryInst

theorem hol_REAL_LT_LMUL : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < x ∧ y < z → x * y < x * z := @HolLightLean.hol_opam.thm_REAL_LT_LMUL holTheoryInst

theorem hol_REAL_LT_RMUL : 
  ∀ (x y z : ℝ), x < y ∧ ↑(0 : ℕ) < z → x * z < y * z := @HolLightLean.hol_opam.thm_REAL_LT_RMUL holTheoryInst

theorem hol_REAL_EQ_MUL_LCANCEL : 
  ∀ (x y z : ℝ), (x * y = x * z) = (x = ↑(0 : ℕ) ∨ y = z) := @HolLightLean.hol_opam.thm_REAL_EQ_MUL_LCANCEL holTheoryInst

theorem hol_REAL_EQ_MUL_RCANCEL : 
  ∀ (x y z : ℝ), (x * z = y * z) = (x = y ∨ z = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_EQ_MUL_RCANCEL holTheoryInst

theorem hol_REAL_MUL_LINV_UNIQ : 
  ∀ (x y : ℝ), x * y = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → y⁻¹ = x := @HolLightLean.hol_opam.thm_REAL_MUL_LINV_UNIQ holTheoryInst

theorem hol_REAL_MUL_RINV_UNIQ : 
  ∀ (x y : ℝ), x * y = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → x⁻¹ = y := @HolLightLean.hol_opam.thm_REAL_MUL_RINV_UNIQ holTheoryInst

theorem hol_REAL_INV_INV : 
  ∀ (x : ℝ), x⁻¹⁻¹ = x := @HolLightLean.hol_opam.thm_REAL_INV_INV holTheoryInst

theorem hol_REAL_EQ_INV2 : 
  ∀ (x y : ℝ), (x⁻¹ = y⁻¹) = (x = y) := @HolLightLean.hol_opam.thm_REAL_EQ_INV2 holTheoryInst

theorem hol_REAL_INV_EQ_0 : 
  ∀ (x : ℝ), (x⁻¹ = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_INV_EQ_0 holTheoryInst

theorem hol_REAL_LT_INV : 
  ∀ (x : ℝ), ↑(0 : ℕ) < x → ↑(0 : ℕ) < x⁻¹ := @HolLightLean.hol_opam.thm_REAL_LT_INV holTheoryInst

theorem hol_REAL_LT_INV_EQ : 
  ∀ (x : ℝ), (↑(0 : ℕ) < x⁻¹) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_REAL_LT_INV_EQ holTheoryInst

theorem hol_REAL_INV_NEG : 
  ∀ (x : ℝ), (-x)⁻¹ = -x⁻¹ := @HolLightLean.hol_opam.thm_REAL_INV_NEG holTheoryInst

theorem hol_REAL_LE_INV_EQ : 
  ∀ (x : ℝ), (↑(0 : ℕ) ≤ x⁻¹) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_LE_INV_EQ holTheoryInst

theorem hol_REAL_LE_INV : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x → ↑(0 : ℕ) ≤ x⁻¹ := @HolLightLean.hol_opam.thm_REAL_LE_INV holTheoryInst

theorem hol_REAL_MUL_RINV : 
  ∀ (x : ℝ), ¬x = ↑(0 : ℕ) → x * x⁻¹ = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_MUL_RINV holTheoryInst

theorem hol_REAL_INV_1 : 
  Eq (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))⁻¹ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_INV_1 holTheoryInst

theorem hol_REAL_INV_EQ_1 : 
  ∀ (x : ℝ), (x⁻¹ = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_INV_EQ_1 holTheoryInst

theorem hol_REAL_DIV_1 : 
  ∀ (x : ℝ), x / ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = x := @HolLightLean.hol_opam.thm_REAL_DIV_1 holTheoryInst

theorem hol_REAL_DIV_REFL : 
  ∀ (x : ℝ), ¬x = ↑(0 : ℕ) → x / x = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_DIV_REFL holTheoryInst

theorem hol_REAL_DIV_RMUL : 
  ∀ (x y : ℝ), ¬y = ↑(0 : ℕ) → x / y * y = x := @HolLightLean.hol_opam.thm_REAL_DIV_RMUL holTheoryInst

theorem hol_REAL_DIV_LMUL : 
  ∀ (x y : ℝ), ¬y = ↑(0 : ℕ) → y * (x / y) = x := @HolLightLean.hol_opam.thm_REAL_DIV_LMUL holTheoryInst

theorem hol_REAL_DIV_EQ_1 : 
  ∀ (x y : ℝ), (x / y = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x = y ∧ ¬x = ↑(0 : ℕ) ∧ ¬y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_DIV_EQ_1 holTheoryInst

theorem hol_REAL_ABS_INV : 
  ∀ (x : ℝ), |x⁻¹| = |x|⁻¹ := @HolLightLean.hol_opam.thm_REAL_ABS_INV holTheoryInst

theorem hol_REAL_ABS_DIV : 
  ∀ (x y : ℝ), |x / y| = |x| / |y| := @HolLightLean.hol_opam.thm_REAL_ABS_DIV holTheoryInst

theorem hol_REAL_INV_MUL : 
  ∀ (x y : ℝ), (x * y)⁻¹ = x⁻¹ * y⁻¹ := @HolLightLean.hol_opam.thm_REAL_INV_MUL holTheoryInst

theorem hol_REAL_INV_DIV : 
  ∀ (x y : ℝ), (x / y)⁻¹ = y / x := @HolLightLean.hol_opam.thm_REAL_INV_DIV holTheoryInst

theorem hol_REAL_POW_MUL : 
  ∀ (x y : ℝ) (n : ℕ), (x * y) ^ n = x ^ n * y ^ n := @HolLightLean.hol_opam.thm_REAL_POW_MUL holTheoryInst

theorem hol_REAL_POW_INV : 
  ∀ (x : ℝ) (n : ℕ), x⁻¹ ^ n = (x ^ n)⁻¹ := @HolLightLean.hol_opam.thm_REAL_POW_INV holTheoryInst

theorem hol_REAL_INV_POW : 
  ∀ (x : ℝ) (n : ℕ), (x ^ n)⁻¹ = x⁻¹ ^ n := @HolLightLean.hol_opam.thm_REAL_INV_POW holTheoryInst

theorem hol_REAL_POW_DIV : 
  ∀ (x y : ℝ) (n : ℕ), (x / y) ^ n = x ^ n / y ^ n := @HolLightLean.hol_opam.thm_REAL_POW_DIV holTheoryInst

theorem hol_REAL_DIV_EQ_0 : 
  ∀ (x y : ℝ), (x / y = ↑(0 : ℕ)) = (x = ↑(0 : ℕ) ∨ y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_DIV_EQ_0 holTheoryInst

theorem hol_REAL_POW_ADD : 
  ∀ (x : ℝ) (m n : ℕ), x ^ (m + n) = x ^ m * x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_ADD holTheoryInst

theorem hol_REAL_POW_NZ : 
  ∀ (x : ℝ) (n : ℕ), ¬x = ↑(0 : ℕ) → ¬x ^ n = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_POW_NZ holTheoryInst

theorem hol_REAL_POW_SUB : 
  ∀ (x : ℝ) (m n : ℕ), ¬x = ↑(0 : ℕ) ∧ m ≤ n → x ^ (n - m) = x ^ n / x ^ m := @HolLightLean.hol_opam.thm_REAL_POW_SUB holTheoryInst

theorem hol_REAL_LT_LCANCEL_IMP : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < x ∧ x * y < x * z → y < z := @HolLightLean.hol_opam.thm_REAL_LT_LCANCEL_IMP holTheoryInst

theorem hol_REAL_LT_RCANCEL_IMP : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z ∧ x * z < y * z → x < y := @HolLightLean.hol_opam.thm_REAL_LT_RCANCEL_IMP holTheoryInst

theorem hol_REAL_LE_LCANCEL_IMP : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < x ∧ x * y ≤ x * z → y ≤ z := @HolLightLean.hol_opam.thm_REAL_LE_LCANCEL_IMP holTheoryInst

theorem hol_REAL_LE_RCANCEL_IMP : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z ∧ x * z ≤ y * z → x ≤ y := @HolLightLean.hol_opam.thm_REAL_LE_RCANCEL_IMP holTheoryInst

theorem hol_REAL_LE_RMUL_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x * z ≤ y * z) = (x ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_RMUL_EQ holTheoryInst

theorem hol_REAL_LE_LMUL_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (z * x ≤ z * y) = (x ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_LMUL_EQ holTheoryInst

theorem hol_REAL_LT_RMUL_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x * z < y * z) = (x < y) := @HolLightLean.hol_opam.thm_REAL_LT_RMUL_EQ holTheoryInst

theorem hol_REAL_LT_LMUL_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (z * x < z * y) = (x < y) := @HolLightLean.hol_opam.thm_REAL_LT_LMUL_EQ holTheoryInst

theorem hol_REAL_LE_MUL_EQ : 
  (∀ (x y : ℝ), ↑(0 : ℕ) < x → (↑(0 : ℕ) ≤ x * y) = (↑(0 : ℕ) ≤ y)) ∧
    ∀ (x y : ℝ), ↑(0 : ℕ) < y → (↑(0 : ℕ) ≤ x * y) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_REAL_LE_MUL_EQ holTheoryInst

theorem hol_REAL_LT_MUL_EQ : 
  (∀ (x y : ℝ), ↑(0 : ℕ) < x → (↑(0 : ℕ) < x * y) = (↑(0 : ℕ) < y)) ∧
    ∀ (x y : ℝ), ↑(0 : ℕ) < y → (↑(0 : ℕ) < x * y) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_REAL_LT_MUL_EQ holTheoryInst

theorem hol_REAL_MUL_POS_LT : 
  ∀ (x y : ℝ), (↑(0 : ℕ) < x * y) = (↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y ∨ x < ↑(0 : ℕ) ∧ y < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_MUL_POS_LT holTheoryInst

theorem hol_REAL_MUL_POS_LE : 
  ∀ (x y : ℝ),
    (↑(0 : ℕ) ≤ x * y) = (x = ↑(0 : ℕ) ∨ y = ↑(0 : ℕ) ∨ ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y ∨ x < ↑(0 : ℕ) ∧ y < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_MUL_POS_LE holTheoryInst

theorem hol_REAL_LE_RDIV_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x ≤ y / z) = (x * z ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_RDIV_EQ holTheoryInst

theorem hol_REAL_LE_LDIV_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x / z ≤ y) = (x ≤ y * z) := @HolLightLean.hol_opam.thm_REAL_LE_LDIV_EQ holTheoryInst

theorem hol_REAL_LT_RDIV_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x < y / z) = (x * z < y) := @HolLightLean.hol_opam.thm_REAL_LT_RDIV_EQ holTheoryInst

theorem hol_REAL_LT_LDIV_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x / z < y) = (x < y * z) := @HolLightLean.hol_opam.thm_REAL_LT_LDIV_EQ holTheoryInst

theorem hol_REAL_EQ_RDIV_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x = y / z) = (x * z = y) := @HolLightLean.hol_opam.thm_REAL_EQ_RDIV_EQ holTheoryInst

theorem hol_REAL_EQ_LDIV_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x / z = y) = (x = y * z) := @HolLightLean.hol_opam.thm_REAL_EQ_LDIV_EQ holTheoryInst

theorem hol_REAL_LT_DIV2_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x / z < y / z) = (x < y) := @HolLightLean.hol_opam.thm_REAL_LT_DIV2_EQ holTheoryInst

theorem hol_REAL_LE_DIV2_EQ : 
  ∀ (x y z : ℝ), ↑(0 : ℕ) < z → (x / z ≤ y / z) = (x ≤ y) := @HolLightLean.hol_opam.thm_REAL_LE_DIV2_EQ holTheoryInst

theorem hol_REAL_MUL_2 : 
  ∀ (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * x = x + x := @HolLightLean.hol_opam.thm_REAL_MUL_2 holTheoryInst

theorem hol_REAL_POW_EQ_0 : 
  ∀ (x : ℝ) (n : ℕ), (x ^ n = ↑(0 : ℕ)) = (x = ↑(0 : ℕ) ∧ ¬n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POW_EQ_0 holTheoryInst

theorem hol_REAL_LE_MUL2 : 
  ∀ (w x y z : ℝ), ↑(0 : ℕ) ≤ w ∧ w ≤ x ∧ ↑(0 : ℕ) ≤ y ∧ y ≤ z → w * y ≤ x * z := @HolLightLean.hol_opam.thm_REAL_LE_MUL2 holTheoryInst

theorem hol_REAL_LT_MUL2 : 
  ∀ (w x y z : ℝ), ↑(0 : ℕ) ≤ w ∧ w < x ∧ ↑(0 : ℕ) ≤ y ∧ y < z → w * y < x * z := @HolLightLean.hol_opam.thm_REAL_LT_MUL2 holTheoryInst

theorem hol_REAL_LT_SQUARE : 
  ∀ (x : ℝ), (↑(0 : ℕ) < x * x) = ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_LT_SQUARE holTheoryInst

theorem hol_REAL_POW_1 : 
  ∀ (x : ℝ), x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = x := @HolLightLean.hol_opam.thm_REAL_POW_1 holTheoryInst

theorem hol_REAL_POW_ONE : 
  ∀ (n : ℕ), HPow.hPow (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POW_ONE holTheoryInst

theorem hol_REAL_LT_INV2 : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ x < y → y⁻¹ < x⁻¹ := @HolLightLean.hol_opam.thm_REAL_LT_INV2 holTheoryInst

theorem hol_REAL_LE_INV2 : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ x ≤ y → y⁻¹ ≤ x⁻¹ := @HolLightLean.hol_opam.thm_REAL_LE_INV2 holTheoryInst

theorem hol_REAL_LT_LINV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < y ∧ y⁻¹ < x → x⁻¹ < y := @HolLightLean.hol_opam.thm_REAL_LT_LINV holTheoryInst

theorem hol_REAL_LT_RINV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ x < y⁻¹ → y < x⁻¹ := @HolLightLean.hol_opam.thm_REAL_LT_RINV holTheoryInst

theorem hol_REAL_LE_LINV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < y ∧ y⁻¹ ≤ x → x⁻¹ ≤ y := @HolLightLean.hol_opam.thm_REAL_LE_LINV holTheoryInst

theorem hol_REAL_LE_RINV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ x ≤ y⁻¹ → y ≤ x⁻¹ := @HolLightLean.hol_opam.thm_REAL_LE_RINV holTheoryInst

theorem hol_REAL_INV_LE_1 : 
  ∀ (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x → x⁻¹ ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_INV_LE_1 holTheoryInst

theorem hol_REAL_INV_1_LE : 
  ∀ (x : ℝ), ↑(0 : ℕ) < x ∧ x ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x⁻¹ := @HolLightLean.hol_opam.thm_REAL_INV_1_LE holTheoryInst

theorem hol_REAL_INV_LT_1 : 
  ∀ (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x → x⁻¹ < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_INV_LT_1 holTheoryInst

theorem hol_REAL_INV_1_LT : 
  ∀ (x : ℝ), ↑(0 : ℕ) < x ∧ x < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x⁻¹ := @HolLightLean.hol_opam.thm_REAL_INV_1_LT holTheoryInst

theorem hol_REAL_SUB_INV : 
  ∀ (x y : ℝ), ¬x = ↑(0 : ℕ) ∧ ¬y = ↑(0 : ℕ) → x⁻¹ - y⁻¹ = (y - x) / (x * y) := @HolLightLean.hol_opam.thm_REAL_SUB_INV holTheoryInst

theorem hol_REAL_DOWN : 
  ∀ (d : ℝ), ↑(0 : ℕ) < d → ∃ (e : ℝ), ↑(0 : ℕ) < e ∧ e < d := @HolLightLean.hol_opam.thm_REAL_DOWN holTheoryInst

theorem hol_REAL_DOWN2 : 
  ∀ (d1 d2 : ℝ), ↑(0 : ℕ) < d1 ∧ ↑(0 : ℕ) < d2 → ∃ (e : ℝ), ↑(0 : ℕ) < e ∧ e < d1 ∧ e < d2 := @HolLightLean.hol_opam.thm_REAL_DOWN2 holTheoryInst

theorem hol_REAL_POW_LE2 : 
  ∀ (n : ℕ) (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ x ≤ y → x ^ n ≤ y ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LE2 holTheoryInst

theorem hol_REAL_POW_LE_1 : 
  ∀ (n : ℕ) (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LE_1 holTheoryInst

theorem hol_REAL_POW_1_LE : 
  ∀ (n : ℕ) (x : ℝ), ↑(0 : ℕ) ≤ x ∧ x ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → x ^ n ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POW_1_LE holTheoryInst

theorem hol_REAL_POW_MONO : 
  ∀ (m n : ℕ) (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x ∧ m ≤ n → x ^ m ≤ x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_MONO holTheoryInst

theorem hol_REAL_POW_LT2 : 
  ∀ (n : ℕ) (x y : ℝ), ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ x ∧ x < y → x ^ n < y ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LT2 holTheoryInst

theorem hol_REAL_POW_LT_1 : 
  ∀ (n : ℕ) (x : ℝ), ¬n = (0 : ℕ) ∧ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LT_1 holTheoryInst

theorem hol_REAL_POW_1_LT : 
  ∀ (n : ℕ) (x : ℝ),
    ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ x ∧ x < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → x ^ n < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POW_1_LT holTheoryInst

theorem hol_REAL_POW_MONO_LT : 
  ∀ (m n : ℕ) (x : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x ∧ m < n → x ^ m < x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_MONO_LT holTheoryInst

theorem hol_REAL_POW_POW : 
  ∀ (x : ℝ) (m n : ℕ), (x ^ m) ^ n = x ^ (m * n) := @HolLightLean.hol_opam.thm_REAL_POW_POW holTheoryInst

theorem hol_REAL_EQ_RCANCEL_IMP : 
  ∀ (x y z : ℝ), ¬z = ↑(0 : ℕ) ∧ x * z = y * z → x = y := @HolLightLean.hol_opam.thm_REAL_EQ_RCANCEL_IMP holTheoryInst

theorem hol_REAL_EQ_LCANCEL_IMP : 
  ∀ (x y z : ℝ), ¬z = ↑(0 : ℕ) ∧ z * x = z * y → x = y := @HolLightLean.hol_opam.thm_REAL_EQ_LCANCEL_IMP holTheoryInst

theorem hol_REAL_LT_DIV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x / y := @HolLightLean.hol_opam.thm_REAL_LT_DIV holTheoryInst

theorem hol_REAL_LE_DIV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) ≤ x / y := @HolLightLean.hol_opam.thm_REAL_LE_DIV holTheoryInst

theorem hol_REAL_DIV_POW2 : 
  ∀ (x : ℝ) (m n : ℕ), ¬x = ↑(0 : ℕ) → x ^ m / x ^ n = if n ≤ m then x ^ (m - n) else (x ^ (n - m))⁻¹ := @HolLightLean.hol_opam.thm_REAL_DIV_POW2 holTheoryInst

theorem hol_REAL_DIV_POW2_ALT : 
  ∀ (x : ℝ) (m n : ℕ), ¬x = ↑(0 : ℕ) → x ^ m / x ^ n = if n < m then x ^ (m - n) else (x ^ (n - m))⁻¹ := @HolLightLean.hol_opam.thm_REAL_DIV_POW2_ALT holTheoryInst

theorem hol_REAL_LT_POW2 : 
  ∀ (n : ℕ), ↑(0 : ℕ) < HPow.hPow (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) n := @HolLightLean.hol_opam.thm_REAL_LT_POW2 holTheoryInst

theorem hol_REAL_LE_POW2 : 
  ∀ (n : ℕ),
    ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤
      HPow.hPow (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) n := @HolLightLean.hol_opam.thm_REAL_LE_POW2 holTheoryInst

theorem hol_REAL_POW2_ABS : 
  ∀ (x : ℝ),
    |x| ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_POW2_ABS holTheoryInst

theorem hol_REAL_LE_SQUARE_ABS : 
  ∀ (x y : ℝ),
    (|x| ≤ |y|) =
      (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ≤
        y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_REAL_LE_SQUARE_ABS holTheoryInst

theorem hol_REAL_LT_SQUARE_ABS : 
  ∀ (x y : ℝ),
    (|x| < |y|) =
      (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) <
        y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_REAL_LT_SQUARE_ABS holTheoryInst

theorem hol_REAL_EQ_SQUARE_ABS : 
  ∀ (x y : ℝ),
    (|x| = |y|) =
      (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_REAL_EQ_SQUARE_ABS holTheoryInst

theorem hol_REAL_LE_POW_2 : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_LE_POW_2 holTheoryInst

theorem hol_REAL_LT_POW_2 : 
  ∀ (x : ℝ), (↑(0 : ℕ) < x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) = ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_LT_POW_2 holTheoryInst

theorem hol_REAL_SOS_EQ_0 : 
  ∀ (x y : ℝ),
    (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) +
          y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        ↑(0 : ℕ)) =
      (x = ↑(0 : ℕ) ∧ y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_SOS_EQ_0 holTheoryInst

theorem hol_REAL_POW_ZERO : 
  ∀ (n : ℕ), HPow.hPow (α := ℝ) (↑(0 : ℕ)) n = if n = (0 : ℕ) then ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_POW_ZERO holTheoryInst

theorem hol_REAL_POW_MONO_INV : 
  ∀ (m n : ℕ) (x : ℝ), ↑(0 : ℕ) ≤ x ∧ x ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ n ≤ m → x ^ m ≤ x ^ n := @HolLightLean.hol_opam.thm_REAL_POW_MONO_INV holTheoryInst

theorem hol_REAL_POW_LE2_REV : 
  ∀ (n : ℕ) (x y : ℝ), ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ y ∧ x ^ n ≤ y ^ n → x ≤ y := @HolLightLean.hol_opam.thm_REAL_POW_LE2_REV holTheoryInst

theorem hol_REAL_POW_LT2_REV : 
  ∀ (n : ℕ) (x y : ℝ), ↑(0 : ℕ) ≤ y ∧ x ^ n < y ^ n → x < y := @HolLightLean.hol_opam.thm_REAL_POW_LT2_REV holTheoryInst

theorem hol_REAL_POW_EQ : 
  ∀ (n : ℕ) (x y : ℝ), ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y ∧ x ^ n = y ^ n → x = y := @HolLightLean.hol_opam.thm_REAL_POW_EQ holTheoryInst

theorem hol_REAL_POW_EQ_ABS : 
  ∀ (n : ℕ) (x y : ℝ), ¬n = (0 : ℕ) ∧ x ^ n = y ^ n → |x| = |y| := @HolLightLean.hol_opam.thm_REAL_POW_EQ_ABS holTheoryInst

theorem hol_REAL_POW_EQ_1_IMP : 
  ∀ (x : ℝ) (n : ℕ), ¬n = (0 : ℕ) ∧ x ^ n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → |x| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POW_EQ_1_IMP holTheoryInst

theorem hol_REAL_POW_EQ_1 : 
  ∀ (x : ℝ) (n : ℕ),
    (x ^ n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      (|x| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ (x < ↑(0 : ℕ) → Even n) ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POW_EQ_1 holTheoryInst

theorem hol_REAL_POW_LT2_ODD : 
  ∀ (n : ℕ) (x y : ℝ), x < y ∧ Odd n → x ^ n < y ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LT2_ODD holTheoryInst

theorem hol_REAL_POW_LE2_ODD : 
  ∀ (n : ℕ) (x y : ℝ), x ≤ y ∧ Odd n → x ^ n ≤ y ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LE2_ODD holTheoryInst

theorem hol_REAL_POW_LT2_ODD_EQ : 
  ∀ (n : ℕ) (x y : ℝ), Odd n → (x ^ n < y ^ n) = (x < y) := @HolLightLean.hol_opam.thm_REAL_POW_LT2_ODD_EQ holTheoryInst

theorem hol_REAL_POW_LE2_ODD_EQ : 
  ∀ (n : ℕ) (x y : ℝ), Odd n → (x ^ n ≤ y ^ n) = (x ≤ y) := @HolLightLean.hol_opam.thm_REAL_POW_LE2_ODD_EQ holTheoryInst

theorem hol_REAL_POW_EQ_ODD_EQ : 
  ∀ (n : ℕ) (x y : ℝ), Odd n → (x ^ n = y ^ n) = (x = y) := @HolLightLean.hol_opam.thm_REAL_POW_EQ_ODD_EQ holTheoryInst

theorem hol_REAL_POW_EQ_ODD : 
  ∀ (n : ℕ) (x y : ℝ), Odd n ∧ x ^ n = y ^ n → x = y := @HolLightLean.hol_opam.thm_REAL_POW_EQ_ODD holTheoryInst

theorem hol_REAL_POW_EQ_EQ : 
  ∀ (n : ℕ) (x y : ℝ), (x ^ n = y ^ n) = if Even n then n = (0 : ℕ) ∨ |x| = |y| else x = y := @HolLightLean.hol_opam.thm_REAL_POW_EQ_EQ holTheoryInst

theorem hol_REAL_EVENPOW_ABS : 
  ∀ (x : ℝ) (n : ℕ), Even n → |x| ^ n = x ^ n := @HolLightLean.hol_opam.thm_REAL_EVENPOW_ABS holTheoryInst

theorem hol_REAL_OF_NUM_MOD : 
  ∀ (m n : ℕ), ↑(m % n) = ↑m - HMul.hMul (α := ℝ) ↑(m / n) ↑n := @HolLightLean.hol_opam.thm_REAL_OF_NUM_MOD holTheoryInst

theorem hol_REAL_OF_NUM_DIV : 
  ∀ (m n : ℕ), ↑(m / n) = HDiv.hDiv (α := ℝ) ↑m ↑n - HDiv.hDiv (α := ℝ) ↑(m % n) ↑n := @HolLightLean.hol_opam.thm_REAL_OF_NUM_DIV holTheoryInst

theorem hol_REAL_CONVEX_BOUND2_LT : 
  ∀ (b x y a u v : ℝ),
    x < a ∧ y < b ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → u * x + v * y < u * a + v * b := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUND2_LT holTheoryInst

theorem hol_REAL_CONVEX_BOUND2_LE : 
  ∀ (b x y a u v : ℝ),
    x ≤ a ∧ y ≤ b ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → u * x + v * y ≤ u * a + v * b := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUND2_LE holTheoryInst

theorem hol_REAL_CONVEX_BOUND_LT : 
  ∀ (x y a u v : ℝ),
    x < a ∧ y < a ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → u * x + v * y < a := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUND_LT holTheoryInst

theorem hol_REAL_CONVEX_BOUND_LE : 
  ∀ (x y a u v : ℝ),
    x ≤ a ∧ y ≤ a ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → u * x + v * y ≤ a := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUND_LE holTheoryInst

theorem hol_REAL_CONVEX_BOUND_GT : 
  ∀ (x y a u v : ℝ),
    a < x ∧ a < y ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → a < u * x + v * y := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUND_GT holTheoryInst

theorem hol_REAL_CONVEX_BOUND_GE : 
  ∀ (x y a u v : ℝ),
    a ≤ x ∧ a ≤ y ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → a ≤ u * x + v * y := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUND_GE holTheoryInst

theorem hol_REAL_CONVEX_BOUNDS_LE : 
  ∀ (x y a b u v : ℝ),
    a ≤ x ∧ x ≤ b ∧ a ≤ y ∧ y ≤ b ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      a ≤ u * x + v * y ∧ u * x + v * y ≤ b := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUNDS_LE holTheoryInst

theorem hol_REAL_CONVEX_BOUNDS_LT : 
  ∀ (x y a b u v : ℝ),
    a < x ∧ x < b ∧ a < y ∧ y < b ∧ ↑(0 : ℕ) ≤ u ∧ ↑(0 : ℕ) ≤ v ∧ u + v = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      a < u * x + v * y ∧ u * x + v * y < b := @HolLightLean.hol_opam.thm_REAL_CONVEX_BOUNDS_LT holTheoryInst

theorem hol_REAL_ARCH_SIMPLE : 
  ∀ (x : ℝ), ∃ (n : ℕ), x ≤ ↑n := @HolLightLean.hol_opam.thm_REAL_ARCH_SIMPLE holTheoryInst

theorem hol_REAL_ARCH_LT : 
  ∀ (x : ℝ), ∃ (n : ℕ), x < ↑n := @HolLightLean.hol_opam.thm_REAL_ARCH_LT holTheoryInst

theorem hol_REAL_ARCH : 
  ∀ (x : ℝ), ↑(0 : ℕ) < x → ∀ (y : ℝ), ∃ (n : ℕ), y < ↑n * x := @HolLightLean.hol_opam.thm_REAL_ARCH holTheoryInst

theorem hol_REAL_ARCH_INV : 
  ∀ (e : ℝ), (↑(0 : ℕ) < e) = ∃ (n : ℕ), ¬n = (0 : ℕ) ∧ LT.lt (α := ℝ) (↑(0 : ℕ)) (↑n)⁻¹ ∧ (↑n)⁻¹ < e := @HolLightLean.hol_opam.thm_REAL_ARCH_INV holTheoryInst

theorem hol_REAL_POW_LBOUND : 
  ∀ (x : ℝ) (n : ℕ), ↑(0 : ℕ) ≤ x → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + ↑n * x ≤ (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + x) ^ n := @HolLightLean.hol_opam.thm_REAL_POW_LBOUND holTheoryInst

theorem hol_REAL_ARCH_POW : 
  ∀ (x y : ℝ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x → ∃ (n : ℕ), y < x ^ n := @HolLightLean.hol_opam.thm_REAL_ARCH_POW holTheoryInst

theorem hol_REAL_ARCH_POW2 : 
  ∀ (x : ℝ), ∃ (n : ℕ), x < HPow.hPow (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) n := @HolLightLean.hol_opam.thm_REAL_ARCH_POW2 holTheoryInst

theorem hol_REAL_ARCH_POW_INV : 
  ∀ (x y : ℝ), ↑(0 : ℕ) < y ∧ x < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → ∃ (n : ℕ), x ^ n < y := @HolLightLean.hol_opam.thm_REAL_ARCH_POW_INV holTheoryInst

theorem hol_real_sgn : 
  ∀ (x : ℝ),
    x.sign =
      if ↑(0 : ℕ) < x then ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))
      else if x < ↑(0 : ℕ) then -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_real_sgn holTheoryInst

theorem hol_REAL_SGN_0 : 
  Real.sign ↑(0 : ℕ) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_SGN_0 holTheoryInst

theorem hol_REAL_SGN_NEG : 
  ∀ (x : ℝ), (-x).sign = -x.sign := @HolLightLean.hol_opam.thm_REAL_SGN_NEG holTheoryInst

theorem hol_REAL_SGN_ABS : 
  ∀ (x : ℝ), x.sign * |x| = x := @HolLightLean.hol_opam.thm_REAL_SGN_ABS holTheoryInst

theorem hol_REAL_SGN_ABS_ALT : 
  ∀ (x : ℝ), x.sign * x = |x| := @HolLightLean.hol_opam.thm_REAL_SGN_ABS_ALT holTheoryInst

theorem hol_REAL_EQ_SGN_ABS : 
  ∀ (x y : ℝ), (x = y) = (x.sign = y.sign ∧ |x| = |y|) := @HolLightLean.hol_opam.thm_REAL_EQ_SGN_ABS holTheoryInst

theorem hol_REAL_ABS_SGN : 
  ∀ (x : ℝ), |x.sign| = |x|.sign := @HolLightLean.hol_opam.thm_REAL_ABS_SGN holTheoryInst

theorem hol_REAL_SGN : 
  ∀ (x : ℝ), x.sign = x / |x| := @HolLightLean.hol_opam.thm_REAL_SGN holTheoryInst

theorem hol_REAL_SGN_MUL : 
  ∀ (x y : ℝ), (x * y).sign = x.sign * y.sign := @HolLightLean.hol_opam.thm_REAL_SGN_MUL holTheoryInst

theorem hol_REAL_SGN_INV : 
  ∀ (x : ℝ), x⁻¹.sign = x.sign := @HolLightLean.hol_opam.thm_REAL_SGN_INV holTheoryInst

theorem hol_REAL_SGN_DIV : 
  ∀ (x y : ℝ), (x / y).sign = x.sign / y.sign := @HolLightLean.hol_opam.thm_REAL_SGN_DIV holTheoryInst

theorem hol_REAL_SGN_EQ : 
  (∀ (x : ℝ), (x.sign = ↑(0 : ℕ)) = (x = ↑(0 : ℕ))) ∧
    (∀ (x : ℝ), (x.sign = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x > ↑(0 : ℕ))) ∧
      ∀ (x : ℝ), (x.sign = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_SGN_EQ holTheoryInst

theorem hol_REAL_SGN_CASES : 
  ∀ (x : ℝ), x.sign = ↑(0 : ℕ) ∨ x.sign = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∨ x.sign = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_SGN_CASES holTheoryInst

theorem hol_REAL_SGN_INEQS : 
  (∀ (x : ℝ), (↑(0 : ℕ) ≤ x.sign) = (↑(0 : ℕ) ≤ x)) ∧
    (∀ (x : ℝ), (↑(0 : ℕ) < x.sign) = (↑(0 : ℕ) < x)) ∧
      (∀ (x : ℝ), (↑(0 : ℕ) ≥ x.sign) = (↑(0 : ℕ) ≥ x)) ∧
        (∀ (x : ℝ), (↑(0 : ℕ) > x.sign) = (↑(0 : ℕ) > x)) ∧
          (∀ (x : ℝ), (↑(0 : ℕ) = x.sign) = (↑(0 : ℕ) = x)) ∧
            (∀ (x : ℝ), (x.sign ≤ ↑(0 : ℕ)) = (x ≤ ↑(0 : ℕ))) ∧
              (∀ (x : ℝ), (x.sign < ↑(0 : ℕ)) = (x < ↑(0 : ℕ))) ∧
                (∀ (x : ℝ), (x.sign ≥ ↑(0 : ℕ)) = (x ≥ ↑(0 : ℕ))) ∧
                  (∀ (x : ℝ), (x.sign > ↑(0 : ℕ)) = (x > ↑(0 : ℕ))) ∧ ∀ (x : ℝ), (x.sign = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_SGN_INEQS holTheoryInst

theorem hol_REAL_SGN_POW : 
  ∀ (x : ℝ) (n : ℕ), (x ^ n).sign = x.sign ^ n := @HolLightLean.hol_opam.thm_REAL_SGN_POW holTheoryInst

theorem hol_REAL_SGN_POW_2 : 
  ∀ (x : ℝ), (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))).sign = |x|.sign := @HolLightLean.hol_opam.thm_REAL_SGN_POW_2 holTheoryInst

theorem hol_REAL_SGN_REAL_SGN : 
  ∀ (x : ℝ), x.sign.sign = x.sign := @HolLightLean.hol_opam.thm_REAL_SGN_REAL_SGN holTheoryInst

theorem hol_REAL_INV_SGN : 
  ∀ (x : ℝ), x.sign⁻¹ = x.sign := @HolLightLean.hol_opam.thm_REAL_INV_SGN holTheoryInst

theorem hol_REAL_SGN_EQ_INEQ : 
  ∀ (x y : ℝ), (x.sign = y.sign) = (x = y ∨ |x - y| < max |x| |y|) := @HolLightLean.hol_opam.thm_REAL_SGN_EQ_INEQ holTheoryInst

theorem hol_REAL_SGNS_EQ : 
  ∀ (x y : ℝ),
    (x.sign = y.sign) =
      ((x = ↑(0 : ℕ)) = (y = ↑(0 : ℕ)) ∧ (x > ↑(0 : ℕ)) = (y > ↑(0 : ℕ)) ∧ (x < ↑(0 : ℕ)) = (y < ↑(0 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_SGNS_EQ holTheoryInst

theorem hol_REAL_SGNS_EQ_ALT : 
  ∀ (x y : ℝ),
    (x.sign = y.sign) = ((x = ↑(0 : ℕ) → y = ↑(0 : ℕ)) ∧ (x > ↑(0 : ℕ) → y > ↑(0 : ℕ)) ∧ (x < ↑(0 : ℕ) → y < ↑(0 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_SGNS_EQ_ALT holTheoryInst

theorem hol_REAL_WLOG_LE : 
  ∀ (P : ℝ → ℝ → Prop), ((∀ (x y : ℝ), P x y = P y x) ∧ ∀ (x y : ℝ), x ≤ y → P x y) → ∀ (x y : ℝ), P x y := @HolLightLean.hol_opam.thm_REAL_WLOG_LE holTheoryInst

theorem hol_REAL_WLOG_LT : 
  ∀ (P : ℝ → ℝ → Prop),
    ((∀ (x : ℝ), P x x) ∧ (∀ (x y : ℝ), P x y = P y x) ∧ ∀ (x y : ℝ), x < y → P x y) → ∀ (x y : ℝ), P x y := @HolLightLean.hol_opam.thm_REAL_WLOG_LT holTheoryInst

theorem hol_REAL_WLOG_LE_3 : 
  ∀ (P : ℝ → ℝ → ℝ → Prop),
    ((∀ (x y z : ℝ), P x y z → P y x z ∧ P x z y) ∧ ∀ (x y z : ℝ), x ≤ y ∧ y ≤ z → P x y z) → ∀ (x y z : ℝ), P x y z := @HolLightLean.hol_opam.thm_REAL_WLOG_LE_3 holTheoryInst

theorem hol_sqrt : 
  ∀ (x : ℝ),
    SQRT_HOL x =
      Classical.epsilon fun (y : ℝ) ↦
        y.sign = x.sign ∧ y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = |x| := @HolLightLean.hol_opam.thm_sqrt holTheoryInst

theorem hol_SQRT_UNIQUE : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ y ∧ y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x → SQRT_HOL x = y := @HolLightLean.hol_opam.thm_SQRT_UNIQUE holTheoryInst

theorem hol_POW_2_SQRT : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x → SQRT_HOL (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) = x := @HolLightLean.hol_opam.thm_POW_2_SQRT holTheoryInst

theorem hol_SQRT_0 : 
  SQRT_HOL ↑(0 : ℕ) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SQRT_0 holTheoryInst

theorem hol_SQRT_1 : 
  SQRT_HOL ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_SQRT_1 holTheoryInst

theorem hol_POW_2_SQRT_ABS : 
  ∀ (x : ℝ), SQRT_HOL (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) = |x| := @HolLightLean.hol_opam.thm_POW_2_SQRT_ABS holTheoryInst

theorem hol_SQRT_WORKS_GEN : 
  ∀ (x : ℝ),
    (SQRT_HOL x).sign = x.sign ∧ SQRT_HOL x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = |x| := @HolLightLean.hol_opam.thm_SQRT_WORKS_GEN holTheoryInst

theorem hol_SQRT_UNIQUE_GEN : 
  ∀ (x y : ℝ),
    y.sign = x.sign ∧ y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = |x| → SQRT_HOL x = y := @HolLightLean.hol_opam.thm_SQRT_UNIQUE_GEN holTheoryInst

theorem hol_SQRT_NEG : 
  ∀ (x : ℝ), SQRT_HOL (-x) = -SQRT_HOL x := @HolLightLean.hol_opam.thm_SQRT_NEG holTheoryInst

theorem hol_REAL_SGN_SQRT : 
  ∀ (x : ℝ), (SQRT_HOL x).sign = x.sign := @HolLightLean.hol_opam.thm_REAL_SGN_SQRT holTheoryInst

theorem hol_SQRT_WORKS : 
  ∀ (x : ℝ),
    ↑(0 : ℕ) ≤ x →
      ↑(0 : ℕ) ≤ SQRT_HOL x ∧ SQRT_HOL x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x := @HolLightLean.hol_opam.thm_SQRT_WORKS holTheoryInst

theorem hol_REAL_POS_EQ_SQUARE : 
  ∀ (x : ℝ), (↑(0 : ℕ) ≤ x) = ∃ (y : ℝ), y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x := @HolLightLean.hol_opam.thm_REAL_POS_EQ_SQUARE holTheoryInst

theorem hol_SQRT_POS_LE : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x → ↑(0 : ℕ) ≤ SQRT_HOL x := @HolLightLean.hol_opam.thm_SQRT_POS_LE holTheoryInst

theorem hol_SQRT_POW_2 : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x → SQRT_HOL x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x := @HolLightLean.hol_opam.thm_SQRT_POW_2 holTheoryInst

theorem hol_SQRT_POW2 : 
  ∀ (x : ℝ), (SQRT_HOL x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_SQRT_POW2 holTheoryInst

theorem hol_SQRT_MUL : 
  ∀ (x y : ℝ), SQRT_HOL (x * y) = SQRT_HOL x * SQRT_HOL y := @HolLightLean.hol_opam.thm_SQRT_MUL holTheoryInst

theorem hol_SQRT_INV : 
  ∀ (x : ℝ), SQRT_HOL x⁻¹ = (SQRT_HOL x)⁻¹ := @HolLightLean.hol_opam.thm_SQRT_INV holTheoryInst

theorem hol_SQRT_DIV : 
  ∀ (x y : ℝ), SQRT_HOL (x / y) = SQRT_HOL x / SQRT_HOL y := @HolLightLean.hol_opam.thm_SQRT_DIV holTheoryInst

theorem hol_SQRT_LT_0 : 
  ∀ (x : ℝ), (↑(0 : ℕ) < SQRT_HOL x) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_SQRT_LT_0 holTheoryInst

theorem hol_SQRT_EQ_0 : 
  ∀ (x : ℝ), (SQRT_HOL x = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_SQRT_EQ_0 holTheoryInst

theorem hol_SQRT_LE_0 : 
  ∀ (x : ℝ), (↑(0 : ℕ) ≤ SQRT_HOL x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_SQRT_LE_0 holTheoryInst

theorem hol_REAL_ABS_SQRT : 
  ∀ (x : ℝ), |SQRT_HOL x| = SQRT_HOL |x| := @HolLightLean.hol_opam.thm_REAL_ABS_SQRT holTheoryInst

theorem hol_SQRT_MONO_LT : 
  ∀ (x y : ℝ), x < y → SQRT_HOL x < SQRT_HOL y := @HolLightLean.hol_opam.thm_SQRT_MONO_LT holTheoryInst

theorem hol_SQRT_MONO_LE : 
  ∀ (x y : ℝ), x ≤ y → SQRT_HOL x ≤ SQRT_HOL y := @HolLightLean.hol_opam.thm_SQRT_MONO_LE holTheoryInst

theorem hol_SQRT_MONO_LT_EQ : 
  ∀ (x y : ℝ), (SQRT_HOL x < SQRT_HOL y) = (x < y) := @HolLightLean.hol_opam.thm_SQRT_MONO_LT_EQ holTheoryInst

theorem hol_SQRT_MONO_LE_EQ : 
  ∀ (x y : ℝ), (SQRT_HOL x ≤ SQRT_HOL y) = (x ≤ y) := @HolLightLean.hol_opam.thm_SQRT_MONO_LE_EQ holTheoryInst

theorem hol_SQRT_INJ : 
  ∀ (x y : ℝ), (SQRT_HOL x = SQRT_HOL y) = (x = y) := @HolLightLean.hol_opam.thm_SQRT_INJ holTheoryInst

theorem hol_SQRT_EQ_1 : 
  ∀ (x : ℝ), (SQRT_HOL x = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_SQRT_EQ_1 holTheoryInst

theorem hol_SQRT_POS_LT : 
  ∀ (x : ℝ), ↑(0 : ℕ) < x → ↑(0 : ℕ) < SQRT_HOL x := @HolLightLean.hol_opam.thm_SQRT_POS_LT holTheoryInst

theorem hol_REAL_LE_LSQRT : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ y ∧ x ≤ y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) → SQRT_HOL x ≤ y := @HolLightLean.hol_opam.thm_REAL_LE_LSQRT holTheoryInst

theorem hol_REAL_LE_RSQRT : 
  ∀ (x y : ℝ), x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ≤ y → x ≤ SQRT_HOL y := @HolLightLean.hol_opam.thm_REAL_LE_RSQRT holTheoryInst

theorem hol_REAL_LT_LSQRT : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ y ∧ x < y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) → SQRT_HOL x < y := @HolLightLean.hol_opam.thm_REAL_LT_LSQRT holTheoryInst

theorem hol_REAL_LT_RSQRT : 
  ∀ (x y : ℝ), x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) < y → x < SQRT_HOL y := @HolLightLean.hol_opam.thm_REAL_LT_RSQRT holTheoryInst

theorem hol_SQRT_EVEN_POW2 : 
  ∀ (n : ℕ),
    Even n →
      SQRT_HOL (HPow.hPow (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) n) =
        HPow.hPow (α := ℝ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))))
          (n / ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_SQRT_EVEN_POW2 holTheoryInst

theorem hol_REAL_DIV_SQRT : 
  ∀ (x : ℝ), ↑(0 : ℕ) ≤ x → x / SQRT_HOL x = SQRT_HOL x := @HolLightLean.hol_opam.thm_REAL_DIV_SQRT holTheoryInst

theorem hol_REAL_RSQRT_LE : 
  ∀ (x y : ℝ),
    ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y ∧ x ≤ SQRT_HOL y → x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ≤ y := @HolLightLean.hol_opam.thm_REAL_RSQRT_LE holTheoryInst

theorem hol_REAL_LSQRT_LE : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ SQRT_HOL x ≤ y → x ≤ y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_LSQRT_LE holTheoryInst

theorem hol_REAL_SQRT_POW_2 : 
  ∀ (x : ℝ), SQRT_HOL x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = |x| := @HolLightLean.hol_opam.thm_REAL_SQRT_POW_2 holTheoryInst

theorem hol_REAL_ABS_LE_SQRT_POS : 
  ∀ (x y : ℝ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → |SQRT_HOL x - SQRT_HOL y| ≤ SQRT_HOL |x - y| := @HolLightLean.hol_opam.thm_REAL_ABS_LE_SQRT_POS holTheoryInst

theorem hol_REAL_ABS_LE_SQRT : 
  ∀ (x y : ℝ),
    |SQRT_HOL x - SQRT_HOL y| ≤ SQRT_HOL (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * |x - y|) := @HolLightLean.hol_opam.thm_REAL_ABS_LE_SQRT holTheoryInst

theorem hol_DECIMAL : 
  ∀ (x y : ℕ), HDiv.hDiv (α := ℝ) ↑x ↑y = HDiv.hDiv (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_DECIMAL holTheoryInst

theorem hol_RAT_LEMMA1 : 
  ∀ (x1 x2 y1 y2 : ℝ), ¬y1 = ↑(0 : ℕ) ∧ ¬y2 = ↑(0 : ℕ) → x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) * (y1⁻¹ * y2⁻¹) := @HolLightLean.hol_opam.thm_RAT_LEMMA1 holTheoryInst

theorem hol_RAT_LEMMA2 : 
  ∀ (x1 x2 y1 y2 : ℝ), ↑(0 : ℕ) < y1 ∧ ↑(0 : ℕ) < y2 → x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) * (y1⁻¹ * y2⁻¹) := @HolLightLean.hol_opam.thm_RAT_LEMMA2 holTheoryInst

theorem hol_RAT_LEMMA3 : 
  ∀ (x1 x2 y1 y2 : ℝ), ↑(0 : ℕ) < y1 ∧ ↑(0 : ℕ) < y2 → x1 / y1 - x2 / y2 = (x1 * y2 - x2 * y1) * (y1⁻¹ * y2⁻¹) := @HolLightLean.hol_opam.thm_RAT_LEMMA3 holTheoryInst

theorem hol_RAT_LEMMA4 : 
  ∀ (x1 y2 x2 y1 : ℝ), ↑(0 : ℕ) < y1 ∧ ↑(0 : ℕ) < y2 → (x1 / y1 ≤ x2 / y2) = (x1 * y2 ≤ x2 * y1) := @HolLightLean.hol_opam.thm_RAT_LEMMA4 holTheoryInst

theorem hol_RAT_LEMMA5 : 
  ∀ (x1 y2 x2 y1 : ℝ), ↑(0 : ℕ) < y1 ∧ ↑(0 : ℕ) < y2 → (x1 / y1 = x2 / y2) = (x1 * y2 = x2 * y1) := @HolLightLean.hol_opam.thm_RAT_LEMMA5 holTheoryInst

theorem hol_REAL_LE_TRANS_LE : 
  ∀ (x y : ℝ), (x ≤ y) = ∀ (z : ℝ), y ≤ z → x ≤ z := @HolLightLean.hol_opam.thm_REAL_LE_TRANS_LE holTheoryInst

theorem hol_REAL_LE_TRANS_LTE : 
  ∀ (x y : ℝ), (x ≤ y) = ∀ (z : ℝ), y < z → x ≤ z := @HolLightLean.hol_opam.thm_REAL_LE_TRANS_LTE holTheoryInst

theorem hol_REAL_LE_TRANS_LT : 
  ∀ (x y : ℝ), (x ≤ y) = ∀ (z : ℝ), y < z → x < z := @HolLightLean.hol_opam.thm_REAL_LE_TRANS_LT holTheoryInst

theorem hol_REAL_SHRINK_RANGE : 
  ∀ (x : ℝ), |x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|)| < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_SHRINK_RANGE holTheoryInst

theorem hol_REAL_SHRINK_LT : 
  ∀ (x y : ℝ), (x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|) < y / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |y|)) = (x < y) := @HolLightLean.hol_opam.thm_REAL_SHRINK_LT holTheoryInst

theorem hol_REAL_SHRINK_LE : 
  ∀ (x y : ℝ), (x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|) ≤ y / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |y|)) = (x ≤ y) := @HolLightLean.hol_opam.thm_REAL_SHRINK_LE holTheoryInst

theorem hol_REAL_SHRINK_EQ : 
  ∀ (x y : ℝ), (x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|) = y / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |y|)) = (x = y) := @HolLightLean.hol_opam.thm_REAL_SHRINK_EQ holTheoryInst

theorem hol_REAL_SHRINK_GALOIS : 
  ∀ (x y : ℝ),
    (x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|) = y) =
      (|y| < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ y / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - |y|) = x) := @HolLightLean.hol_opam.thm_REAL_SHRINK_GALOIS holTheoryInst

theorem hol_REAL_GROW_SHRINK : 
  ∀ (x : ℝ),
    x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|) /
        (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - |x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x|)|) =
      x := @HolLightLean.hol_opam.thm_REAL_GROW_SHRINK holTheoryInst

theorem hol_REAL_SHRINK_GROW_EQ : 
  ∀ (x : ℝ),
    (x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - |x|) /
          (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - |x|)|) =
        x) =
      (|x| < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_REAL_SHRINK_GROW_EQ holTheoryInst

theorem hol_REAL_SHRINK_GROW : 
  ∀ (x : ℝ),
    |x| < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - |x|) /
          (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + |x / (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - |x|)|) =
        x := @HolLightLean.hol_opam.thm_REAL_SHRINK_GROW holTheoryInst

theorem hol_integer : 
  ∀ (x : ℝ), (∃ (n : ℕ), |x| = ↑n) = ∃ (n : ℕ), |x| = ↑n := @HolLightLean.hol_opam.thm_integer holTheoryInst

theorem hol_is_int : 
  ∀ (x : ℝ), (∃ (n : ℕ), |x| = ↑n) = ∃ (n : ℕ), x = ↑n ∨ x = -↑n := @HolLightLean.hol_opam.thm_is_int holTheoryInst

theorem hol_dest_int_rep : 
  ∀ (i : ℤ), ∃ (n : ℕ), Eq (α := ℝ) ↑i ↑n ∨ Eq (α := ℝ) (↑i) (-↑n) := @HolLightLean.hol_opam.thm_dest_int_rep holTheoryInst

theorem hol_INTEGER_REAL_OF_INT : 
  ∀ (x : ℤ), ∃ (n : ℕ), Eq (α := ℝ) |↑x| ↑n := @HolLightLean.hol_opam.thm_INTEGER_REAL_OF_INT holTheoryInst

theorem hol_int_eq : 
  ∀ (x y : ℤ), (x = y) = Eq (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_eq holTheoryInst

theorem hol_int_le : 
  ∀ (x y : ℤ), (x ≤ y) = LE.le (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_le holTheoryInst

theorem hol_int_lt : 
  ∀ (x y : ℤ), (x < y) = LT.lt (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_lt holTheoryInst

theorem hol_int_ge : 
  ∀ (x y : ℤ), (x ≥ y) = GE.ge (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_ge holTheoryInst

theorem hol_int_gt : 
  ∀ (x y : ℤ), (x > y) = GT.gt (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_gt holTheoryInst

theorem hol_int_of_num : 
  ∀ (n : ℕ), ↑n = Int.floor (α := ℝ) ↑n := @HolLightLean.hol_opam.thm_int_of_num holTheoryInst

theorem hol_int_of_num_th : 
  ∀ (n : ℕ), Eq (α := ℝ) ↑↑n ↑n := @HolLightLean.hol_opam.thm_int_of_num_th holTheoryInst

theorem hol_int_neg : 
  ∀ (i : ℤ), -i = Int.floor (α := ℝ) (-↑i) := @HolLightLean.hol_opam.thm_int_neg holTheoryInst

theorem hol_int_neg_th : 
  ∀ (x : ℤ), Eq (α := ℝ) (↑(-x)) (-↑x) := @HolLightLean.hol_opam.thm_int_neg_th holTheoryInst

theorem hol_int_add : 
  ∀ (x y : ℤ), x + y = ⌊HAdd.hAdd (α := ℝ) ↑x ↑y⌋ := @HolLightLean.hol_opam.thm_int_add holTheoryInst

theorem hol_int_add_th : 
  ∀ (x y : ℤ), ↑(x + y) = HAdd.hAdd (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_add_th holTheoryInst

theorem hol_int_sub : 
  ∀ (x y : ℤ), x - y = ⌊HSub.hSub (α := ℝ) ↑x ↑y⌋ := @HolLightLean.hol_opam.thm_int_sub holTheoryInst

theorem hol_int_sub_th : 
  ∀ (x y : ℤ), ↑(x - y) = HSub.hSub (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_sub_th holTheoryInst

theorem hol_int_mul : 
  ∀ (x y : ℤ), x * y = ⌊HMul.hMul (α := ℝ) ↑x ↑y⌋ := @HolLightLean.hol_opam.thm_int_mul holTheoryInst

theorem hol_int_mul_th : 
  ∀ (x y : ℤ), ↑(x * y) = HMul.hMul (α := ℝ) ↑x ↑y := @HolLightLean.hol_opam.thm_int_mul_th holTheoryInst

theorem hol_int_abs : 
  ∀ (x : ℤ), |x| = Int.floor (α := ℝ) |↑x| := @HolLightLean.hol_opam.thm_int_abs holTheoryInst

theorem hol_int_abs_th : 
  ∀ (x : ℤ), Eq (α := ℝ) ↑|x| |↑x| := @HolLightLean.hol_opam.thm_int_abs_th holTheoryInst

theorem hol_int_sgn : 
  ∀ (x : ℤ), x.sign = ⌊Real.sign ↑x⌋ := @HolLightLean.hol_opam.thm_int_sgn holTheoryInst

theorem hol_int_sgn_th : 
  ∀ (x : ℤ), ↑x.sign = Real.sign ↑x := @HolLightLean.hol_opam.thm_int_sgn_th holTheoryInst

theorem hol_int_max : 
  ∀ (x y : ℤ), max x y = Int.floor (α := ℝ) (max ↑x ↑y) := @HolLightLean.hol_opam.thm_int_max holTheoryInst

theorem hol_int_max_th : 
  ∀ (x y : ℤ), Eq (α := ℝ) (↑(max x y)) (max ↑x ↑y) := @HolLightLean.hol_opam.thm_int_max_th holTheoryInst

theorem hol_int_min : 
  ∀ (x y : ℤ), min x y = Int.floor (α := ℝ) (min ↑x ↑y) := @HolLightLean.hol_opam.thm_int_min holTheoryInst

theorem hol_int_min_th : 
  ∀ (x y : ℤ), Eq (α := ℝ) (↑(min x y)) (min ↑x ↑y) := @HolLightLean.hol_opam.thm_int_min_th holTheoryInst

theorem hol_int_pow : 
  ∀ (x : ℤ) (n : ℕ), x ^ n = ⌊HPow.hPow (α := ℝ) (↑x) n⌋ := @HolLightLean.hol_opam.thm_int_pow holTheoryInst

theorem hol_int_pow_th : 
  ∀ (x : ℤ) (n : ℕ), ↑(x ^ n) = HPow.hPow (α := ℝ) (↑x) n := @HolLightLean.hol_opam.thm_int_pow_th holTheoryInst

theorem hol_REAL_OF_INT_CLAUSES : 
  (∀ (x y : ℤ), Eq (α := ℝ) ↑x ↑y = (x = y)) ∧
    (∀ (x y : ℤ), GE.ge (α := ℝ) ↑x ↑y = (x ≥ y)) ∧
      (∀ (x y : ℤ), GT.gt (α := ℝ) ↑x ↑y = (x > y)) ∧
        (∀ (x y : ℤ), LE.le (α := ℝ) ↑x ↑y = (x ≤ y)) ∧
          (∀ (x y : ℤ), LT.lt (α := ℝ) ↑x ↑y = (x < y)) ∧
            (∀ (x y : ℤ), Eq (α := ℝ) (max ↑x ↑y) ↑(max x y)) ∧
              (∀ (x y : ℤ), Eq (α := ℝ) (min ↑x ↑y) ↑(min x y)) ∧
                (∀ (n : ℕ), Eq (α := ℝ) ↑n ↑↑n) ∧
                  (∀ (x : ℤ), Eq (α := ℝ) (-↑x) ↑(-x)) ∧
                    (∀ (x : ℤ), Eq (α := ℝ) |↑x| ↑|x|) ∧
                      (∀ (x y : ℤ), Eq (α := ℝ) (max ↑x ↑y) ↑(max x y)) ∧
                        (∀ (x y : ℤ), Eq (α := ℝ) (min ↑x ↑y) ↑(min x y)) ∧
                          (∀ (x : ℤ), Real.sign ↑x = ↑x.sign) ∧
                            (∀ (x y : ℤ), HAdd.hAdd (α := ℝ) ↑x ↑y = ↑(x + y)) ∧
                              (∀ (x y : ℤ), HSub.hSub (α := ℝ) ↑x ↑y = ↑(x - y)) ∧
                                (∀ (x y : ℤ), HMul.hMul (α := ℝ) ↑x ↑y = ↑(x * y)) ∧
                                  ∀ (x : ℤ) (n : ℕ), HPow.hPow (α := ℝ) (↑x) n = ↑(x ^ n) := @HolLightLean.hol_opam.thm_REAL_OF_INT_CLAUSES holTheoryInst

theorem hol_INT_IMAGE : 
  ∀ (x : ℤ), (∃ (n : ℕ), x = ↑n) ∨ ∃ (n : ℕ), x = -↑n := @HolLightLean.hol_opam.thm_INT_IMAGE holTheoryInst

theorem hol_FORALL_INT_CASES : 
  ∀ (P : Set ℤ), (∀ (x : ℤ), P x) = ((∀ (n : ℕ), P ↑n) ∧ ∀ (n : ℕ), P (-↑n)) := @HolLightLean.hol_opam.thm_FORALL_INT_CASES holTheoryInst

theorem hol_EXISTS_INT_CASES : 
  ∀ (P : Set ℤ), (∃ (x : ℤ), P x) = ((∃ (n : ℕ), P ↑n) ∨ ∃ (n : ℕ), P (-↑n)) := @HolLightLean.hol_opam.thm_EXISTS_INT_CASES holTheoryInst

theorem hol_INT_LT_DISCRETE : 
  ∀ (x y : ℤ), (x < y) = (x + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ y) := @HolLightLean.hol_opam.thm_INT_LT_DISCRETE holTheoryInst

theorem hol_INT_GT_DISCRETE : 
  ∀ (x y : ℤ), (x > y) = (x ≥ y + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_GT_DISCRETE holTheoryInst

theorem hol_INT_ABS_0 : 
  Eq (α := ℤ) |↑(0 : ℕ)| ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_ABS_0 holTheoryInst

theorem hol_INT_ABS_1 : 
  Eq (α := ℤ) |↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))| ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_ABS_1 holTheoryInst

theorem hol_INT_ABS_ABS : 
  ∀ (x : ℤ), |(|x|)| = |x| := @HolLightLean.hol_opam.thm_INT_ABS_ABS holTheoryInst

theorem hol_INT_ABS_BETWEEN : 
  ∀ (x y d : ℤ), (↑(0 : ℕ) < d ∧ x - d < y ∧ y < x + d) = (|y - x| < d) := @HolLightLean.hol_opam.thm_INT_ABS_BETWEEN holTheoryInst

theorem hol_INT_ABS_BETWEEN1 : 
  ∀ (x y z : ℤ), x < z ∧ |y - x| < z - x → y < z := @HolLightLean.hol_opam.thm_INT_ABS_BETWEEN1 holTheoryInst

theorem hol_INT_ABS_BETWEEN2 : 
  ∀ (x0 x y0 y : ℤ),
    x0 < y0 ∧
        ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * |x - x0| < y0 - x0 ∧
          ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * |y - y0| < y0 - x0 →
      x < y := @HolLightLean.hol_opam.thm_INT_ABS_BETWEEN2 holTheoryInst

theorem hol_INT_ABS_BOUND : 
  ∀ (x y d : ℤ), |x - y| < d → y < x + d := @HolLightLean.hol_opam.thm_INT_ABS_BOUND holTheoryInst

theorem hol_INT_ABS_BOUNDS : 
  ∀ (x k : ℤ), (|x| ≤ k) = (-k ≤ x ∧ x ≤ k) := @HolLightLean.hol_opam.thm_INT_ABS_BOUNDS holTheoryInst

theorem hol_INT_ABS_CASES : 
  ∀ (x : ℤ), x = ↑(0 : ℕ) ∨ ↑(0 : ℕ) < |x| := @HolLightLean.hol_opam.thm_INT_ABS_CASES holTheoryInst

theorem hol_INT_ABS_CIRCLE : 
  ∀ (x y h : ℤ), |h| < |y| - |x| → |x + h| < |y| := @HolLightLean.hol_opam.thm_INT_ABS_CIRCLE holTheoryInst

theorem hol_INT_ABS_LE : 
  ∀ (x : ℤ), x ≤ |x| := @HolLightLean.hol_opam.thm_INT_ABS_LE holTheoryInst

theorem hol_INT_ABS_MUL : 
  ∀ (x y : ℤ), |x * y| = |x| * |y| := @HolLightLean.hol_opam.thm_INT_ABS_MUL holTheoryInst

theorem hol_INT_ABS_NEG : 
  ∀ (x : ℤ), |(-x)| = |x| := @HolLightLean.hol_opam.thm_INT_ABS_NEG holTheoryInst

theorem hol_INT_ABS_NUM : 
  ∀ (n : ℕ), Eq (α := ℤ) |↑n| ↑n := @HolLightLean.hol_opam.thm_INT_ABS_NUM holTheoryInst

theorem hol_INT_ABS_NZ : 
  ∀ (x : ℤ), (¬x = ↑(0 : ℕ)) = (↑(0 : ℕ) < |x|) := @HolLightLean.hol_opam.thm_INT_ABS_NZ holTheoryInst

theorem hol_INT_ABS_POS : 
  ∀ (x : ℤ), ↑(0 : ℕ) ≤ |x| := @HolLightLean.hol_opam.thm_INT_ABS_POS holTheoryInst

theorem hol_INT_ABS_POW : 
  ∀ (x : ℤ) (n : ℕ), |x ^ n| = |x| ^ n := @HolLightLean.hol_opam.thm_INT_ABS_POW holTheoryInst

theorem hol_INT_ABS_REFL : 
  ∀ (x : ℤ), (|x| = x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_ABS_REFL holTheoryInst

theorem hol_INT_ABS_SGN : 
  ∀ (x : ℤ), |x.sign| = |x|.sign := @HolLightLean.hol_opam.thm_INT_ABS_SGN holTheoryInst

theorem hol_INT_ABS_SIGN : 
  ∀ (x y : ℤ), |x - y| < y → ↑(0 : ℕ) < x := @HolLightLean.hol_opam.thm_INT_ABS_SIGN holTheoryInst

theorem hol_INT_ABS_SIGN2 : 
  ∀ (x y : ℤ), |x - y| < -y → x < ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_ABS_SIGN2 holTheoryInst

theorem hol_INT_ABS_STILLNZ : 
  ∀ (x y : ℤ), |x - y| < |y| → ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_ABS_STILLNZ holTheoryInst

theorem hol_INT_ABS_SUB : 
  ∀ (x y : ℤ), |x - y| = |y - x| := @HolLightLean.hol_opam.thm_INT_ABS_SUB holTheoryInst

theorem hol_INT_ABS_SUB_ABS : 
  ∀ (x y : Int),
    @LE.le Int Int.instLEInt
      (@abs Int instLatticeInt Int.instAddGroup
        (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@abs Int instLatticeInt Int.instAddGroup x)
          (@abs Int instLatticeInt Int.instAddGroup y)))
      (@abs Int instLatticeInt Int.instAddGroup (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) x y)) := @HolLightLean.hol_opam.thm_INT_ABS_SUB_ABS holTheoryInst

theorem hol_INT_ABS_TRIANGLE : 
  ∀ (x y : ℤ), |x + y| ≤ |x| + |y| := @HolLightLean.hol_opam.thm_INT_ABS_TRIANGLE holTheoryInst

theorem hol_INT_ABS_ZERO : 
  ∀ (x : ℤ), (|x| = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_ABS_ZERO holTheoryInst

theorem hol_INT_ADD2_SUB2 : 
  ∀ (a b c d : ℤ), a + b - (c + d) = a - c + (b - d) := @HolLightLean.hol_opam.thm_INT_ADD2_SUB2 holTheoryInst

theorem hol_INT_ADD_AC : 
  ∀ (n m p : ℤ), m + n = n + m ∧ m + n + p = m + (n + p) ∧ m + (n + p) = n + (m + p) := @HolLightLean.hol_opam.thm_INT_ADD_AC holTheoryInst

theorem hol_INT_ADD_ASSOC : 
  ∀ (x y z : ℤ), x + (y + z) = x + y + z := @HolLightLean.hol_opam.thm_INT_ADD_ASSOC holTheoryInst

theorem hol_INT_ADD_LDISTRIB : 
  ∀ (x y z : ℤ), x * (y + z) = x * y + x * z := @HolLightLean.hol_opam.thm_INT_ADD_LDISTRIB holTheoryInst

theorem hol_INT_ADD_LID : 
  ∀ (x : ℤ), ↑(0 : ℕ) + x = x := @HolLightLean.hol_opam.thm_INT_ADD_LID holTheoryInst

theorem hol_INT_ADD_LINV : 
  ∀ (x : ℤ), -x + x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_ADD_LINV holTheoryInst

theorem hol_INT_ADD_RDISTRIB : 
  ∀ (x y z : ℤ), (x + y) * z = x * z + y * z := @HolLightLean.hol_opam.thm_INT_ADD_RDISTRIB holTheoryInst

theorem hol_INT_ADD_RID : 
  ∀ (x : ℤ), x + ↑(0 : ℕ) = x := @HolLightLean.hol_opam.thm_INT_ADD_RID holTheoryInst

theorem hol_INT_ADD_RINV : 
  ∀ (x : ℤ), x + -x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_ADD_RINV holTheoryInst

theorem hol_INT_ADD_SUB : 
  ∀ (x y : ℤ), x + y - x = y := @HolLightLean.hol_opam.thm_INT_ADD_SUB holTheoryInst

theorem hol_INT_ADD_SUB2 : 
  ∀ (x y : ℤ), x - (x + y) = -y := @HolLightLean.hol_opam.thm_INT_ADD_SUB2 holTheoryInst

theorem hol_INT_ADD_SYM : 
  ∀ (x y : ℤ), x + y = y + x := @HolLightLean.hol_opam.thm_INT_ADD_SYM holTheoryInst

theorem hol_INT_BOUNDS_LE : 
  ∀ (x k : ℤ), (-k ≤ x ∧ x ≤ k) = (|x| ≤ k) := @HolLightLean.hol_opam.thm_INT_BOUNDS_LE holTheoryInst

theorem hol_INT_BOUNDS_LT : 
  ∀ (x k : ℤ), (-k < x ∧ x < k) = (|x| < k) := @HolLightLean.hol_opam.thm_INT_BOUNDS_LT holTheoryInst

theorem hol_INT_DIFFSQ : 
  ∀ (x y : ℤ), (x + y) * (x - y) = x * x - y * y := @HolLightLean.hol_opam.thm_INT_DIFFSQ holTheoryInst

theorem hol_INT_ENTIRE : 
  ∀ (x y : ℤ), (x * y = ↑(0 : ℕ)) = (x = ↑(0 : ℕ) ∨ y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_ENTIRE holTheoryInst

theorem hol_INT_EQ_ADD_LCANCEL : 
  ∀ (x y z : ℤ), (x + y = x + z) = (y = z) := @HolLightLean.hol_opam.thm_INT_EQ_ADD_LCANCEL holTheoryInst

theorem hol_INT_EQ_ADD_LCANCEL_0 : 
  ∀ (x y : ℤ), (x + y = x) = (y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_EQ_ADD_LCANCEL_0 holTheoryInst

theorem hol_INT_EQ_ADD_RCANCEL : 
  ∀ (x y z : ℤ), (x + z = y + z) = (x = y) := @HolLightLean.hol_opam.thm_INT_EQ_ADD_RCANCEL holTheoryInst

theorem hol_INT_EQ_ADD_RCANCEL_0 : 
  ∀ (x y : ℤ), (x + y = y) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_EQ_ADD_RCANCEL_0 holTheoryInst

theorem hol_INT_EQ_IMP_LE : 
  ∀ (x y : ℤ), x = y → x ≤ y := @HolLightLean.hol_opam.thm_INT_EQ_IMP_LE holTheoryInst

theorem hol_INT_EQ_LCANCEL_IMP : 
  ∀ (x y z : ℤ), ¬z = ↑(0 : ℕ) ∧ z * x = z * y → x = y := @HolLightLean.hol_opam.thm_INT_EQ_LCANCEL_IMP holTheoryInst

theorem hol_INT_EQ_MUL_LCANCEL : 
  ∀ (x y z : ℤ), (x * y = x * z) = (x = ↑(0 : ℕ) ∨ y = z) := @HolLightLean.hol_opam.thm_INT_EQ_MUL_LCANCEL holTheoryInst

theorem hol_INT_EQ_MUL_RCANCEL : 
  ∀ (x y z : ℤ), (x * z = y * z) = (x = y ∨ z = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_EQ_MUL_RCANCEL holTheoryInst

theorem hol_INT_EQ_NEG2 : 
  ∀ (x y : ℤ), (-x = -y) = (x = y) := @HolLightLean.hol_opam.thm_INT_EQ_NEG2 holTheoryInst

theorem hol_INT_EQ_RCANCEL_IMP : 
  ∀ (x y z : ℤ), ¬z = ↑(0 : ℕ) ∧ x * z = y * z → x = y := @HolLightLean.hol_opam.thm_INT_EQ_RCANCEL_IMP holTheoryInst

theorem hol_INT_EQ_SGN_ABS : 
  ∀ (x y : ℤ), (x = y) = (x.sign = y.sign ∧ |x| = |y|) := @HolLightLean.hol_opam.thm_INT_EQ_SGN_ABS holTheoryInst

theorem hol_INT_EQ_SQUARE_ABS : 
  ∀ (x y : ℤ),
    (|x| = |y|) =
      (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_INT_EQ_SQUARE_ABS holTheoryInst

theorem hol_INT_EQ_SUB_LADD : 
  ∀ (x y z : ℤ), (x = y - z) = (x + z = y) := @HolLightLean.hol_opam.thm_INT_EQ_SUB_LADD holTheoryInst

theorem hol_INT_EQ_SUB_RADD : 
  ∀ (x y z : ℤ), (x - y = z) = (x = z + y) := @HolLightLean.hol_opam.thm_INT_EQ_SUB_RADD holTheoryInst

theorem hol_INT_EVENPOW_ABS : 
  ∀ (x : ℤ) (n : ℕ), Even n → |x| ^ n = x ^ n := @HolLightLean.hol_opam.thm_INT_EVENPOW_ABS holTheoryInst

theorem hol_INT_LET_ADD : 
  ∀ (x y : ℤ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x + y := @HolLightLean.hol_opam.thm_INT_LET_ADD holTheoryInst

theorem hol_INT_LET_ADD2 : 
  ∀ (w x y z : ℤ), w ≤ x ∧ y < z → w + y < x + z := @HolLightLean.hol_opam.thm_INT_LET_ADD2 holTheoryInst

theorem hol_INT_LET_ANTISYM : 
  ∀ (x y : ℤ), ¬(x ≤ y ∧ y < x) := @HolLightLean.hol_opam.thm_INT_LET_ANTISYM holTheoryInst

theorem hol_INT_LET_TOTAL : 
  ∀ (x y : ℤ), x ≤ y ∨ y < x := @HolLightLean.hol_opam.thm_INT_LET_TOTAL holTheoryInst

theorem hol_INT_LET_TRANS : 
  ∀ (x y z : ℤ), x ≤ y ∧ y < z → x < z := @HolLightLean.hol_opam.thm_INT_LET_TRANS holTheoryInst

theorem hol_INT_LE_01 : 
  LE.le (α := ℤ) ↑(0 : ℕ) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LE_01 holTheoryInst

theorem hol_INT_LE_ADD : 
  ∀ (x y : ℤ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) ≤ x + y := @HolLightLean.hol_opam.thm_INT_LE_ADD holTheoryInst

theorem hol_INT_LE_ADD2 : 
  ∀ (w x y z : ℤ), w ≤ x ∧ y ≤ z → w + y ≤ x + z := @HolLightLean.hol_opam.thm_INT_LE_ADD2 holTheoryInst

theorem hol_INT_LE_ADDL : 
  ∀ (x y : ℤ), (y ≤ x + y) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_LE_ADDL holTheoryInst

theorem hol_INT_LE_ADDR : 
  ∀ (x y : ℤ), (x ≤ x + y) = (↑(0 : ℕ) ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_ADDR holTheoryInst

theorem hol_INT_LE_ANTISYM : 
  ∀ (x y : ℤ), (x ≤ y ∧ y ≤ x) = (x = y) := @HolLightLean.hol_opam.thm_INT_LE_ANTISYM holTheoryInst

theorem hol_INT_LE_DOUBLE : 
  ∀ (x : ℤ), (↑(0 : ℕ) ≤ x + x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_LE_DOUBLE holTheoryInst

theorem hol_INT_LE_LADD : 
  ∀ (x y z : ℤ), (x + y ≤ x + z) = (y ≤ z) := @HolLightLean.hol_opam.thm_INT_LE_LADD holTheoryInst

theorem hol_INT_LE_LADD_IMP : 
  ∀ (x y z : ℤ), y ≤ z → x + y ≤ x + z := @HolLightLean.hol_opam.thm_INT_LE_LADD_IMP holTheoryInst

theorem hol_INT_LE_LCANCEL_IMP : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < x ∧ x * y ≤ x * z → y ≤ z := @HolLightLean.hol_opam.thm_INT_LE_LCANCEL_IMP holTheoryInst

theorem hol_INT_LE_LMUL : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) ≤ x ∧ y ≤ z → x * y ≤ x * z := @HolLightLean.hol_opam.thm_INT_LE_LMUL holTheoryInst

theorem hol_INT_LE_LMUL_EQ : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < z → (z * x ≤ z * y) = (x ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_LMUL_EQ holTheoryInst

theorem hol_INT_LE_LNEG : 
  ∀ (x y : ℤ), (-x ≤ y) = (↑(0 : ℕ) ≤ x + y) := @HolLightLean.hol_opam.thm_INT_LE_LNEG holTheoryInst

theorem hol_INT_LE_LT : 
  ∀ (x y : ℤ), (x ≤ y) = (x < y ∨ x = y) := @HolLightLean.hol_opam.thm_INT_LE_LT holTheoryInst

theorem hol_INT_LE_MAX : 
  ∀ (x y z : ℤ), (z ≤ max x y) = (z ≤ x ∨ z ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_MAX holTheoryInst

theorem hol_INT_LE_MIN : 
  ∀ (x y z : ℤ), (z ≤ min x y) = (z ≤ x ∧ z ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_MIN holTheoryInst

theorem hol_INT_LE_MUL : 
  ∀ (x y : ℤ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) ≤ x * y := @HolLightLean.hol_opam.thm_INT_LE_MUL holTheoryInst

theorem hol_INT_LE_MUL2 : 
  ∀ (w x y z : ℤ), ↑(0 : ℕ) ≤ w ∧ w ≤ x ∧ ↑(0 : ℕ) ≤ y ∧ y ≤ z → w * y ≤ x * z := @HolLightLean.hol_opam.thm_INT_LE_MUL2 holTheoryInst

theorem hol_INT_LE_MUL_EQ : 
  (∀ (x y : ℤ), ↑(0 : ℕ) < x → (↑(0 : ℕ) ≤ x * y) = (↑(0 : ℕ) ≤ y)) ∧
    ∀ (x y : ℤ), ↑(0 : ℕ) < y → (↑(0 : ℕ) ≤ x * y) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_LE_MUL_EQ holTheoryInst

theorem hol_INT_LE_NEG2 : 
  ∀ (x y : ℤ), (-x ≤ -y) = (y ≤ x) := @HolLightLean.hol_opam.thm_INT_LE_NEG2 holTheoryInst

theorem hol_INT_LE_NEGL : 
  ∀ (x : ℤ), (-x ≤ x) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_LE_NEGL holTheoryInst

theorem hol_INT_LE_NEGR : 
  ∀ (x : ℤ), (x ≤ -x) = (x ≤ ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LE_NEGR holTheoryInst

theorem hol_INT_LE_NEGTOTAL : 
  ∀ (x : ℤ), ↑(0 : ℕ) ≤ x ∨ ↑(0 : ℕ) ≤ -x := @HolLightLean.hol_opam.thm_INT_LE_NEGTOTAL holTheoryInst

theorem hol_INT_LE_POW2 : 
  ∀ (n : ℕ),
    ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤
      HPow.hPow (α := ℤ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) n := @HolLightLean.hol_opam.thm_INT_LE_POW2 holTheoryInst

theorem hol_INT_LE_POW_2 : 
  ∀ (x : ℤ), ↑(0 : ℕ) ≤ x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_LE_POW_2 holTheoryInst

theorem hol_INT_LE_RADD : 
  ∀ (x y z : ℤ), (x + z ≤ y + z) = (x ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_RADD holTheoryInst

theorem hol_INT_LE_RCANCEL_IMP : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < z ∧ x * z ≤ y * z → x ≤ y := @HolLightLean.hol_opam.thm_INT_LE_RCANCEL_IMP holTheoryInst

theorem hol_INT_LE_REFL : 
  ∀ (x : ℤ), x ≤ x := @HolLightLean.hol_opam.thm_INT_LE_REFL holTheoryInst

theorem hol_INT_LE_RMUL : 
  ∀ (x y z : ℤ), x ≤ y ∧ ↑(0 : ℕ) ≤ z → x * z ≤ y * z := @HolLightLean.hol_opam.thm_INT_LE_RMUL holTheoryInst

theorem hol_INT_LE_RMUL_EQ : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < z → (x * z ≤ y * z) = (x ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_RMUL_EQ holTheoryInst

theorem hol_INT_LE_RNEG : 
  ∀ (x y : ℤ), (x ≤ -y) = (x + y ≤ ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LE_RNEG holTheoryInst

theorem hol_INT_LE_SQUARE : 
  ∀ (x : ℤ), ↑(0 : ℕ) ≤ x * x := @HolLightLean.hol_opam.thm_INT_LE_SQUARE holTheoryInst

theorem hol_INT_LE_SQUARE_ABS : 
  ∀ (x y : ℤ),
    (|x| ≤ |y|) =
      (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ≤
        y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_INT_LE_SQUARE_ABS holTheoryInst

theorem hol_INT_LE_SUB_LADD : 
  ∀ (x y z : ℤ), (x ≤ y - z) = (x + z ≤ y) := @HolLightLean.hol_opam.thm_INT_LE_SUB_LADD holTheoryInst

theorem hol_INT_LE_SUB_RADD : 
  ∀ (x y z : ℤ), (x - y ≤ z) = (x ≤ z + y) := @HolLightLean.hol_opam.thm_INT_LE_SUB_RADD holTheoryInst

theorem hol_INT_LE_TOTAL : 
  ∀ (x y : ℤ), x ≤ y ∨ y ≤ x := @HolLightLean.hol_opam.thm_INT_LE_TOTAL holTheoryInst

theorem hol_INT_LE_TRANS : 
  ∀ (x y z : ℤ), x ≤ y ∧ y ≤ z → x ≤ z := @HolLightLean.hol_opam.thm_INT_LE_TRANS holTheoryInst

theorem hol_INT_LNEG_UNIQ : 
  ∀ (x y : ℤ), (x + y = ↑(0 : ℕ)) = (x = -y) := @HolLightLean.hol_opam.thm_INT_LNEG_UNIQ holTheoryInst

theorem hol_INT_LTE_ADD : 
  ∀ (x y : ℤ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) ≤ y → ↑(0 : ℕ) < x + y := @HolLightLean.hol_opam.thm_INT_LTE_ADD holTheoryInst

theorem hol_INT_LTE_ADD2 : 
  ∀ (w x y z : ℤ), w < x ∧ y ≤ z → w + y < x + z := @HolLightLean.hol_opam.thm_INT_LTE_ADD2 holTheoryInst

theorem hol_INT_LTE_ANTISYM : 
  ∀ (x y : ℤ), ¬(x < y ∧ y ≤ x) := @HolLightLean.hol_opam.thm_INT_LTE_ANTISYM holTheoryInst

theorem hol_INT_LTE_TOTAL : 
  ∀ (x y : ℤ), x < y ∨ y ≤ x := @HolLightLean.hol_opam.thm_INT_LTE_TOTAL holTheoryInst

theorem hol_INT_LTE_TRANS : 
  ∀ (x y z : ℤ), x < y ∧ y ≤ z → x < z := @HolLightLean.hol_opam.thm_INT_LTE_TRANS holTheoryInst

theorem hol_INT_LT_01 : 
  LT.lt (α := ℤ) ↑(0 : ℕ) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LT_01 holTheoryInst

theorem hol_INT_LT_ADD : 
  ∀ (x y : ℤ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x + y := @HolLightLean.hol_opam.thm_INT_LT_ADD holTheoryInst

theorem hol_INT_LT_ADD1 : 
  ∀ (x y : ℤ), x ≤ y → x < y + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LT_ADD1 holTheoryInst

theorem hol_INT_LT_ADD2 : 
  ∀ (w x y z : ℤ), w < x ∧ y < z → w + y < x + z := @HolLightLean.hol_opam.thm_INT_LT_ADD2 holTheoryInst

theorem hol_INT_LT_ADDL : 
  ∀ (x y : ℤ), (y < x + y) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_INT_LT_ADDL holTheoryInst

theorem hol_INT_LT_ADDNEG : 
  ∀ (x y z : ℤ), (y < x + -z) = (y + z < x) := @HolLightLean.hol_opam.thm_INT_LT_ADDNEG holTheoryInst

theorem hol_INT_LT_ADDNEG2 : 
  ∀ (x y z : ℤ), (x + -y < z) = (x < z + y) := @HolLightLean.hol_opam.thm_INT_LT_ADDNEG2 holTheoryInst

theorem hol_INT_LT_ADDR : 
  ∀ (x y : ℤ), (x < x + y) = (↑(0 : ℕ) < y) := @HolLightLean.hol_opam.thm_INT_LT_ADDR holTheoryInst

theorem hol_INT_LT_ADD_SUB : 
  ∀ (x y z : ℤ), (x + y < z) = (x < z - y) := @HolLightLean.hol_opam.thm_INT_LT_ADD_SUB holTheoryInst

theorem hol_INT_LT_ANTISYM : 
  ∀ (x y : ℤ), ¬(x < y ∧ y < x) := @HolLightLean.hol_opam.thm_INT_LT_ANTISYM holTheoryInst

theorem hol_INT_LT_GT : 
  ∀ (x y : ℤ), x < y → ¬y < x := @HolLightLean.hol_opam.thm_INT_LT_GT holTheoryInst

theorem hol_INT_LT_IMP_LE : 
  ∀ (x y : ℤ), x < y → x ≤ y := @HolLightLean.hol_opam.thm_INT_LT_IMP_LE holTheoryInst

theorem hol_INT_LT_IMP_NE : 
  ∀ (x y : ℤ), x < y → ¬x = y := @HolLightLean.hol_opam.thm_INT_LT_IMP_NE holTheoryInst

theorem hol_INT_LT_LADD : 
  ∀ (x y z : ℤ), (x + y < x + z) = (y < z) := @HolLightLean.hol_opam.thm_INT_LT_LADD holTheoryInst

theorem hol_INT_LT_LADD_IMP : 
  ∀ (x y z : ℤ), y < z → x + y < x + z := @HolLightLean.hol_opam.thm_INT_LT_LADD_IMP holTheoryInst

theorem hol_INT_LT_LCANCEL_IMP : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < x ∧ x * y < x * z → y < z := @HolLightLean.hol_opam.thm_INT_LT_LCANCEL_IMP holTheoryInst

theorem hol_INT_LT_LE : 
  ∀ (x y : ℤ), (x < y) = (x ≤ y ∧ ¬x = y) := @HolLightLean.hol_opam.thm_INT_LT_LE holTheoryInst

theorem hol_INT_LT_LMUL : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < x ∧ y < z → x * y < x * z := @HolLightLean.hol_opam.thm_INT_LT_LMUL holTheoryInst

theorem hol_INT_LT_LMUL_EQ : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < z → (z * x < z * y) = (x < y) := @HolLightLean.hol_opam.thm_INT_LT_LMUL_EQ holTheoryInst

theorem hol_INT_LT_LNEG : 
  ∀ (x y : ℤ), (-x < y) = (↑(0 : ℕ) < x + y) := @HolLightLean.hol_opam.thm_INT_LT_LNEG holTheoryInst

theorem hol_INT_LT_MAX : 
  ∀ (x y z : ℤ), (z < max x y) = (z < x ∨ z < y) := @HolLightLean.hol_opam.thm_INT_LT_MAX holTheoryInst

theorem hol_INT_LT_MIN : 
  ∀ (x y z : ℤ), (z < min x y) = (z < x ∧ z < y) := @HolLightLean.hol_opam.thm_INT_LT_MIN holTheoryInst

theorem hol_INT_LT_MUL : 
  ∀ (x y : ℤ), ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y → ↑(0 : ℕ) < x * y := @HolLightLean.hol_opam.thm_INT_LT_MUL holTheoryInst

theorem hol_INT_LT_MUL2 : 
  ∀ (w x y z : ℤ), ↑(0 : ℕ) ≤ w ∧ w < x ∧ ↑(0 : ℕ) ≤ y ∧ y < z → w * y < x * z := @HolLightLean.hol_opam.thm_INT_LT_MUL2 holTheoryInst

theorem hol_INT_LT_MUL_EQ : 
  (∀ (x y : ℤ), ↑(0 : ℕ) < x → (↑(0 : ℕ) < x * y) = (↑(0 : ℕ) < y)) ∧
    ∀ (x y : ℤ), ↑(0 : ℕ) < y → (↑(0 : ℕ) < x * y) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_INT_LT_MUL_EQ holTheoryInst

theorem hol_INT_LT_NEG2 : 
  ∀ (x y : ℤ), (-x < -y) = (y < x) := @HolLightLean.hol_opam.thm_INT_LT_NEG2 holTheoryInst

theorem hol_INT_LT_NEGTOTAL : 
  ∀ (x : ℤ), x = ↑(0 : ℕ) ∨ ↑(0 : ℕ) < x ∨ ↑(0 : ℕ) < -x := @HolLightLean.hol_opam.thm_INT_LT_NEGTOTAL holTheoryInst

theorem hol_INT_LT_POW2 : 
  ∀ (n : ℕ), ↑(0 : ℕ) < HPow.hPow (α := ℤ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) n := @HolLightLean.hol_opam.thm_INT_LT_POW2 holTheoryInst

theorem hol_INT_LT_POW_2 : 
  ∀ (x : ℤ), (↑(0 : ℕ) < x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) = ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_LT_POW_2 holTheoryInst

theorem hol_INT_LT_RADD : 
  ∀ (x y z : ℤ), (x + z < y + z) = (x < y) := @HolLightLean.hol_opam.thm_INT_LT_RADD holTheoryInst

theorem hol_INT_LT_RCANCEL_IMP : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < z ∧ x * z < y * z → x < y := @HolLightLean.hol_opam.thm_INT_LT_RCANCEL_IMP holTheoryInst

theorem hol_INT_LT_REFL : 
  ∀ (x : ℤ), ¬x < x := @HolLightLean.hol_opam.thm_INT_LT_REFL holTheoryInst

theorem hol_INT_LT_RMUL : 
  ∀ (x y z : ℤ), x < y ∧ ↑(0 : ℕ) < z → x * z < y * z := @HolLightLean.hol_opam.thm_INT_LT_RMUL holTheoryInst

theorem hol_INT_LT_RMUL_EQ : 
  ∀ (x y z : ℤ), ↑(0 : ℕ) < z → (x * z < y * z) = (x < y) := @HolLightLean.hol_opam.thm_INT_LT_RMUL_EQ holTheoryInst

theorem hol_INT_LT_RNEG : 
  ∀ (x y : ℤ), (x < -y) = (x + y < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LT_RNEG holTheoryInst

theorem hol_INT_LT_SQUARE : 
  ∀ (x : ℤ), (↑(0 : ℕ) < x * x) = ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_LT_SQUARE holTheoryInst

theorem hol_INT_LT_SQUARE_ABS : 
  ∀ (x y : ℤ),
    (|x| < |y|) =
      (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) <
        y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_INT_LT_SQUARE_ABS holTheoryInst

theorem hol_INT_LT_SUB_LADD : 
  ∀ (x y z : ℤ), (x < y - z) = (x + z < y) := @HolLightLean.hol_opam.thm_INT_LT_SUB_LADD holTheoryInst

theorem hol_INT_LT_SUB_RADD : 
  ∀ (x y z : ℤ), (x - y < z) = (x < z + y) := @HolLightLean.hol_opam.thm_INT_LT_SUB_RADD holTheoryInst

theorem hol_INT_LT_TOTAL : 
  ∀ (x y : ℤ), x = y ∨ x < y ∨ y < x := @HolLightLean.hol_opam.thm_INT_LT_TOTAL holTheoryInst

theorem hol_INT_LT_TRANS : 
  ∀ (x y z : ℤ), x < y ∧ y < z → x < z := @HolLightLean.hol_opam.thm_INT_LT_TRANS holTheoryInst

theorem hol_INT_MAX_ACI : 
  ∀ (z x y : ℤ),
    max x y = max y x ∧
      max (max x y) z = max x (max y z) ∧ max x (max y z) = max y (max x z) ∧ max x x = x ∧ max x (max x y) = max x y := @HolLightLean.hol_opam.thm_INT_MAX_ACI holTheoryInst

theorem hol_INT_MAX_ASSOC : 
  ∀ (x y z : ℤ), max x (max y z) = max (max x y) z := @HolLightLean.hol_opam.thm_INT_MAX_ASSOC holTheoryInst

theorem hol_INT_MAX_LE : 
  ∀ (x y z : ℤ), (max x y ≤ z) = (x ≤ z ∧ y ≤ z) := @HolLightLean.hol_opam.thm_INT_MAX_LE holTheoryInst

theorem hol_INT_MAX_LT : 
  ∀ (x y z : ℤ), (max x y < z) = (x < z ∧ y < z) := @HolLightLean.hol_opam.thm_INT_MAX_LT holTheoryInst

theorem hol_INT_MAX_MAX : 
  ∀ (x y : ℤ), x ≤ max x y ∧ y ≤ max x y := @HolLightLean.hol_opam.thm_INT_MAX_MAX holTheoryInst

theorem hol_INT_MAX_MIN : 
  ∀ (x y : ℤ), max x y = -min (-x) (-y) := @HolLightLean.hol_opam.thm_INT_MAX_MIN holTheoryInst

theorem hol_INT_MAX_SYM : 
  ∀ (x y : ℤ), max x y = max y x := @HolLightLean.hol_opam.thm_INT_MAX_SYM holTheoryInst

theorem hol_INT_MIN_ACI : 
  ∀ (z x y : ℤ),
    min x y = min y x ∧
      min (min x y) z = min x (min y z) ∧ min x (min y z) = min y (min x z) ∧ min x x = x ∧ min x (min x y) = min x y := @HolLightLean.hol_opam.thm_INT_MIN_ACI holTheoryInst

theorem hol_INT_MIN_ASSOC : 
  ∀ (x y z : ℤ), min x (min y z) = min (min x y) z := @HolLightLean.hol_opam.thm_INT_MIN_ASSOC holTheoryInst

theorem hol_INT_MIN_LE : 
  ∀ (x y z : ℤ), (min x y ≤ z) = (x ≤ z ∨ y ≤ z) := @HolLightLean.hol_opam.thm_INT_MIN_LE holTheoryInst

theorem hol_INT_MIN_LT : 
  ∀ (x y z : ℤ), (min x y < z) = (x < z ∨ y < z) := @HolLightLean.hol_opam.thm_INT_MIN_LT holTheoryInst

theorem hol_INT_MIN_MAX : 
  ∀ (x y : ℤ), min x y = -max (-x) (-y) := @HolLightLean.hol_opam.thm_INT_MIN_MAX holTheoryInst

theorem hol_INT_MIN_MIN : 
  ∀ (x y : ℤ), min x y ≤ x ∧ min x y ≤ y := @HolLightLean.hol_opam.thm_INT_MIN_MIN holTheoryInst

theorem hol_INT_MIN_SYM : 
  ∀ (x y : ℤ), min x y = min y x := @HolLightLean.hol_opam.thm_INT_MIN_SYM holTheoryInst

theorem hol_INT_MUL_2 : 
  ∀ (x : ℤ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * x = x + x := @HolLightLean.hol_opam.thm_INT_MUL_2 holTheoryInst

theorem hol_INT_MUL_AC : 
  ∀ (n m p : ℤ), m * n = n * m ∧ m * n * p = m * (n * p) ∧ m * (n * p) = n * (m * p) := @HolLightLean.hol_opam.thm_INT_MUL_AC holTheoryInst

theorem hol_INT_MUL_ASSOC : 
  ∀ (x y z : ℤ), x * (y * z) = x * y * z := @HolLightLean.hol_opam.thm_INT_MUL_ASSOC holTheoryInst

theorem hol_INT_MUL_LID : 
  ∀ (x : ℤ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * x = x := @HolLightLean.hol_opam.thm_INT_MUL_LID holTheoryInst

theorem hol_INT_MUL_LNEG : 
  ∀ (x y : ℤ), -x * y = -(x * y) := @HolLightLean.hol_opam.thm_INT_MUL_LNEG holTheoryInst

theorem hol_INT_MUL_LZERO : 
  ∀ (x : ℤ), ↑(0 : ℕ) * x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_MUL_LZERO holTheoryInst

theorem hol_INT_MUL_POS_LE : 
  ∀ (x y : ℤ),
    (↑(0 : ℕ) ≤ x * y) = (x = ↑(0 : ℕ) ∨ y = ↑(0 : ℕ) ∨ ↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y ∨ x < ↑(0 : ℕ) ∧ y < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_MUL_POS_LE holTheoryInst

theorem hol_INT_MUL_POS_LT : 
  ∀ (x y : ℤ), (↑(0 : ℕ) < x * y) = (↑(0 : ℕ) < x ∧ ↑(0 : ℕ) < y ∨ x < ↑(0 : ℕ) ∧ y < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_MUL_POS_LT holTheoryInst

theorem hol_INT_MUL_RID : 
  ∀ (x : ℤ), x * ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = x := @HolLightLean.hol_opam.thm_INT_MUL_RID holTheoryInst

theorem hol_INT_MUL_RNEG : 
  ∀ (x y : ℤ), x * -y = -(x * y) := @HolLightLean.hol_opam.thm_INT_MUL_RNEG holTheoryInst

theorem hol_INT_MUL_RZERO : 
  ∀ (x : ℤ), x * ↑(0 : ℕ) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_MUL_RZERO holTheoryInst

theorem hol_INT_MUL_SYM : 
  ∀ (x y : ℤ), x * y = y * x := @HolLightLean.hol_opam.thm_INT_MUL_SYM holTheoryInst

theorem hol_INT_NEG_0 : 
  Eq (α := ℤ) (-↑(0 : ℕ)) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_NEG_0 holTheoryInst

theorem hol_INT_NEG_ADD : 
  ∀ (x y : ℤ), -(x + y) = -x + -y := @HolLightLean.hol_opam.thm_INT_NEG_ADD holTheoryInst

theorem hol_INT_NEG_EQ : 
  ∀ (x y : ℤ), (-x = y) = (x = -y) := @HolLightLean.hol_opam.thm_INT_NEG_EQ holTheoryInst

theorem hol_INT_NEG_EQ_0 : 
  ∀ (x : ℤ), (-x = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_NEG_EQ_0 holTheoryInst

theorem hol_INT_NEG_GE0 : 
  ∀ (x : ℤ), (↑(0 : ℕ) ≤ -x) = (x ≤ ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_NEG_GE0 holTheoryInst

theorem hol_INT_NEG_GT0 : 
  ∀ (x : ℤ), (↑(0 : ℕ) < -x) = (x < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_NEG_GT0 holTheoryInst

theorem hol_INT_NEG_LE0 : 
  ∀ (x : ℤ), (-x ≤ ↑(0 : ℕ)) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_NEG_LE0 holTheoryInst

theorem hol_INT_NEG_LMUL : 
  ∀ (x y : ℤ), -(x * y) = -x * y := @HolLightLean.hol_opam.thm_INT_NEG_LMUL holTheoryInst

theorem hol_INT_NEG_LT0 : 
  ∀ (x : ℤ), (-x < ↑(0 : ℕ)) = (↑(0 : ℕ) < x) := @HolLightLean.hol_opam.thm_INT_NEG_LT0 holTheoryInst

theorem hol_INT_NEG_MINUS1 : 
  ∀ (x : ℤ), -x = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) * x := @HolLightLean.hol_opam.thm_INT_NEG_MINUS1 holTheoryInst

theorem hol_INT_NEG_MUL2 : 
  ∀ (x y : ℤ), -x * -y = x * y := @HolLightLean.hol_opam.thm_INT_NEG_MUL2 holTheoryInst

theorem hol_INT_NEG_NEG : 
  ∀ (x : ℤ), - -x = x := @HolLightLean.hol_opam.thm_INT_NEG_NEG holTheoryInst

theorem hol_INT_NEG_RMUL : 
  ∀ (x y : ℤ), -(x * y) = x * -y := @HolLightLean.hol_opam.thm_INT_NEG_RMUL holTheoryInst

theorem hol_INT_NEG_SUB : 
  ∀ (x y : ℤ), -(x - y) = y - x := @HolLightLean.hol_opam.thm_INT_NEG_SUB holTheoryInst

theorem hol_INT_NOT_EQ : 
  ∀ (x y : ℤ), (¬x = y) = (x < y ∨ y < x) := @HolLightLean.hol_opam.thm_INT_NOT_EQ holTheoryInst

theorem hol_INT_NOT_LE : 
  ∀ (x y : ℤ), (¬x ≤ y) = (y < x) := @HolLightLean.hol_opam.thm_INT_NOT_LE holTheoryInst

theorem hol_INT_NOT_LT : 
  ∀ (x y : ℤ), (¬x < y) = (y ≤ x) := @HolLightLean.hol_opam.thm_INT_NOT_LT holTheoryInst

theorem hol_INT_OF_NUM_ADD : 
  ∀ (m n : ℕ), HAdd.hAdd (α := ℤ) ↑m ↑n = ↑(m + n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_ADD holTheoryInst

theorem hol_INT_OF_NUM_CLAUSES : 
  (∀ (m n : ℕ), Eq (α := ℤ) ↑m ↑n = (m = n)) ∧
    (∀ (m n : ℕ), GE.ge (α := ℤ) ↑m ↑n = (m ≥ n)) ∧
      (∀ (m n : ℕ), GT.gt (α := ℤ) ↑m ↑n = (m > n)) ∧
        (∀ (m n : ℕ), LE.le (α := ℤ) ↑m ↑n = (m ≤ n)) ∧
          (∀ (m n : ℕ), LT.lt (α := ℤ) ↑m ↑n = (m < n)) ∧
            (∀ (m n : ℕ), Eq (α := ℤ) (max ↑m ↑n) ↑(max m n)) ∧
              (∀ (m n : ℕ), Eq (α := ℤ) (min ↑m ↑n) ↑(min m n)) ∧
                (∀ (m n : ℕ), HAdd.hAdd (α := ℤ) ↑m ↑n = ↑(m + n)) ∧
                  (∀ (m n : ℕ), HMul.hMul (α := ℤ) ↑m ↑n = ↑(m * n)) ∧ ∀ (x n : ℕ), HPow.hPow (α := ℤ) (↑x) n = ↑(x ^ n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_CLAUSES holTheoryInst

theorem hol_INT_OF_NUM_EQ : 
  ∀ (m n : ℕ), Eq (α := ℤ) ↑m ↑n = (m = n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_EQ holTheoryInst

theorem hol_INT_OF_NUM_GE : 
  ∀ (m n : ℕ), GE.ge (α := ℤ) ↑m ↑n = (m ≥ n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_GE holTheoryInst

theorem hol_INT_OF_NUM_GT : 
  ∀ (m n : ℕ), GT.gt (α := ℤ) ↑m ↑n = (m > n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_GT holTheoryInst

theorem hol_INT_OF_NUM_LE : 
  ∀ (m n : ℕ), LE.le (α := ℤ) ↑m ↑n = (m ≤ n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_LE holTheoryInst

theorem hol_INT_OF_NUM_LT : 
  ∀ (m n : ℕ), LT.lt (α := ℤ) ↑m ↑n = (m < n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_LT holTheoryInst

theorem hol_INT_OF_NUM_MAX : 
  ∀ (m n : ℕ), Eq (α := ℤ) (max ↑m ↑n) ↑(max m n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_MAX holTheoryInst

theorem hol_INT_OF_NUM_MIN : 
  ∀ (m n : ℕ), Eq (α := ℤ) (min ↑m ↑n) ↑(min m n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_MIN holTheoryInst

theorem hol_INT_OF_NUM_MOD : 
  ∀ (m n : ℕ), ↑(m % n) = ↑m - HMul.hMul (α := ℤ) ↑(m / n) ↑n := @HolLightLean.hol_opam.thm_INT_OF_NUM_MOD holTheoryInst

theorem hol_INT_OF_NUM_MUL : 
  ∀ (m n : ℕ), HMul.hMul (α := ℤ) ↑m ↑n = ↑(m * n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_MUL holTheoryInst

theorem hol_INT_OF_NUM_POW : 
  ∀ (x n : ℕ), HPow.hPow (α := ℤ) (↑x) n = ↑(x ^ n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_POW holTheoryInst

theorem hol_INT_OF_NUM_SUB : 
  ∀ (m n : ℕ), m ≤ n → HSub.hSub (α := ℤ) ↑n ↑m = ↑(n - m) := @HolLightLean.hol_opam.thm_INT_OF_NUM_SUB holTheoryInst

theorem hol_INT_OF_NUM_SUB_CASES : 
  ∀ (m n : ℕ), HSub.hSub (α := ℤ) ↑m ↑n = if n ≤ m then ↑(m - n) else -↑(n - m) := @HolLightLean.hol_opam.thm_INT_OF_NUM_SUB_CASES holTheoryInst

theorem hol_INT_OF_NUM_SUC : 
  ∀ (n : ℕ), HAdd.hAdd (α := ℤ) ↑n ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = ↑(n + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_OF_NUM_SUC holTheoryInst

theorem hol_INT_POS : 
  ∀ (n : ℕ), LE.le (α := ℤ) ↑(0 : ℕ) ↑n := @HolLightLean.hol_opam.thm_INT_POS holTheoryInst

theorem hol_INT_POS_EQ_SQUARE : 
  ∀ (x : ℤ), (↑(0 : ℕ) ≤ x) = ∃ (y : ℝ), y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑x := @HolLightLean.hol_opam.thm_INT_POS_EQ_SQUARE holTheoryInst

theorem hol_INT_POS_NZ : 
  ∀ (x : ℤ), ↑(0 : ℕ) < x → ¬x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_POS_NZ holTheoryInst

theorem hol_INT_POW2_ABS : 
  ∀ (x : ℤ),
    |x| ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_POW2_ABS holTheoryInst

theorem hol_INT_POW_1 : 
  ∀ (x : ℤ), x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = x := @HolLightLean.hol_opam.thm_INT_POW_1 holTheoryInst

theorem hol_INT_POW_1_LE : 
  ∀ (n : ℕ) (x : ℤ), ↑(0 : ℕ) ≤ x ∧ x ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → x ^ n ≤ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_POW_1_LE holTheoryInst

theorem hol_INT_POW_1_LT : 
  ∀ (n : ℕ) (x : ℤ),
    ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ x ∧ x < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → x ^ n < ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_POW_1_LT holTheoryInst

theorem hol_INT_POW_2 : 
  ∀ (x : ℤ), x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x * x := @HolLightLean.hol_opam.thm_INT_POW_2 holTheoryInst

theorem hol_INT_POW_ADD : 
  ∀ (x : ℤ) (m n : ℕ), x ^ (m + n) = x ^ m * x ^ n := @HolLightLean.hol_opam.thm_INT_POW_ADD holTheoryInst

theorem hol_INT_POW_EQ : 
  ∀ (n : ℕ) (x y : ℤ), ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y ∧ x ^ n = y ^ n → x = y := @HolLightLean.hol_opam.thm_INT_POW_EQ holTheoryInst

theorem hol_INT_POW_EQ_0 : 
  ∀ (x : ℤ) (n : ℕ), (x ^ n = ↑(0 : ℕ)) = (x = ↑(0 : ℕ) ∧ ¬n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_POW_EQ_0 holTheoryInst

theorem hol_INT_POW_EQ_1 : 
  ∀ (x : ℤ) (n : ℕ),
    (x ^ n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      (|x| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ (x < ↑(0 : ℕ) → Even n) ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_POW_EQ_1 holTheoryInst

theorem hol_INT_POW_EQ_1_IMP : 
  ∀ (x : ℤ) (n : ℕ), ¬n = (0 : ℕ) ∧ x ^ n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) → |x| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_POW_EQ_1_IMP holTheoryInst

theorem hol_INT_POW_EQ_ABS : 
  ∀ (n : ℕ) (x y : ℤ), ¬n = (0 : ℕ) ∧ x ^ n = y ^ n → |x| = |y| := @HolLightLean.hol_opam.thm_INT_POW_EQ_ABS holTheoryInst

theorem hol_INT_POW_EQ_EQ : 
  ∀ (n : ℕ) (x y : ℤ), (x ^ n = y ^ n) = if Even n then n = (0 : ℕ) ∨ |x| = |y| else x = y := @HolLightLean.hol_opam.thm_INT_POW_EQ_EQ holTheoryInst

theorem hol_INT_POW_EQ_ODD : 
  ∀ (n : ℕ) (x y : ℤ), Odd n ∧ x ^ n = y ^ n → x = y := @HolLightLean.hol_opam.thm_INT_POW_EQ_ODD holTheoryInst

theorem hol_INT_POW_EQ_ODD_EQ : 
  ∀ (n : ℕ) (x y : ℤ), Odd n → (x ^ n = y ^ n) = (x = y) := @HolLightLean.hol_opam.thm_INT_POW_EQ_ODD_EQ holTheoryInst

theorem hol_INT_POW_LBOUND : 
  ∀ (x : ℤ) (n : ℕ), ↑(0 : ℕ) ≤ x → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + ↑n * x ≤ (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + x) ^ n := @HolLightLean.hol_opam.thm_INT_POW_LBOUND holTheoryInst

theorem hol_INT_POW_LE : 
  ∀ (x : ℤ) (n : ℕ), ↑(0 : ℕ) ≤ x → ↑(0 : ℕ) ≤ x ^ n := @HolLightLean.hol_opam.thm_INT_POW_LE holTheoryInst

theorem hol_INT_POW_LE2 : 
  ∀ (n : ℕ) (x y : ℤ), ↑(0 : ℕ) ≤ x ∧ x ≤ y → x ^ n ≤ y ^ n := @HolLightLean.hol_opam.thm_INT_POW_LE2 holTheoryInst

theorem hol_INT_POW_LE2_ODD : 
  ∀ (n : ℕ) (x y : ℤ), x ≤ y ∧ Odd n → x ^ n ≤ y ^ n := @HolLightLean.hol_opam.thm_INT_POW_LE2_ODD holTheoryInst

theorem hol_INT_POW_LE2_ODD_EQ : 
  ∀ (n : ℕ) (x y : ℤ), Odd n → (x ^ n ≤ y ^ n) = (x ≤ y) := @HolLightLean.hol_opam.thm_INT_POW_LE2_ODD_EQ holTheoryInst

theorem hol_INT_POW_LE2_REV : 
  ∀ (n : ℕ) (x y : ℤ), ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ y ∧ x ^ n ≤ y ^ n → x ≤ y := @HolLightLean.hol_opam.thm_INT_POW_LE2_REV holTheoryInst

theorem hol_INT_POW_LE_1 : 
  ∀ (n : ℕ) (x : ℤ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x ^ n := @HolLightLean.hol_opam.thm_INT_POW_LE_1 holTheoryInst

theorem hol_INT_POW_LT : 
  ∀ (x : ℤ) (n : ℕ), ↑(0 : ℕ) < x → ↑(0 : ℕ) < x ^ n := @HolLightLean.hol_opam.thm_INT_POW_LT holTheoryInst

theorem hol_INT_POW_LT2 : 
  ∀ (n : ℕ) (x y : ℤ), ¬n = (0 : ℕ) ∧ ↑(0 : ℕ) ≤ x ∧ x < y → x ^ n < y ^ n := @HolLightLean.hol_opam.thm_INT_POW_LT2 holTheoryInst

theorem hol_INT_POW_LT2_ODD : 
  ∀ (n : ℕ) (x y : ℤ), x < y ∧ Odd n → x ^ n < y ^ n := @HolLightLean.hol_opam.thm_INT_POW_LT2_ODD holTheoryInst

theorem hol_INT_POW_LT2_ODD_EQ : 
  ∀ (n : ℕ) (x y : ℤ), Odd n → (x ^ n < y ^ n) = (x < y) := @HolLightLean.hol_opam.thm_INT_POW_LT2_ODD_EQ holTheoryInst

theorem hol_INT_POW_LT2_REV : 
  ∀ (n : ℕ) (x y : ℤ), ↑(0 : ℕ) ≤ y ∧ x ^ n < y ^ n → x < y := @HolLightLean.hol_opam.thm_INT_POW_LT2_REV holTheoryInst

theorem hol_INT_POW_LT_1 : 
  ∀ (n : ℕ) (x : ℤ), ¬n = (0 : ℕ) ∧ ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x → ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x ^ n := @HolLightLean.hol_opam.thm_INT_POW_LT_1 holTheoryInst

theorem hol_INT_POW_MONO : 
  ∀ (m n : ℕ) (x : ℤ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ x ∧ m ≤ n → x ^ m ≤ x ^ n := @HolLightLean.hol_opam.thm_INT_POW_MONO holTheoryInst

theorem hol_INT_POW_MONO_LT : 
  ∀ (m n : ℕ) (x : ℤ), ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) < x ∧ m < n → x ^ m < x ^ n := @HolLightLean.hol_opam.thm_INT_POW_MONO_LT holTheoryInst

theorem hol_INT_POW_MUL : 
  ∀ (x y : ℤ) (n : ℕ), (x * y) ^ n = x ^ n * y ^ n := @HolLightLean.hol_opam.thm_INT_POW_MUL holTheoryInst

theorem hol_INT_POW_NEG : 
  ∀ (x : ℤ) (n : ℕ), (-x) ^ n = if Even n then x ^ n else -x ^ n := @HolLightLean.hol_opam.thm_INT_POW_NEG holTheoryInst

theorem hol_INT_POW_NZ : 
  ∀ (x : ℤ) (n : ℕ), ¬x = ↑(0 : ℕ) → ¬x ^ n = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_POW_NZ holTheoryInst

theorem hol_INT_POW_ONE : 
  ∀ (n : ℕ), HPow.hPow (α := ℤ) (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_POW_ONE holTheoryInst

theorem hol_INT_POW_POW : 
  ∀ (x : ℤ) (m n : ℕ), (x ^ m) ^ n = x ^ (m * n) := @HolLightLean.hol_opam.thm_INT_POW_POW holTheoryInst

theorem hol_INT_POW_ZERO : 
  ∀ (n : ℕ), HPow.hPow (α := ℤ) (↑(0 : ℕ)) n = if n = (0 : ℕ) then ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_POW_ZERO holTheoryInst

theorem hol_INT_RNEG_UNIQ : 
  ∀ (x y : ℤ), (x + y = ↑(0 : ℕ)) = (y = -x) := @HolLightLean.hol_opam.thm_INT_RNEG_UNIQ holTheoryInst

theorem hol_INT_SGN : 
  ∀ (x : ℤ),
    x.sign =
      if ↑(0 : ℕ) < x then ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))
      else if x < ↑(0 : ℕ) then -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_SGN holTheoryInst

theorem hol_INT_SGNS_EQ : 
  ∀ (x y : ℤ),
    (x.sign = y.sign) =
      ((x = ↑(0 : ℕ)) = (y = ↑(0 : ℕ)) ∧ (x > ↑(0 : ℕ)) = (y > ↑(0 : ℕ)) ∧ (x < ↑(0 : ℕ)) = (y < ↑(0 : ℕ))) := @HolLightLean.hol_opam.thm_INT_SGNS_EQ holTheoryInst

theorem hol_INT_SGNS_EQ_ALT : 
  ∀ (x y : ℤ),
    (x.sign = y.sign) = ((x = ↑(0 : ℕ) → y = ↑(0 : ℕ)) ∧ (x > ↑(0 : ℕ) → y > ↑(0 : ℕ)) ∧ (x < ↑(0 : ℕ) → y < ↑(0 : ℕ))) := @HolLightLean.hol_opam.thm_INT_SGNS_EQ_ALT holTheoryInst

theorem hol_INT_SGN_0 : 
  Int.sign ↑(0 : ℕ) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_SGN_0 holTheoryInst

theorem hol_INT_SGN_ABS : 
  ∀ (x : ℤ), x.sign * |x| = x := @HolLightLean.hol_opam.thm_INT_SGN_ABS holTheoryInst

theorem hol_INT_SGN_ABS_ALT : 
  ∀ (x : ℤ), x.sign * x = |x| := @HolLightLean.hol_opam.thm_INT_SGN_ABS_ALT holTheoryInst

theorem hol_INT_SGN_CASES : 
  ∀ (x : ℤ), x.sign = ↑(0 : ℕ) ∨ x.sign = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∨ x.sign = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_SGN_CASES holTheoryInst

theorem hol_INT_SGN_EQ : 
  (∀ (x : ℤ), (x.sign = ↑(0 : ℕ)) = (x = ↑(0 : ℕ))) ∧
    (∀ (x : ℤ), (x.sign = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x > ↑(0 : ℕ))) ∧
      ∀ (x : ℤ), (x.sign = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = (x < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_SGN_EQ holTheoryInst

theorem hol_INT_SGN_EQ_INEQ : 
  ∀ (x y : ℤ), (x.sign = y.sign) = (x = y ∨ |x - y| < max |x| |y|) := @HolLightLean.hol_opam.thm_INT_SGN_EQ_INEQ holTheoryInst

theorem hol_INT_SGN_INEQS : 
  (∀ (x : ℤ), (↑(0 : ℕ) ≤ x.sign) = (↑(0 : ℕ) ≤ x)) ∧
    (∀ (x : ℤ), (↑(0 : ℕ) < x.sign) = (↑(0 : ℕ) < x)) ∧
      (∀ (x : ℤ), (↑(0 : ℕ) ≥ x.sign) = (↑(0 : ℕ) ≥ x)) ∧
        (∀ (x : ℤ), (↑(0 : ℕ) > x.sign) = (↑(0 : ℕ) > x)) ∧
          (∀ (x : ℤ), (↑(0 : ℕ) = x.sign) = (↑(0 : ℕ) = x)) ∧
            (∀ (x : ℤ), (x.sign ≤ ↑(0 : ℕ)) = (x ≤ ↑(0 : ℕ))) ∧
              (∀ (x : ℤ), (x.sign < ↑(0 : ℕ)) = (x < ↑(0 : ℕ))) ∧
                (∀ (x : ℤ), (x.sign ≥ ↑(0 : ℕ)) = (x ≥ ↑(0 : ℕ))) ∧
                  (∀ (x : ℤ), (x.sign > ↑(0 : ℕ)) = (x > ↑(0 : ℕ))) ∧ ∀ (x : ℤ), (x.sign = ↑(0 : ℕ)) = (x = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_SGN_INEQS holTheoryInst

theorem hol_INT_SGN_INT_SGN : 
  ∀ (x : ℤ), x.sign.sign = x.sign := @HolLightLean.hol_opam.thm_INT_SGN_INT_SGN holTheoryInst

theorem hol_INT_SGN_MUL : 
  ∀ (x y : ℤ), (x * y).sign = x.sign * y.sign := @HolLightLean.hol_opam.thm_INT_SGN_MUL holTheoryInst

theorem hol_INT_SGN_NEG : 
  ∀ (x : ℤ), (-x).sign = -x.sign := @HolLightLean.hol_opam.thm_INT_SGN_NEG holTheoryInst

theorem hol_INT_SGN_POW : 
  ∀ (x : ℤ) (n : ℕ), (x ^ n).sign = x.sign ^ n := @HolLightLean.hol_opam.thm_INT_SGN_POW holTheoryInst

theorem hol_INT_SGN_POW_2 : 
  ∀ (x : ℤ), (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))).sign = |x|.sign := @HolLightLean.hol_opam.thm_INT_SGN_POW_2 holTheoryInst

theorem hol_INT_SOS_EQ_0 : 
  ∀ (x y : ℤ),
    (x ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) +
          y ^ ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        ↑(0 : ℕ)) =
      (x = ↑(0 : ℕ) ∧ y = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_SOS_EQ_0 holTheoryInst

theorem hol_INT_SUB_0 : 
  ∀ (x y : ℤ), (x - y = ↑(0 : ℕ)) = (x = y) := @HolLightLean.hol_opam.thm_INT_SUB_0 holTheoryInst

theorem hol_INT_SUB_ABS : 
  ∀ (x y : ℤ), |x| - |y| ≤ |x - y| := @HolLightLean.hol_opam.thm_INT_SUB_ABS holTheoryInst

theorem hol_INT_SUB_ADD : 
  ∀ (x y : ℤ), x - y + y = x := @HolLightLean.hol_opam.thm_INT_SUB_ADD holTheoryInst

theorem hol_INT_SUB_ADD2 : 
  ∀ (x y : ℤ), y + (x - y) = x := @HolLightLean.hol_opam.thm_INT_SUB_ADD2 holTheoryInst

theorem hol_INT_SUB_LDISTRIB : 
  ∀ (x y z : ℤ), x * (y - z) = x * y - x * z := @HolLightLean.hol_opam.thm_INT_SUB_LDISTRIB holTheoryInst

theorem hol_INT_SUB_LE : 
  ∀ (x y : ℤ), (↑(0 : ℕ) ≤ x - y) = (y ≤ x) := @HolLightLean.hol_opam.thm_INT_SUB_LE holTheoryInst

theorem hol_INT_SUB_LNEG : 
  ∀ (x y : ℤ), -x - y = -(x + y) := @HolLightLean.hol_opam.thm_INT_SUB_LNEG holTheoryInst

theorem hol_INT_SUB_LT : 
  ∀ (x y : ℤ), (↑(0 : ℕ) < x - y) = (y < x) := @HolLightLean.hol_opam.thm_INT_SUB_LT holTheoryInst

theorem hol_INT_SUB_LZERO : 
  ∀ (x : ℤ), ↑(0 : ℕ) - x = -x := @HolLightLean.hol_opam.thm_INT_SUB_LZERO holTheoryInst

theorem hol_INT_SUB_NEG2 : 
  ∀ (x y : ℤ), -x - -y = y - x := @HolLightLean.hol_opam.thm_INT_SUB_NEG2 holTheoryInst

theorem hol_INT_SUB_RDISTRIB : 
  ∀ (x y z : ℤ), (x - y) * z = x * z - y * z := @HolLightLean.hol_opam.thm_INT_SUB_RDISTRIB holTheoryInst

theorem hol_INT_SUB_REFL : 
  ∀ (x : ℤ), x - x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_SUB_REFL holTheoryInst

theorem hol_INT_SUB_RNEG : 
  ∀ (x y : ℤ), x - -y = x + y := @HolLightLean.hol_opam.thm_INT_SUB_RNEG holTheoryInst

theorem hol_INT_SUB_RZERO : 
  ∀ (x : ℤ), x - ↑(0 : ℕ) = x := @HolLightLean.hol_opam.thm_INT_SUB_RZERO holTheoryInst

theorem hol_INT_SUB_SUB : 
  ∀ (x y : ℤ), x - y - x = -y := @HolLightLean.hol_opam.thm_INT_SUB_SUB holTheoryInst

theorem hol_INT_SUB_SUB2 : 
  ∀ (x y : ℤ), x - (x - y) = y := @HolLightLean.hol_opam.thm_INT_SUB_SUB2 holTheoryInst

theorem hol_INT_SUB_TRIANGLE : 
  ∀ (a b c : ℤ), a - b + (b - c) = a - c := @HolLightLean.hol_opam.thm_INT_SUB_TRIANGLE holTheoryInst

theorem hol_INT_WLOG_LE : 
  ∀ (P : ℤ → ℤ → Prop), ((∀ (x y : ℤ), P x y = P y x) ∧ ∀ (x y : ℤ), x ≤ y → P x y) → ∀ (x y : ℤ), P x y := @HolLightLean.hol_opam.thm_INT_WLOG_LE holTheoryInst

theorem hol_INT_WLOG_LT : 
  ∀ (P : ℤ → ℤ → Prop),
    ((∀ (x : ℤ), P x x) ∧ (∀ (x y : ℤ), P x y = P y x) ∧ ∀ (x y : ℤ), x < y → P x y) → ∀ (x y : ℤ), P x y := @HolLightLean.hol_opam.thm_INT_WLOG_LT holTheoryInst

theorem hol_INT_WLOG_LE_3 : 
  ∀ (P : ℤ → ℤ → ℤ → Prop),
    ((∀ (x y z : ℤ), P x y z → P y x z ∧ P x z y) ∧ ∀ (x y z : ℤ), x ≤ y ∧ y ≤ z → P x y z) → ∀ (x y z : ℤ), P x y z := @HolLightLean.hol_opam.thm_INT_WLOG_LE_3 holTheoryInst

theorem hol_INT_FORALL_POS : 
  ∀ (P : Set ℤ), Eq (α := Prop) (∀ (n : ℕ), P ↑n) (∀ (i : ℤ), ↑(0 : ℕ) ≤ i → P i) := @HolLightLean.hol_opam.thm_INT_FORALL_POS holTheoryInst

theorem hol_INT_EXISTS_POS : 
  ∀ (P : Set ℤ), (∃ (n : ℕ), P ↑n) = ∃ (i : ℤ), ↑(0 : ℕ) ≤ i ∧ P i := @HolLightLean.hol_opam.thm_INT_EXISTS_POS holTheoryInst

theorem hol_INT_FORALL_ABS : 
  ∀ (P : Set ℤ), Eq (α := Prop) (∀ (n : ℕ), P ↑n) (∀ (x : ℤ), P |x|) := @HolLightLean.hol_opam.thm_INT_FORALL_ABS holTheoryInst

theorem hol_INT_EXISTS_ABS : 
  ∀ (P : Set ℤ), (∃ (n : ℕ), P ↑n) = ∃ (x : ℤ), P |x| := @HolLightLean.hol_opam.thm_INT_EXISTS_ABS holTheoryInst

theorem hol_INT_POW : 
  ∀ (x : ℤ), x ^ (0 : ℕ) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ ∀ (n : ℕ), x ^ (n + (1 : ℕ)) = x * x ^ n := @HolLightLean.hol_opam.thm_INT_POW holTheoryInst

theorem hol_INT_ABS : 
  ∀ (x : ℤ), |x| = if ↑(0 : ℕ) ≤ x then x else -x := @HolLightLean.hol_opam.thm_INT_ABS holTheoryInst

theorem hol_INT_GE : 
  ∀ (x y : ℤ), (x ≥ y) = (y ≤ x) := @HolLightLean.hol_opam.thm_INT_GE holTheoryInst

theorem hol_INT_GT : 
  ∀ (x y : ℤ), (x > y) = (y < x) := @HolLightLean.hol_opam.thm_INT_GT holTheoryInst

theorem hol_INT_LT : 
  ∀ (x y : ℤ), (x < y) = ¬y ≤ x := @HolLightLean.hol_opam.thm_INT_LT holTheoryInst

theorem hol_INT_SUB : 
  ∀ (x y : ℤ), x - y = x + -y := @HolLightLean.hol_opam.thm_INT_SUB holTheoryInst

theorem hol_INT_MAX : 
  ∀ (x y : ℤ), max x y = if x ≤ y then y else x := @HolLightLean.hol_opam.thm_INT_MAX holTheoryInst

theorem hol_INT_MIN : 
  ∀ (x y : ℤ), min x y = if x ≤ y then x else y := @HolLightLean.hol_opam.thm_INT_MIN holTheoryInst

theorem hol_INT_OF_NUM_EXISTS : 
  ∀ (x : ℤ), (∃ (n : ℕ), x = ↑n) = (↑(0 : ℕ) ≤ x) := @HolLightLean.hol_opam.thm_INT_OF_NUM_EXISTS holTheoryInst

theorem hol_INT_LE_DISCRETE : 
  ∀ (x y : ℤ), (x ≤ y) = (x < y + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_LE_DISCRETE holTheoryInst

theorem hol_INT_LE_TRANS_LE : 
  ∀ (x y : ℤ), (x ≤ y) = ∀ (z : ℤ), y ≤ z → x ≤ z := @HolLightLean.hol_opam.thm_INT_LE_TRANS_LE holTheoryInst

theorem hol_INT_LE_TRANS_LT : 
  ∀ (x y : ℤ), (x ≤ y) = ∀ (z : ℤ), y < z → x < z := @HolLightLean.hol_opam.thm_INT_LE_TRANS_LT holTheoryInst

theorem hol_INT_MUL_EQ_1 : 
  ∀ (x y : ℤ),
    (x * y = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      (x = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ y = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∨
        x = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ y = -↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_MUL_EQ_1 holTheoryInst

theorem hol_INT_ABS_MUL_1 : 
  ∀ (x y : ℤ),
    (|x * y| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      (|x| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ |y| = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_ABS_MUL_1 holTheoryInst

theorem hol_INT_WOP : 
  ∀ (P : Set ℤ), (∃ (x : ℤ), ↑(0 : ℕ) ≤ x ∧ P x) = ∃ (x : ℤ), ↑(0 : ℕ) ≤ x ∧ P x ∧ ∀ (y : ℤ), ↑(0 : ℕ) ≤ y ∧ P y → x ≤ y := @HolLightLean.hol_opam.thm_INT_WOP holTheoryInst

theorem hol_INT_ARCH : 
  ∀ (x d : ℤ), ¬d = ↑(0 : ℕ) → ∃ (c : ℤ), x < c * d := @HolLightLean.hol_opam.thm_INT_ARCH holTheoryInst

theorem hol_INT_DIVMOD_EXIST_0 : 
  ∀ (m n : ℤ), ∃ (q : ℤ) (r : ℤ), if n = ↑(0 : ℕ) then q = ↑(0 : ℕ) ∧ r = m else ↑(0 : ℕ) ≤ r ∧ r < |n| ∧ m = q * n + r := @HolLightLean.hol_opam.thm_INT_DIVMOD_EXIST_0 holTheoryInst

theorem hol_INT_DIVISION : 
  ∀ (m n : ℤ), ¬n = ↑(0 : ℕ) → m = m / n * n + m % n ∧ ↑(0 : ℕ) ≤ m % n ∧ m % n < |n| := @HolLightLean.hol_opam.thm_INT_DIVISION holTheoryInst

theorem hol_INT_DIVISION_SIMP : 
  ∀ (m n : ℤ), m / n * n + m % n = m := @HolLightLean.hol_opam.thm_INT_DIVISION_SIMP holTheoryInst

theorem hol_INT_REM_POS : 
  ∀ (a b : ℤ), ¬b = ↑(0 : ℕ) → ↑(0 : ℕ) ≤ a % b := @HolLightLean.hol_opam.thm_INT_REM_POS holTheoryInst

theorem hol_INT_DIV_0 : 
  ∀ (m : ℤ), m / ↑(0 : ℕ) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_DIV_0 holTheoryInst

theorem hol_INT_REM_0 : 
  ∀ (m : ℤ), m % ↑(0 : ℕ) = m := @HolLightLean.hol_opam.thm_INT_REM_0 holTheoryInst

theorem hol_INT_REM_POS_EQ : 
  ∀ (m n : ℤ), (↑(0 : ℕ) ≤ m % n) = (n = ↑(0 : ℕ) → ↑(0 : ℕ) ≤ m) := @HolLightLean.hol_opam.thm_INT_REM_POS_EQ holTheoryInst

theorem hol_INT_REM_DIV : 
  ∀ (m n : ℤ), m % n = m - m / n * n := @HolLightLean.hol_opam.thm_INT_REM_DIV holTheoryInst

theorem hol_INT_LT_REM : 
  ∀ (x n : ℤ), ↑(0 : ℕ) < n → x % n < n := @HolLightLean.hol_opam.thm_INT_LT_REM holTheoryInst

theorem hol_INT_LT_REM_EQ : 
  ∀ (m n : ℤ), (m % n < n) = (↑(0 : ℕ) < n ∨ n = ↑(0 : ℕ) ∧ m < ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_LT_REM_EQ holTheoryInst

theorem hol_cong : 
  ∀ {A : Type} [Nonempty A] (rel : A → A → Prop) (x y : A), rel x y = rel x y := @HolLightLean.hol_opam.thm_cong holTheoryInst

theorem hol_real_mod : 
  ∀ (x y n : ℝ), (∃ (q : ℝ), (∃ (n : ℕ), |q| = ↑n) ∧ x - y = q * n) = ∃ (q : ℝ), (∃ (n : ℕ), |q| = ↑n) ∧ x - y = q * n := @HolLightLean.hol_opam.thm_real_mod holTheoryInst

theorem hol_int_divides : 
  ∀ (b a : ℤ), (a ∣ b) = ∃ (x : ℤ), b = a * x := @HolLightLean.hol_opam.thm_int_divides holTheoryInst

theorem hol_INT_DIVIDES_LE : 
  ∀ (x y : ℤ), x ∣ y → |x| ≤ |y| ∨ y = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_DIVIDES_LE holTheoryInst

theorem hol_int_mod : 
  ∀ (n x y : ℤ), (n ∣ x - y) = (n ∣ x - y) := @HolLightLean.hol_opam.thm_int_mod holTheoryInst

theorem hol_int_congruent : 
  ∀ (x y n : ℤ), (fun (x y : ℤ) ↦ n ∣ x - y) x y = ∃ (d : ℤ), x - y = n * d := @HolLightLean.hol_opam.thm_int_congruent holTheoryInst

theorem hol_INT_CONG_IMP_EQ : 
  ∀ (x y n : ℤ), |x - y| < n ∧ (fun (x y : ℤ) ↦ n ∣ x - y) x y → x = y := @HolLightLean.hol_opam.thm_INT_CONG_IMP_EQ holTheoryInst

theorem hol_int_coprime : 
  ∀ (a b : ℤ), IsCoprime (a, b).1 (a, b).2 = ∃ (x : ℤ) (y : ℤ), a * x + b * y = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_int_coprime holTheoryInst

theorem hol_INT_DIVMOD_UNIQ : 
  ∀ (m n q r : ℤ), m = q * n + r ∧ ↑(0 : ℕ) ≤ r ∧ r < |n| → m / n = q ∧ m % n = r := @HolLightLean.hol_opam.thm_INT_DIVMOD_UNIQ holTheoryInst

theorem hol_INT_DIV_UNIQ : 
  ∀ (m n q r : ℤ), m = q * n + r ∧ ↑(0 : ℕ) ≤ r ∧ r < |n| → m / n = q := @HolLightLean.hol_opam.thm_INT_DIV_UNIQ holTheoryInst

theorem hol_INT_REM_UNIQ : 
  ∀ (m n q r : ℤ), m = q * n + r ∧ ↑(0 : ℕ) ≤ r ∧ r < |n| → m % n = r := @HolLightLean.hol_opam.thm_INT_REM_UNIQ holTheoryInst

theorem hol_INT_REM_LT : 
  ∀ (m n : ℤ), (¬n = ↑(0 : ℕ) → ↑(0 : ℕ) ≤ m) ∧ m < n → m % n = m := @HolLightLean.hol_opam.thm_INT_REM_LT holTheoryInst

theorem hol_INT_DIV_LT : 
  ∀ (m n : ℤ), (¬n = ↑(0 : ℕ) → ↑(0 : ℕ) ≤ m) ∧ m < n → m / n = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_DIV_LT holTheoryInst

theorem hol_INT_REM_RNEG : 
  ∀ (m n : ℤ), m % -n = m % n := @HolLightLean.hol_opam.thm_INT_REM_RNEG holTheoryInst

theorem hol_INT_DIV_RNEG : 
  ∀ (m n : ℤ), m / -n = -(m / n) := @HolLightLean.hol_opam.thm_INT_DIV_RNEG holTheoryInst

theorem hol_INT_REM_RABS : 
  ∀ (x y : ℤ), x % |y| = x % y := @HolLightLean.hol_opam.thm_INT_REM_RABS holTheoryInst

theorem hol_INT_REM_REM : 
  ∀ (m n : ℤ), m % n % n = m % n := @HolLightLean.hol_opam.thm_INT_REM_REM holTheoryInst

theorem hol_INT_REM_EQ : 
  ∀ (m n p : ℤ), (m % p = n % p) = (fun (x y : ℤ) ↦ p ∣ x - y) m n := @HolLightLean.hol_opam.thm_INT_REM_EQ holTheoryInst

theorem hol_INT_REM_ZERO : 
  ∀ (n : ℤ), ↑(0 : ℕ) % n = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_REM_ZERO holTheoryInst

theorem hol_INT_DIV_ZERO : 
  ∀ (n : ℤ), ↑(0 : ℕ) / n = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_DIV_ZERO holTheoryInst

theorem hol_INT_REM_EQ_0 : 
  ∀ (m n : ℤ), (m % n = ↑(0 : ℕ)) = (n ∣ m) := @HolLightLean.hol_opam.thm_INT_REM_EQ_0 holTheoryInst

theorem hol_INT_MUL_DIV_EQ : 
  (∀ (m n : ℤ), (n * (m / n) = m) = (n ∣ m)) ∧ ∀ (m n : ℤ), (m / n * n = m) = (n ∣ m) := @HolLightLean.hol_opam.thm_INT_MUL_DIV_EQ holTheoryInst

theorem hol_INT_CONG_LREM : 
  ∀ (x y n : ℤ), Eq (α := Prop) ((fun (x y : ℤ) ↦ n ∣ x - y) (x % n) y) ((fun (x y : ℤ) ↦ n ∣ x - y) x y) := @HolLightLean.hol_opam.thm_INT_CONG_LREM holTheoryInst

theorem hol_INT_CONG_RREM : 
  ∀ (x y n : ℤ), Eq (α := Prop) ((fun (x y : ℤ) ↦ n ∣ x - y) x (y % n)) ((fun (x y : ℤ) ↦ n ∣ x - y) x y) := @HolLightLean.hol_opam.thm_INT_CONG_RREM holTheoryInst

theorem hol_INT_REM_MOD_SELF : 
  ∀ (m n : ℤ), (fun (x y : ℤ) ↦ n ∣ x - y) (m % n) m := @HolLightLean.hol_opam.thm_INT_REM_MOD_SELF holTheoryInst

theorem hol_INT_REM_REM_MUL : 
  (∀ (m n p : ℤ), m % (n * p) % n = m % n) ∧ ∀ (m n p : ℤ), m % (n * p) % p = m % p := @HolLightLean.hol_opam.thm_INT_REM_REM_MUL holTheoryInst

theorem hol_INT_CONG_SOLVE_BOUNDS : 
  ∀ (a n : ℤ), ¬n = ↑(0 : ℕ) → ∃ (x : ℤ), ↑(0 : ℕ) ≤ x ∧ x < |n| ∧ (fun (x y : ℤ) ↦ n ∣ x - y) x a := @HolLightLean.hol_opam.thm_INT_CONG_SOLVE_BOUNDS holTheoryInst

theorem hol_INT_NEG_REM : 
  ∀ (n p : ℤ), -(n % p) % p = -n % p := @HolLightLean.hol_opam.thm_INT_NEG_REM holTheoryInst

theorem hol_INT_ADD_REM : 
  ∀ (m n p : ℤ), (m % p + n % p) % p = (m + n) % p := @HolLightLean.hol_opam.thm_INT_ADD_REM holTheoryInst

theorem hol_INT_SUB_REM : 
  ∀ (m n p : ℤ), (m % p - n % p) % p = (m - n) % p := @HolLightLean.hol_opam.thm_INT_SUB_REM holTheoryInst

theorem hol_INT_MUL_REM : 
  ∀ (m n p : ℤ), m % p * (n % p) % p = m * n % p := @HolLightLean.hol_opam.thm_INT_MUL_REM holTheoryInst

theorem hol_INT_POW_REM : 
  ∀ (m : ℤ) (n : ℕ) (p : ℤ), (m % p) ^ n % p = m ^ n % p := @HolLightLean.hol_opam.thm_INT_POW_REM holTheoryInst

theorem hol_INT_OF_NUM_REM : 
  ∀ (m n : ℕ), HMod.hMod (α := ℤ) ↑m ↑n = ↑(m % n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_REM holTheoryInst

theorem hol_INT_OF_NUM_DIV : 
  ∀ (m n : ℕ), HDiv.hDiv (α := ℤ) ↑m ↑n = ↑(m / n) := @HolLightLean.hol_opam.thm_INT_OF_NUM_DIV holTheoryInst

theorem hol_INT_REM_REFL : 
  ∀ (n : ℤ), n % n = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_REM_REFL holTheoryInst

theorem hol_INT_DIV_REFL : 
  ∀ (n : ℤ), n / n = if n = ↑(0 : ℕ) then ↑(0 : ℕ) else ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_DIV_REFL holTheoryInst

theorem hol_INT_REM_LNEG : 
  ∀ (m n : ℤ), -m % n = if m % n = ↑(0 : ℕ) then ↑(0 : ℕ) else |n| - m % n := @HolLightLean.hol_opam.thm_INT_REM_LNEG holTheoryInst

theorem hol_INT_DIV_LNEG : 
  ∀ (m n : ℤ), -m / n = if m % n = ↑(0 : ℕ) then -(m / n) else -(m / n) - n.sign := @HolLightLean.hol_opam.thm_INT_DIV_LNEG holTheoryInst

theorem hol_INT_DIV_NEG2 : 
  ∀ (m n : ℤ), -m / -n = if m % n = ↑(0 : ℕ) then m / n else m / n + n.sign := @HolLightLean.hol_opam.thm_INT_DIV_NEG2 holTheoryInst

theorem hol_INT_REM_NEG2 : 
  ∀ (m n : ℤ), -m % -n = if m % n = ↑(0 : ℕ) then ↑(0 : ℕ) else |n| - m % n := @HolLightLean.hol_opam.thm_INT_REM_NEG2 holTheoryInst

theorem hol_INT_REM_1 : 
  ∀ (n : ℤ), n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_REM_1 holTheoryInst

theorem hol_INT_DIV_1 : 
  ∀ (n : ℤ), n / ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = n := @HolLightLean.hol_opam.thm_INT_DIV_1 holTheoryInst

theorem hol_INT_REM_MUL : 
  (∀ (m n : ℤ), m * n % n = ↑(0 : ℕ)) ∧ ∀ (m n : ℤ), m * n % m = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_INT_REM_MUL holTheoryInst

theorem hol_INT_DIV_MUL : 
  (∀ (m n : ℤ), ¬n = ↑(0 : ℕ) → m * n / n = m) ∧ ∀ (m n : ℤ), ¬m = ↑(0 : ℕ) → m * n / m = n := @HolLightLean.hol_opam.thm_INT_DIV_MUL holTheoryInst

theorem hol_INT_DIV_LT_EQ : 
  ∀ (a b c : ℤ), ↑(0 : ℕ) < a → (b / a < c) = (b < a * c) := @HolLightLean.hol_opam.thm_INT_DIV_LT_EQ holTheoryInst

theorem hol_INT_LE_DIV_EQ : 
  ∀ (a b c : ℤ), ↑(0 : ℕ) < a → (c ≤ b / a) = (a * c ≤ b) := @HolLightLean.hol_opam.thm_INT_LE_DIV_EQ holTheoryInst

theorem hol_INT_DIV_LE_EQ : 
  ∀ (a b c : ℤ), ↑(0 : ℕ) < a → (b / a ≤ c) = (b < a * (c + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_INT_DIV_LE_EQ holTheoryInst

theorem hol_INT_LT_DIV_EQ : 
  ∀ (a b c : ℤ), ↑(0 : ℕ) < a → (c < b / a) = (a * (c + ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ≤ b) := @HolLightLean.hol_opam.thm_INT_LT_DIV_EQ holTheoryInst

theorem hol_INT_DIV_LE : 
  ∀ (m n : ℤ), |m / n| ≤ |m| := @HolLightLean.hol_opam.thm_INT_DIV_LE holTheoryInst

theorem hol_INT_REM_MUL_REM : 
  ∀ (m n p : ℤ), ↑(0 : ℕ) ≤ n → m % (n * p) = n * (m / n % p) + m % n := @HolLightLean.hol_opam.thm_INT_REM_MUL_REM holTheoryInst

theorem hol_INT_DIV_DIV : 
  ∀ (m n p : ℤ), ↑(0 : ℕ) ≤ n → m / n / p = m / (n * p) := @HolLightLean.hol_opam.thm_INT_DIV_DIV holTheoryInst

theorem hol_INT_DIV_EQ_0 : 
  ∀ (m n : ℤ), (m / n = ↑(0 : ℕ)) = (n = ↑(0 : ℕ) ∨ ↑(0 : ℕ) ≤ m ∧ m < |n|) := @HolLightLean.hol_opam.thm_INT_DIV_EQ_0 holTheoryInst

theorem hol_INT_REM_EQ_SELF : 
  ∀ (m n : ℤ), (m % n = m) = (n = ↑(0 : ℕ) ∨ ↑(0 : ℕ) ≤ m ∧ m < |n|) := @HolLightLean.hol_opam.thm_INT_REM_EQ_SELF holTheoryInst

theorem hol_INT_REM_UNIQUE : 
  ∀ (m n p : ℤ), (m % n = p) = ((n = ↑(0 : ℕ) ∧ m = p ∨ ↑(0 : ℕ) ≤ p ∧ p < |n|) ∧ (fun (x y : ℤ) ↦ n ∣ x - y) m p) := @HolLightLean.hol_opam.thm_INT_REM_UNIQUE holTheoryInst

theorem hol_INT_DIV_REM : 
  ∀ (m n p : ℤ), ↑(0 : ℕ) ≤ n → m / n % p = m % (n * p) / n := @HolLightLean.hol_opam.thm_INT_DIV_REM holTheoryInst

theorem hol_INT_REM_REM_LE : 
  ∀ (m n p : ℤ), ¬n = ↑(0 : ℕ) ∧ |n| ≤ |p| → m % n % p = m % n := @HolLightLean.hol_opam.thm_INT_REM_REM_LE holTheoryInst

theorem hol_INT_LE_DIV : 
  ∀ (m n : ℤ), ↑(0 : ℕ) ≤ m ∧ ↑(0 : ℕ) ≤ n → ↑(0 : ℕ) ≤ m / n := @HolLightLean.hol_opam.thm_INT_LE_DIV holTheoryInst

theorem hol_INT_LT_DIV : 
  ∀ (m n : ℤ), ↑(0 : ℕ) < n ∧ n ≤ m → ↑(0 : ℕ) < m / n := @HolLightLean.hol_opam.thm_INT_LT_DIV holTheoryInst

theorem hol_INT_REM_LE_EQ : 
  ∀ (m n : ℤ), (m % n ≤ m) = (n = ↑(0 : ℕ) ∨ ↑(0 : ℕ) ≤ m) := @HolLightLean.hol_opam.thm_INT_REM_LE_EQ holTheoryInst

theorem hol_INT_REM_LE : 
  ∀ (m n p : ℤ), (n = ↑(0 : ℕ) ∨ ↑(0 : ℕ) ≤ m) ∧ m ≤ p → m % n ≤ p := @HolLightLean.hol_opam.thm_INT_REM_LE holTheoryInst

theorem hol_INT_REM_MUL_ADD : 
  (∀ (m n p : ℤ), (m * n + p) % n = p % n) ∧
    (∀ (m n p : ℤ), (n * m + p) % n = p % n) ∧
      (∀ (m n p : ℤ), (p + m * n) % n = p % n) ∧ ∀ (m n p : ℤ), (p + n * m) % n = p % n := @HolLightLean.hol_opam.thm_INT_REM_MUL_ADD holTheoryInst

theorem hol_INT_DIV_MUL_ADD : 
  (∀ (m n p : ℤ), ¬n = ↑(0 : ℕ) → (m * n + p) / n = m + p / n) ∧
    (∀ (m n p : ℤ), ¬n = ↑(0 : ℕ) → (n * m + p) / n = m + p / n) ∧
      (∀ (m n p : ℤ), ¬n = ↑(0 : ℕ) → (p + m * n) / n = p / n + m) ∧
        ∀ (m n p : ℤ), ¬n = ↑(0 : ℕ) → (p + n * m) / n = p / n + m := @HolLightLean.hol_opam.thm_INT_DIV_MUL_ADD holTheoryInst

theorem hol_INT_CONG_DIV2 : 
  ∀ (a b m n : ℤ), m * n ∣ a - b → (fun (x y : ℤ) ↦ n ∣ x - y) (a / m) (b / m) := @HolLightLean.hol_opam.thm_INT_CONG_DIV2 holTheoryInst

theorem hol_INT_REM_2_CASES : 
  ∀ (n : ℤ),
    n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑(0 : ℕ) ∨
      n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_REM_2_CASES holTheoryInst

theorem hol_NOT_INT_REM_2 : 
  (∀ (n : ℤ),
      (¬n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑(0 : ℕ)) =
        (n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) ∧
    ∀ (n : ℤ),
      (¬n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        (n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_NOT_INT_REM_2 holTheoryInst

theorem hol_INT_REM_2_DIVIDES : 
  (∀ (n : ℤ),
      (n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑(0 : ℕ)) =
        (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n)) ∧
    ∀ (n : ℤ),
      (n % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
        ¬↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n := @HolLightLean.hol_opam.thm_INT_REM_2_DIVIDES holTheoryInst

theorem hol_INT_REM_2_EXPAND : 
  ∀ (x : ℤ),
    x % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      if ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ x then ↑(0 : ℕ)
      else ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_INT_REM_2_EXPAND holTheoryInst

theorem hol_INT_REM_2_NEG : 
  ∀ (x : ℤ),
    -x % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) =
      x % ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_INT_REM_2_NEG holTheoryInst

theorem hol_INT_DIVIDES_DIV_SELF : 
  ∀ (n d : ℤ), d ∣ n → n / d ∣ n := @HolLightLean.hol_opam.thm_INT_DIVIDES_DIV_SELF holTheoryInst

theorem hol_INT_DIV_BY_DIV : 
  ∀ (m n : ℤ), ¬n = ↑(0 : ℕ) ∧ m ∣ n → n / (n / m) = m := @HolLightLean.hol_opam.thm_INT_DIV_BY_DIV holTheoryInst

theorem hol_INT_DIVIDES_DIV_DIVIDES : 
  ∀ (n d e : ℤ), d ∣ n ∧ (n = ↑(0 : ℕ) → e = ↑(0 : ℕ)) → (n / d ∣ e) = (n ∣ d * e) := @HolLightLean.hol_opam.thm_INT_DIVIDES_DIV_DIVIDES holTheoryInst

theorem hol_INT_DIVIDES_DIVIDES_DIV : 
  ∀ (n d e : ℤ), d ∣ n → (e ∣ n / d) = (d * e ∣ n) := @HolLightLean.hol_opam.thm_INT_DIVIDES_DIVIDES_DIV holTheoryInst

theorem hol_INT_DIVIDES_DIVIDES_DIV_EQ : 
  ∀ (n d e : ℤ), (d ∣ n ∧ e ∣ n / d) = (d * e ∣ n) := @HolLightLean.hol_opam.thm_INT_DIVIDES_DIVIDES_DIV_EQ holTheoryInst

theorem hol_INT_2_DIVIDES_ADD : 
  ∀ (m n : ℤ),
    (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ m + n) =
      ((↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ m) =
        (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n)) := @HolLightLean.hol_opam.thm_INT_2_DIVIDES_ADD holTheoryInst

theorem hol_INT_2_DIVIDES_SUB : 
  ∀ (m n : ℤ),
    (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ m - n) =
      ((↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ m) =
        (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n)) := @HolLightLean.hol_opam.thm_INT_2_DIVIDES_SUB holTheoryInst

theorem hol_INT_2_DIVIDES_MUL : 
  ∀ (m n : ℤ),
    (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ m * n) =
      (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ m ∨
        ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n) := @HolLightLean.hol_opam.thm_INT_2_DIVIDES_MUL holTheoryInst

theorem hol_INT_2_DIVIDES_POW : 
  ∀ (n : ℤ) (k : ℕ),
    (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n ^ k) =
      (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∣ n ∧ ¬k = (0 : ℕ)) := @HolLightLean.hol_opam.thm_INT_2_DIVIDES_POW holTheoryInst

theorem hol_WF_INT_MEASURE : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (m : A → ℤ),
    ((∀ (x : A), ↑(0 : ℕ) ≤ m x) ∧ ∀ (x : A), (∀ (y : A), m y < m x → P y) → P x) → ∀ (x : A), P x := @HolLightLean.hol_opam.thm_WF_INT_MEASURE holTheoryInst

theorem hol_WF_INT_MEASURE_2 : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop) (m : A → B → ℤ),
    ((∀ (x : A) (y : B), ↑(0 : ℕ) ≤ m x y) ∧
        ∀ (x : A) (y : B), (∀ (x' : A) (y' : B), m x' y' < m x y → P x' y') → P x y) →
      ∀ (x : A) (y : B), P x y := @HolLightLean.hol_opam.thm_WF_INT_MEASURE_2 holTheoryInst

theorem hol_INT_GCD_EXISTS : 
  ∀ (a b : ℤ), ∃ (d : ℤ), d ∣ a ∧ d ∣ b ∧ ∃ (x : ℤ) (y : ℤ), d = a * x + b * y := @HolLightLean.hol_opam.thm_INT_GCD_EXISTS holTheoryInst

theorem hol_INT_GCD_EXISTS_POS : 
  ∀ (a b : ℤ), ∃ (d : ℤ), ↑(0 : ℕ) ≤ d ∧ d ∣ a ∧ d ∣ b ∧ ∃ (x : ℤ) (y : ℤ), d = a * x + b * y := @HolLightLean.hol_opam.thm_INT_GCD_EXISTS_POS holTheoryInst

theorem hol_int_lcm : 
  ∀ (m n : ℤ), ↑((m, n).1.lcm (m, n).2) = if m * n = ↑(0 : ℕ) then ↑(0 : ℕ) else |m * n| / ↑((m, n).1.gcd (m, n).2) := @HolLightLean.hol_opam.thm_int_lcm holTheoryInst

theorem hol_INT_DIVIDES_LABS : 
  ∀ (d n : ℤ), (|d| ∣ n) = (d ∣ n) := @HolLightLean.hol_opam.thm_INT_DIVIDES_LABS holTheoryInst

theorem hol_INT_DIVIDES_RABS : 
  ∀ (d n : ℤ), (d ∣ |n|) = (d ∣ n) := @HolLightLean.hol_opam.thm_INT_DIVIDES_RABS holTheoryInst

theorem hol_INT_DIVIDES_ABS : 
  (∀ (d n : ℤ), (|d| ∣ n) = (d ∣ n)) ∧ ∀ (d n : ℤ), (d ∣ |n|) = (d ∣ n) := @HolLightLean.hol_opam.thm_INT_DIVIDES_ABS holTheoryInst

theorem hol_INT_LCM_POS : 
  ∀ (m n : ℤ), LE.le (α := ℤ) ↑(0 : ℕ) ↑((m, n).1.lcm (m, n).2) := @HolLightLean.hol_opam.thm_INT_LCM_POS holTheoryInst

theorem hol_INT_MUL_GCD_LCM : 
  ∀ (m n : ℤ), HMul.hMul (α := ℤ) ↑((m, n).1.gcd (m, n).2) ↑((m, n).1.lcm (m, n).2) = |m * n| := @HolLightLean.hol_opam.thm_INT_MUL_GCD_LCM holTheoryInst

theorem hol_INT_MUL_LCM_GCD : 
  ∀ (m n : ℤ), HMul.hMul (α := ℤ) ↑((m, n).1.lcm (m, n).2) ↑((m, n).1.gcd (m, n).2) = |m * n| := @HolLightLean.hol_opam.thm_INT_MUL_LCM_GCD holTheoryInst

theorem hol_INT_DIVIDES_LCM_GCD : 
  ∀ (m n d : ℤ), (d ∣ ↑((m, n).1.lcm (m, n).2)) = (d * ↑((m, n).1.gcd (m, n).2) ∣ m * n) := @HolLightLean.hol_opam.thm_INT_DIVIDES_LCM_GCD holTheoryInst

theorem hol_INT_LCM_DIVIDES : 
  ∀ (m n d : ℤ), (↑((m, n).1.lcm (m, n).2) ∣ d) = (m ∣ d ∧ n ∣ d) := @HolLightLean.hol_opam.thm_INT_LCM_DIVIDES holTheoryInst

theorem hol_INT_LCM : 
  ∀ (m n : ℤ),
    m ∣ ↑((m, n).1.lcm (m, n).2) ∧
      n ∣ ↑((m, n).1.lcm (m, n).2) ∧ ∀ (d : ℤ), m ∣ d ∧ n ∣ d → ↑((m, n).1.lcm (m, n).2) ∣ d := @HolLightLean.hol_opam.thm_INT_LCM holTheoryInst

theorem hol_num_of_int : 
  ∀ (x : ℤ), num_of_int x = Classical.epsilon fun (n : ℕ) ↦ ↑n = x := @HolLightLean.hol_opam.thm_num_of_int holTheoryInst

theorem hol_NUM_OF_INT_OF_NUM : 
  ∀ (n : ℕ), num_of_int ↑n = n := @HolLightLean.hol_opam.thm_NUM_OF_INT_OF_NUM holTheoryInst

theorem hol_INT_OF_NUM_OF_INT : 
  ∀ (x : ℤ), ↑(0 : ℕ) ≤ x → ↑(num_of_int x) = x := @HolLightLean.hol_opam.thm_INT_OF_NUM_OF_INT holTheoryInst

theorem hol_NUM_OF_INT : 
  ∀ (x : ℤ), (↑(0 : ℕ) ≤ x) = (↑(num_of_int x) = x) := @HolLightLean.hol_opam.thm_NUM_OF_INT holTheoryInst

theorem hol_NUM_OF_INT_ADD : 
  ∀ (x y : ℤ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → num_of_int (x + y) = num_of_int x + num_of_int y := @HolLightLean.hol_opam.thm_NUM_OF_INT_ADD holTheoryInst

theorem hol_NUM_OF_INT_MUL : 
  ∀ (x y : ℤ), ↑(0 : ℕ) ≤ x ∧ ↑(0 : ℕ) ≤ y → num_of_int (x * y) = num_of_int x * num_of_int y := @HolLightLean.hol_opam.thm_NUM_OF_INT_MUL holTheoryInst

theorem hol_NUM_OF_INT_POW : 
  ∀ (x : ℤ) (n : ℕ), ↑(0 : ℕ) ≤ x → num_of_int (x ^ n) = num_of_int x ^ n := @HolLightLean.hol_opam.thm_NUM_OF_INT_POW holTheoryInst

theorem hol_num_divides : 
  ∀ (a b : ℕ), num_divides a b = Dvd.dvd (α := ℤ) ↑a ↑b := @HolLightLean.hol_opam.thm_num_divides holTheoryInst

theorem hol_num_mod : 
  ∀ (n x y : ℕ), num_mod n x y = (↑n ∣ HSub.hSub (α := ℤ) ↑x ↑y) := @HolLightLean.hol_opam.thm_num_mod holTheoryInst

theorem hol_num_congruent : 
  ∀ (x y n : ℕ), num_mod n x y = (fun (x y : ℤ) ↦ ↑n ∣ x - y) ↑x ↑y := @HolLightLean.hol_opam.thm_num_congruent holTheoryInst

theorem hol_num_coprime : 
  ∀ (a b : ℕ), num_coprime (a, b) = IsCoprime (R := ℤ) (↑a, ↑b).1 (↑a, ↑b).2 := @HolLightLean.hol_opam.thm_num_coprime holTheoryInst

theorem hol_num_gcd : 
  ∀ (a b : ℕ), num_gcd (a, b) = num_of_int ↑(Int.gcd (↑a, ↑b).1 (↑a, ↑b).2) := @HolLightLean.hol_opam.thm_num_gcd holTheoryInst

theorem hol_num_lcm : 
  ∀ (a b : ℕ), num_lcm (a, b) = num_of_int ↑(Int.lcm (↑a, ↑b).1 (↑a, ↑b).2) := @HolLightLean.hol_opam.thm_num_lcm holTheoryInst

theorem hol_BINARY_INDUCT : 
  ∀ (P : Set ℕ),
    (P (0 : ℕ) ∧
        ∀ (n : ℕ),
          P n →
            P (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n) ∧
              P (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) →
      ∀ (n : ℕ), P n := @HolLightLean.hol_opam.thm_BINARY_INDUCT holTheoryInst

theorem hol_NUM_CASES_BINARY : 
  ∀ (P : Set ℕ),
    (∀ (n : ℕ), P n) =
      ((∀ (n : ℕ), P (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n)) ∧
        ∀ (n : ℕ),
          P (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_NUM_CASES_BINARY holTheoryInst

theorem hol_num_WF_DOWN : 
  ∀ (P : Set ℕ) (m : ℕ), ((∀ (n : ℕ), m ≤ n → P n) ∧ ∀ (n : ℕ), (n < m ∧ ∀ (p : ℕ), n < p → P p) → P n) → ∀ (n : ℕ), P n := @HolLightLean.hol_opam.thm_num_WF_DOWN holTheoryInst

theorem hol_INT_REM_REM_POW_MIN : 
  ∀ (x p : ℤ) (m n : ℕ), x % p ^ m % p ^ n = x % p ^ min m n := @HolLightLean.hol_opam.thm_INT_REM_REM_POW_MIN holTheoryInst

theorem hol_NUM_GCD : 
  ∀ (a b : ℕ), Eq (α := ℤ) ↑(num_gcd (a, b)) ↑(Int.gcd (↑a, ↑b).1 (↑a, ↑b).2) := @HolLightLean.hol_opam.thm_NUM_GCD holTheoryInst

theorem hol_NUM_LCM : 
  ∀ (a b : ℕ), Eq (α := ℤ) ↑(num_lcm (a, b)) ↑(Int.lcm (↑a, ↑b).1 (↑a, ↑b).2) := @HolLightLean.hol_opam.thm_NUM_LCM holTheoryInst

theorem hol_CONG : 
  ∀ (x y n : ℕ), num_mod n x y = (x % n = y % n) := @HolLightLean.hol_opam.thm_CONG holTheoryInst

theorem hol_CONG_LMOD : 
  ∀ (x y n : ℕ), num_mod n (x % n) y = num_mod n x y := @HolLightLean.hol_opam.thm_CONG_LMOD holTheoryInst

theorem hol_CONG_RMOD : 
  ∀ (x y n : ℕ), num_mod n x (y % n) = num_mod n x y := @HolLightLean.hol_opam.thm_CONG_RMOD holTheoryInst

theorem hol_CONG_DIV2 : 
  ∀ (a b m n : ℕ), num_mod (m * n) a b → num_mod n (a / m) (b / m) := @HolLightLean.hol_opam.thm_CONG_DIV2 holTheoryInst

theorem hol_divides : 
  ∀ (b a : ℕ), num_divides a b = ∃ (x : ℕ), b = a * x := @HolLightLean.hol_opam.thm_divides holTheoryInst

theorem hol_DIVIDES_LE : 
  ∀ (m n : ℕ), num_divides m n → m ≤ n ∨ n = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIVIDES_LE holTheoryInst

theorem hol_DIVIDES_LE_STRONG : 
  ∀ (m n : ℕ), num_divides m n → (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ m ∧ m ≤ n ∨ n = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIVIDES_LE_STRONG holTheoryInst

theorem hol_DIVIDES_LE_IMP : 
  ∀ (m n : ℕ), num_divides m n ∧ (n = (0 : ℕ) → m = (0 : ℕ)) → m ≤ n := @HolLightLean.hol_opam.thm_DIVIDES_LE_IMP holTheoryInst

theorem hol_PROPERLY_DIVIDES_LE_IMP : 
  ∀ (m n : ℕ),
    num_divides m n ∧ ¬n = (0 : ℕ) ∧ ¬m = n → ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m ≤ n := @HolLightLean.hol_opam.thm_PROPERLY_DIVIDES_LE_IMP holTheoryInst

theorem hol_DIVIDES_ANTISYM : 
  ∀ (m n : ℕ), (num_divides m n ∧ num_divides n m) = (m = n) := @HolLightLean.hol_opam.thm_DIVIDES_ANTISYM holTheoryInst

theorem hol_DIVIDES_ONE : 
  ∀ (n : ℕ), num_divides n ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = (n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_DIVIDES_ONE holTheoryInst

theorem hol_DIV_ADD : 
  ∀ (d a b : ℕ), num_divides d a ∨ num_divides d b → (a + b) / d = a / d + b / d := @HolLightLean.hol_opam.thm_DIV_ADD holTheoryInst

theorem hol_DIVIDES_MOD : 
  ∀ (m n : ℕ), num_divides m n = (n % m = (0 : ℕ)) := @HolLightLean.hol_opam.thm_DIVIDES_MOD holTheoryInst

theorem hol_DIVIDES_DIV_MULT : 
  ∀ (m n : ℕ), num_divides m n = (n / m * m = n) := @HolLightLean.hol_opam.thm_DIVIDES_DIV_MULT holTheoryInst

theorem hol_DIV_BY_DIV : 
  ∀ (m n : ℕ), ¬n = (0 : ℕ) ∧ num_divides m n → n / (n / m) = m := @HolLightLean.hol_opam.thm_DIV_BY_DIV holTheoryInst

theorem hol_DIVIDES_DIV_DIVIDES : 
  ∀ (n d e : ℕ), num_divides d n ∧ (n = (0 : ℕ) → e = (0 : ℕ)) → num_divides (n / d) e = num_divides n (d * e) := @HolLightLean.hol_opam.thm_DIVIDES_DIV_DIVIDES holTheoryInst

theorem hol_DIVIDES_DIV_SELF : 
  ∀ (n d : ℕ), num_divides d n → num_divides (n / d) n := @HolLightLean.hol_opam.thm_DIVIDES_DIV_SELF holTheoryInst

theorem hol_DIVIDES_DIVIDES_DIV : 
  ∀ (n d e : ℕ), num_divides d n → num_divides e (n / d) = num_divides (d * e) n := @HolLightLean.hol_opam.thm_DIVIDES_DIVIDES_DIV holTheoryInst

theorem hol_DIVIDES_DIVIDES_DIV_EQ : 
  ∀ (n d e : ℕ), (num_divides d n ∧ num_divides e (n / d)) = num_divides (d * e) n := @HolLightLean.hol_opam.thm_DIVIDES_DIVIDES_DIV_EQ holTheoryInst

theorem hol_DIVIDES_DIVIDES_DIV_IMP : 
  ∀ (n d e : ℕ), num_divides (d * e) n → num_divides e (n / d) := @HolLightLean.hol_opam.thm_DIVIDES_DIVIDES_DIV_IMP holTheoryInst

theorem hol_MULT_DIV : 
  (∀ (m n p : ℕ), num_divides p m → m * n / p = m / p * n) ∧ ∀ (m n p : ℕ), num_divides p n → m * n / p = m * (n / p) := @HolLightLean.hol_opam.thm_MULT_DIV holTheoryInst

theorem hol_COPRIME_LMOD : 
  ∀ (a n : ℕ), num_coprime (a % n, n) = num_coprime (a, n) := @HolLightLean.hol_opam.thm_COPRIME_LMOD holTheoryInst

theorem hol_COPRIME_RMOD : 
  ∀ (a n : ℕ), num_coprime (n, a % n) = num_coprime (n, a) := @HolLightLean.hol_opam.thm_COPRIME_RMOD holTheoryInst

theorem hol_INT_CONG_NUM_EXISTS : 
  ∀ (x y : ℤ), (y = ↑(0 : ℕ) → ↑(0 : ℕ) ≤ x) → ∃ (n : ℕ), (fun (x y_1 : ℤ) ↦ y ∣ x - y_1) (↑n) x := @HolLightLean.hol_opam.thm_INT_CONG_NUM_EXISTS holTheoryInst

theorem hol_GCD : 
  ∀ (a b : ℕ),
    (num_divides (num_gcd (a, b)) a ∧ num_divides (num_gcd (a, b)) b) ∧
      ∀ (e : ℕ), num_divides e a ∧ num_divides e b → num_divides e (num_gcd (a, b)) := @HolLightLean.hol_opam.thm_GCD holTheoryInst

theorem hol_coprime : 
  ∀ (a b : ℕ), num_coprime (a, b) = ∀ (d : ℕ), num_divides d a ∧ num_divides d b → d = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_coprime holTheoryInst

theorem hol_prime : 
  ∀ (p : ℕ),
    prime p = (¬p = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∧ ∀ (x : ℕ), num_divides x p → x = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ x = p) := @HolLightLean.hol_opam.thm_prime holTheoryInst

theorem hol_ONE_OR_PRIME : 
  ∀ (p : ℕ),
    (p = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ prime p) = ∀ (n : ℕ), num_divides n p → n = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ n = p := @HolLightLean.hol_opam.thm_ONE_OR_PRIME holTheoryInst

theorem hol_ONE_OR_PRIME_DIVIDES_OR_COPRIME : 
  ∀ (p : ℕ), (p = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ prime p) = ∀ (n : ℕ), num_divides p n ∨ num_coprime (p, n) := @HolLightLean.hol_opam.thm_ONE_OR_PRIME_DIVIDES_OR_COPRIME holTheoryInst

theorem hol_PRIME_COPRIME_EQ_NONDIVISIBLE : 
  ∀ (p : ℕ), prime p = ∀ (n : ℕ), num_coprime (p, n) = ¬num_divides p n := @HolLightLean.hol_opam.thm_PRIME_COPRIME_EQ_NONDIVISIBLE holTheoryInst

theorem hol_ZERO_ONE_OR_PRIME_DIVPROD : 
  ∀ (p a b : ℕ),
    p = (0 : ℕ) ∨ p = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ prime p →
      num_divides p (a * b) = (num_divides p a ∨ num_divides p b) := @HolLightLean.hol_opam.thm_ZERO_ONE_OR_PRIME_DIVPROD holTheoryInst

theorem hol_ZERO_ONE_OR_PRIME : 
  ∀ (p : ℕ),
    (p = (0 : ℕ) ∨ p = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∨ prime p) =
      ∀ (a b : ℕ), num_divides p (a * b) → num_divides p a ∨ num_divides p b := @HolLightLean.hol_opam.thm_ZERO_ONE_OR_PRIME holTheoryInst

theorem hol_real_zpow : 
  ∀ (z : ℝ) (i : ℤ), real_zpow z i = if ↑(0 : ℕ) ≤ i then z ^ num_of_int i else (z ^ num_of_int (-i))⁻¹ := @HolLightLean.hol_opam.thm_real_zpow holTheoryInst

theorem hol_REAL_POW_ZPOW : 
  ∀ (x : ℝ) (n : ℕ), x ^ n = real_zpow x ↑n := @HolLightLean.hol_opam.thm_REAL_POW_ZPOW holTheoryInst

theorem hol_REAL_ZPOW_NUM : 
  ∀ (x : ℝ) (n : ℕ), real_zpow x ↑n = x ^ n := @HolLightLean.hol_opam.thm_REAL_ZPOW_NUM holTheoryInst

theorem hol_REAL_ZPOW_0 : 
  ∀ (x : ℝ), real_zpow x ↑(0 : ℕ) = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_ZPOW_0 holTheoryInst

theorem hol_REAL_ZPOW_1 : 
  ∀ (x : ℝ), real_zpow x ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = x := @HolLightLean.hol_opam.thm_REAL_ZPOW_1 holTheoryInst

theorem hol_REAL_ZPOW_2 : 
  ∀ (x : ℝ), real_zpow x ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x * x := @HolLightLean.hol_opam.thm_REAL_ZPOW_2 holTheoryInst

theorem hol_REAL_ZPOW_ONE : 
  ∀ (n : ℤ), real_zpow (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n = ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_ZPOW_ONE holTheoryInst

theorem hol_REAL_ZPOW_NEG : 
  ∀ (x : ℝ) (n : ℤ), real_zpow x (-n) = (real_zpow x n)⁻¹ := @HolLightLean.hol_opam.thm_REAL_ZPOW_NEG holTheoryInst

theorem hol_REAL_ZPOW_MINUS1 : 
  ∀ (x : ℝ), real_zpow x (-↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) = x⁻¹ := @HolLightLean.hol_opam.thm_REAL_ZPOW_MINUS1 holTheoryInst

theorem hol_REAL_ZPOW_ZERO : 
  ∀ (n : ℤ), real_zpow (↑(0 : ℕ)) n = if n = ↑(0 : ℕ) then ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_ZPOW_ZERO holTheoryInst

theorem hol_REAL_ZPOW_POW : 
  (∀ (x : ℝ) (n : ℕ), real_zpow x ↑n = x ^ n) ∧ ∀ (x : ℝ) (n : ℕ), real_zpow x (-↑n) = (x ^ n)⁻¹ := @HolLightLean.hol_opam.thm_REAL_ZPOW_POW holTheoryInst

theorem hol_REAL_INV_ZPOW : 
  ∀ (x : ℝ) (n : ℤ), (real_zpow x n)⁻¹ = real_zpow x⁻¹ n := @HolLightLean.hol_opam.thm_REAL_INV_ZPOW holTheoryInst

theorem hol_REAL_ZPOW_INV : 
  ∀ (x : ℝ) (n : ℤ), real_zpow x⁻¹ n = (real_zpow x n)⁻¹ := @HolLightLean.hol_opam.thm_REAL_ZPOW_INV holTheoryInst

theorem hol_REAL_ZPOW_ZPOW : 
  ∀ (x : ℝ) (m n : ℤ), real_zpow (real_zpow x m) n = real_zpow x (m * n) := @HolLightLean.hol_opam.thm_REAL_ZPOW_ZPOW holTheoryInst

theorem hol_REAL_ZPOW_MUL : 
  ∀ (x y : ℝ) (n : ℤ), real_zpow (x * y) n = real_zpow x n * real_zpow y n := @HolLightLean.hol_opam.thm_REAL_ZPOW_MUL holTheoryInst

theorem hol_REAL_ZPOW_DIV : 
  ∀ (x y : ℝ) (n : ℤ), real_zpow (x / y) n = real_zpow x n / real_zpow y n := @HolLightLean.hol_opam.thm_REAL_ZPOW_DIV holTheoryInst

theorem hol_REAL_ZPOW_ADD : 
  ∀ (x : ℝ) (m n : ℤ), ¬x = ↑(0 : ℕ) → real_zpow x (m + n) = real_zpow x m * real_zpow x n := @HolLightLean.hol_opam.thm_REAL_ZPOW_ADD holTheoryInst

theorem hol_REAL_ZPOW_SUB : 
  ∀ (x : ℝ) (m n : ℤ), ¬x = ↑(0 : ℕ) → real_zpow x (m - n) = real_zpow x m / real_zpow x n := @HolLightLean.hol_opam.thm_REAL_ZPOW_SUB holTheoryInst

theorem hol_REAL_ZPOW_LE : 
  ∀ (x : ℝ) (n : ℤ), ↑(0 : ℕ) ≤ x → ↑(0 : ℕ) ≤ real_zpow x n := @HolLightLean.hol_opam.thm_REAL_ZPOW_LE holTheoryInst

theorem hol_REAL_ZPOW_LT : 
  ∀ (x : ℝ) (n : ℤ), ↑(0 : ℕ) < x → ↑(0 : ℕ) < real_zpow x n := @HolLightLean.hol_opam.thm_REAL_ZPOW_LT holTheoryInst

theorem hol_REAL_ZPOW_EQ_0 : 
  ∀ (x : ℝ) (n : ℤ), (real_zpow x n = ↑(0 : ℕ)) = (x = ↑(0 : ℕ) ∧ ¬n = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_ZPOW_EQ_0 holTheoryInst

theorem hol_REAL_ABS_ZPOW : 
  ∀ (x : ℝ) (n : ℤ), |real_zpow x n| = real_zpow |x| n := @HolLightLean.hol_opam.thm_REAL_ABS_ZPOW holTheoryInst

theorem hol_REAL_SGN_ZPOW : 
  ∀ (x : ℝ) (n : ℤ), (real_zpow x n).sign = real_zpow x.sign n := @HolLightLean.hol_opam.thm_REAL_SGN_ZPOW holTheoryInst

theorem hol_IN : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (x : A), (x ∈ P) = P x := @HolLightLean.hol_opam.thm_IN holTheoryInst

theorem hol_EXTENSION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s = t) = ∀ (x : A), (x ∈ s) = (x ∈ t) := @HolLightLean.hol_opam.thm_EXTENSION holTheoryInst

theorem hol_GSPEC : 
  ∀ {A : Type} [Nonempty A] (p : Set A), id p = p := @HolLightLean.hol_opam.thm_GSPEC holTheoryInst

theorem hol_SETSPEC : 
  ∀ {A : Type} [Nonempty A] (P : Prop) (v t : A), {x' : A | P ∧ v = x'} t = (P ∧ v = t) := @HolLightLean.hol_opam.thm_SETSPEC holTheoryInst

theorem hol_IN_ELIM_THM : 
  ∀ {A : Type} [Nonempty A],
    (∀ (P : Set (Prop → A → Prop)) (x : A),
        Membership.mem (γ := Set A) (id fun (v : A) ↦ P fun (P : Prop) ↦ {x' : A | P ∧ v = x'}) x =
          P fun (p : Prop) (t : A) ↦ p ∧ x = t) ∧
      (∀ (p : Set A) (x : A),
          Membership.mem (γ := Set A) (id fun (v : A) ↦ ∃ (y : A), {x' : A | p y ∧ v = x'} y) x = p x) ∧
        (∀ (P : Set (Prop → A → Prop)) (x : A),
            id (fun (v : A) ↦ P fun (P : Prop) ↦ {x' : A | P ∧ v = x'}) x = P fun (p : Prop) (t : A) ↦ p ∧ x = t) ∧
          (∀ (p : Set A) (x : A), id (fun (v : A) ↦ ∃ (y : A), {x' : A | p y ∧ v = x'} y) x = p x) ∧
            ∀ (p : Set A) (x : A), Membership.mem (γ := Set A) (fun (y : A) ↦ p y) x = p x := @HolLightLean.hol_opam.thm_IN_ELIM_THM holTheoryInst

theorem hol_EMPTY : 
  ∀ {A : Type} [Nonempty A], Eq (α := Set A) ∅ fun (x : A) ↦ False := @HolLightLean.hol_opam.thm_EMPTY holTheoryInst

theorem hol_INSERT_DEF : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A), insert x s = fun (y : A) ↦ y ∈ s ∨ y = x := @HolLightLean.hol_opam.thm_INSERT_DEF holTheoryInst

theorem hol_UNIV : 
  ∀ {A : Type} [Nonempty A], Eq (α := Set A) Set.univ fun (x : A) ↦ True := @HolLightLean.hol_opam.thm_UNIV holTheoryInst

theorem hol_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A),
    s ∪ t = id fun (GEN_PVAR_0 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∨ x ∈ t) ∧ GEN_PVAR_0 = x'} x := @HolLightLean.hol_opam.thm_UNION holTheoryInst

theorem hol_UNIONS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)),
    ⋃₀ s = id fun (GEN_PVAR_1 : A) ↦ ∃ (x : A), {x' : A | (∃ u ∈ s, x ∈ u) ∧ GEN_PVAR_1 = x'} x := @HolLightLean.hol_opam.thm_UNIONS holTheoryInst

theorem hol_INTER : 
  ∀ {A : Type} [Nonempty A] (s t : Set A),
    s ∩ t = id fun (GEN_PVAR_2 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ x ∈ t) ∧ GEN_PVAR_2 = x'} x := @HolLightLean.hol_opam.thm_INTER holTheoryInst

theorem hol_INTERS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)),
    ⋂₀ s = id fun (GEN_PVAR_3 : A) ↦ ∃ (x : A), {x' : A | (∀ u ∈ s, x ∈ u) ∧ GEN_PVAR_3 = x'} x := @HolLightLean.hol_opam.thm_INTERS holTheoryInst

theorem hol_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A),
    s \ t = id fun (GEN_PVAR_4 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ x ∉ t) ∧ GEN_PVAR_4 = x'} x := @HolLightLean.hol_opam.thm_DIFF holTheoryInst

theorem hol_INSERT : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A),
    insert x s = id fun (GEN_PVAR_5 : A) ↦ ∃ (y : A), {x' : A | (y ∈ s ∨ y = x) ∧ GEN_PVAR_5 = x'} y := @HolLightLean.hol_opam.thm_INSERT holTheoryInst

theorem hol_DELETE : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A),
    s \ {x} = id fun (GEN_PVAR_6 : A) ↦ ∃ (y : A), {x' : A | (y ∈ s ∧ ¬y = x) ∧ GEN_PVAR_6 = x'} y := @HolLightLean.hol_opam.thm_DELETE holTheoryInst

theorem hol_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊆ t) = ∀ x ∈ s, x ∈ t := @HolLightLean.hol_opam.thm_SUBSET holTheoryInst

theorem hol_PSUBSET : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊂ t) = (s ⊆ t ∧ ¬s = t) := @HolLightLean.hol_opam.thm_PSUBSET holTheoryInst

theorem hol_DISJOINT : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), Disjoint s t = (s ∩ t = ∅) := @HolLightLean.hol_opam.thm_DISJOINT holTheoryInst

theorem hol_SING : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (∃ (a : A), s = {a}) = ∃ (x : A), s = insert x ∅ := @HolLightLean.hol_opam.thm_SING holTheoryInst

theorem hol_FINITE_RULES : 
  ∀ {A : Type} [Nonempty A], Set.Finite (α := A) ∅ ∧ ∀ (x : A) (s : Set A), s.Finite → (insert x s).Finite := @HolLightLean.hol_opam.thm_FINITE_RULES holTheoryInst

theorem hol_FINITE_CASES : 
  ∀ {A : Type} [Nonempty A] (a : Set A), a.Finite = (a = ∅ ∨ ∃ (x : A) (s : Set A), a = insert x s ∧ s.Finite) := @HolLightLean.hol_opam.thm_FINITE_CASES holTheoryInst

theorem hol_FINITE_INDUCT : 
  ∀ {A : Type} [Nonempty A] (FINITE' : Set (Set A)),
    (FINITE' ∅ ∧ ∀ (x : A) (s : Set A), FINITE' s → FINITE' (insert x s)) → ∀ (a : Set A), a.Finite → FINITE' a := @HolLightLean.hol_opam.thm_FINITE_INDUCT holTheoryInst

theorem hol_INFINITE : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (¬s.Finite) = ¬s.Finite := @HolLightLean.hol_opam.thm_INFINITE holTheoryInst

theorem hol_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (f : A → B),
    f '' s = id fun (GEN_PVAR_7 : B) ↦ ∃ (y : B), {x' : B | (∃ x ∈ s, y = f x) ∧ GEN_PVAR_7 = x'} y := @HolLightLean.hol_opam.thm_IMAGE holTheoryInst

theorem hol_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A) (f : A → B),
    (f '' s ⊆ t ∧ Set.InjOn f s) = ((∀ x ∈ s, f x ∈ t) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) := @HolLightLean.hol_opam.thm_INJ holTheoryInst

theorem hol_SURJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A) (f : A → B),
    (f '' s ⊆ t ∧ Set.SurjOn f s t) = ((∀ x ∈ s, f x ∈ t) ∧ ∀ x ∈ t, ∃ y ∈ s, f y = x) := @HolLightLean.hol_opam.thm_SURJ holTheoryInst

theorem hol_BIJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    (f '' s ⊆ t ∧ Set.BijOn f s t) = ((f '' s ⊆ t ∧ Set.InjOn f s) ∧ f '' s ⊆ t ∧ Set.SurjOn f s t) := @HolLightLean.hol_opam.thm_BIJ holTheoryInst

theorem hol_CHOICE : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), Classical.epsilon s = Classical.epsilon fun (x : A) ↦ x ∈ s := @HolLightLean.hol_opam.thm_CHOICE holTheoryInst

theorem hol_REST : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s \ {Classical.epsilon s} = s \ {Classical.epsilon s} := @HolLightLean.hol_opam.thm_REST holTheoryInst

theorem hol_NOT_IN_EMPTY : 
  ∀ {A : Type} [Nonempty A] (x : A), x ∉ @EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A) := @HolLightLean.hol_opam.thm_NOT_IN_EMPTY holTheoryInst

theorem hol_IN_UNIV : 
  ∀ {A : Type} [Nonempty A] (x : A), Membership.mem (γ := Set A) Set.univ x := @HolLightLean.hol_opam.thm_IN_UNIV holTheoryInst

theorem hol_IN_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), (x ∈ s ∪ t) = (x ∈ s ∨ x ∈ t) := @HolLightLean.hol_opam.thm_IN_UNION holTheoryInst

theorem hol_IN_UNIONS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)) (x : A), (x ∈ ⋃₀ s) = ∃ t ∈ s, x ∈ t := @HolLightLean.hol_opam.thm_IN_UNIONS holTheoryInst

theorem hol_IN_INTER : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), (x ∈ s ∩ t) = (x ∈ s ∧ x ∈ t) := @HolLightLean.hol_opam.thm_IN_INTER holTheoryInst

theorem hol_IN_INTERS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)) (x : A), (x ∈ ⋂₀ s) = ∀ t ∈ s, x ∈ t := @HolLightLean.hol_opam.thm_IN_INTERS holTheoryInst

theorem hol_IN_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), (x ∈ s \ t) = (x ∈ s ∧ x ∉ t) := @HolLightLean.hol_opam.thm_IN_DIFF holTheoryInst

theorem hol_IN_INSERT : 
  ∀ {A : Type} [Nonempty A] (x y : A) (s : Set A), (x ∈ insert y s) = (x = y ∨ x ∈ s) := @HolLightLean.hol_opam.thm_IN_INSERT holTheoryInst

theorem hol_IN_DELETE : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x y : A), (x ∈ s \ {y}) = (x ∈ s ∧ ¬x = y) := @HolLightLean.hol_opam.thm_IN_DELETE holTheoryInst

theorem hol_IN_SING : 
  ∀ {A : Type} [Nonempty A] (x y : A), Membership.mem (γ := Set A) (insert y ∅) x = (x = y) := @HolLightLean.hol_opam.thm_IN_SING holTheoryInst

theorem hol_IN_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (y : B) (s : Set A) (f : A → B), (y ∈ f '' s) = ∃ (x : A), y = f x ∧ x ∈ s := @HolLightLean.hol_opam.thm_IN_IMAGE holTheoryInst

theorem hol_IN_REST : 
  ∀ {A : Type} [inst : Nonempty A] (x : A) (s : Set A),
    (x ∈ s \ {Classical.epsilon s}) = (x ∈ s ∧ ¬x = Classical.epsilon s) := @HolLightLean.hol_opam.thm_IN_REST holTheoryInst

theorem hol_FORALL_IN_INSERT : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (a : A) (s : Set A), (∀ x ∈ insert a s, P x) = (P a ∧ ∀ x ∈ s, P x) := @HolLightLean.hol_opam.thm_FORALL_IN_INSERT holTheoryInst

theorem hol_EXISTS_IN_INSERT : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (a : A) (s : Set A), (∃ x ∈ insert a s, P x) = (P a ∨ ∃ x ∈ s, P x) := @HolLightLean.hol_opam.thm_EXISTS_IN_INSERT holTheoryInst

theorem hol_FORALL_IN_UNION : 
  ∀ {A : Type} [Nonempty A] (P s t : Set A), (∀ x ∈ s ∪ t, P x) = ((∀ x ∈ s, P x) ∧ ∀ x ∈ t, P x) := @HolLightLean.hol_opam.thm_FORALL_IN_UNION holTheoryInst

theorem hol_EXISTS_IN_UNION : 
  ∀ {A : Type} [Nonempty A] (P s t : Set A), (∃ x ∈ s ∪ t, P x) = ((∃ x ∈ s, P x) ∨ ∃ x ∈ t, P x) := @HolLightLean.hol_opam.thm_EXISTS_IN_UNION holTheoryInst

theorem hol_FORALL_IN_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set B) (f : A → B) (s : Set A),
    Eq (α := Prop) (∀ y ∈ f '' s, P y) (∀ x ∈ s, P (f x)) := @HolLightLean.hol_opam.thm_FORALL_IN_IMAGE holTheoryInst

theorem hol_EXISTS_IN_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set B) (f : A → B) (s : Set A), (∃ y ∈ f '' s, P y) = ∃ x ∈ s, P (f x) := @HolLightLean.hol_opam.thm_EXISTS_IN_IMAGE holTheoryInst

theorem hol_FORALL_IN_GSPEC : 
  ∀ {A B C D E : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E],
    (∀ (P : Set A) (Q : Set B) (f : A → B),
        Eq (α := Prop)
          (∀ (z : B),
            Membership.mem (γ := Set B) (id fun (GEN_PVAR_8 : B) ↦ ∃ (x : A), {x' : B | P x ∧ GEN_PVAR_8 = x'} (f x))
                z →
              Q z)
          (∀ (x : A), P x → Q (f x))) ∧
      (∀ (P : A → B → Prop) (Q : Set C) (f : A → B → C),
          Eq (α := Prop)
            (∀ (z : C),
              Membership.mem (γ := Set C)
                  (id fun (GEN_PVAR_9 : C) ↦ ∃ (x : A) (y : B), {x' : C | P x y ∧ GEN_PVAR_9 = x'} (f x y)) z →
                Q z)
            (∀ (x : A) (y : B), P x y → Q (f x y))) ∧
        (∀ (P : A → B → C → Prop) (Q : Set D) (f : A → B → C → D),
            Eq (α := Prop)
              (∀ (z : D),
                Membership.mem (γ := Set D)
                    (id fun (GEN_PVAR_10 : D) ↦
                      ∃ (w : A) (x : B) (y : C), {x' : D | P w x y ∧ GEN_PVAR_10 = x'} (f w x y))
                    z →
                  Q z)
              (∀ (w : A) (x : B) (y : C), P w x y → Q (f w x y))) ∧
          ∀ (P : A → B → C → D → Prop) (Q : Set E) (f : A → B → C → D → E),
            Eq (α := Prop)
              (∀ (z : E),
                Membership.mem (γ := Set E)
                    (id fun (GEN_PVAR_11 : E) ↦
                      ∃ (v : A) (w : B) (x : C) (y : D), {x' : E | P v w x y ∧ GEN_PVAR_11 = x'} (f v w x y))
                    z →
                  Q z)
              (∀ (v : A) (w : B) (x : C) (y : D), P v w x y → Q (f v w x y)) := @HolLightLean.hol_opam.thm_FORALL_IN_GSPEC holTheoryInst

theorem hol_EXISTS_IN_GSPEC : 
  ∀ {A B C D E : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E],
    (∀ (P : Set A) (Q : Set B) (f : A → B),
        (∃ (z : B),
            Membership.mem (γ := Set B) (id fun (GEN_PVAR_12 : B) ↦ ∃ (x : A), {x' : B | P x ∧ GEN_PVAR_12 = x'} (f x))
                z ∧
              Q z) =
          ∃ (x : A), P x ∧ Q (f x)) ∧
      (∀ (P : A → B → Prop) (Q : Set C) (f : A → B → C),
          (∃ (z : C),
              Membership.mem (γ := Set C)
                  (id fun (GEN_PVAR_13 : C) ↦ ∃ (x : A) (y : B), {x' : C | P x y ∧ GEN_PVAR_13 = x'} (f x y)) z ∧
                Q z) =
            ∃ (x : A) (y : B), P x y ∧ Q (f x y)) ∧
        (∀ (P : A → B → C → Prop) (Q : Set D) (f : A → B → C → D),
            (∃ (z : D),
                Membership.mem (γ := Set D)
                    (id fun (GEN_PVAR_14 : D) ↦
                      ∃ (w : A) (x : B) (y : C), {x' : D | P w x y ∧ GEN_PVAR_14 = x'} (f w x y))
                    z ∧
                  Q z) =
              ∃ (w : A) (x : B) (y : C), P w x y ∧ Q (f w x y)) ∧
          ∀ (P : A → B → C → D → Prop) (Q : Set E) (f : A → B → C → D → E),
            (∃ (z : E),
                Membership.mem (γ := Set E)
                    (id fun (GEN_PVAR_15 : E) ↦
                      ∃ (v : A) (w : B) (x : C) (y : D), {x' : E | P v w x y ∧ GEN_PVAR_15 = x'} (f v w x y))
                    z ∧
                  Q z) =
              ∃ (v : A) (w : B) (x : C) (y : D), P v w x y ∧ Q (f v w x y) := @HolLightLean.hol_opam.thm_EXISTS_IN_GSPEC holTheoryInst

theorem hol_UNIONS_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → Prop) (s : Set A),
    @Eq (Set B) (@Set.sUnion B (@Set.image A (Set B) f s))
      (@id (Set B) fun (GEN_PVAR_16 : B) ↦
        ∃ (y : B),
          @setOf B
            (fun (x' : B) ↦
              And
                (∃ (x : A),
                  And (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                    (@Membership.mem B (Set B) (@Set.instMembership B) (f x) y))
                (@Eq B GEN_PVAR_16 x'))
            y) := @HolLightLean.hol_opam.thm_UNIONS_IMAGE holTheoryInst

theorem hol_INTERS_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → Prop) (s : Set A),
    @Eq (Set B) (@Set.sInter B (@Set.image A (Set B) f s))
      (@id (Set B) fun (GEN_PVAR_17 : B) ↦
        ∃ (y : B),
          @setOf B
            (fun (x' : B) ↦
              And
                (∀ (x : A),
                  @Membership.mem A (Set A) (@Set.instMembership A) s x →
                    @Membership.mem B (Set B) (@Set.instMembership B) (f x) y)
                (@Eq B GEN_PVAR_17 x'))
            y) := @HolLightLean.hol_opam.thm_INTERS_IMAGE holTheoryInst

theorem hol_UNIONS_GSPEC : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D],
    And
      (∀ (P : Set A) (f : A → B → Prop),
        @Eq (Set B)
          (@Set.sUnion B
            (@id (Set (Set B)) fun (GEN_PVAR_18 : Set B) ↦
              ∃ (x : A), @setOf (Set B) (fun (x' : Set B) ↦ And (P x) (@Eq (Set B) GEN_PVAR_18 x')) (f x)))
          (@id (Set B) fun (GEN_PVAR_19 : B) ↦
            ∃ (a : B),
              @setOf B
                (fun (x' : B) ↦
                  And (∃ (x : A), And (P x) (@Membership.mem B (Set B) (@Set.instMembership B) (f x) a))
                    (@Eq B GEN_PVAR_19 x'))
                a))
      (And
        (∀ (P : A → B → Prop) (f : A → B → C → Prop),
          @Eq (Set C)
            (@Set.sUnion C
              (@id (Set (Set C)) fun (GEN_PVAR_20 : Set C) ↦
                ∃ (x : A) (y : B),
                  @setOf (Set C) (fun (x' : Set C) ↦ And (P x y) (@Eq (Set C) GEN_PVAR_20 x')) (f x y)))
            (@id (Set C) fun (GEN_PVAR_21 : C) ↦
              ∃ (a : C),
                @setOf C
                  (fun (x' : C) ↦
                    And (∃ (x : A) (y : B), And (P x y) (@Membership.mem C (Set C) (@Set.instMembership C) (f x y) a))
                      (@Eq C GEN_PVAR_21 x'))
                  a))
        (∀ (P : A → B → C → Prop) (f : A → B → C → D → Prop),
          @Eq (Set D)
            (@Set.sUnion D
              (@id (Set (Set D)) fun (GEN_PVAR_22 : Set D) ↦
                ∃ (x : A) (y : B) (z : C),
                  @setOf (Set D) (fun (x' : Set D) ↦ And (P x y z) (@Eq (Set D) GEN_PVAR_22 x')) (f x y z)))
            (@id (Set D) fun (GEN_PVAR_23 : D) ↦
              ∃ (a : D),
                @setOf D
                  (fun (x' : D) ↦
                    And
                      (∃ (x : A) (y : B) (z : C),
                        And (P x y z) (@Membership.mem D (Set D) (@Set.instMembership D) (f x y z) a))
                      (@Eq D GEN_PVAR_23 x'))
                  a))) := @HolLightLean.hol_opam.thm_UNIONS_GSPEC holTheoryInst

theorem hol_INTERS_GSPEC : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D],
    And
      (∀ (P : Set A) (f : A → B → Prop),
        @Eq (Set B)
          (@Set.sInter B
            (@id (Set (Set B)) fun (GEN_PVAR_24 : Set B) ↦
              ∃ (x : A), @setOf (Set B) (fun (x' : Set B) ↦ And (P x) (@Eq (Set B) GEN_PVAR_24 x')) (f x)))
          (@id (Set B) fun (GEN_PVAR_25 : B) ↦
            ∃ (a : B),
              @setOf B
                (fun (x' : B) ↦
                  And (∀ (x : A), P x → @Membership.mem B (Set B) (@Set.instMembership B) (f x) a)
                    (@Eq B GEN_PVAR_25 x'))
                a))
      (And
        (∀ (P : A → B → Prop) (f : A → B → C → Prop),
          @Eq (Set C)
            (@Set.sInter C
              (@id (Set (Set C)) fun (GEN_PVAR_26 : Set C) ↦
                ∃ (x : A) (y : B),
                  @setOf (Set C) (fun (x' : Set C) ↦ And (P x y) (@Eq (Set C) GEN_PVAR_26 x')) (f x y)))
            (@id (Set C) fun (GEN_PVAR_27 : C) ↦
              ∃ (a : C),
                @setOf C
                  (fun (x' : C) ↦
                    And (∀ (x : A) (y : B), P x y → @Membership.mem C (Set C) (@Set.instMembership C) (f x y) a)
                      (@Eq C GEN_PVAR_27 x'))
                  a))
        (∀ (P : A → B → C → Prop) (f : A → B → C → D → Prop),
          @Eq (Set D)
            (@Set.sInter D
              (@id (Set (Set D)) fun (GEN_PVAR_28 : Set D) ↦
                ∃ (x : A) (y : B) (z : C),
                  @setOf (Set D) (fun (x' : Set D) ↦ And (P x y z) (@Eq (Set D) GEN_PVAR_28 x')) (f x y z)))
            (@id (Set D) fun (GEN_PVAR_29 : D) ↦
              ∃ (a : D),
                @setOf D
                  (fun (x' : D) ↦
                    And
                      (∀ (x : A) (y : B) (z : C),
                        P x y z → @Membership.mem D (Set D) (@Set.instMembership D) (f x y z) a)
                      (@Eq D GEN_PVAR_29 x'))
                  a))) := @HolLightLean.hol_opam.thm_INTERS_GSPEC holTheoryInst

theorem hol_CHOICE_DEF : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), ¬s = ∅ → Classical.epsilon s ∈ s := @HolLightLean.hol_opam.thm_CHOICE_DEF holTheoryInst

theorem hol_NOT_EQUAL_SETS : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (¬s = t) = ∃ (x : A), (x ∈ t) = (x ∉ s) := @HolLightLean.hol_opam.thm_NOT_EQUAL_SETS holTheoryInst

theorem hol_INSERT_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (P s : Set A) (a : A),
    Eq (α := Set A) (id fun (GEN_PVAR_30 : A) ↦ ∃ (x : A), {x' : A | (x ∈ insert a s ∧ P x) ∧ GEN_PVAR_30 = x'} x)
      (if P a then insert a (id fun (GEN_PVAR_31 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_31 = x'} x)
      else id fun (GEN_PVAR_32 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_32 = x'} x) := @HolLightLean.hol_opam.thm_INSERT_RESTRICT holTheoryInst

theorem hol_UNIV_1 : 
  Eq (α := Set Unit) Set.univ (insert () ∅) := @HolLightLean.hol_opam.thm_UNIV_1 holTheoryInst

theorem hol_MEMBER_NOT_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (∃ (x : A), x ∈ s) = ¬s = ∅ := @HolLightLean.hol_opam.thm_MEMBER_NOT_EMPTY holTheoryInst

theorem hol_UNIV_NOT_EMPTY : 
  ∀ {A : Type} [Nonempty A], ¬Eq (α := Set A) Set.univ ∅ := @HolLightLean.hol_opam.thm_UNIV_NOT_EMPTY holTheoryInst

theorem hol_EMPTY_NOT_UNIV : 
  ∀ {A : Type} [Nonempty A], ¬Eq (α := Set A) ∅ Set.univ := @HolLightLean.hol_opam.thm_EMPTY_NOT_UNIV holTheoryInst

theorem hol_EQ_UNIV : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (∀ (x : A), x ∈ s) = (s = Set.univ) := @HolLightLean.hol_opam.thm_EQ_UNIV holTheoryInst

theorem hol_SUBSET_TRANS : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ⊆ t ∧ t ⊆ u → s ⊆ u := @HolLightLean.hol_opam.thm_SUBSET_TRANS holTheoryInst

theorem hol_SUBSET_REFL : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s ⊆ s := @HolLightLean.hol_opam.thm_SUBSET_REFL holTheoryInst

theorem hol_SUBSET_ANTISYM : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s ⊆ t ∧ t ⊆ s → s = t := @HolLightLean.hol_opam.thm_SUBSET_ANTISYM holTheoryInst

theorem hol_SUBSET_ANTISYM_EQ : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊆ t ∧ t ⊆ s) = (s = t) := @HolLightLean.hol_opam.thm_SUBSET_ANTISYM_EQ holTheoryInst

theorem hol_EMPTY_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ∅ ⊆ s := @HolLightLean.hol_opam.thm_EMPTY_SUBSET holTheoryInst

theorem hol_SUBSET_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (s ⊆ ∅) = (s = ∅) := @HolLightLean.hol_opam.thm_SUBSET_EMPTY holTheoryInst

theorem hol_SUBSET_UNIV : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s ⊆ Set.univ := @HolLightLean.hol_opam.thm_SUBSET_UNIV holTheoryInst

theorem hol_UNIV_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (Set.univ ⊆ s) = (s = Set.univ) := @HolLightLean.hol_opam.thm_UNIV_SUBSET holTheoryInst

theorem hol_SING_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A), (insert x ∅ ⊆ s) = (x ∈ s) := @HolLightLean.hol_opam.thm_SING_SUBSET holTheoryInst

theorem hol_SUBSET_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (s P : Set A),
    @Subset (Set A) (@Set.instHasSubset A)
      (@id (Set A) fun (GEN_PVAR_33 : A) ↦
        ∃ (x : A),
          @setOf A
            (fun (x' : A) ↦
              And (And (@Membership.mem A (Set A) (@Set.instMembership A) s x) (P x)) (@Eq A GEN_PVAR_33 x'))
            x)
      s := @HolLightLean.hol_opam.thm_SUBSET_RESTRICT holTheoryInst

theorem hol_PSUBSET_TRANS : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ⊂ t ∧ t ⊂ u → s ⊂ u := @HolLightLean.hol_opam.thm_PSUBSET_TRANS holTheoryInst

theorem hol_PSUBSET_SUBSET_TRANS : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ⊂ t ∧ t ⊆ u → s ⊂ u := @HolLightLean.hol_opam.thm_PSUBSET_SUBSET_TRANS holTheoryInst

theorem hol_SUBSET_PSUBSET_TRANS : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ⊆ t ∧ t ⊂ u → s ⊂ u := @HolLightLean.hol_opam.thm_SUBSET_PSUBSET_TRANS holTheoryInst

theorem hol_PSUBSET_IRREFL : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ¬s ⊂ s := @HolLightLean.hol_opam.thm_PSUBSET_IRREFL holTheoryInst

theorem hol_NOT_PSUBSET_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ¬s ⊂ ∅ := @HolLightLean.hol_opam.thm_NOT_PSUBSET_EMPTY holTheoryInst

theorem hol_NOT_UNIV_PSUBSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ¬Set.univ ⊂ s := @HolLightLean.hol_opam.thm_NOT_UNIV_PSUBSET holTheoryInst

theorem hol_PSUBSET_UNIV : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (s ⊂ Set.univ) = ∃ (x : A), x ∉ s := @HolLightLean.hol_opam.thm_PSUBSET_UNIV holTheoryInst

theorem hol_PSUBSET_ALT : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊂ t) = (s ⊆ t ∧ ∃ a ∈ t, a ∉ s) := @HolLightLean.hol_opam.thm_PSUBSET_ALT holTheoryInst

theorem hol_UNION_ASSOC : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ∪ t ∪ u = s ∪ (t ∪ u) := @HolLightLean.hol_opam.thm_UNION_ASSOC holTheoryInst

theorem hol_UNION_IDEMPOT : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s ∪ s = s := @HolLightLean.hol_opam.thm_UNION_IDEMPOT holTheoryInst

theorem hol_UNION_COMM : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s ∪ t = t ∪ s := @HolLightLean.hol_opam.thm_UNION_COMM holTheoryInst

theorem hol_SUBSET_UNION : 
  ∀ {A : Type} [Nonempty A], (∀ (s t : Set A), s ⊆ s ∪ t) ∧ ∀ (s t : Set A), s ⊆ t ∪ s := @HolLightLean.hol_opam.thm_SUBSET_UNION holTheoryInst

theorem hol_SUBSET_UNION_ABSORPTION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊆ t) = (s ∪ t = t) := @HolLightLean.hol_opam.thm_SUBSET_UNION_ABSORPTION holTheoryInst

theorem hol_UNION_EMPTY : 
  ∀ {A : Type} [Nonempty A], (∀ (s : Set A), ∅ ∪ s = s) ∧ ∀ (s : Set A), s ∪ ∅ = s := @HolLightLean.hol_opam.thm_UNION_EMPTY holTheoryInst

theorem hol_UNION_UNIV : 
  ∀ {A : Type} [Nonempty A], (∀ (s : Set A), Set.univ ∪ s = Set.univ) ∧ ∀ (s : Set A), s ∪ Set.univ = Set.univ := @HolLightLean.hol_opam.thm_UNION_UNIV holTheoryInst

theorem hol_EMPTY_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ∪ t = ∅) = (s = ∅ ∧ t = ∅) := @HolLightLean.hol_opam.thm_EMPTY_UNION holTheoryInst

theorem hol_UNION_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), (s ∪ t ⊆ u) = (s ⊆ u ∧ t ⊆ u) := @HolLightLean.hol_opam.thm_UNION_SUBSET holTheoryInst

theorem hol_UNION_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (P s t : Set A),
    Eq (α := Set A) (id fun (GEN_PVAR_34 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∪ t ∧ P x) ∧ GEN_PVAR_34 = x'} x)
      ((id fun (GEN_PVAR_35 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_35 = x'} x) ∪
        id fun (GEN_PVAR_36 : A) ↦ ∃ (x : A), {x' : A | (x ∈ t ∧ P x) ∧ GEN_PVAR_36 = x'} x) := @HolLightLean.hol_opam.thm_UNION_RESTRICT holTheoryInst

theorem hol_FORALL_SUBSET_UNION : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (t u : Set A),
    Eq (α := Prop) (∀ s ⊆ t ∪ u, P s) (∀ (t' u' : Set A), t' ⊆ t ∧ u' ⊆ u → P (t' ∪ u')) := @HolLightLean.hol_opam.thm_FORALL_SUBSET_UNION holTheoryInst

theorem hol_EXISTS_SUBSET_UNION : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (t u : Set A),
    (∃ s ⊆ t ∪ u, P s) = ∃ (t' : Set A) (u' : Set A), t' ⊆ t ∧ u' ⊆ u ∧ P (t' ∪ u') := @HolLightLean.hol_opam.thm_EXISTS_SUBSET_UNION holTheoryInst

theorem hol_FORALL_SUBSET_INSERT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (a : A) (t : Set A),
    Eq (α := Prop) (∀ s ⊆ insert a t, P s) (∀ s ⊆ t, P s ∧ P (insert a s)) := @HolLightLean.hol_opam.thm_FORALL_SUBSET_INSERT holTheoryInst

theorem hol_EXISTS_SUBSET_INSERT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (a : A) (t : Set A),
    (∃ s ⊆ insert a t, P s) = ∃ s ⊆ t, P s ∨ P (insert a s) := @HolLightLean.hol_opam.thm_EXISTS_SUBSET_INSERT holTheoryInst

theorem hol_INTER_ASSOC : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ∩ t ∩ u = s ∩ (t ∩ u) := @HolLightLean.hol_opam.thm_INTER_ASSOC holTheoryInst

theorem hol_INTER_IDEMPOT : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s ∩ s = s := @HolLightLean.hol_opam.thm_INTER_IDEMPOT holTheoryInst

theorem hol_INTER_COMM : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s ∩ t = t ∩ s := @HolLightLean.hol_opam.thm_INTER_COMM holTheoryInst

theorem hol_INTER_SUBSET : 
  ∀ {A : Type} [Nonempty A], (∀ (s t : Set A), s ∩ t ⊆ s) ∧ ∀ (s t : Set A), t ∩ s ⊆ s := @HolLightLean.hol_opam.thm_INTER_SUBSET holTheoryInst

theorem hol_SUBSET_INTER_ABSORPTION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊆ t) = (s ∩ t = s) := @HolLightLean.hol_opam.thm_SUBSET_INTER_ABSORPTION holTheoryInst

theorem hol_INTER_EMPTY : 
  ∀ {A : Type} [Nonempty A], (∀ (s : Set A), ∅ ∩ s = ∅) ∧ ∀ (s : Set A), s ∩ ∅ = ∅ := @HolLightLean.hol_opam.thm_INTER_EMPTY holTheoryInst

theorem hol_INTER_UNIV : 
  ∀ {A : Type} [Nonempty A], (∀ (s : Set A), Set.univ ∩ s = s) ∧ ∀ (s : Set A), s ∩ Set.univ = s := @HolLightLean.hol_opam.thm_INTER_UNIV holTheoryInst

theorem hol_SUBSET_INTER : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), (s ⊆ t ∩ u) = (s ⊆ t ∧ s ⊆ u) := @HolLightLean.hol_opam.thm_SUBSET_INTER holTheoryInst

theorem hol_INTER_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (P s t : Set A),
    Eq (α := Set A) (id fun (GEN_PVAR_37 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∩ t ∧ P x) ∧ GEN_PVAR_37 = x'} x)
      ((id fun (GEN_PVAR_38 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_38 = x'} x) ∩
        id fun (GEN_PVAR_39 : A) ↦ ∃ (x : A), {x' : A | (x ∈ t ∧ P x) ∧ GEN_PVAR_39 = x'} x) := @HolLightLean.hol_opam.thm_INTER_RESTRICT holTheoryInst

theorem hol_UNION_OVER_INTER : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u := @HolLightLean.hol_opam.thm_UNION_OVER_INTER holTheoryInst

theorem hol_INTER_OVER_UNION : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) := @HolLightLean.hol_opam.thm_INTER_OVER_UNION holTheoryInst

theorem hol_IN_DISJOINT : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), Disjoint s t = ¬∃ x ∈ s, x ∈ t := @HolLightLean.hol_opam.thm_IN_DISJOINT holTheoryInst

theorem hol_DISJOINT_SYM : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), Disjoint s t = Disjoint t s := @HolLightLean.hol_opam.thm_DISJOINT_SYM holTheoryInst

theorem hol_DISJOINT_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), Disjoint ∅ s ∧ Disjoint s ∅ := @HolLightLean.hol_opam.thm_DISJOINT_EMPTY holTheoryInst

theorem hol_DISJOINT_EMPTY_REFL : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (s = ∅) = Disjoint s s := @HolLightLean.hol_opam.thm_DISJOINT_EMPTY_REFL holTheoryInst

theorem hol_DISJOINT_UNION : 
  ∀ {A : Type} [Nonempty A] (s t u : Set A), Disjoint (s ∪ t) u = (Disjoint s u ∧ Disjoint t u) := @HolLightLean.hol_opam.thm_DISJOINT_UNION holTheoryInst

theorem hol_DISJOINT_SING : 
  ∀ {A : Type} [Nonempty A],
    (∀ (s : Set A) (a : A), Disjoint s (insert a ∅) = (a ∉ s)) ∧
      ∀ (s : Set A) (a : A), Disjoint (insert a ∅) s = (a ∉ s) := @HolLightLean.hol_opam.thm_DISJOINT_SING holTheoryInst

theorem hol_DIFF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s \ ∅ = s := @HolLightLean.hol_opam.thm_DIFF_EMPTY holTheoryInst

theorem hol_EMPTY_DIFF : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ∅ \ s = ∅ := @HolLightLean.hol_opam.thm_EMPTY_DIFF holTheoryInst

theorem hol_DIFF_UNIV : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s \ Set.univ = ∅ := @HolLightLean.hol_opam.thm_DIFF_UNIV holTheoryInst

theorem hol_DIFF_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s \ t) \ t = s \ t := @HolLightLean.hol_opam.thm_DIFF_DIFF holTheoryInst

theorem hol_DIFF_EQ_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s \ s = ∅ := @HolLightLean.hol_opam.thm_DIFF_EQ_EMPTY holTheoryInst

theorem hol_SUBSET_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s \ t ⊆ s := @HolLightLean.hol_opam.thm_SUBSET_DIFF holTheoryInst

theorem hol_COMPL_COMPL : 
  ∀ {A : Type} [Nonempty A] (s : Set A), Set.univ \ (Set.univ \ s) = s := @HolLightLean.hol_opam.thm_COMPL_COMPL holTheoryInst

theorem hol_DIFF_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (P s t : Set A),
    Eq (α := Set A) (id fun (GEN_PVAR_40 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s \ t ∧ P x) ∧ GEN_PVAR_40 = x'} x)
      ((id fun (GEN_PVAR_41 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_41 = x'} x) \
        id fun (GEN_PVAR_42 : A) ↦ ∃ (x : A), {x' : A | (x ∈ t ∧ P x) ∧ GEN_PVAR_42 = x'} x) := @HolLightLean.hol_opam.thm_DIFF_RESTRICT holTheoryInst

theorem hol_COMPONENT : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), x ∈ insert x s := @HolLightLean.hol_opam.thm_COMPONENT holTheoryInst

theorem hol_DECOMPOSITION : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A), (x ∈ s) = ∃ (t : Set A), s = insert x t ∧ x ∉ t := @HolLightLean.hol_opam.thm_DECOMPOSITION holTheoryInst

theorem hol_SET_CASES : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s = ∅ ∨ ∃ (x : A) (t : Set A), s = insert x t ∧ x ∉ t := @HolLightLean.hol_opam.thm_SET_CASES holTheoryInst

theorem hol_ABSORPTION : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), (x ∈ s) = (insert x s = s) := @HolLightLean.hol_opam.thm_ABSORPTION holTheoryInst

theorem hol_INSERT_INSERT : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), insert x (insert x s) = insert x s := @HolLightLean.hol_opam.thm_INSERT_INSERT holTheoryInst

theorem hol_INSERT_COMM : 
  ∀ {A : Type} [Nonempty A] (x y : A) (s : Set A), insert x (insert y s) = insert y (insert x s) := @HolLightLean.hol_opam.thm_INSERT_COMM holTheoryInst

theorem hol_INSERT_UNIV : 
  ∀ {A : Type} [Nonempty A] (x : A), Eq (α := Set A) (insert x Set.univ) Set.univ := @HolLightLean.hol_opam.thm_INSERT_UNIV holTheoryInst

theorem hol_NOT_INSERT_EMPTY : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), ¬insert x s = ∅ := @HolLightLean.hol_opam.thm_NOT_INSERT_EMPTY holTheoryInst

theorem hol_NOT_EMPTY_INSERT : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), ¬∅ = insert x s := @HolLightLean.hol_opam.thm_NOT_EMPTY_INSERT holTheoryInst

theorem hol_INSERT_UNION : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), insert x s ∪ t = if x ∈ t then s ∪ t else insert x (s ∪ t) := @HolLightLean.hol_opam.thm_INSERT_UNION holTheoryInst

theorem hol_INSERT_UNION_EQ : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), insert x s ∪ t = insert x (s ∪ t) := @HolLightLean.hol_opam.thm_INSERT_UNION_EQ holTheoryInst

theorem hol_INSERT_INTER : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), insert x s ∩ t = if x ∈ t then insert x (s ∩ t) else s ∩ t := @HolLightLean.hol_opam.thm_INSERT_INTER holTheoryInst

theorem hol_DISJOINT_INSERT : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), Disjoint (insert x s) t = (Disjoint s t ∧ x ∉ t) := @HolLightLean.hol_opam.thm_DISJOINT_INSERT holTheoryInst

theorem hol_INSERT_SUBSET : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), (insert x s ⊆ t) = (x ∈ t ∧ s ⊆ t) := @HolLightLean.hol_opam.thm_INSERT_SUBSET holTheoryInst

theorem hol_SUBSET_INSERT : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), x ∉ s → ∀ (t : Set A), (s ⊆ insert x t) = (s ⊆ t) := @HolLightLean.hol_opam.thm_SUBSET_INSERT holTheoryInst

theorem hol_INSERT_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), insert x s \ t = if x ∈ t then s \ t else insert x (s \ t) := @HolLightLean.hol_opam.thm_INSERT_DIFF holTheoryInst

theorem hol_INSERT_AC : 
  ∀ {A : Type} [Nonempty A] (y x : A) (s : Set A),
    insert x (insert y s) = insert y (insert x s) ∧ insert x (insert x s) = insert x s := @HolLightLean.hol_opam.thm_INSERT_AC holTheoryInst

theorem hol_INTER_ACI : 
  ∀ {A : Type} [Nonempty A] (r p q : Set A),
    p ∩ q = q ∩ p ∧ p ∩ q ∩ r = p ∩ (q ∩ r) ∧ p ∩ (q ∩ r) = q ∩ (p ∩ r) ∧ p ∩ p = p ∧ p ∩ (p ∩ q) = p ∩ q := @HolLightLean.hol_opam.thm_INTER_ACI holTheoryInst

theorem hol_UNION_ACI : 
  ∀ {A : Type} [Nonempty A] (r p q : Set A),
    p ∪ q = q ∪ p ∧ p ∪ q ∪ r = p ∪ (q ∪ r) ∧ p ∪ (q ∪ r) = q ∪ (p ∪ r) ∧ p ∪ p = p ∧ p ∪ (p ∪ q) = p ∪ q := @HolLightLean.hol_opam.thm_UNION_ACI holTheoryInst

theorem hol_DELETE_NON_ELEMENT : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), (x ∉ s) = (s \ {x} = s) := @HolLightLean.hol_opam.thm_DELETE_NON_ELEMENT holTheoryInst

theorem hol_IN_DELETE_EQ : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x x' : A), ((x ∈ s) = (x' ∈ s)) = ((x ∈ s \ {x'}) = (x' ∈ s \ {x})) := @HolLightLean.hol_opam.thm_IN_DELETE_EQ holTheoryInst

theorem hol_EMPTY_DELETE : 
  ∀ {A : Type} [Nonempty A] (x : A), Eq (α := Set A) (∅ \ {x}) ∅ := @HolLightLean.hol_opam.thm_EMPTY_DELETE holTheoryInst

theorem hol_DELETE_DELETE : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), (s \ {x}) \ {x} = s \ {x} := @HolLightLean.hol_opam.thm_DELETE_DELETE holTheoryInst

theorem hol_DELETE_COMM : 
  ∀ {A : Type} [Nonempty A] (x y : A) (s : Set A), (s \ {x}) \ {y} = (s \ {y}) \ {x} := @HolLightLean.hol_opam.thm_DELETE_COMM holTheoryInst

theorem hol_DELETE_SUBSET : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), s \ {x} ⊆ s := @HolLightLean.hol_opam.thm_DELETE_SUBSET holTheoryInst

theorem hol_SUBSET_DELETE : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), (s ⊆ t \ {x}) = (x ∉ s ∧ s ⊆ t) := @HolLightLean.hol_opam.thm_SUBSET_DELETE holTheoryInst

theorem hol_SUBSET_INSERT_DELETE : 
  ∀ {A : Type} [Nonempty A] (x : A) (s t : Set A), (s ⊆ insert x t) = (s \ {x} ⊆ t) := @HolLightLean.hol_opam.thm_SUBSET_INSERT_DELETE holTheoryInst

theorem hol_DIFF_INSERT : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), s \ insert x t = (s \ {x}) \ t := @HolLightLean.hol_opam.thm_DIFF_INSERT holTheoryInst

theorem hol_PSUBSET_INSERT_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ⊂ t) = ∃ x ∉ s, insert x s ⊆ t := @HolLightLean.hol_opam.thm_PSUBSET_INSERT_SUBSET holTheoryInst

theorem hol_DELETE_INSERT : 
  ∀ {A : Type} [Nonempty A] (x y : A) (s : Set A), insert x s \ {y} = if x = y then s \ {y} else insert x (s \ {y}) := @HolLightLean.hol_opam.thm_DELETE_INSERT holTheoryInst

theorem hol_INSERT_DELETE : 
  ∀ {A : Type} [Nonempty A] (x : A) (s : Set A), x ∈ s → insert x (s \ {x}) = s := @HolLightLean.hol_opam.thm_INSERT_DELETE holTheoryInst

theorem hol_DELETE_INTER : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), s \ {x} ∩ t = (s ∩ t) \ {x} := @HolLightLean.hol_opam.thm_DELETE_INTER holTheoryInst

theorem hol_DISJOINT_DELETE_SYM : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (x : A), Disjoint (s \ {x}) t = Disjoint (t \ {x}) s := @HolLightLean.hol_opam.thm_DISJOINT_DELETE_SYM holTheoryInst

theorem hol_UNIONS_0 : 
  ∀ {A : Type} [Nonempty A], Eq (α := Set A) (⋃₀ ∅) ∅ := @HolLightLean.hol_opam.thm_UNIONS_0 holTheoryInst

theorem hol_UNIONS_1 : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ⋃₀ insert s ∅ = s := @HolLightLean.hol_opam.thm_UNIONS_1 holTheoryInst

theorem hol_UNIONS_2 : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), ⋃₀ insert s (insert t ∅) = s ∪ t := @HolLightLean.hol_opam.thm_UNIONS_2 holTheoryInst

theorem hol_UNIONS_INSERT : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (u : Set (Set A)), ⋃₀ insert s u = s ∪ ⋃₀ u := @HolLightLean.hol_opam.thm_UNIONS_INSERT holTheoryInst

theorem hol_FORALL_IN_UNIONS : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (s : Set (Set A)),
    Eq (α := Prop) (∀ x ∈ ⋃₀ s, P x) (∀ (t : Set A) (x : A), t ∈ s ∧ x ∈ t → P x) := @HolLightLean.hol_opam.thm_FORALL_IN_UNIONS holTheoryInst

theorem hol_EXISTS_IN_UNIONS : 
  ∀ {A : Type} [Nonempty A] (P : Set A) (s : Set (Set A)),
    (∃ x ∈ ⋃₀ s, P x) = ∃ (t : Set A) (x : A), t ∈ s ∧ x ∈ t ∧ P x := @HolLightLean.hol_opam.thm_EXISTS_IN_UNIONS holTheoryInst

theorem hol_EMPTY_UNIONS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)), (⋃₀ s = ∅) = ∀ t ∈ s, t = ∅ := @HolLightLean.hol_opam.thm_EMPTY_UNIONS holTheoryInst

theorem hol_INTER_UNIONS : 
  ∀ {A : Type} [Nonempty A],
    (∀ (s : Set (Set A)) (t : Set A),
        ⋃₀ s ∩ t = ⋃₀ id fun (GEN_PVAR_43 : Set A) ↦ ∃ (x : Set A), {x' : Set A | x ∈ s ∧ GEN_PVAR_43 = x'} (x ∩ t)) ∧
      ∀ (s : Set (Set A)) (t : Set A),
        t ∩ ⋃₀ s = ⋃₀ id fun (GEN_PVAR_44 : Set A) ↦ ∃ (x : Set A), {x' : Set A | x ∈ s ∧ GEN_PVAR_44 = x'} (t ∩ x) := @HolLightLean.hol_opam.thm_INTER_UNIONS holTheoryInst

theorem hol_UNIONS_SUBSET : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)) (t : Set A), (⋃₀ f ⊆ t) = ∀ s ∈ f, s ⊆ t := @HolLightLean.hol_opam.thm_UNIONS_SUBSET holTheoryInst

theorem hol_SUBSET_UNIONS : 
  ∀ {A : Type} [Nonempty A] (f g : Set (Set A)), f ⊆ g → ⋃₀ f ⊆ ⋃₀ g := @HolLightLean.hol_opam.thm_SUBSET_UNIONS holTheoryInst

theorem hol_UNIONS_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set (Set A)), ⋃₀ (s ∪ t) = ⋃₀ s ∪ ⋃₀ t := @HolLightLean.hol_opam.thm_UNIONS_UNION holTheoryInst

theorem hol_INTERS_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set (Set A)), ⋂₀ (s ∪ t) = ⋂₀ s ∩ ⋂₀ t := @HolLightLean.hol_opam.thm_INTERS_UNION holTheoryInst

theorem hol_UNIONS_MONO : 
  ∀ {A : Type} [Nonempty A] (s t : Set (Set A)), (∀ x ∈ s, ∃ y ∈ t, x ⊆ y) → ⋃₀ s ⊆ ⋃₀ t := @HolLightLean.hol_opam.thm_UNIONS_MONO holTheoryInst

theorem hol_UNIONS_MONO_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f g : A → B → Prop) (s : Set A),
    (∀ (x : A),
        @Membership.mem A (Set A) (@Set.instMembership A) s x → @Subset (Set B) (@Set.instHasSubset B) (f x) (g x)) →
      @Subset (Set B) (@Set.instHasSubset B) (@Set.sUnion B (@Set.image A (Set B) f s))
        (@Set.sUnion B (@Set.image A (Set B) g s)) := @HolLightLean.hol_opam.thm_UNIONS_MONO_IMAGE holTheoryInst

theorem hol_UNIONS_UNIV : 
  ∀ {A : Type} [Nonempty A], Eq (α := Set A) (⋃₀ Set.univ) Set.univ := @HolLightLean.hol_opam.thm_UNIONS_UNIV holTheoryInst

theorem hol_UNIONS_INSERT_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)), ⋃₀ insert ∅ s = ⋃₀ s := @HolLightLean.hol_opam.thm_UNIONS_INSERT_EMPTY holTheoryInst

theorem hol_UNIONS_DELETE_EMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)), ⋃₀ (s \ {∅}) = ⋃₀ s := @HolLightLean.hol_opam.thm_UNIONS_DELETE_EMPTY holTheoryInst

theorem hol_INTERS_0 : 
  ∀ {A : Type} [Nonempty A], Eq (α := Set A) (⋂₀ ∅) Set.univ := @HolLightLean.hol_opam.thm_INTERS_0 holTheoryInst

theorem hol_INTERS_1 : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ⋂₀ insert s ∅ = s := @HolLightLean.hol_opam.thm_INTERS_1 holTheoryInst

theorem hol_INTERS_2 : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), ⋂₀ insert s (insert t ∅) = s ∩ t := @HolLightLean.hol_opam.thm_INTERS_2 holTheoryInst

theorem hol_INTERS_INSERT : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (u : Set (Set A)), ⋂₀ insert s u = s ∩ ⋂₀ u := @HolLightLean.hol_opam.thm_INTERS_INSERT holTheoryInst

theorem hol_SUBSET_INTERS : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (f : Set (Set A)), (s ⊆ ⋂₀ f) = ∀ t ∈ f, s ⊆ t := @HolLightLean.hol_opam.thm_SUBSET_INTERS holTheoryInst

theorem hol_INTERS_SUBSET : 
  ∀ {A : Type} [Nonempty A] (u : Set (Set A)) (s : Set A), (¬u = ∅ ∧ ∀ t ∈ u, t ⊆ s) → ⋂₀ u ⊆ s := @HolLightLean.hol_opam.thm_INTERS_SUBSET holTheoryInst

theorem hol_INTERS_SUBSET_STRONG : 
  ∀ {A : Type} [Nonempty A] (u : Set (Set A)) (s : Set A), (∃ t ∈ u, t ⊆ s) → ⋂₀ u ⊆ s := @HolLightLean.hol_opam.thm_INTERS_SUBSET_STRONG holTheoryInst

theorem hol_INTERS_ANTIMONO : 
  ∀ {A : Type} [Nonempty A] (f g : Set (Set A)), g ⊆ f → ⋂₀ f ⊆ ⋂₀ g := @HolLightLean.hol_opam.thm_INTERS_ANTIMONO holTheoryInst

theorem hol_INTERS_EQ_UNIV : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)), (⋂₀ f = Set.univ) = ∀ s ∈ f, s = Set.univ := @HolLightLean.hol_opam.thm_INTERS_EQ_UNIV holTheoryInst

theorem hol_INTERS_ANTIMONO_GEN : 
  ∀ {A : Type} [Nonempty A] (s t : Set (Set A)), (∀ y ∈ t, ∃ x ∈ s, x ⊆ y) → ⋂₀ s ⊆ ⋂₀ t := @HolLightLean.hol_opam.thm_INTERS_ANTIMONO_GEN holTheoryInst

theorem hol_IMAGE_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A) (f : A → B) (s : Set A),
    f '' ∅ = ∅ ∧ f '' insert x s = insert (f x) (f '' s) := @HolLightLean.hol_opam.thm_IMAGE_CLAUSES holTheoryInst

theorem hol_IMAGE_UNION : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A), f '' (s ∪ t) = f '' s ∪ f '' t := @HolLightLean.hol_opam.thm_IMAGE_UNION holTheoryInst

theorem hol_IMAGE_ID : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (fun (x : A) ↦ x) '' s = s := @HolLightLean.hol_opam.thm_IMAGE_ID holTheoryInst

theorem hol_IMAGE_I : 
  ∀ {A : Type} [Nonempty A] (s : Set A), id '' s = s := @HolLightLean.hol_opam.thm_IMAGE_I holTheoryInst

theorem hol_IMAGE_o : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : B → C) (g : A → B) (s : Set A), f ∘ g '' s = f '' g '' s := @HolLightLean.hol_opam.thm_IMAGE_o holTheoryInst

theorem hol_IMAGE_SUBSET : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A), s ⊆ t → f '' s ⊆ f '' t := @HolLightLean.hol_opam.thm_IMAGE_SUBSET holTheoryInst

theorem hol_IMAGE_INTER_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A),
    (∀ (x y : A), f x = f y → x = y) → f '' (s ∩ t) = f '' s ∩ f '' t := @HolLightLean.hol_opam.thm_IMAGE_INTER_INJ holTheoryInst

theorem hol_IMAGE_DIFF_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ t ∧ f x = f y → x = y) → f '' (s \ t) = f '' s \ f '' t := @HolLightLean.hol_opam.thm_IMAGE_DIFF_INJ holTheoryInst

theorem hol_IMAGE_DIFF_INJ_ALT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧ t ⊆ s → f '' (s \ t) = f '' s \ f '' t := @HolLightLean.hol_opam.thm_IMAGE_DIFF_INJ_ALT holTheoryInst

theorem hol_IMAGE_DELETE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (a : A),
    (∀ (x : A), x ∈ s ∧ f x = f a → x = a) → f '' (s \ {a}) = f '' s \ {f a} := @HolLightLean.hol_opam.thm_IMAGE_DELETE_INJ holTheoryInst

theorem hol_IMAGE_DELETE_INJ_ALT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (a : A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧ a ∈ s → f '' (s \ {a}) = f '' s \ {f a} := @HolLightLean.hol_opam.thm_IMAGE_DELETE_INJ_ALT holTheoryInst

theorem hol_IMAGE_EQ_EMPTY : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A), (f '' s = ∅) = (s = ∅) := @HolLightLean.hol_opam.thm_IMAGE_EQ_EMPTY holTheoryInst

theorem hol_FORALL_IN_IMAGE_2 : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (P : B → B → Prop) (s : Set A),
    Eq (α := Prop) (∀ (x y : B), x ∈ f '' s ∧ y ∈ f '' s → P x y) (∀ (x y : A), x ∈ s ∧ y ∈ s → P (f x) (f y)) := @HolLightLean.hol_opam.thm_FORALL_IN_IMAGE_2 holTheoryInst

theorem hol_IMAGE_CONST : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (c : B),
    Eq (α := Set B) ((fun (x : A) ↦ c) '' s) (if s = ∅ then ∅ else insert c ∅) := @HolLightLean.hol_opam.thm_IMAGE_CONST holTheoryInst

theorem hol_SIMPLE_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    (id fun (GEN_PVAR_45 : B) ↦ ∃ (x : A), {x' : B | x ∈ s ∧ GEN_PVAR_45 = x'} (f x)) = f '' s := @HolLightLean.hol_opam.thm_SIMPLE_IMAGE holTheoryInst

theorem hol_SIMPLE_IMAGE_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (P : Set A),
    (id fun (GEN_PVAR_46 : B) ↦ ∃ (x : A), {x' : B | P x ∧ GEN_PVAR_46 = x'} (f x)) =
      f '' id fun (GEN_PVAR_47 : A) ↦ ∃ (x : A), {x' : A | P x ∧ GEN_PVAR_47 = x'} x := @HolLightLean.hol_opam.thm_SIMPLE_IMAGE_GEN holTheoryInst

theorem hol_IMAGE_UNIONS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set (Set A)), f '' ⋃₀ s = ⋃₀ (Set.image f '' s) := @HolLightLean.hol_opam.thm_IMAGE_UNIONS holTheoryInst

theorem hol_FUN_IN_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A), ∀ x ∈ s, f x ∈ f '' s := @HolLightLean.hol_opam.thm_FUN_IN_IMAGE holTheoryInst

theorem hol_SURJECTIVE_IMAGE_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    ((∀ y ∈ t, ∃ (x : A), f x = y) ∧ ∀ (x : A), (f x ∈ t) = (x ∈ s)) → f '' s = t := @HolLightLean.hol_opam.thm_SURJECTIVE_IMAGE_EQ holTheoryInst

theorem hol_IMAGE_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f g : A → B) (s : Set A), (∀ x ∈ s, f x = g x) → f '' s = g '' s := @HolLightLean.hol_opam.thm_IMAGE_EQ holTheoryInst

theorem hol_EMPTY_GSPEC : 
  ∀ {A : Type} [Nonempty A],
    Eq (α := Set A) (id fun (GEN_PVAR_48 : A) ↦ ∃ (x : A), {x' : A | False ∧ GEN_PVAR_48 = x'} x) ∅ := @HolLightLean.hol_opam.thm_EMPTY_GSPEC holTheoryInst

theorem hol_UNIV_GSPEC : 
  ∀ {A : Type} [Nonempty A],
    Eq (α := Set A) (id fun (GEN_PVAR_49 : A) ↦ ∃ (x : A), {x' : A | True ∧ GEN_PVAR_49 = x'} x) Set.univ := @HolLightLean.hol_opam.thm_UNIV_GSPEC holTheoryInst

theorem hol_SING_GSPEC : 
  ∀ {A : Type} [Nonempty A],
    (∀ (a : A),
        Eq (α := Set A) (id fun (GEN_PVAR_50 : A) ↦ ∃ (x : A), {x' : A | x = a ∧ GEN_PVAR_50 = x'} x) (insert a ∅)) ∧
      ∀ (a : A),
        Eq (α := Set A) (id fun (GEN_PVAR_51 : A) ↦ ∃ (x : A), {x' : A | a = x ∧ GEN_PVAR_51 = x'} x) (insert a ∅) := @HolLightLean.hol_opam.thm_SING_GSPEC holTheoryInst

theorem hol_SING_ALT : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (∃ (x : A), s = insert x ∅) = ∃! x : A, x ∈ s := @HolLightLean.hol_opam.thm_SING_ALT holTheoryInst

theorem hol_IN_GSPEC : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    (id fun (GEN_PVAR_52 : A) ↦ ∃ (x : A), {x' : A | x ∈ s ∧ GEN_PVAR_52 = x'} x) = s := @HolLightLean.hol_opam.thm_IN_GSPEC holTheoryInst

theorem hol_IN_ELIM_PAIR_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : A → B → Prop) (a : A) (b : B),
    Membership.mem (γ := Set (A × B))
        (id fun (GEN_PVAR_53 : A × B) ↦ ∃ (x : A) (y : B), {x' : A × B | P x y ∧ GEN_PVAR_53 = x'} (x, y)) (a, b) =
      P a b := @HolLightLean.hol_opam.thm_IN_ELIM_PAIR_THM holTheoryInst

theorem hol_IN_ELIM_TRIPLE_THM : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C],
    (∀ (P : A → B → C → Prop) (a : A) (b : B) (c : C),
        Membership.mem (γ := Set (A × B × C))
            (id fun (GEN_PVAR_54 : A × B × C) ↦
              ∃ (x : A) (y : B) (z : C), {x' : A × B × C | P x y z ∧ GEN_PVAR_54 = x'} (x, y, z))
            (a, b, c) =
          P a b c) ∧
      ∀ (P : A → B → C → Prop) (a : A) (b : B) (c : C),
        Membership.mem (γ := Set ((A × B) × C))
            (id fun (GEN_PVAR_55 : (A × B) × C) ↦
              ∃ (x : A) (y : B) (z : C), {x' : (A × B) × C | P x y z ∧ GEN_PVAR_55 = x'} ((x, y), z))
            ((a, b), c) =
          P a b c := @HolLightLean.hol_opam.thm_IN_ELIM_TRIPLE_THM holTheoryInst

theorem hol_IN_ELIM_QUAD_THM : 
  ∀ {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D],
    (∀ (P : A → B → C → D → Prop) (a : A) (b : B) (c : C) (d : D),
        Membership.mem (γ := Set (A × B × C × D))
            (id fun (GEN_PVAR_56 : A × B × C × D) ↦
              ∃ (w : A) (x : B) (y : C) (z : D), {x' : A × B × C × D | P w x y z ∧ GEN_PVAR_56 = x'} (w, x, y, z))
            (a, b, c, d) =
          P a b c d) ∧
      (∀ (P : A → B → C → D → Prop) (a : A) (b : B) (c : C) (d : D),
          Membership.mem (γ := Set ((A × B) × C × D))
              (id fun (GEN_PVAR_57 : (A × B) × C × D) ↦
                ∃ (w : A) (x : B) (y : C) (z : D), {x' : (A × B) × C × D | P w x y z ∧ GEN_PVAR_57 = x'} ((w, x), y, z))
              ((a, b), c, d) =
            P a b c d) ∧
        ∀ (P : A → B → C → D → Prop) (a : A) (b : B) (c : C) (d : D),
          Membership.mem (γ := Set (((A × B) × C) × D))
              (id fun (GEN_PVAR_58 : ((A × B) × C) × D) ↦
                ∃ (w : A) (x : B) (y : C) (z : D),
                  {x' : ((A × B) × C) × D | P w x y z ∧ GEN_PVAR_58 = x'} (((w, x), y), z))
              (((a, b), c), d) =
            P a b c d := @HolLightLean.hol_opam.thm_IN_ELIM_QUAD_THM holTheoryInst

theorem hol_SET_PAIR_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A × B)),
    Eq (α := Set (A × B)) (id fun (GEN_PVAR_59 : A × B) ↦ ∃ (p : A × B), {x' : A × B | P p ∧ GEN_PVAR_59 = x'} p)
      (id fun (GEN_PVAR_60 : A × B) ↦ ∃ (a : A) (b : B), {x' : A × B | P (a, b) ∧ GEN_PVAR_60 = x'} (a, b)) := @HolLightLean.hol_opam.thm_SET_PAIR_THM holTheoryInst

theorem hol_SET_PROVE_CASES : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (P ∅ ∧ ∀ (a : A) (s : Set A), a ∉ s → P (insert a s)) → ∀ (s : Set A), P s := @HolLightLean.hol_opam.thm_SET_PROVE_CASES holTheoryInst

theorem hol_UNIONS_SINGS_GEN : 
  ∀ {A : Type} [Nonempty A] (P : Set A),
    Eq (α := Set A) (⋃₀ id fun (GEN_PVAR_61 : Set A) ↦ ∃ (x : A), {x' : Set A | P x ∧ GEN_PVAR_61 = x'} (insert x ∅))
      (id fun (GEN_PVAR_62 : A) ↦ ∃ (x : A), {x' : A | P x ∧ GEN_PVAR_62 = x'} x) := @HolLightLean.hol_opam.thm_UNIONS_SINGS_GEN holTheoryInst

theorem hol_UNIONS_SINGS : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    (⋃₀ id fun (GEN_PVAR_63 : Set A) ↦ ∃ (x : A), {x' : Set A | x ∈ s ∧ GEN_PVAR_63 = x'} (insert x ∅)) = s := @HolLightLean.hol_opam.thm_UNIONS_SINGS holTheoryInst

theorem hol_IMAGE_INTERS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set (Set A)),
    (¬s = ∅ ∧ ∀ (x y : A), x ∈ ⋃₀ s ∧ y ∈ ⋃₀ s ∧ f x = f y → x = y) → f '' ⋂₀ s = ⋂₀ (Set.image f '' s) := @HolLightLean.hol_opam.thm_IMAGE_INTERS holTheoryInst

theorem hol_DIFF_INTERS : 
  ∀ {A : Type} [Nonempty A] (u : Set A) (s : Set (Set A)),
    u \ ⋂₀ s = ⋃₀ id fun (GEN_PVAR_64 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ s ∧ GEN_PVAR_64 = x'} (u \ t) := @HolLightLean.hol_opam.thm_DIFF_INTERS holTheoryInst

theorem hol_INTERS_UNIONS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)),
    ⋂₀ s =
      Set.univ \ ⋃₀ id fun (GEN_PVAR_65 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ s ∧ GEN_PVAR_65 = x'} (Set.univ \ t) := @HolLightLean.hol_opam.thm_INTERS_UNIONS holTheoryInst

theorem hol_UNIONS_INTERS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)),
    ⋃₀ s =
      Set.univ \ ⋂₀ id fun (GEN_PVAR_66 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ s ∧ GEN_PVAR_66 = x'} (Set.univ \ t) := @HolLightLean.hol_opam.thm_UNIONS_INTERS holTheoryInst

theorem hol_UNIONS_DIFF : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)) (t : Set A),
    ⋃₀ s \ t = ⋃₀ id fun (GEN_PVAR_67 : Set A) ↦ ∃ (x : Set A), {x' : Set A | x ∈ s ∧ GEN_PVAR_67 = x'} (x \ t) := @HolLightLean.hol_opam.thm_UNIONS_DIFF holTheoryInst

theorem hol_DIFF_UNIONS : 
  ∀ {A : Type} [Nonempty A] (u : Set A) (s : Set (Set A)),
    u \ ⋃₀ s = u ∩ ⋂₀ id fun (GEN_PVAR_68 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ s ∧ GEN_PVAR_68 = x'} (u \ t) := @HolLightLean.hol_opam.thm_DIFF_UNIONS holTheoryInst

theorem hol_DIFF_UNIONS_NONEMPTY : 
  ∀ {A : Type} [Nonempty A] (u : Set A) (s : Set (Set A)),
    ¬s = ∅ → u \ ⋃₀ s = ⋂₀ id fun (GEN_PVAR_69 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ s ∧ GEN_PVAR_69 = x'} (u \ t) := @HolLightLean.hol_opam.thm_DIFF_UNIONS_NONEMPTY holTheoryInst

theorem hol_INTERS_OVER_UNIONS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → Set B → Prop) (s : Set A),
    @Eq (Set B)
      (@Set.sInter B
        (@id (Set (Set B)) fun (GEN_PVAR_70 : Set B) ↦
          ∃ (x : A),
            @setOf (Set B)
              (fun (x' : Set B) ↦
                And (@Membership.mem A (Set A) (@Set.instMembership A) s x) (@Eq (Set B) GEN_PVAR_70 x'))
              (@Set.sUnion B (f x))))
      (@Set.sUnion B
        (@id (Set (Set B)) fun (GEN_PVAR_74 : Set B) ↦
          ∃ (g : A → B → Prop),
            @setOf (Set B)
              (fun (x' : Set B) ↦
                And
                  (∀ (x : A),
                    @Membership.mem A (Set A) (@Set.instMembership A) s x →
                      @Membership.mem (Set B) (Set (Set B)) (@Set.instMembership (Set B)) (f x) (g x))
                  (@Eq (Set B) GEN_PVAR_74 x'))
              (@Set.sInter B
                (@id (Set (Set B)) fun (GEN_PVAR_73 : Set B) ↦
                  ∃ (x : A),
                    @setOf (Set B)
                      (fun (x' : Set B) ↦
                        And (@Membership.mem A (Set A) (@Set.instMembership A) s x) (@Eq (Set B) GEN_PVAR_73 x'))
                      (g x))))) := @HolLightLean.hol_opam.thm_INTERS_OVER_UNIONS holTheoryInst

theorem hol_INTER_INTERS : 
  ∀ {A : Type} [Nonempty A],
    (∀ (f : Set (Set A)) (s : Set A),
        s ∩ ⋂₀ f =
          if f = ∅ then s
          else ⋂₀ id fun (GEN_PVAR_75 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ f ∧ GEN_PVAR_75 = x'} (s ∩ t)) ∧
      ∀ (f : Set (Set A)) (s : Set A),
        ⋂₀ f ∩ s =
          if f = ∅ then s
          else ⋂₀ id fun (GEN_PVAR_76 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ∈ f ∧ GEN_PVAR_76 = x'} (t ∩ s) := @HolLightLean.hol_opam.thm_INTER_INTERS holTheoryInst

theorem hol_UNIONS_OVER_INTERS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → Set B → Prop) (s : Set A),
    @Eq (Set B)
      (@Set.sUnion B
        (@id (Set (Set B)) fun (GEN_PVAR_77 : Set B) ↦
          ∃ (x : A),
            @setOf (Set B)
              (fun (x' : Set B) ↦
                And (@Membership.mem A (Set A) (@Set.instMembership A) s x) (@Eq (Set B) GEN_PVAR_77 x'))
              (@Set.sInter B (f x))))
      (@Set.sInter B
        (@id (Set (Set B)) fun (GEN_PVAR_81 : Set B) ↦
          ∃ (g : A → B → Prop),
            @setOf (Set B)
              (fun (x' : Set B) ↦
                And
                  (∀ (x : A),
                    @Membership.mem A (Set A) (@Set.instMembership A) s x →
                      @Membership.mem (Set B) (Set (Set B)) (@Set.instMembership (Set B)) (f x) (g x))
                  (@Eq (Set B) GEN_PVAR_81 x'))
              (@Set.sUnion B
                (@id (Set (Set B)) fun (GEN_PVAR_80 : Set B) ↦
                  ∃ (x : A),
                    @setOf (Set B)
                      (fun (x' : Set B) ↦
                        And (@Membership.mem A (Set A) (@Set.instMembership A) s x) (@Eq (Set B) GEN_PVAR_80 x'))
                      (g x))))) := @HolLightLean.hol_opam.thm_UNIONS_OVER_INTERS holTheoryInst

theorem hol_UNIONS_EQ_INTERS : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)), (⋃₀ f = ⋂₀ f) = ∃ (s : Set A), f = insert s ∅ := @HolLightLean.hol_opam.thm_UNIONS_EQ_INTERS holTheoryInst

theorem hol_EXISTS_UNIQUE_UNIONS_INTERS : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (∃! s : Set A, P s) =
      Eq (α := Set A) (⋃₀ id fun (GEN_PVAR_82 : Set A) ↦ ∃ (s : Set A), {x' : Set A | P s ∧ GEN_PVAR_82 = x'} s)
        (⋂₀ id fun (GEN_PVAR_83 : Set A) ↦ ∃ (s : Set A), {x' : Set A | P s ∧ GEN_PVAR_83 = x'} s) := @HolLightLean.hol_opam.thm_EXISTS_UNIQUE_UNIONS_INTERS holTheoryInst

theorem hol_IMAGE_INTERS_SUBSET : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : Set (Set A)), f '' ⋂₀ g ⊆ ⋂₀ (Set.image f '' g) := @HolLightLean.hol_opam.thm_IMAGE_INTERS_SUBSET holTheoryInst

theorem hol_IMAGE_INTER_SUBSET : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A), f '' (s ∩ t) ⊆ f '' s ∩ f '' t := @HolLightLean.hol_opam.thm_IMAGE_INTER_SUBSET holTheoryInst

theorem hol_IMAGE_INTER_SATURATED_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t u : Set A),
    Or
        (And
          (@Subset (Set A) (@Set.instHasSubset A)
            (@id (Set A) fun (GEN_PVAR_84 : A) ↦
              ∃ (x : A),
                @setOf A
                  (fun (x' : A) ↦
                    And
                      (And (@Membership.mem A (Set A) (@Set.instMembership A) u x)
                        (@Membership.mem B (Set B) (@Set.instMembership B) (@Set.image A B f s) (f x)))
                      (@Eq A GEN_PVAR_84 x'))
                  x)
            s)
          (@Subset (Set A) (@Set.instHasSubset A) t u))
        (And
          (@Subset (Set A) (@Set.instHasSubset A)
            (@id (Set A) fun (GEN_PVAR_85 : A) ↦
              ∃ (x : A),
                @setOf A
                  (fun (x' : A) ↦
                    And
                      (And (@Membership.mem A (Set A) (@Set.instMembership A) u x)
                        (@Membership.mem B (Set B) (@Set.instMembership B) (@Set.image A B f t) (f x)))
                      (@Eq A GEN_PVAR_85 x'))
                  x)
            t)
          (@Subset (Set A) (@Set.instHasSubset A) s u)) →
      @Eq (Set B) (@Set.image A B f (@Inter.inter (Set A) (@Set.instInter A) s t))
        (@Inter.inter (Set B) (@Set.instInter B) (@Set.image A B f s) (@Set.image A B f t)) := @HolLightLean.hol_opam.thm_IMAGE_INTER_SATURATED_GEN holTheoryInst

theorem hol_IMAGE_INTERS_SATURATED_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : Set (Set A)) (s u : Set A),
    And (Not (@Eq (Set (Set A)) g (@EmptyCollection.emptyCollection (Set (Set A)) (@Set.instEmptyCollection (Set A)))))
        (And
          (∀ (t : Set A),
            @Membership.mem (Set A) (Set (Set A)) (@Set.instMembership (Set A)) g t →
              @Subset (Set A) (@Set.instHasSubset A) t u)
          (∀ (t : Set A),
            @Membership.mem (Set A) (Set (Set A)) (@Set.instMembership (Set A))
                (@sdiff (Set (Set A))
                  (@Pi.sdiff (Set A) (fun (a : Set A) ↦ Prop) fun (i : Set A) ↦
                    @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                  g (@singleton (Set A) (Set (Set A)) (@Set.instSingletonSet (Set A)) s))
                t →
              @Subset (Set A) (@Set.instHasSubset A)
                (@id (Set A) fun (GEN_PVAR_87 : A) ↦
                  ∃ (x : A),
                    @setOf A
                      (fun (x' : A) ↦
                        And
                          (And (@Membership.mem A (Set A) (@Set.instMembership A) u x)
                            (@Membership.mem B (Set B) (@Set.instMembership B) (@Set.image A B f t) (f x)))
                          (@Eq A GEN_PVAR_87 x'))
                      x)
                t)) →
      @Eq (Set B) (@Set.image A B f (@Set.sInter A g)) (@Set.sInter B (@Set.image (Set A) (Set B) (@Set.image A B f) g)) := @HolLightLean.hol_opam.thm_IMAGE_INTERS_SATURATED_GEN holTheoryInst

theorem hol_IMAGE_INTER_SATURATED : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s t : Set A),
    Or
        (@Subset (Set A) (@Set.instHasSubset A)
          (@id (Set A) fun (GEN_PVAR_88 : A) ↦
            ∃ (x : A),
              @setOf A
                (fun (x' : A) ↦
                  And (@Membership.mem B (Set B) (@Set.instMembership B) (@Set.image A B f s) (f x))
                    (@Eq A GEN_PVAR_88 x'))
                x)
          s)
        (@Subset (Set A) (@Set.instHasSubset A)
          (@id (Set A) fun (GEN_PVAR_89 : A) ↦
            ∃ (x : A),
              @setOf A
                (fun (x' : A) ↦
                  And (@Membership.mem B (Set B) (@Set.instMembership B) (@Set.image A B f t) (f x))
                    (@Eq A GEN_PVAR_89 x'))
                x)
          t) →
      @Eq (Set B) (@Set.image A B f (@Inter.inter (Set A) (@Set.instInter A) s t))
        (@Inter.inter (Set B) (@Set.instInter B) (@Set.image A B f s) (@Set.image A B f t)) := @HolLightLean.hol_opam.thm_IMAGE_INTER_SATURATED holTheoryInst

theorem hol_IMAGE_INTERS_SATURATED : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : Set (Set A)) (s : Set A),
    And (Not (@Eq (Set (Set A)) g (@EmptyCollection.emptyCollection (Set (Set A)) (@Set.instEmptyCollection (Set A)))))
        (∀ (t : Set A),
          @Membership.mem (Set A) (Set (Set A)) (@Set.instMembership (Set A))
              (@sdiff (Set (Set A))
                (@Pi.sdiff (Set A) (fun (a : Set A) ↦ Prop) fun (i : Set A) ↦
                  @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                g (@singleton (Set A) (Set (Set A)) (@Set.instSingletonSet (Set A)) s))
              t →
            @Subset (Set A) (@Set.instHasSubset A)
              (@id (Set A) fun (GEN_PVAR_90 : A) ↦
                ∃ (x : A),
                  @setOf A
                    (fun (x' : A) ↦
                      And (@Membership.mem B (Set B) (@Set.instMembership B) (@Set.image A B f t) (f x))
                        (@Eq A GEN_PVAR_90 x'))
                    x)
              t) →
      @Eq (Set B) (@Set.image A B f (@Set.sInter A g)) (@Set.sInter B (@Set.image (Set A) (Set B) (@Set.image A B f) g)) := @HolLightLean.hol_opam.thm_IMAGE_INTERS_SATURATED holTheoryInst

theorem hol_FINITE_INDUCT_STRONG : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (P ∅ ∧ ∀ (x : A) (s : Set A), P s ∧ x ∉ s ∧ s.Finite → P (insert x s)) → ∀ (s : Set A), s.Finite → P s := @HolLightLean.hol_opam.thm_FINITE_INDUCT_STRONG holTheoryInst

theorem hol_INJECTIVE_ON_ALT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set A) (f : A → B),
    Eq (α := Prop) (∀ (x y : A), P x ∧ P y ∧ f x = f y → x = y) (∀ (x y : A), P x ∧ P y → (f x = f y) = (x = y)) := @HolLightLean.hol_opam.thm_INJECTIVE_ON_ALT holTheoryInst

theorem hol_INJECTIVE_ALT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (x y : A), f x = f y → x = y) (∀ (x y : A), (f x = f y) = (x = y)) := @HolLightLean.hol_opam.thm_INJECTIVE_ALT holTheoryInst

theorem hol_SURJECTIVE_ON_RIGHT_INVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (f : A → B) (t : Set B),
    (∀ y ∈ t, ∃ x ∈ s, f x = y) = ∃ (g : B → A), ∀ y ∈ t, g y ∈ s ∧ f (g y) = y := @HolLightLean.hol_opam.thm_SURJECTIVE_ON_RIGHT_INVERSE holTheoryInst

theorem hol_INJECTIVE_ON_LEFT_INVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) = ∃ (g : B → A), ∀ x ∈ s, g (f x) = x := @HolLightLean.hol_opam.thm_INJECTIVE_ON_LEFT_INVERSE holTheoryInst

theorem hol_BIJECTIVE_ON_LEFT_RIGHT_INVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    (∀ x ∈ s, f x ∈ t) →
      ((∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧ ∀ y ∈ t, ∃ x ∈ s, f x = y) =
        ∃ (g : B → A), (∀ y ∈ t, g y ∈ s) ∧ (∀ y ∈ t, f (g y) = y) ∧ ∀ x ∈ s, g (f x) = x := @HolLightLean.hol_opam.thm_BIJECTIVE_ON_LEFT_RIGHT_INVERSE holTheoryInst

theorem hol_SURJECTIVE_RIGHT_INVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    (∀ (y : B), ∃ (x : A), f x = y) = ∃ (g : B → A), ∀ (y : B), f (g y) = y := @HolLightLean.hol_opam.thm_SURJECTIVE_RIGHT_INVERSE holTheoryInst

theorem hol_INJECTIVE_LEFT_INVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    (∀ (x y : A), f x = f y → x = y) = ∃ (g : B → A), ∀ (x : A), g (f x) = x := @HolLightLean.hol_opam.thm_INJECTIVE_LEFT_INVERSE holTheoryInst

theorem hol_BIJECTIVE_LEFT_RIGHT_INVERSE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    ((∀ (x y : A), f x = f y → x = y) ∧ ∀ (y : B), ∃ (x : A), f x = y) =
      ∃ (g : B → A), (∀ (y : B), f (g y) = y) ∧ ∀ (x : A), g (f x) = x := @HolLightLean.hol_opam.thm_BIJECTIVE_LEFT_RIGHT_INVERSE holTheoryInst

theorem hol_FUNCTION_FACTORS_LEFT_GEN : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set A) (f : A → B) (g : A → C),
    (∀ (x y : A), P x ∧ P y ∧ g x = g y → f x = f y) = ∃ (h : C → B), ∀ (x : A), P x → f x = h (g x) := @HolLightLean.hol_opam.thm_FUNCTION_FACTORS_LEFT_GEN holTheoryInst

theorem hol_FUNCTION_FACTORS_LEFT : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A → B) (g : A → C),
    (∀ (x y : A), g x = g y → f x = f y) = ∃ (h : C → B), f = h ∘ g := @HolLightLean.hol_opam.thm_FUNCTION_FACTORS_LEFT holTheoryInst

theorem hol_FUNCTION_FACTORS_RIGHT_GEN : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set A) (f : A → C) (g : B → C),
    (∀ (x : A), P x → ∃ (y : B), g y = f x) = ∃ (h : A → B), ∀ (x : A), P x → f x = g (h x) := @HolLightLean.hol_opam.thm_FUNCTION_FACTORS_RIGHT_GEN holTheoryInst

theorem hol_FUNCTION_FACTORS_RIGHT : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A → C) (g : B → C),
    (∀ (x : A), ∃ (y : B), g y = f x) = ∃ (h : A → B), f = g ∘ h := @HolLightLean.hol_opam.thm_FUNCTION_FACTORS_RIGHT holTheoryInst

theorem hol_SURJECTIVE_FORALL_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (y : B), ∃ (x : A), f x = y) (∀ (P : Set B), Eq (α := Prop) (∀ (x : A), P (f x)) (∀ (y : B), P y)) := @HolLightLean.hol_opam.thm_SURJECTIVE_FORALL_THM holTheoryInst

theorem hol_SURJECTIVE_EXISTS_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (y : B), ∃ (x : A), f x = y) (∀ (P : Set B), (∃ (x : A), P (f x)) = ∃ (y : B), P y) := @HolLightLean.hol_opam.thm_SURJECTIVE_EXISTS_THM holTheoryInst

theorem hol_SURJECTIVE_IMAGE_THM : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (y : B), ∃ (x : A), f x = y)
      (∀ (P : Set B),
        (f '' id fun (GEN_PVAR_91 : A) ↦ ∃ (x : A), {x' : A | P (f x) ∧ GEN_PVAR_91 = x'} x) =
          id fun (GEN_PVAR_92 : B) ↦ ∃ (x : B), {x' : B | P x ∧ GEN_PVAR_92 = x'} x) := @HolLightLean.hol_opam.thm_SURJECTIVE_IMAGE_THM holTheoryInst

theorem hol_IMAGE_INJECTIVE_IMAGE_OF_SUBSET : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    ∃ t ⊆ s, f '' s = f '' t ∧ ∀ (x y : A), x ∈ t ∧ y ∈ t ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_IMAGE_INJECTIVE_IMAGE_OF_SUBSET holTheoryInst

theorem hol_FINITE_EMPTY : 
  ∀ {A : Type} [Nonempty A], Set.Finite (α := A) ∅ := @HolLightLean.hol_opam.thm_FINITE_EMPTY holTheoryInst

theorem hol_FINITE_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), t.Finite ∧ s ⊆ t → s.Finite := @HolLightLean.hol_opam.thm_FINITE_SUBSET holTheoryInst

theorem hol_FINITE_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (s P : Set A),
    s.Finite → Set.Finite (α := A) (id fun (GEN_PVAR_93 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_93 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_RESTRICT holTheoryInst

theorem hol_FINITE_UNION_IMP : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s.Finite ∧ t.Finite → (s ∪ t).Finite := @HolLightLean.hol_opam.thm_FINITE_UNION_IMP holTheoryInst

theorem hol_FINITE_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), (s ∪ t).Finite = (s.Finite ∧ t.Finite) := @HolLightLean.hol_opam.thm_FINITE_UNION holTheoryInst

theorem hol_FINITE_INTER : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s.Finite ∨ t.Finite → (s ∩ t).Finite := @HolLightLean.hol_opam.thm_FINITE_INTER holTheoryInst

theorem hol_FINITE_INSERT : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A), (insert x s).Finite = s.Finite := @HolLightLean.hol_opam.thm_FINITE_INSERT holTheoryInst

theorem hol_FINITE_SING : 
  ∀ {A : Type} [Nonempty A] (a : A), Set.Finite (α := A) (insert a ∅) := @HolLightLean.hol_opam.thm_FINITE_SING holTheoryInst

theorem hol_FINITE_DELETE_IMP : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A), s.Finite → (s \ {x}).Finite := @HolLightLean.hol_opam.thm_FINITE_DELETE_IMP holTheoryInst

theorem hol_FINITE_DELETE : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (x : A), (s \ {x}).Finite = s.Finite := @HolLightLean.hol_opam.thm_FINITE_DELETE holTheoryInst

theorem hol_FINITE_FINITE_UNIONS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)), s.Finite → (⋃₀ s).Finite = ∀ t ∈ s, t.Finite := @HolLightLean.hol_opam.thm_FINITE_FINITE_UNIONS holTheoryInst

theorem hol_FINITE_IMAGE_EXPAND : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    s.Finite →
      Set.Finite (α := B) (id fun (GEN_PVAR_96 : B) ↦ ∃ (y : B), {x' : B | (∃ x ∈ s, y = f x) ∧ GEN_PVAR_96 = x'} y) := @HolLightLean.hol_opam.thm_FINITE_IMAGE_EXPAND holTheoryInst

theorem hol_FINITE_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A), s.Finite → (f '' s).Finite := @HolLightLean.hol_opam.thm_FINITE_IMAGE holTheoryInst

theorem hol_FINITE_IMAGE_INJ_GENERAL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (A' : Set B) (s : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧ A'.Finite →
      Set.Finite (α := A) (id fun (GEN_PVAR_97 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x ∈ A') ∧ GEN_PVAR_97 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_IMAGE_INJ_GENERAL holTheoryInst

theorem hol_FINITE_FINITE_PREIMAGE_GENERAL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    (t.Finite ∧
        ∀ y ∈ t,
          Set.Finite (α := A)
            (id fun (GEN_PVAR_100 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = y) ∧ GEN_PVAR_100 = x'} x)) →
      Set.Finite (α := A) (id fun (GEN_PVAR_101 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x ∈ t) ∧ GEN_PVAR_101 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_FINITE_PREIMAGE_GENERAL holTheoryInst

theorem hol_FINITE_FINITE_PREIMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (t : Set B),
    (t.Finite ∧
        ∀ y ∈ t,
          Set.Finite (α := A) (id fun (GEN_PVAR_102 : A) ↦ ∃ (x : A), {x' : A | f x = y ∧ GEN_PVAR_102 = x'} x)) →
      Set.Finite (α := A) (id fun (GEN_PVAR_103 : A) ↦ ∃ (x : A), {x' : A | f x ∈ t ∧ GEN_PVAR_103 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_FINITE_PREIMAGE holTheoryInst

theorem hol_FINITE_IMAGE_INJ_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) → (f '' s).Finite = s.Finite := @HolLightLean.hol_opam.thm_FINITE_IMAGE_INJ_EQ holTheoryInst

theorem hol_FINITE_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (A' : Set B),
    (∀ (x y : A), f x = f y → x = y) ∧ A'.Finite →
      Set.Finite (α := A) (id fun (GEN_PVAR_104 : A) ↦ ∃ (x : A), {x' : A | f x ∈ A' ∧ GEN_PVAR_104 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_IMAGE_INJ holTheoryInst

theorem hol_FINITE_IMAGE_GEN : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A → B) (g : A → C) (s : Set A) (t : Set B),
    (f '' s ⊆ t ∧ t.Finite ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → g x = g y) → (g '' s).Finite := @HolLightLean.hol_opam.thm_FINITE_IMAGE_GEN holTheoryInst

theorem hol_INFINITE_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    (¬s.Finite ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) → ¬(f '' s).Finite := @HolLightLean.hol_opam.thm_INFINITE_IMAGE holTheoryInst

theorem hol_INFINITE_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    (∀ (x y : A), f x = f y → x = y) → ∀ (s : Set A), ¬s.Finite → ¬(f '' s).Finite := @HolLightLean.hol_opam.thm_INFINITE_IMAGE_INJ holTheoryInst

theorem hol_INFINITE_NONEMPTY : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ¬s.Finite → ¬s = ∅ := @HolLightLean.hol_opam.thm_INFINITE_NONEMPTY holTheoryInst

theorem hol_INFINITE_DIFF_FINITE : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), ¬s.Finite ∧ t.Finite → ¬(s \ t).Finite := @HolLightLean.hol_opam.thm_INFINITE_DIFF_FINITE holTheoryInst

theorem hol_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set B) (t : Set A),
    (s ⊆ f '' t) = ∃ u ⊆ t, (∀ (x y : A), x ∈ u ∧ y ∈ u → (f x = f y) = (x = y)) ∧ s = f '' u := @HolLightLean.hol_opam.thm_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_SUBSET_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set B) (t : Set A), (s ⊆ f '' t) = ∃ u ⊆ t, s = f '' u := @HolLightLean.hol_opam.thm_SUBSET_IMAGE holTheoryInst

theorem hol_EXISTS_SUBSET_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    (∃ t ⊆ f '' s, P t) = ∃ t ⊆ s, P (f '' t) := @HolLightLean.hol_opam.thm_EXISTS_SUBSET_IMAGE holTheoryInst

theorem hol_FORALL_SUBSET_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    Eq (α := Prop) (∀ t ⊆ f '' s, P t) (∀ t ⊆ s, P (f '' t)) := @HolLightLean.hol_opam.thm_FORALL_SUBSET_IMAGE holTheoryInst

theorem hol_EXISTS_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    (∃ t ⊆ f '' s, P t) = ∃ t ⊆ s, (∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y)) ∧ P (f '' t) := @HolLightLean.hol_opam.thm_EXISTS_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_FORALL_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    Eq (α := Prop) (∀ t ⊆ f '' s, P t)
      (∀ (t : Set A), (t ⊆ s ∧ ∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y)) → P (f '' t)) := @HolLightLean.hol_opam.thm_FORALL_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_EXISTS_FINITE_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    (∃ (t : Set B), t.Finite ∧ t ⊆ f '' s ∧ P t) =
      ∃ (t : Set A), t.Finite ∧ t ⊆ s ∧ (∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y)) ∧ P (f '' t) := @HolLightLean.hol_opam.thm_EXISTS_FINITE_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_FORALL_FINITE_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    Eq (α := Prop) (∀ (t : Set B), t.Finite ∧ t ⊆ f '' s → P t)
      (∀ (t : Set A), (t.Finite ∧ t ⊆ s ∧ ∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y)) → P (f '' t)) := @HolLightLean.hol_opam.thm_FORALL_FINITE_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_EXISTS_FINITE_SUBSET_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    (∃ (t : Set B), t.Finite ∧ t ⊆ f '' s ∧ P t) = ∃ (t : Set A), t.Finite ∧ t ⊆ s ∧ P (f '' t) := @HolLightLean.hol_opam.thm_EXISTS_FINITE_SUBSET_IMAGE holTheoryInst

theorem hol_FORALL_FINITE_SUBSET_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A),
    Eq (α := Prop) (∀ (t : Set B), t.Finite ∧ t ⊆ f '' s → P t) (∀ (t : Set A), t.Finite ∧ t ⊆ s → P (f '' t)) := @HolLightLean.hol_opam.thm_FORALL_FINITE_SUBSET_IMAGE holTheoryInst

theorem hol_FINITE_SUBSET_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    (t.Finite ∧ t ⊆ f '' s) = ∃ (s' : Set A), s'.Finite ∧ s' ⊆ s ∧ t = f '' s' := @HolLightLean.hol_opam.thm_FINITE_SUBSET_IMAGE holTheoryInst

theorem hol_FINITE_SUBSET_IMAGE_IMP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    t.Finite ∧ t ⊆ f '' s → ∃ (s' : Set A), s'.Finite ∧ s' ⊆ s ∧ t ⊆ f '' s' := @HolLightLean.hol_opam.thm_FINITE_SUBSET_IMAGE_IMP holTheoryInst

theorem hol_FINITE_IMAGE_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    (f '' s).Finite = ∃ (t : Set A), t.Finite ∧ t ⊆ s ∧ f '' s = f '' t := @HolLightLean.hol_opam.thm_FINITE_IMAGE_EQ holTheoryInst

theorem hol_FINITE_IMAGE_EQ_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    (f '' s).Finite =
      ∃ (t : Set A), t.Finite ∧ t ⊆ s ∧ f '' s = f '' t ∧ ∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y) := @HolLightLean.hol_opam.thm_FINITE_IMAGE_EQ_INJ holTheoryInst

theorem hol_FINITE_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), s.Finite → (s \ t).Finite := @HolLightLean.hol_opam.thm_FINITE_DIFF holTheoryInst

theorem hol_INFINITE_SUPERSET : 
  ∀ {A : Type} [Nonempty A] (s t : Set A), ¬s.Finite ∧ s ⊆ t → ¬t.Finite := @HolLightLean.hol_opam.thm_INFINITE_SUPERSET holTheoryInst

theorem hol_FINITE_TRANSITIVITY_CHAIN : 
  ∀ {A : Type} [Nonempty A] (R' : A → A → Prop) (s : Set A),
    (s.Finite ∧ (∀ (x : A), ¬R' x x) ∧ (∀ (x y z : A), R' x y ∧ R' y z → R' x z) ∧ ∀ x ∈ s, ∃ y ∈ s, R' x y) → s = ∅ := @HolLightLean.hol_opam.thm_FINITE_TRANSITIVITY_CHAIN holTheoryInst

theorem hol_UNIONS_MAXIMAL_SETS : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)),
    f.Finite →
      (⋃₀
          id fun (GEN_PVAR_106 : Set A) ↦
            ∃ (t : Set A), {x' : Set A | (t ∈ f ∧ ∀ u ∈ f, ¬t ⊂ u) ∧ GEN_PVAR_106 = x'} t) =
        ⋃₀ f := @HolLightLean.hol_opam.thm_UNIONS_MAXIMAL_SETS holTheoryInst

theorem hol_FINITE_SUBSET_UNIONS : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)) (s : Set A),
    s.Finite ∧ s ⊆ ⋃₀ f → ∃ (f' : Set (Set A)), f'.Finite ∧ f' ⊆ f ∧ s ⊆ ⋃₀ f' := @HolLightLean.hol_opam.thm_FINITE_SUBSET_UNIONS holTheoryInst

theorem hol_UNIONS_IN_CHAIN : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)),
    (f.Finite ∧ ¬f = ∅ ∧ ∀ (s t : Set A), s ∈ f ∧ t ∈ f → s ⊆ t ∨ t ⊆ s) → ⋃₀ f ∈ f := @HolLightLean.hol_opam.thm_UNIONS_IN_CHAIN holTheoryInst

theorem hol_INTERS_IN_CHAIN : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)),
    (f.Finite ∧ ¬f = ∅ ∧ ∀ (s t : Set A), s ∈ f ∧ t ∈ f → s ⊆ t ∨ t ⊆ s) → ⋂₀ f ∈ f := @HolLightLean.hol_opam.thm_INTERS_IN_CHAIN holTheoryInst

theorem hol_FINITE_SUBSET_UNIONS_DIRECTED_EQ : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)) (s : Set A),
    ¬f = ∅ ∧ (∀ (t u : Set A), t ∈ f ∧ u ∈ f → ∃ v ∈ f, t ⊆ v ∧ u ⊆ v) ∧ s.Finite → (s ⊆ ⋃₀ f) = ∃ t ∈ f, s ⊆ t := @HolLightLean.hol_opam.thm_FINITE_SUBSET_UNIONS_DIRECTED_EQ holTheoryInst

theorem hol_FINITE_SUBSET_UNIONS_CHAIN : 
  ∀ {A : Type} [Nonempty A] (f : Set (Set A)) (s : Set A),
    (s.Finite ∧ s ⊆ ⋃₀ f ∧ ¬f = ∅ ∧ ∀ (t u : Set A), t ∈ f ∧ u ∈ f → t ⊆ u ∨ u ⊆ t) → ∃ t ∈ f, s ⊆ t := @HolLightLean.hol_opam.thm_FINITE_SUBSET_UNIONS_CHAIN holTheoryInst

theorem hol_FINREC : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (b : B) (s : Set A) (n : Nat) (a : B) (f : A → B → B),
    And
      (@Eq Prop (@FINREC A B inst inst_1 f b s a (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (And (@Eq (Set A) s (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))) (@Eq B a b)))
      (@Eq Prop
        (@FINREC A B inst inst_1 f b s a
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (∃ (x : A) (c : B),
          And (@Membership.mem A (Set A) (@Set.instMembership A) s x)
            (And
              (@FINREC A B inst inst_1 f b
                (@sdiff (Set A)
                  (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦
                    @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                  s (@singleton A (Set A) (@Set.instSingletonSet A) x))
                c n)
              (@Eq B a (f x c))))) := @HolLightLean.hol_opam.thm_FINREC holTheoryInst

theorem hol_FINREC_1_LEMMA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B → B) (b : B) (s : Set A) (a : B),
    FINREC f b s a ((0 : ℕ) + (1 : ℕ)) = ∃ (x : A), s = insert x ∅ ∧ a = f x b := @HolLightLean.hol_opam.thm_FINREC_1_LEMMA holTheoryInst

theorem hol_FINREC_SUC_LEMMA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B → B) (b : B),
    (∀ (x y : A) (s : B), Not (@Eq A x y) → @Eq B (f x (f y s)) (f y (f x s))) →
      ∀ (n : Nat) (s : Set A) (z : B),
        @FINREC A B inst inst_1 f b s z
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          ∀ (x : A),
            @Membership.mem A (Set A) (@Set.instMembership A) s x →
              ∃ (w : B),
                And
                  (@FINREC A B inst inst_1 f b
                    (@sdiff (Set A)
                      (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦
                        @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                      s (@singleton A (Set A) (@Set.instSingletonSet A) x))
                    w n)
                  (@Eq B z (f x w)) := @HolLightLean.hol_opam.thm_FINREC_SUC_LEMMA holTheoryInst

theorem hol_FINREC_UNIQUE_LEMMA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B → B) (b : B),
    (∀ (x y : A) (s : B), ¬x = y → f x (f y s) = f y (f x s)) →
      ∀ (n1 n2 : ℕ) (s : Set A) (a1 a2 : B), FINREC f b s a1 n1 ∧ FINREC f b s a2 n2 → a1 = a2 ∧ n1 = n2 := @HolLightLean.hol_opam.thm_FINREC_UNIQUE_LEMMA holTheoryInst

theorem hol_FINREC_EXISTS_LEMMA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B → B) (b : B) (s : Set A),
    s.Finite → ∃ (a : B) (n : ℕ), FINREC f b s a n := @HolLightLean.hol_opam.thm_FINREC_EXISTS_LEMMA holTheoryInst

theorem hol_FINREC_FUN_LEMMA : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (P : Set A) (R' : A → B → C → Prop),
    ((∀ (s : A), P s → ∃ (a : B) (n : C), R' s a n) ∧
        ∀ (n1 n2 : C) (s : A) (a1 a2 : B), R' s a1 n1 ∧ R' s a2 n2 → a1 = a2 ∧ n1 = n2) →
      ∃ (f : A → B), ∀ (s : A) (a : B), P s → (∃ (n : C), R' s a n) = (f s = a) := @HolLightLean.hol_opam.thm_FINREC_FUN_LEMMA holTheoryInst

theorem hol_FINREC_FUN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → B) (b : B),
    (∀ (x y : A) (s : B), ¬x = y → f x (f y s) = f y (f x s)) →
      ∃ (g : Set A → B), g ∅ = b ∧ ∀ (s : Set A) (x : A), s.Finite ∧ x ∈ s → g s = f x (g (s \ {x})) := @HolLightLean.hol_opam.thm_FINREC_FUN holTheoryInst

theorem hol_SET_RECURSION_LEMMA : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → B) (b : B),
    (∀ (x y : A) (s : B), ¬x = y → f x (f y s) = f y (f x s)) →
      ∃ (g : Set A → B), g ∅ = b ∧ ∀ (x : A) (s : Set A), s.Finite → g (insert x s) = if x ∈ s then g s else f x (g s) := @HolLightLean.hol_opam.thm_SET_RECURSION_LEMMA holTheoryInst

theorem hol_ITSET : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (b : B) (f : A → B → B) (s : Set A),
    ITSET f s b =
      Classical.epsilon
        (fun (g : Set A → B) ↦
          g ∅ = b ∧ ∀ (x : A) (s' : Set A), s'.Finite → g (insert x s') = if x ∈ s' then g s' else f x (g s'))
        s := @HolLightLean.hol_opam.thm_ITSET holTheoryInst

theorem hol_FINITE_RECURSION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B → B) (b : B),
    (∀ (x y : A) (s : B), Not (@Eq A x y) → @Eq B (f x (f y s)) (f y (f x s))) →
      And (@Eq B (@ITSET A B inst inst_1 f (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)) b) b)
        (∀ (x : A) (s : Set A),
          @Set.Finite A s →
            @Eq B (@ITSET A B inst inst_1 f (@insert A (Set A) (@Set.instInsert A) x s) b)
              (@ite B (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                (Classical.propDecidable (@Membership.mem A (Set A) (@Set.instMembership A) s x))
                (@ITSET A B inst inst_1 f s b) (f x (@ITSET A B inst inst_1 f s b)))) := @HolLightLean.hol_opam.thm_FINITE_RECURSION holTheoryInst

theorem hol_FINITE_RECURSION_DELETE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B → B) (b : B),
    (∀ (x y : A) (s : B), Not (@Eq A x y) → @Eq B (f x (f y s)) (f y (f x s))) →
      And (@Eq B (@ITSET A B inst inst_1 f (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)) b) b)
        (∀ (x : A) (s : Set A),
          @Set.Finite A s →
            @Eq B (@ITSET A B inst inst_1 f s b)
              (@ite B (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                (Classical.propDecidable (@Membership.mem A (Set A) (@Set.instMembership A) s x))
                (f x
                  (@ITSET A B inst inst_1 f
                    (@sdiff (Set A)
                      (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦
                        @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                      s (@singleton A (Set A) (@Set.instSingletonSet A) x))
                    b))
                (@ITSET A B inst inst_1 f
                  (@sdiff (Set A)
                    (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦
                      @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                    s (@singleton A (Set A) (@Set.instSingletonSet A) x))
                  b))) := @HolLightLean.hol_opam.thm_FINITE_RECURSION_DELETE holTheoryInst

theorem hol_ITSET_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f g : A → B → B) (b : B),
    (s.Finite ∧
        (∀ x ∈ s, f x = g x) ∧
          (∀ (x y : A) (s' : B), ¬x = y → f x (f y s') = f y (f x s')) ∧
            ∀ (x y : A) (s' : B), ¬x = y → g x (g y s') = g y (g x s')) →
      ITSET f s b = ITSET g s b := @HolLightLean.hol_opam.thm_ITSET_EQ holTheoryInst

theorem hol_CARD : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), CARD s = ITSET (fun (x : A) (n : ℕ) ↦ n + (1 : ℕ)) s (0 : ℕ) := @HolLightLean.hol_opam.thm_CARD holTheoryInst

theorem hol_CARD_CLAUSES : 
  ∀ {A : Type} [inst : Nonempty A],
    And
      (@Eq Nat (@CARD A inst (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
        (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (∀ (x : A) (s : Set A),
        @Set.Finite A s →
          @Eq Nat (@CARD A inst (@insert A (Set A) (@Set.instInsert A) x s))
            (@ite Nat (@Membership.mem A (Set A) (@Set.instMembership A) s x)
              (Classical.propDecidable (@Membership.mem A (Set A) (@Set.instMembership A) s x)) (@CARD A inst s)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@CARD A inst s)
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := @HolLightLean.hol_opam.thm_CARD_CLAUSES holTheoryInst

theorem hol_CARD_UNION : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A),
    And (@Set.Finite A s)
        (And (@Set.Finite A t)
          (@Eq (Set A) (@Inter.inter (Set A) (@Set.instInter A) s t)
            (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))) →
      @Eq Nat (@CARD A inst (@Union.union (Set A) (@Set.instUnion A) s t))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@CARD A inst s) (@CARD A inst t)) := @HolLightLean.hol_opam.thm_CARD_UNION holTheoryInst

theorem hol_CARD_DELETE : 
  ∀ {A : Type} [inst : Nonempty A] (x : A) (s : Set A),
    @Set.Finite A s →
      @Eq Nat
        (@CARD A inst
          (@sdiff (Set A)
            (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦ @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra) s
            (@singleton A (Set A) (@Set.instSingletonSet A) x)))
        (@ite Nat (@Membership.mem A (Set A) (@Set.instMembership A) s x)
          (Classical.propDecidable (@Membership.mem A (Set A) (@Set.instMembership A) s x))
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (@CARD A inst s)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@CARD A inst s)) := @HolLightLean.hol_opam.thm_CARD_DELETE holTheoryInst

theorem hol_CARD_UNION_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (s t u : Set A), u.Finite ∧ s ∩ t = ∅ ∧ s ∪ t = u → CARD s + CARD t = CARD u := @HolLightLean.hol_opam.thm_CARD_UNION_EQ holTheoryInst

theorem hol_CARD_DIFF : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A), s.Finite ∧ t ⊆ s → CARD (s \ t) = CARD s - CARD t := @HolLightLean.hol_opam.thm_CARD_DIFF holTheoryInst

theorem hol_CARD_EQ_0 : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s.Finite → (CARD s = (0 : ℕ)) = (s = ∅) := @HolLightLean.hol_opam.thm_CARD_EQ_0 holTheoryInst

theorem hol_CARD_SING : 
  ∀ {A : Type} [inst : Nonempty A] (a : A),
    @Eq Nat
      (@CARD A inst
        (@insert A (Set A) (@Set.instInsert A) a
          (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @HolLightLean.hol_opam.thm_CARD_SING holTheoryInst

theorem hol_FINITE_INDUCT_DELETE : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (P ∅ ∧ ∀ (s : Set A), s.Finite ∧ ¬s = ∅ → ∃ x ∈ s, P (s \ {x}) → P s) → ∀ (s : Set A), s.Finite → P s := @HolLightLean.hol_opam.thm_FINITE_INDUCT_DELETE holTheoryInst

theorem hol_HAS_SIZE : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (n : ℕ), (s.Finite ∧ s.ncard = n) = (s.Finite ∧ CARD s = n) := @HolLightLean.hol_opam.thm_HAS_SIZE holTheoryInst

theorem hol_HAS_SIZE_CARD : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (n : ℕ), s.Finite ∧ s.ncard = n → CARD s = n := @HolLightLean.hol_opam.thm_HAS_SIZE_CARD holTheoryInst

theorem hol_HAS_SIZE_0 : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (s.Finite ∧ s.ncard = (0 : ℕ)) = (s = ∅) := @HolLightLean.hol_opam.thm_HAS_SIZE_0 holTheoryInst

theorem hol_HAS_SIZE_SUC : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (n : ℕ),
    (s.Finite ∧ s.ncard = n + (1 : ℕ)) = (¬s = ∅ ∧ ∀ a ∈ s, (s \ {a}).Finite ∧ (s \ {a}).ncard = n) := @HolLightLean.hol_opam.thm_HAS_SIZE_SUC holTheoryInst

theorem hol_HAS_SIZE_UNION : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (m n : ℕ),
    (s.Finite ∧ s.ncard = m) ∧ (t.Finite ∧ t.ncard = n) ∧ Disjoint s t → (s ∪ t).Finite ∧ (s ∪ t).ncard = m + n := @HolLightLean.hol_opam.thm_HAS_SIZE_UNION holTheoryInst

theorem hol_HAS_SIZE_DIFF : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (m n : ℕ),
    (s.Finite ∧ s.ncard = m) ∧ (t.Finite ∧ t.ncard = n) ∧ t ⊆ s → (s \ t).Finite ∧ (s \ t).ncard = m - n := @HolLightLean.hol_opam.thm_HAS_SIZE_DIFF holTheoryInst

theorem hol_HAS_SIZE_UNIONS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : A → B → Prop) (m n : ℕ),
    ((s.Finite ∧ s.ncard = m) ∧
        (∀ x ∈ s, Set.Finite (t x) ∧ Set.ncard (t x) = n) ∧
          ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → Disjoint (t x) (t y)) →
      Set.Finite (α := B)
          (⋃₀ id fun (GEN_PVAR_109 : Set B) ↦ ∃ (x : A), {x' : Set B | x ∈ s ∧ GEN_PVAR_109 = x'} (t x)) ∧
        Set.ncard (α := B)
            (⋃₀ id fun (GEN_PVAR_109 : Set B) ↦ ∃ (x : A), {x' : Set B | x ∈ s ∧ GEN_PVAR_109 = x'} (t x)) =
          m * n := @HolLightLean.hol_opam.thm_HAS_SIZE_UNIONS holTheoryInst

theorem hol_FINITE_HAS_SIZE : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s.Finite = (s.Finite ∧ s.ncard = CARD s) := @HolLightLean.hol_opam.thm_FINITE_HAS_SIZE holTheoryInst

theorem hol_HAS_SIZE_CLAUSES : 
  ∀ {A : Type} [Nonempty A] (n : ℕ) (s : Set A),
    (s.Finite ∧ s.ncard = (0 : ℕ)) = (s = ∅) ∧
      (s.Finite ∧ s.ncard = n + (1 : ℕ)) = ∃ (a : A) (t : Set A), (t.Finite ∧ t.ncard = n) ∧ a ∉ t ∧ s = insert a t := @HolLightLean.hol_opam.thm_HAS_SIZE_CLAUSES holTheoryInst

theorem hol_CARD_SUBSET_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (a b : Set A), b.Finite ∧ a ⊆ b ∧ CARD a = CARD b → a = b := @HolLightLean.hol_opam.thm_CARD_SUBSET_EQ holTheoryInst

theorem hol_CARD_SUBSET : 
  ∀ {A : Type} [inst : Nonempty A] (a b : Set A), a ⊆ b ∧ b.Finite → CARD a ≤ CARD b := @HolLightLean.hol_opam.thm_CARD_SUBSET holTheoryInst

theorem hol_CARD_SUBSET_LE : 
  ∀ {A : Type} [inst : Nonempty A] (a b : Set A), b.Finite ∧ a ⊆ b ∧ CARD b ≤ CARD a → a = b := @HolLightLean.hol_opam.thm_CARD_SUBSET_LE holTheoryInst

theorem hol_SUBSET_CARD_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A), t.Finite ∧ s ⊆ t → (CARD s = CARD t) = (s = t) := @HolLightLean.hol_opam.thm_SUBSET_CARD_EQ holTheoryInst

theorem hol_FINITE_CARD_LE_SUBSET : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A) (n : ℕ), s ⊆ t ∧ t.Finite ∧ CARD t ≤ n → s.Finite ∧ CARD s ≤ n := @HolLightLean.hol_opam.thm_FINITE_CARD_LE_SUBSET holTheoryInst

theorem hol_CARD_PSUBSET : 
  ∀ {A : Type} [inst : Nonempty A] (a b : Set A), a ⊂ b ∧ b.Finite → CARD a < CARD b := @HolLightLean.hol_opam.thm_CARD_PSUBSET holTheoryInst

theorem hol_CARD_PSUBSET_IMP : 
  ∀ {A : Type} [inst : Nonempty A] (a b : Set A), a ⊆ b ∧ ¬CARD a = CARD b → a ⊂ b := @HolLightLean.hol_opam.thm_CARD_PSUBSET_IMP holTheoryInst

theorem hol_CARD_PSUBSET_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (a b : Set A), b.Finite ∧ a ⊆ b → (a ⊂ b) = (CARD a < CARD b) := @HolLightLean.hol_opam.thm_CARD_PSUBSET_EQ holTheoryInst

theorem hol_CARD_UNION_LE : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A),
    And (@Set.Finite A s) (@Set.Finite A t) →
      @LE.le Nat instLENat (@CARD A inst (@Union.union (Set A) (@Set.instUnion A) s t))
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@CARD A inst s) (@CARD A inst t)) := @HolLightLean.hol_opam.thm_CARD_UNION_LE holTheoryInst

theorem hol_FINITE_CARD_LE_UNION : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A) (m n : Nat),
    And (And (@Set.Finite A s) (@LE.le Nat instLENat (@CARD A inst s) m))
        (And (@Set.Finite A t) (@LE.le Nat instLENat (@CARD A inst t) n)) →
      And (@Set.Finite A (@Union.union (Set A) (@Set.instUnion A) s t))
        (@LE.le Nat instLENat (@CARD A inst (@Union.union (Set A) (@Set.instUnion A) s t))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n)) := @HolLightLean.hol_opam.thm_FINITE_CARD_LE_UNION holTheoryInst

theorem hol_CARD_UNIONS_LE : 
  ∀ {A B : Type} [Nonempty A] [inst : Nonempty B] (s : Set A) (t : A → B → Prop) (m n : ℕ),
    ((s.Finite ∧ s.ncard = m) ∧ ∀ x ∈ s, Set.Finite (t x) ∧ CARD (t x) ≤ n) →
      CARD (A := B) (⋃₀ id fun (GEN_PVAR_115 : Set B) ↦ ∃ (x : A), {x' : Set B | x ∈ s ∧ GEN_PVAR_115 = x'} (t x)) ≤
        m * n := @HolLightLean.hol_opam.thm_CARD_UNIONS_LE holTheoryInst

theorem hol_CARD_UNION_GEN : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A),
    And (@Set.Finite A s) (@Set.Finite A t) →
      @Eq Nat (@CARD A inst (@Union.union (Set A) (@Set.instUnion A) s t))
        (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@CARD A inst s) (@CARD A inst t))
          (@CARD A inst (@Inter.inter (Set A) (@Set.instInter A) s t))) := @HolLightLean.hol_opam.thm_CARD_UNION_GEN holTheoryInst

theorem hol_CARD_UNION_OVERLAP_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A),
    And (@Set.Finite A s) (@Set.Finite A t) →
      @Eq Prop
        (@Eq Nat (@CARD A inst (@Union.union (Set A) (@Set.instUnion A) s t))
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@CARD A inst s) (@CARD A inst t)))
        (@Eq (Set A) (@Inter.inter (Set A) (@Set.instInter A) s t)
          (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))) := @HolLightLean.hol_opam.thm_CARD_UNION_OVERLAP_EQ holTheoryInst

theorem hol_CARD_UNION_OVERLAP : 
  ∀ {A : Type} [inst : Nonempty A] (s t : Set A),
    And (@Set.Finite A s)
        (And (@Set.Finite A t)
          (@LT.lt Nat instLTNat (@CARD A inst (@Union.union (Set A) (@Set.instUnion A) s t))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@CARD A inst s) (@CARD A inst t)))) →
      Not
        (@Eq (Set A) (@Inter.inter (Set A) (@Set.instInter A) s t)
          (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))) := @HolLightLean.hol_opam.thm_CARD_UNION_OVERLAP holTheoryInst

theorem hol_CARD_IMAGE_INJ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧ s.Finite → CARD (f '' s) = CARD s := @HolLightLean.hol_opam.thm_CARD_IMAGE_INJ holTheoryInst

theorem hol_HAS_SIZE_IMAGE_INJ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (n : ℕ),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧ s.Finite ∧ s.ncard = n → (f '' s).Finite ∧ (f '' s).ncard = n := @HolLightLean.hol_opam.thm_HAS_SIZE_IMAGE_INJ holTheoryInst

theorem hol_CARD_IMAGE_LE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A), s.Finite → CARD (f '' s) ≤ CARD s := @HolLightLean.hol_opam.thm_CARD_IMAGE_LE holTheoryInst

theorem hol_FINITE_CARD_LE_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A) (n : ℕ),
    s.Finite ∧ CARD s ≤ n → (f '' s).Finite ∧ CARD (f '' s) ≤ n := @HolLightLean.hol_opam.thm_FINITE_CARD_LE_IMAGE holTheoryInst

theorem hol_CARD_IMAGE_INJ_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A) (t : Set B),
    (s.Finite ∧ (∀ x ∈ s, f x ∈ t) ∧ ∀ y ∈ t, ∃! x : A, x ∈ s ∧ f x = y) → CARD t = CARD s := @HolLightLean.hol_opam.thm_CARD_IMAGE_INJ_EQ holTheoryInst

theorem hol_CARD_SUBSET_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set B) (t : Set A),
    t.Finite ∧ s ⊆ f '' t → CARD s ≤ CARD t := @HolLightLean.hol_opam.thm_CARD_SUBSET_IMAGE holTheoryInst

theorem hol_HAS_SIZE_IMAGE_INJ_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (n : ℕ),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) → ((f '' s).Finite ∧ (f '' s).ncard = n) = (s.Finite ∧ s.ncard = n) := @HolLightLean.hol_opam.thm_HAS_SIZE_IMAGE_INJ_EQ holTheoryInst

theorem hol_CARD_IMAGE_EQ_INJ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A),
    s.Finite → (CARD (f '' s) = CARD s) = ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_CARD_IMAGE_EQ_INJ holTheoryInst

theorem hol_EXISTS_SMALL_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A) (n : ℕ),
    (∃ (t : Set B), t.Finite ∧ CARD t < n ∧ t ⊆ f '' s ∧ P t) =
      ∃ (t : Set A), t.Finite ∧ CARD t < n ∧ t ⊆ s ∧ (∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y)) ∧ P (f '' t) := @HolLightLean.hol_opam.thm_EXISTS_SMALL_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_FORALL_SMALL_SUBSET_IMAGE_INJ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A) (n : ℕ),
    Eq (α := Prop) (∀ (t : Set B), t.Finite ∧ CARD t < n ∧ t ⊆ f '' s → P t)
      (∀ (t : Set A), (t.Finite ∧ CARD t < n ∧ t ⊆ s ∧ ∀ (x y : A), x ∈ t ∧ y ∈ t → (f x = f y) = (x = y)) → P (f '' t)) := @HolLightLean.hol_opam.thm_FORALL_SMALL_SUBSET_IMAGE_INJ holTheoryInst

theorem hol_EXISTS_SMALL_SUBSET_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A) (n : ℕ),
    (∃ (t : Set B), t.Finite ∧ CARD t < n ∧ t ⊆ f '' s ∧ P t) =
      ∃ (t : Set A), t.Finite ∧ CARD t < n ∧ t ⊆ s ∧ P (f '' t) := @HolLightLean.hol_opam.thm_EXISTS_SMALL_SUBSET_IMAGE holTheoryInst

theorem hol_FORALL_SMALL_SUBSET_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (P : Set (Set B)) (f : A → B) (s : Set A) (n : ℕ),
    Eq (α := Prop) (∀ (t : Set B), t.Finite ∧ CARD t < n ∧ t ⊆ f '' s → P t)
      (∀ (t : Set A), t.Finite ∧ CARD t < n ∧ t ⊆ s → P (f '' t)) := @HolLightLean.hol_opam.thm_FORALL_SMALL_SUBSET_IMAGE holTheoryInst

theorem hol_CARD_IMAGE_LE2 : 
  ∀ {A B C : Type} [Nonempty A] [inst : Nonempty B] [inst_1 : Nonempty C] (f : A → B) (g : A → C) (s : Set A),
    (s.Finite ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ g x = g y → f x = f y) → CARD (f '' s) ≤ CARD (g '' s) := @HolLightLean.hol_opam.thm_CARD_IMAGE_LE2 holTheoryInst

theorem hol_CARD_IMAGE_LT2 : 
  ∀ {A B C : Type} [Nonempty A] [inst : Nonempty B] [inst_1 : Nonempty C] (f : A → B) (g : A → C) (s : Set A),
    (s.Finite ∧
        (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ g x = g y → f x = f y) ∧ ¬∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → g x = g y) →
      CARD (f '' s) < CARD (g '' s) := @HolLightLean.hol_opam.thm_CARD_IMAGE_LT2 holTheoryInst

theorem hol_CHOOSE_SUBSET_STRONG : 
  ∀ {A : Type} [inst : Nonempty A] (n : ℕ) (s : Set A), (s.Finite → n ≤ CARD s) → ∃ t ⊆ s, t.Finite ∧ t.ncard = n := @HolLightLean.hol_opam.thm_CHOOSE_SUBSET_STRONG holTheoryInst

theorem hol_CHOOSE_SUBSET_EQ : 
  ∀ {A : Type} [inst : Nonempty A] (n : ℕ) (s : Set A), (s.Finite → n ≤ CARD s) = ∃ t ⊆ s, t.Finite ∧ t.ncard = n := @HolLightLean.hol_opam.thm_CHOOSE_SUBSET_EQ holTheoryInst

theorem hol_CHOOSE_SUBSET : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s.Finite → ∀ n ≤ CARD s, ∃ t ⊆ s, t.Finite ∧ t.ncard = n := @HolLightLean.hol_opam.thm_CHOOSE_SUBSET holTheoryInst

theorem hol_CHOOSE_SUBSET_BETWEEN : 
  ∀ {A : Type} [inst : Nonempty A] (n : ℕ) (s u : Set A),
    s ⊆ u ∧ s.Finite ∧ CARD s ≤ n ∧ (u.Finite → n ≤ CARD u) → ∃ (t : Set A), s ⊆ t ∧ t ⊆ u ∧ t.Finite ∧ t.ncard = n := @HolLightLean.hol_opam.thm_CHOOSE_SUBSET_BETWEEN holTheoryInst

theorem hol_CARD_LE_UNIONS_CHAIN : 
  ∀ {A : Type} [inst : Nonempty A] (f : Set (Set A)) (n : ℕ),
    ((∀ (t u : Set A), t ∈ f ∧ u ∈ f → t ⊆ u ∨ u ⊆ t) ∧ ∀ t ∈ f, t.Finite ∧ CARD t ≤ n) →
      (⋃₀ f).Finite ∧ CARD (⋃₀ f) ≤ n := @HolLightLean.hol_opam.thm_CARD_LE_UNIONS_CHAIN holTheoryInst

theorem hol_CARD_LE_1 : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    (s.Finite ∧ CARD s ≤ (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) = ∃ (a : A), s ⊆ insert a ∅ := @HolLightLean.hol_opam.thm_CARD_LE_1 holTheoryInst

theorem hol_INVOLUTION_EVEN_NOFIXPOINTS : 
  ∀ {A : Type} [inst : Nonempty A] (f : A → A) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, f x ∈ s ∧ ¬f x = x ∧ f (f x) = x) → Even (CARD s) := @HolLightLean.hol_opam.thm_INVOLUTION_EVEN_NOFIXPOINTS holTheoryInst

theorem hol_INVOLUTION_EVEN_FIXPOINTS : 
  ∀ {A : Type} [inst : Nonempty A] (f : A → A) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, f x ∈ s ∧ f (f x) = x) →
      Even (CARD (A := A) (id fun (GEN_PVAR_120 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = x) ∧ GEN_PVAR_120 = x'} x)) =
        Even (CARD s) := @HolLightLean.hol_opam.thm_INVOLUTION_EVEN_FIXPOINTS holTheoryInst

theorem hol_HAS_SIZE_PRODUCT_DEPENDENT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (m : Nat) (t : A → B → Prop) (n : Nat),
    And (And (@Set.Finite A s) (@Eq Nat (@Set.ncard A s) m))
        (∀ (x : A),
          @Membership.mem A (Set A) (@Set.instMembership A) s x →
            And (@Set.Finite B (t x)) (@Eq Nat (@Set.ncard B (t x)) n)) →
      And
        (@Set.Finite (Prod A B)
          (@id (Set (Prod A B)) fun (GEN_PVAR_123 : Prod A B) ↦
            ∃ (x : A) (y : B),
              @setOf (Prod A B)
                (fun (x' : Prod A B) ↦
                  And
                    (And (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                      (@Membership.mem B (Set B) (@Set.instMembership B) (t x) y))
                    (@Eq (Prod A B) GEN_PVAR_123 x'))
                (@Prod.mk A B x y)))
        (@Eq Nat
          (@Set.ncard (Prod A B)
            (@id (Set (Prod A B)) fun (GEN_PVAR_123 : Prod A B) ↦
              ∃ (x : A) (y : B),
                @setOf (Prod A B)
                  (fun (x' : Prod A B) ↦
                    And
                      (And (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                        (@Membership.mem B (Set B) (@Set.instMembership B) (t x) y))
                      (@Eq (Prod A B) GEN_PVAR_123 x'))
                  (@Prod.mk A B x y)))
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) m n)) := @HolLightLean.hol_opam.thm_HAS_SIZE_PRODUCT_DEPENDENT holTheoryInst

theorem hol_FINITE_PRODUCT_DEPENDENT : 
  ∀ {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] (f : A → B → C) (s : Set A) (t : A → B → Prop),
    And (@Set.Finite A s) (∀ (x : A), @Membership.mem A (Set A) (@Set.instMembership A) s x → @Set.Finite B (t x)) →
      @Set.Finite C
        (@id (Set C) fun (GEN_PVAR_128 : C) ↦
          ∃ (x : A) (y : B),
            @setOf C
              (fun (x' : C) ↦
                And
                  (And (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                    (@Membership.mem B (Set B) (@Set.instMembership B) (t x) y))
                  (@Eq C GEN_PVAR_128 x'))
              (f x y)) := @HolLightLean.hol_opam.thm_FINITE_PRODUCT_DEPENDENT holTheoryInst

theorem hol_FINITE_PRODUCT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      Set.Finite (α := A × B)
        (id fun (GEN_PVAR_129 : A × B) ↦ ∃ (x : A) (y : B), {x' : A × B | (x ∈ s ∧ y ∈ t) ∧ GEN_PVAR_129 = x'} (x, y)) := @HolLightLean.hol_opam.thm_FINITE_PRODUCT holTheoryInst

theorem hol_CARD_PRODUCT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      CARD (A := A × B)
          (id fun (GEN_PVAR_130 : A × B) ↦
            ∃ (x : A) (y : B), {x' : A × B | (x ∈ s ∧ y ∈ t) ∧ GEN_PVAR_130 = x'} (x, y)) =
        CARD s * CARD t := @HolLightLean.hol_opam.thm_CARD_PRODUCT holTheoryInst

theorem hol_HAS_SIZE_PRODUCT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (m : ℕ) (t : Set B) (n : ℕ),
    (s.Finite ∧ s.ncard = m) ∧ t.Finite ∧ t.ncard = n →
      Set.Finite (α := A × B)
          (id fun (GEN_PVAR_131 : A × B) ↦
            ∃ (x : A) (y : B), {x' : A × B | (x ∈ s ∧ y ∈ t) ∧ GEN_PVAR_131 = x'} (x, y)) ∧
        Set.ncard (α := A × B)
            (id fun (GEN_PVAR_131 : A × B) ↦
              ∃ (x : A) (y : B), {x' : A × B | (x ∈ s ∧ y ∈ t) ∧ GEN_PVAR_131 = x'} (x, y)) =
          m * n := @HolLightLean.hol_opam.thm_HAS_SIZE_PRODUCT holTheoryInst

theorem hol_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B),
    s.prod t =
      id fun (GEN_PVAR_132 : A × B) ↦ ∃ (x : A) (y : B), {x' : A × B | (x ∈ s ∧ y ∈ t) ∧ GEN_PVAR_132 = x'} (x, y) := @HolLightLean.hol_opam.thm_CROSS holTheoryInst

theorem hol_IN_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A) (y : B) (s : Set A) (t : Set B),
    ((x, y) ∈ s.prod t) = (x ∈ s ∧ y ∈ t) := @HolLightLean.hol_opam.thm_IN_CROSS holTheoryInst

theorem hol_HAS_SIZE_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (m n : ℕ),
    (s.Finite ∧ s.ncard = m) ∧ t.Finite ∧ t.ncard = n → (s.prod t).Finite ∧ (s.prod t).ncard = m * n := @HolLightLean.hol_opam.thm_HAS_SIZE_CROSS holTheoryInst

theorem hol_FINITE_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B), s.Finite ∧ t.Finite → (s.prod t).Finite := @HolLightLean.hol_opam.thm_FINITE_CROSS holTheoryInst

theorem hol_CARD_CROSS : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite → CARD (s.prod t) = CARD s * CARD t := @HolLightLean.hol_opam.thm_CARD_CROSS holTheoryInst

theorem hol_CROSS_EQ_EMPTY : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B), (s.prod t = ∅) = (s = ∅ ∨ t = ∅) := @HolLightLean.hol_opam.thm_CROSS_EQ_EMPTY holTheoryInst

theorem hol_CROSS_EMPTY : 
  ∀ {_98772 _98785 A B : Type} [Nonempty _98772] [Nonempty _98785] [Nonempty A] [Nonempty B],
    (∀ (s : Set A), Eq (α := Set (A × _98772)) (s.prod ∅) ∅) ∧
      ∀ (t : Set B), Eq (α := Set (_98785 × B)) (Set.prod ∅ t) ∅ := @HolLightLean.hol_opam.thm_CROSS_EMPTY holTheoryInst

theorem hol_CROSS_SING : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (x : A) (y : B),
    Eq (α := Set (A × B)) (Set.prod (insert x ∅) (insert y ∅)) (insert (x, y) ∅) := @HolLightLean.hol_opam.thm_CROSS_SING holTheoryInst

theorem hol_CROSS_UNIV : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B], Eq (α := Set (A × B)) (Set.prod Set.univ Set.univ) Set.univ := @HolLightLean.hol_opam.thm_CROSS_UNIV holTheoryInst

theorem hol_FINITE_CROSS_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B),
    (s.prod t).Finite = (s = ∅ ∨ t = ∅ ∨ s.Finite ∧ t.Finite) := @HolLightLean.hol_opam.thm_FINITE_CROSS_EQ holTheoryInst

theorem hol_INFINITE_CROSS_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B),
    (¬(s.prod t).Finite) = (¬s = ∅ ∧ ¬t.Finite ∨ ¬s.Finite ∧ ¬t = ∅) := @HolLightLean.hol_opam.thm_INFINITE_CROSS_EQ holTheoryInst

theorem hol_FINITE_CROSS_UNIV : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    Set.Finite (α := A × B) Set.univ = (Set.Finite (α := A) Set.univ ∧ Set.Finite (α := B) Set.univ) := @HolLightLean.hol_opam.thm_FINITE_CROSS_UNIV holTheoryInst

theorem hol_INFINITE_CROSS_UNIV : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (¬Set.Finite (α := A × B) Set.univ) = (¬Set.Finite (α := A) Set.univ ∨ ¬Set.Finite (α := B) Set.univ) := @HolLightLean.hol_opam.thm_INFINITE_CROSS_UNIV holTheoryInst

theorem hol_FINITE_UNIV_PAIR : 
  ∀ {A : Type} [Nonempty A], Set.Finite (α := A × A) Set.univ = Set.Finite (α := A) Set.univ := @HolLightLean.hol_opam.thm_FINITE_UNIV_PAIR holTheoryInst

theorem hol_INFINITE_UNIV_PAIR : 
  ∀ {A : Type} [Nonempty A], (¬Set.Finite (α := A × A) Set.univ) = ¬Set.Finite (α := A) Set.univ := @HolLightLean.hol_opam.thm_INFINITE_UNIV_PAIR holTheoryInst

theorem hol_FORALL_IN_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A × B)) (s : Set A) (t : Set B),
    Eq (α := Prop) (∀ z ∈ s.prod t, P z) (∀ (x : A) (y : B), x ∈ s ∧ y ∈ t → P (x, y)) := @HolLightLean.hol_opam.thm_FORALL_IN_CROSS holTheoryInst

theorem hol_EXISTS_IN_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (P : Set (A × B)) (s : Set A) (t : Set B),
    (∃ z ∈ s.prod t, P z) = ∃ (x : A) (y : B), x ∈ s ∧ y ∈ t ∧ P (x, y) := @HolLightLean.hol_opam.thm_EXISTS_IN_CROSS holTheoryInst

theorem hol_SUBSET_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (s' : Set A) (t' : Set B),
    (s.prod t ⊆ s'.prod t') = (s = ∅ ∨ t = ∅ ∨ s ⊆ s' ∧ t ⊆ t') := @HolLightLean.hol_opam.thm_SUBSET_CROSS holTheoryInst

theorem hol_CROSS_MONO : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (s' : Set A) (t' : Set B),
    s ⊆ s' ∧ t ⊆ t' → s.prod t ⊆ s'.prod t' := @HolLightLean.hol_opam.thm_CROSS_MONO holTheoryInst

theorem hol_CROSS_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s s' : Set A) (t t' : Set B),
    (s.prod t = s'.prod t') = ((s = ∅ ∨ t = ∅) ∧ (s' = ∅ ∨ t' = ∅) ∨ s = s' ∧ t = t') := @HolLightLean.hol_opam.thm_CROSS_EQ holTheoryInst

theorem hol_IMAGE_FST_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B), Prod.fst '' s.prod t = if t = ∅ then ∅ else s := @HolLightLean.hol_opam.thm_IMAGE_FST_CROSS holTheoryInst

theorem hol_IMAGE_SND_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B), Prod.snd '' s.prod t = if s = ∅ then ∅ else t := @HolLightLean.hol_opam.thm_IMAGE_SND_CROSS holTheoryInst

theorem hol_IMAGE_PAIRED_CROSS : 
  ∀ {A B C D : Type} [Nonempty A] [inst : Nonempty B] [Nonempty C] [inst_2 : Nonempty D] (f : A → B) (g : C → D)
    (s : Set A) (t : Set C),
    (Classical.epsilon fun (f' : A × C → B × D) ↦ ∀ (x : A) (y : C), f' (x, y) = (f x, g y)) '' s.prod t =
      (f '' s).prod (g '' t) := @HolLightLean.hol_opam.thm_IMAGE_PAIRED_CROSS holTheoryInst

theorem hol_CROSS_INTER : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (s : Set A) (t u : Set B), s.prod (t ∩ u) = s.prod t ∩ s.prod u) ∧
      ∀ (s t : Set A) (u : Set B), (s ∩ t).prod u = s.prod u ∩ t.prod u := @HolLightLean.hol_opam.thm_CROSS_INTER holTheoryInst

theorem hol_CROSS_UNION : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (s : Set A) (t u : Set B), s.prod (t ∪ u) = s.prod t ∪ s.prod u) ∧
      ∀ (s t : Set A) (u : Set B), (s ∪ t).prod u = s.prod u ∪ t.prod u := @HolLightLean.hol_opam.thm_CROSS_UNION holTheoryInst

theorem hol_CROSS_DIFF : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (s : Set A) (t u : Set B), s.prod (t \ u) = s.prod t \ s.prod u) ∧
      ∀ (s t : Set A) (u : Set B), (s \ t).prod u = s.prod u \ t.prod u := @HolLightLean.hol_opam.thm_CROSS_DIFF holTheoryInst

theorem hol_INTER_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s s' : Set A) (t t' : Set B), s.prod t ∩ s'.prod t' = (s ∩ s').prod (t ∩ t') := @HolLightLean.hol_opam.thm_INTER_CROSS holTheoryInst

theorem hol_CROSS_UNIONS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (s : Set A) (f : Set (Set A)),
        s.prod (⋃₀ f) =
          ⋃₀
            id fun (GEN_PVAR_134 : Set (A × A)) ↦
              ∃ (t : Set A), {x' : Set (A × A) | t ∈ f ∧ GEN_PVAR_134 = x'} (s.prod t)) ∧
      ∀ (f : Set (Set A)) (t : Set B),
        (⋃₀ f).prod t =
          ⋃₀
            id fun (GEN_PVAR_135 : Set (A × B)) ↦
              ∃ (s : Set A), {x' : Set (A × B) | s ∈ f ∧ GEN_PVAR_135 = x'} (s.prod t) := @HolLightLean.hol_opam.thm_CROSS_UNIONS holTheoryInst

theorem hol_CROSS_UNIONS_UNIONS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : Set (Set A)) (g : Set (Set B)),
    (⋃₀ f).prod (⋃₀ g) =
      ⋃₀
        id fun (GEN_PVAR_133 : Set (A × B)) ↦
          ∃ (s : Set A) (t : Set B), {x' : Set (A × B) | (s ∈ f ∧ t ∈ g) ∧ GEN_PVAR_133 = x'} (s.prod t) := @HolLightLean.hol_opam.thm_CROSS_UNIONS_UNIONS holTheoryInst

theorem hol_CROSS_INTERS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (s : Set A) (f : Set (Set A)),
        s.prod (⋂₀ f) =
          if f = ∅ then s.prod Set.univ
          else
            ⋂₀
              id fun (GEN_PVAR_139 : Set (A × A)) ↦
                ∃ (t : Set A), {x' : Set (A × A) | t ∈ f ∧ GEN_PVAR_139 = x'} (s.prod t)) ∧
      ∀ (f : Set (Set A)) (t : Set B),
        (⋂₀ f).prod t =
          if f = ∅ then Set.prod Set.univ t
          else
            ⋂₀
              id fun (GEN_PVAR_140 : Set (A × B)) ↦
                ∃ (s : Set A), {x' : Set (A × B) | s ∈ f ∧ GEN_PVAR_140 = x'} (s.prod t) := @HolLightLean.hol_opam.thm_CROSS_INTERS holTheoryInst

theorem hol_CROSS_INTERS_INTERS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : Set (Set A)) (g : Set (Set B)),
    (⋂₀ f).prod (⋂₀ g) =
      if f = ∅ then
        ⋂₀
          id fun (GEN_PVAR_136 : Set (A × B)) ↦
            ∃ (t : Set B), {x' : Set (A × B) | t ∈ g ∧ GEN_PVAR_136 = x'} (Set.prod Set.univ t)
      else
        if g = ∅ then
          ⋂₀
            id fun (GEN_PVAR_137 : Set (A × B)) ↦
              ∃ (s : Set A), {x' : Set (A × B) | s ∈ f ∧ GEN_PVAR_137 = x'} (s.prod Set.univ)
        else
          ⋂₀
            id fun (GEN_PVAR_138 : Set (A × B)) ↦
              ∃ (s : Set A) (t : Set B), {x' : Set (A × B) | (s ∈ f ∧ t ∈ g) ∧ GEN_PVAR_138 = x'} (s.prod t) := @HolLightLean.hol_opam.thm_CROSS_INTERS_INTERS holTheoryInst

theorem hol_DISJOINT_CROSS : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (s' : Set A) (t' : Set B),
    Disjoint (s.prod t) (s'.prod t') = (Disjoint s s' ∨ Disjoint t t') := @HolLightLean.hol_opam.thm_DISJOINT_CROSS holTheoryInst

theorem hol_ARB : 
  ∀ {A : Type} [inst : Nonempty A], Eq (α := A) ARB (Classical.epsilon fun (x : A) ↦ False) := @HolLightLean.hol_opam.thm_ARB holTheoryInst

theorem hol_EXTENSIONAL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A),
    Eq (α := Set (A → B)) (EXTENSIONAL s)
      (id fun (GEN_PVAR_141 : A → B) ↦ ∃ (f : A → B), {x' : A → B | (∀ x ∉ s, f x = ARB) ∧ GEN_PVAR_141 = x'} f) := @HolLightLean.hol_opam.thm_EXTENSIONAL holTheoryInst

theorem hol_IN_EXTENSIONAL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B),
    Membership.mem (γ := Set (A → B)) (EXTENSIONAL s) f = ∀ x ∉ s, f x = ARB := @HolLightLean.hol_opam.thm_IN_EXTENSIONAL holTheoryInst

theorem hol_IN_EXTENSIONAL_UNDEFINED : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B) (x : A),
    Membership.mem (γ := Set (A → B)) (EXTENSIONAL s) f ∧ x ∉ s → f x = ARB := @HolLightLean.hol_opam.thm_IN_EXTENSIONAL_UNDEFINED holTheoryInst

theorem hol_EXTENSIONAL_EMPTY : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    @Eq (Set (A → B))
      (@EXTENSIONAL A B inst inst_1 (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
      (@insert (A → B) (Set (A → B)) (@Set.instInsert (A → B)) (fun (x : A) ↦ @ARB B inst_1)
        (@EmptyCollection.emptyCollection (Set (A → B)) (@Set.instEmptyCollection (A → B)))) := @HolLightLean.hol_opam.thm_EXTENSIONAL_EMPTY holTheoryInst

theorem hol_EXTENSIONAL_UNIV : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B), EXTENSIONAL Set.univ f := @HolLightLean.hol_opam.thm_EXTENSIONAL_UNIV holTheoryInst

theorem hol_EXTENSIONAL_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f g : A → B),
    (Membership.mem (γ := Set (A → B)) (EXTENSIONAL s) f ∧
        Membership.mem (γ := Set (A → B)) (EXTENSIONAL s) g ∧ ∀ x ∈ s, f x = g x) →
      f = g := @HolLightLean.hol_opam.thm_EXTENSIONAL_EQ holTheoryInst

theorem hol_RESTRICTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B) (x : A),
    RESTRICTION s f x = if x ∈ s then f x else ARB := @HolLightLean.hol_opam.thm_RESTRICTION holTheoryInst

theorem hol_RESTRICTION_THM : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B),
    RESTRICTION s f = fun (x : A) ↦ if x ∈ s then f x else ARB := @HolLightLean.hol_opam.thm_RESTRICTION_THM holTheoryInst

theorem hol_RESTRICTION_DEFINED : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B), ∀ x ∈ s, RESTRICTION s f x = f x := @HolLightLean.hol_opam.thm_RESTRICTION_DEFINED holTheoryInst

theorem hol_RESTRICTION_UNDEFINED : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B), ∀ x ∉ s, RESTRICTION s f x = ARB := @HolLightLean.hol_opam.thm_RESTRICTION_UNDEFINED holTheoryInst

theorem hol_RESTRICTION_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B) (x : A) (y : B),
    x ∈ s ∧ f x = y → RESTRICTION s f x = y := @HolLightLean.hol_opam.thm_RESTRICTION_EQ holTheoryInst

theorem hol_RESTRICTION_IN_EXTENSIONAL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B),
    Membership.mem (γ := Set (A → B)) (EXTENSIONAL s) (RESTRICTION s f) := @HolLightLean.hol_opam.thm_RESTRICTION_IN_EXTENSIONAL holTheoryInst

theorem hol_RESTRICTION_EXTENSION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f g : A → B),
    (RESTRICTION s f = RESTRICTION s g) = ∀ x ∈ s, f x = g x := @HolLightLean.hol_opam.thm_RESTRICTION_EXTENSION holTheoryInst

theorem hol_RESTRICTION_FIXPOINT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B),
    (RESTRICTION s f = f) = Membership.mem (γ := Set (A → B)) (EXTENSIONAL s) f := @HolLightLean.hol_opam.thm_RESTRICTION_FIXPOINT holTheoryInst

theorem hol_RESTRICTION_UNIV : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B), RESTRICTION Set.univ f = f := @HolLightLean.hol_opam.thm_RESTRICTION_UNIV holTheoryInst

theorem hol_RESTRICTION_RESTRICTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s t : Set A) (f : A → B),
    s ⊆ t → RESTRICTION s (RESTRICTION t f) = RESTRICTION s f := @HolLightLean.hol_opam.thm_RESTRICTION_RESTRICTION holTheoryInst

theorem hol_RESTRICTION_IDEMP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B),
    RESTRICTION s (RESTRICTION s f) = RESTRICTION s f := @HolLightLean.hol_opam.thm_RESTRICTION_IDEMP holTheoryInst

theorem hol_IMAGE_RESTRICTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s t : Set A),
    s ⊆ t → RESTRICTION t f '' s = f '' s := @HolLightLean.hol_opam.thm_IMAGE_RESTRICTION holTheoryInst

theorem hol_RESTRICTION_COMPOSE_RIGHT : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (f : A → B) (g : B → C) (s : Set A),
    RESTRICTION s (g ∘ RESTRICTION s f) = RESTRICTION s (g ∘ f) := @HolLightLean.hol_opam.thm_RESTRICTION_COMPOSE_RIGHT holTheoryInst

theorem hol_RESTRICTION_COMPOSE_LEFT : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (f : A → B) (g : B → C) (s : Set A)
    (t : Set B), f '' s ⊆ t → RESTRICTION s (RESTRICTION t g ∘ f) = RESTRICTION s (g ∘ f) := @HolLightLean.hol_opam.thm_RESTRICTION_COMPOSE_LEFT holTheoryInst

theorem hol_RESTRICTION_COMPOSE : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (f : A → B) (g : B → C) (s : Set A)
    (t : Set B), f '' s ⊆ t → RESTRICTION s (RESTRICTION t g ∘ RESTRICTION s f) = RESTRICTION s (g ∘ f) := @HolLightLean.hol_opam.thm_RESTRICTION_COMPOSE holTheoryInst

theorem hol_RESTRICTION_UNIQUE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f g : A → B),
    (RESTRICTION s f = g) = (EXTENSIONAL s g ∧ ∀ x ∈ s, f x = g x) := @HolLightLean.hol_opam.thm_RESTRICTION_UNIQUE holTheoryInst

theorem hol_RESTRICTION_UNIQUE_ALT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f g : A → B),
    (f = RESTRICTION s g) = (EXTENSIONAL s f ∧ ∀ x ∈ s, f x = g x) := @HolLightLean.hol_opam.thm_RESTRICTION_UNIQUE_ALT holTheoryInst

theorem hol_cartesian_product : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop),
    @Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
      (@id (Set (K → A)) fun (GEN_PVAR_142 : K → A) ↦
        ∃ (f : K → A),
          @setOf (K → A)
            (fun (x' : K → A) ↦
              And
                (And (@EXTENSIONAL K A inst_1 inst k f)
                  (∀ (i : K),
                    @Membership.mem K (Set K) (@Set.instMembership K) k i →
                      @Membership.mem A (Set A) (@Set.instMembership A) (s i) (f i)))
                (@Eq (K → A) GEN_PVAR_142 x'))
            f) := @HolLightLean.hol_opam.thm_cartesian_product holTheoryInst

theorem hol_IN_CARTESIAN_PRODUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop) (x : K → A),
    @Eq Prop
      (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s) x)
      (And (@EXTENSIONAL K A inst_1 inst k x)
        (∀ (i : K),
          @Membership.mem K (Set K) (@Set.instMembership K) k i →
            @Membership.mem A (Set A) (@Set.instMembership A) (s i) (x i))) := @HolLightLean.hol_opam.thm_IN_CARTESIAN_PRODUCT holTheoryInst

theorem hol_CARTESIAN_PRODUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop),
    @Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
      (@id (Set (K → A)) fun (GEN_PVAR_143 : K → A) ↦
        ∃ (f : K → A),
          @setOf (K → A)
            (fun (x' : K → A) ↦
              And
                (∀ (i : K),
                  @Membership.mem A (Set A) (@Set.instMembership A)
                    (@ite (Set A) (@Membership.mem K (Set K) (@Set.instMembership K) k i)
                      (Classical.propDecidable (@Membership.mem K (Set K) (@Set.instMembership K) k i)) (s i)
                      (@insert A (Set A) (@Set.instInsert A) (@ARB A inst)
                        (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                    (f i))
                (@Eq (K → A) GEN_PVAR_143 x'))
            f) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT holTheoryInst

theorem hol_RESTRICTION_IN_CARTESIAN_PRODUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop) (f : K → A),
    @Eq Prop
      (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s)
        (@RESTRICTION K A inst_1 inst k f))
      (∀ (i : K),
        @Membership.mem K (Set K) (@Set.instMembership K) k i →
          @Membership.mem A (Set A) (@Set.instMembership A) (s i) (f i)) := @HolLightLean.hol_opam.thm_RESTRICTION_IN_CARTESIAN_PRODUCT holTheoryInst

theorem hol_CARTESIAN_PRODUCT_AS_RESTRICTIONS : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop),
    @Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
      (@id (Set (K → A)) fun (GEN_PVAR_144 : K → A) ↦
        ∃ (f : K → A),
          @setOf (K → A)
            (fun (x' : K → A) ↦
              And
                (∀ (i : K),
                  @Membership.mem K (Set K) (@Set.instMembership K) k i →
                    @Membership.mem A (Set A) (@Set.instMembership A) (s i) (f i))
                (@Eq (K → A) GEN_PVAR_144 x'))
            (@RESTRICTION K A inst_1 inst k f)) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_AS_RESTRICTIONS holTheoryInst

theorem hol_CARTESIAN_PRODUCT_EQ_EMPTY : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop),
    @Eq Prop
      (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
        (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A))))
      (∃ (i : K),
        And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
          (@Eq (Set A) (s i) (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_EQ_EMPTY holTheoryInst

theorem hol_CARTESIAN_PRODUCT_EMPTY : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (s : K → A → Prop),
    @Eq (Set (K → A))
      (@cartesian_product A K inst inst_1 (@EmptyCollection.emptyCollection (Set K) (@Set.instEmptyCollection K)) s)
      (@insert (K → A) (Set (K → A)) (@Set.instInsert (K → A)) (fun (i : K) ↦ @ARB A inst)
        (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A)))) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_EMPTY holTheoryInst

theorem hol_CARTESIAN_PRODUCT_EQ_MEMBERS : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop) (x y : K → A),
    And (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s) x)
        (And
          (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s)
            y)
          (∀ (i : K), @Membership.mem K (Set K) (@Set.instMembership K) k i → @Eq A (x i) (y i))) →
      @Eq (K → A) x y := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_EQ_MEMBERS holTheoryInst

theorem hol_CARTESIAN_PRODUCT_EQ_MEMBERS_EQ : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop) (x y : K → A),
    And (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s) x)
        (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s)
          y) →
      @Eq Prop (@Eq (K → A) x y) (∀ (i : K), @Membership.mem K (Set K) (@Set.instMembership K) k i → @Eq A (x i) (y i)) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_EQ_MEMBERS_EQ holTheoryInst

theorem hol_SUBSET_CARTESIAN_PRODUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s t : K → A → Prop),
    @Eq Prop
      (@Subset (Set (K → A)) (@Set.instHasSubset (K → A)) (@cartesian_product A K inst inst_1 k s)
        (@cartesian_product A K inst inst_1 k t))
      (Or
        (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
          (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A))))
        (∀ (i : K),
          @Membership.mem K (Set K) (@Set.instMembership K) k i → @Subset (Set A) (@Set.instHasSubset A) (s i) (t i))) := @HolLightLean.hol_opam.thm_SUBSET_CARTESIAN_PRODUCT holTheoryInst

theorem hol_CARTESIAN_PRODUCT_EQ : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s t : K → A → Prop),
    @Eq Prop (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s) (@cartesian_product A K inst inst_1 k t))
      (Or
        (And
          (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
            (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A))))
          (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k t)
            (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A)))))
        (∀ (i : K), @Membership.mem K (Set K) (@Set.instMembership K) k i → @Eq (Set A) (s i) (t i))) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_EQ holTheoryInst

theorem hol_INTER_CARTESIAN_PRODUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s t : K → A → Prop),
    @Eq (Set (K → A))
      (@Inter.inter (Set (K → A)) (@Set.instInter (K → A)) (@cartesian_product A K inst inst_1 k s)
        (@cartesian_product A K inst inst_1 k t))
      (@cartesian_product A K inst inst_1 k fun (i : K) ↦ @Inter.inter (Set A) (@Set.instInter A) (s i) (t i)) := @HolLightLean.hol_opam.thm_INTER_CARTESIAN_PRODUCT holTheoryInst

theorem hol_CARTESIAN_PRODUCT_UNIV : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K],
    Eq (α := Set (K → A)) (cartesian_product Set.univ fun (i : K) ↦ Set.univ) Set.univ := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_UNIV holTheoryInst

theorem hol_CARTESIAN_PRODUCT_SINGS : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (x : K → A),
    @EXTENSIONAL K A inst_1 inst k x →
      @Eq (Set (K → A))
        (@cartesian_product A K inst inst_1 k fun (i : K) ↦
          @insert A (Set A) (@Set.instInsert A) (x i)
            (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
        (@insert (K → A) (Set (K → A)) (@Set.instInsert (K → A)) x
          (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A)))) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_SINGS holTheoryInst

theorem hol_CARTESIAN_PRODUCT_SINGS_GEN : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (x : K → A),
    @Eq (Set (K → A))
      (@cartesian_product A K inst inst_1 k fun (i : K) ↦
        @insert A (Set A) (@Set.instInsert A) (x i)
          (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
      (@insert (K → A) (Set (K → A)) (@Set.instInsert (K → A)) (@RESTRICTION K A inst_1 inst k x)
        (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A)))) := @HolLightLean.hol_opam.thm_CARTESIAN_PRODUCT_SINGS_GEN holTheoryInst

theorem hol_IMAGE_PROJECTION_CARTESIAN_PRODUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (k : Set K) (s : K → A → Prop) (i : K),
    @Eq (Set A) (@Set.image (K → A) A (fun (x : K → A) ↦ x i) (@cartesian_product A K inst inst_1 k s))
      (@ite (Set A)
        (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
          (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A))))
        (Classical.propDecidable
          (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
            (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A)))))
        (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))
        (@ite (Set A) (@Membership.mem K (Set K) (@Set.instMembership K) k i)
          (Classical.propDecidable (@Membership.mem K (Set K) (@Set.instMembership K) k i)) (s i)
          (@insert A (Set A) (@Set.instInsert A) (@ARB A inst)
            (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))) := @HolLightLean.hol_opam.thm_IMAGE_PROJECTION_CARTESIAN_PRODUCT holTheoryInst

theorem hol_FORALL_CARTESIAN_PRODUCT_ELEMENTS : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (P : K → A → Prop) (k : Set K) (s : K → A → Prop),
    @Eq Prop
      (∀ (z : K → A) (i : K),
        And
            (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A))
              (@cartesian_product A K inst inst_1 k s) z)
            (@Membership.mem K (Set K) (@Set.instMembership K) k i) →
          P i (z i))
      (Or
        (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
          (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A))))
        (∀ (i : K) (x : A),
          And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
              (@Membership.mem A (Set A) (@Set.instMembership A) (s i) x) →
            P i x)) := @HolLightLean.hol_opam.thm_FORALL_CARTESIAN_PRODUCT_ELEMENTS holTheoryInst

theorem hol_FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (P : K → A → Prop) (k : Set K) (s : K → A → Prop),
    Not
        (@Eq (Set (K → A)) (@cartesian_product A K inst inst_1 k s)
          (@EmptyCollection.emptyCollection (Set (K → A)) (@Set.instEmptyCollection (K → A)))) →
      @Eq Prop
        (∀ (i : K) (x : A),
          And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
              (@Membership.mem A (Set A) (@Set.instMembership A) (s i) x) →
            P i x)
        (∀ (z : K → A) (i : K),
          And
              (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A))
                (@cartesian_product A K inst inst_1 k s) z)
              (@Membership.mem K (Set K) (@Set.instMembership K) k i) →
            P i (z i)) := @HolLightLean.hol_opam.thm_FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ holTheoryInst

theorem hol_EXISTS_CARTESIAN_PRODUCT_ELEMENT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (P : K → A → Prop) (k : Set K) (s : K → A → Prop),
    @Eq Prop
      (∃ (z : K → A),
        And
          (@Membership.mem (K → A) (Set (K → A)) (@Set.instMembership (K → A)) (@cartesian_product A K inst inst_1 k s)
            z)
          (∀ (i : K), @Membership.mem K (Set K) (@Set.instMembership K) k i → P i (z i)))
      (∀ (i : K),
        @Membership.mem K (Set K) (@Set.instMembership K) k i →
          ∃ (x : A), And (@Membership.mem A (Set A) (@Set.instMembership A) (s i) x) (P i x)) := @HolLightLean.hol_opam.thm_EXISTS_CARTESIAN_PRODUCT_ELEMENT holTheoryInst

theorem hol_product_map : 
  ∀ {A B K : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty K] (k : Set K) (f : K → A → B),
    product_map k f = fun (x : K → A) ↦ RESTRICTION k fun (i : K) ↦ f i (x i) := @HolLightLean.hol_opam.thm_product_map holTheoryInst

theorem hol_PRODUCT_MAP_RESTRICTION : 
  ∀ {A B K : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty K] (f : K → A → B) (k : Set K)
    (x : K → A), product_map k f (RESTRICTION k x) = RESTRICTION k fun (i : K) ↦ f i (x i) := @HolLightLean.hol_opam.thm_PRODUCT_MAP_RESTRICTION holTheoryInst

theorem hol_IMAGE_PRODUCT_MAP : 
  ∀ {A B K : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty K] (f : K → A → B) (k : Set K)
    (s : K → A → Prop), product_map k f '' cartesian_product k s = cartesian_product k fun (i : K) ↦ f i '' s i := @HolLightLean.hol_opam.thm_IMAGE_PRODUCT_MAP holTheoryInst

theorem hol_disjoint_union : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s : K → A → Prop),
    @Eq (Set (Prod K A))
      (@setOf (Prod K A) fun (x : Prod K A) ↦
        @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (s i x))
      (@id (Set (Prod K A)) fun (GEN_PVAR_145 : Prod K A) ↦
        ∃ (i : K) (x : A),
          @setOf (Prod K A)
            (fun (x' : Prod K A) ↦
              And
                (And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
                  (@Membership.mem A (Set A) (@Set.instMembership A) (s i) x))
                (@Eq (Prod K A) GEN_PVAR_145 x'))
            (@Prod.mk K A i x)) := @HolLightLean.hol_opam.thm_disjoint_union holTheoryInst

theorem hol_SUBSET_DISJOINT_UNION : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s t : K → A → Prop),
    @Eq Prop
      (@Subset (Set (Prod K A)) (@Set.instHasSubset (Prod K A))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (s i x))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (t i x)))
      (∀ (i : K),
        @Membership.mem K (Set K) (@Set.instMembership K) k i → @Subset (Set A) (@Set.instHasSubset A) (s i) (t i)) := @HolLightLean.hol_opam.thm_SUBSET_DISJOINT_UNION holTheoryInst

theorem hol_DISJOINT_UNION_EQ : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s t : K → A → Prop),
    Eq (α := Set (K × A)) {(i, x) : K × A | k i ∧ s i x} {(i, x) : K × A | k i ∧ t i x} = ∀ i ∈ k, s i = t i := @HolLightLean.hol_opam.thm_DISJOINT_UNION_EQ holTheoryInst

theorem hol_SUBSET_DISJOINT_UNION_EXISTS : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s : K → A → Prop) (u : Set (Prod K A)),
    @Eq Prop
      (@Subset (Set (Prod K A)) (@Set.instHasSubset (Prod K A)) u
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (s i x)))
      (∃ (t : K → A → Prop),
        And
          (@Eq (Set (Prod K A)) u
            (@setOf (Prod K A) fun (x : Prod K A) ↦
              @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (t i x)))
          (∀ (i : K),
            @Membership.mem K (Set K) (@Set.instMembership K) k i → @Subset (Set A) (@Set.instHasSubset A) (t i) (s i))) := @HolLightLean.hol_opam.thm_SUBSET_DISJOINT_UNION_EXISTS holTheoryInst

theorem hol_INTER_DISJOINT_UNION : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s t : K → A → Prop),
    @Eq (Set (Prod K A))
      (@Inter.inter (Set (Prod K A)) (@Set.instInter (Prod K A))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (s i x))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (t i x)))
      (@setOf (Prod K A) fun (x : Prod K A) ↦
        @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦
          And (k i) ((fun (i : K) ↦ @Inter.inter (Set A) (@Set.instInter A) (s i) (t i)) i x)) := @HolLightLean.hol_opam.thm_INTER_DISJOINT_UNION holTheoryInst

theorem hol_UNION_DISJOINT_UNION : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s t : K → A → Prop),
    @Eq (Set (Prod K A))
      (@Union.union (Set (Prod K A)) (@Set.instUnion (Prod K A))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (s i x))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (t i x)))
      (@setOf (Prod K A) fun (x : Prod K A) ↦
        @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦
          And (k i) ((fun (i : K) ↦ @Union.union (Set A) (@Set.instUnion A) (s i) (t i)) i x)) := @HolLightLean.hol_opam.thm_UNION_DISJOINT_UNION holTheoryInst

theorem hol_DISJOINT_UNION_EQ_EMPTY : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s : K → A → Prop),
    @Eq Prop
      (@Eq (Set (Prod K A))
        (@setOf (Prod K A) fun (x : Prod K A) ↦
          @holTheoryInst.match_1 A K (fun (x : Prod K A) ↦ Prop) x fun (i : K) (x : A) ↦ And (k i) (s i x))
        (@EmptyCollection.emptyCollection (Set (Prod K A)) (@Set.instEmptyCollection (Prod K A))))
      (∀ (i : K),
        @Membership.mem K (Set K) (@Set.instMembership K) k i →
          @Eq (Set A) (s i) (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))) := @HolLightLean.hol_opam.thm_DISJOINT_UNION_EQ_EMPTY holTheoryInst

theorem hol_DISJOINT_DISJOINT_UNION : 
  ∀ {A K : Type} [Nonempty A] [Nonempty K] (k : Set K) (s t : K → A → Prop),
    Disjoint (α := Set (K × A)) {(i, x) : K × A | k i ∧ s i x} {(i, x) : K × A | k i ∧ t i x} =
      ∀ i ∈ k, Disjoint (s i) (t i) := @HolLightLean.hol_opam.thm_DISJOINT_DISJOINT_UNION holTheoryInst

theorem hol_HAS_SIZE_FUNSPACE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (d : B) (n : ℕ) (t : Set B) (m : ℕ) (s : Set A),
    (s.Finite ∧ s.ncard = m) ∧ t.Finite ∧ t.ncard = n →
      Set.Finite (α := A → B)
          (id fun (GEN_PVAR_150 : A → B) ↦
            ∃ (f : A → B), {x' : A → B | ((∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = d) ∧ GEN_PVAR_150 = x'} f) ∧
        Set.ncard (α := A → B)
            (id fun (GEN_PVAR_150 : A → B) ↦
              ∃ (f : A → B), {x' : A → B | ((∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = d) ∧ GEN_PVAR_150 = x'} f) =
          n ^ m := @HolLightLean.hol_opam.thm_HAS_SIZE_FUNSPACE holTheoryInst

theorem hol_CARD_FUNSPACE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (d : B) (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      CARD (A := A → B)
          (id fun (GEN_PVAR_151 : A → B) ↦
            ∃ (f : A → B), {x' : A → B | ((∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = d) ∧ GEN_PVAR_151 = x'} f) =
        CARD t ^ CARD s := @HolLightLean.hol_opam.thm_CARD_FUNSPACE holTheoryInst

theorem hol_FINITE_FUNSPACE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (d : B) (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      Set.Finite (α := A → B)
        (id fun (GEN_PVAR_152 : A → B) ↦
          ∃ (f : A → B), {x' : A → B | ((∀ x ∈ s, f x ∈ t) ∧ ∀ x ∉ s, f x = d) ∧ GEN_PVAR_152 = x'} f) := @HolLightLean.hol_opam.thm_FINITE_FUNSPACE holTheoryInst

theorem hol_HAS_SIZE_FUNSPACE_UNIV : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (m n : ℕ),
    (Set.Finite (α := A) Set.univ ∧ Set.ncard (α := A) Set.univ = m) ∧
        Set.Finite (α := B) Set.univ ∧ Set.ncard (α := B) Set.univ = n →
      Set.Finite (α := A → B) Set.univ ∧ Set.ncard (α := A → B) Set.univ = n ^ m := @HolLightLean.hol_opam.thm_HAS_SIZE_FUNSPACE_UNIV holTheoryInst

theorem hol_CARD_FUNSPACE_UNIV : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Set.Finite (α := A) Set.univ ∧ Set.Finite (α := B) Set.univ →
      CARD (A := A → B) Set.univ = CARD (A := B) Set.univ ^ CARD (A := A) Set.univ := @HolLightLean.hol_opam.thm_CARD_FUNSPACE_UNIV holTheoryInst

theorem hol_FINITE_FUNSPACE_UNIV : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    Set.Finite (α := A) Set.univ ∧ Set.Finite (α := B) Set.univ → Set.Finite (α := A → B) Set.univ := @HolLightLean.hol_opam.thm_FINITE_FUNSPACE_UNIV holTheoryInst

theorem hol_HAS_SIZE_BOOL : 
  Set.Finite (α := Prop) Set.univ ∧
    Set.ncard (α := Prop) Set.univ = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_HAS_SIZE_BOOL holTheoryInst

theorem hol_CARD_BOOL : 
  CARD (A := Prop) Set.univ = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_CARD_BOOL holTheoryInst

theorem hol_FINITE_BOOL : 
  Set.Finite (α := Prop) Set.univ := @HolLightLean.hol_opam.thm_FINITE_BOOL holTheoryInst

theorem hol_HAS_SIZE_POWERSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (n : ℕ),
    s.Finite ∧ s.ncard = n →
      Set.Finite (α := Set A)
          (id fun (GEN_PVAR_155 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ⊆ s ∧ GEN_PVAR_155 = x'} t) ∧
        Set.ncard (α := Set A)
            (id fun (GEN_PVAR_155 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ⊆ s ∧ GEN_PVAR_155 = x'} t) =
          ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ^ n := @HolLightLean.hol_opam.thm_HAS_SIZE_POWERSET holTheoryInst

theorem hol_CARD_POWERSET : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    s.Finite →
      CARD (A := Set A) (id fun (GEN_PVAR_156 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ⊆ s ∧ GEN_PVAR_156 = x'} t) =
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ^ CARD s := @HolLightLean.hol_opam.thm_CARD_POWERSET holTheoryInst

theorem hol_FINITE_POWERSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    s.Finite →
      Set.Finite (α := Set A)
        (id fun (GEN_PVAR_157 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ⊆ s ∧ GEN_PVAR_157 = x'} t) := @HolLightLean.hol_opam.thm_FINITE_POWERSET holTheoryInst

theorem hol_FINITE_POWERSET_EQ : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    Set.Finite (α := Set A)
        (id fun (GEN_PVAR_158 : Set A) ↦ ∃ (t : Set A), {x' : Set A | t ⊆ s ∧ GEN_PVAR_158 = x'} t) =
      s.Finite := @HolLightLean.hol_opam.thm_FINITE_POWERSET_EQ holTheoryInst

theorem hol_FINITE_RESTRICTED_SUBSETS : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    s.Finite →
      Set.Finite (α := Set A)
        (id fun (GEN_PVAR_160 : Set A) ↦ ∃ (t : Set A), {x' : Set A | (t ⊆ s ∧ P t) ∧ GEN_PVAR_160 = x'} t) := @HolLightLean.hol_opam.thm_FINITE_RESTRICTED_SUBSETS holTheoryInst

theorem hol_FINITE_UNIONS : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)), (⋃₀ s).Finite = (s.Finite ∧ ∀ t ∈ s, t.Finite) := @HolLightLean.hol_opam.thm_FINITE_UNIONS holTheoryInst

theorem hol_FINITE_CARD_LE_UNIONS : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : A → B → Prop) (m n : ℕ),
    (∀ x ∈ s, Set.Finite (t x) ∧ CARD (t x) ≤ n) ∧ s.Finite ∧ CARD s ≤ m →
      Set.Finite (α := B)
          (⋃₀ id fun (GEN_PVAR_161 : Set B) ↦ ∃ (x : A), {x' : Set B | x ∈ s ∧ GEN_PVAR_161 = x'} (t x)) ∧
        CARD (A := B) (⋃₀ id fun (GEN_PVAR_162 : Set B) ↦ ∃ (x : A), {x' : Set B | x ∈ s ∧ GEN_PVAR_162 = x'} (t x)) ≤
          m * n := @HolLightLean.hol_opam.thm_FINITE_CARD_LE_UNIONS holTheoryInst

theorem hol_POWERSET_CLAUSES : 
  ∀ {A : Type} [Nonempty A],
    Eq (α := Set (Set A)) (id fun (GEN_PVAR_163 : Set A) ↦ ∃ (s : Set A), {x' : Set A | s ⊆ ∅ ∧ GEN_PVAR_163 = x'} s)
        (insert ∅ ∅) ∧
      ∀ (a : A) (t : Set A),
        Eq (α := Set (Set A))
          (id fun (GEN_PVAR_164 : Set A) ↦ ∃ (s : Set A), {x' : Set A | s ⊆ insert a t ∧ GEN_PVAR_164 = x'} s)
          ((id fun (GEN_PVAR_165 : Set A) ↦ ∃ (s : Set A), {x' : Set A | s ⊆ t ∧ GEN_PVAR_165 = x'} s) ∪
            (fun (s : Set A) ↦ insert a s) ''
              id fun (GEN_PVAR_166 : Set A) ↦ ∃ (s : Set A), {x' : Set A | s ⊆ t ∧ GEN_PVAR_166 = x'} s) := @HolLightLean.hol_opam.thm_POWERSET_CLAUSES holTheoryInst

theorem hol_FINITE_IMAGE_INFINITE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A),
    ¬s.Finite ∧ (f '' s).Finite →
      ∃ a ∈ s,
        ¬Set.Finite (α := A)
            (id fun (GEN_PVAR_171 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = f a) ∧ GEN_PVAR_171 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_IMAGE_INFINITE holTheoryInst

theorem hol_FINITE_RESTRICTED_POWERSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (n : ℕ),
    Set.Finite (α := Set A)
        (id fun (GEN_PVAR_176 : Set A) ↦
          ∃ (t : Set A), {x' : Set A | (t ⊆ s ∧ t.Finite ∧ t.ncard = n) ∧ GEN_PVAR_176 = x'} t) =
      (s.Finite ∨ n = (0 : ℕ)) := @HolLightLean.hol_opam.thm_FINITE_RESTRICTED_POWERSET holTheoryInst

theorem hol_FINITE_RESTRICTED_FUNSPACE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (k : A → B),
    And (@Set.Finite A s) (@Set.Finite B t) →
      @Set.Finite (A → B)
        (@id (Set (A → B)) fun (GEN_PVAR_180 : A → B) ↦
          ∃ (f : A → B),
            @setOf (A → B)
              (fun (x' : A → B) ↦
                And
                  (And (@Subset (Set B) (@Set.instHasSubset B) (@Set.image A B f s) t)
                    (@Subset (Set A) (@Set.instHasSubset A)
                      (@id (Set A) fun (GEN_PVAR_179 : A) ↦
                        ∃ (x : A), @setOf A (fun (x' : A) ↦ And (Not (@Eq B (f x) (k x))) (@Eq A GEN_PVAR_179 x')) x)
                      s))
                  (@Eq (A → B) GEN_PVAR_180 x'))
              f) := @HolLightLean.hol_opam.thm_FINITE_RESTRICTED_FUNSPACE holTheoryInst

theorem hol_NUMSEG_CLAUSES_LT : 
  Eq (α := Set ℕ) (id fun (GEN_PVAR_181 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < (0 : ℕ) ∧ GEN_PVAR_181 = x'} i) ∅ ∧
    ∀ (k : ℕ),
      Eq (α := Set ℕ) (id fun (GEN_PVAR_182 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k + (1 : ℕ) ∧ GEN_PVAR_182 = x'} i)
        (insert k (id fun (GEN_PVAR_183 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k ∧ GEN_PVAR_183 = x'} i)) := @HolLightLean.hol_opam.thm_NUMSEG_CLAUSES_LT holTheoryInst

theorem hol_HAS_SIZE_NUMSEG_LT : 
  ∀ (n : ℕ),
    Set.Finite (α := ℕ) (id fun (GEN_PVAR_184 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m < n ∧ GEN_PVAR_184 = x'} m) ∧
      Set.ncard (α := ℕ) (id fun (GEN_PVAR_184 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m < n ∧ GEN_PVAR_184 = x'} m) = n := @HolLightLean.hol_opam.thm_HAS_SIZE_NUMSEG_LT holTheoryInst

theorem hol_CARD_NUMSEG_LT : 
  ∀ (n : ℕ), CARD (A := ℕ) (id fun (GEN_PVAR_185 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m < n ∧ GEN_PVAR_185 = x'} m) = n := @HolLightLean.hol_opam.thm_CARD_NUMSEG_LT holTheoryInst

theorem hol_FINITE_NUMSEG_LT : 
  ∀ (n : ℕ), Set.Finite (α := ℕ) (id fun (GEN_PVAR_186 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m < n ∧ GEN_PVAR_186 = x'} m) := @HolLightLean.hol_opam.thm_FINITE_NUMSEG_LT holTheoryInst

theorem hol_NUMSEG_CLAUSES_LE : 
  Eq (α := Set ℕ) (id fun (GEN_PVAR_187 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ (0 : ℕ) ∧ GEN_PVAR_187 = x'} i)
      (insert (0 : ℕ) ∅) ∧
    ∀ (k : ℕ),
      Eq (α := Set ℕ) (id fun (GEN_PVAR_188 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k + (1 : ℕ) ∧ GEN_PVAR_188 = x'} i)
        (insert (k + (1 : ℕ)) (id fun (GEN_PVAR_189 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k ∧ GEN_PVAR_189 = x'} i)) := @HolLightLean.hol_opam.thm_NUMSEG_CLAUSES_LE holTheoryInst

theorem hol_HAS_SIZE_NUMSEG_LE : 
  ∀ (n : ℕ),
    Set.Finite (α := ℕ) (id fun (GEN_PVAR_190 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m ≤ n ∧ GEN_PVAR_190 = x'} m) ∧
      Set.ncard (α := ℕ) (id fun (GEN_PVAR_190 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m ≤ n ∧ GEN_PVAR_190 = x'} m) =
        n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_HAS_SIZE_NUMSEG_LE holTheoryInst

theorem hol_FINITE_NUMSEG_LE : 
  ∀ (n : ℕ), Set.Finite (α := ℕ) (id fun (GEN_PVAR_191 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m ≤ n ∧ GEN_PVAR_191 = x'} m) := @HolLightLean.hol_opam.thm_FINITE_NUMSEG_LE holTheoryInst

theorem hol_CARD_NUMSEG_LE : 
  ∀ (n : ℕ),
    CARD (A := ℕ) (id fun (GEN_PVAR_192 : ℕ) ↦ ∃ (m : ℕ), {x' : ℕ | m ≤ n ∧ GEN_PVAR_192 = x'} m) =
      n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_CARD_NUMSEG_LE holTheoryInst

theorem hol_num_FINITE : 
  ∀ (s : Set ℕ), s.Finite = ∃ (a : ℕ), ∀ x ∈ s, x ≤ a := @HolLightLean.hol_opam.thm_num_FINITE holTheoryInst

theorem hol_num_FINITE_AVOID : 
  ∀ (s : Set ℕ), s.Finite → ∃ (a : ℕ), a ∉ s := @HolLightLean.hol_opam.thm_num_FINITE_AVOID holTheoryInst

theorem hol_num_INFINITE_EQ : 
  ∀ (s : Set ℕ), (¬s.Finite) = ∀ (N' : ℕ), ∃ (n : ℕ), N' ≤ n ∧ n ∈ s := @HolLightLean.hol_opam.thm_num_INFINITE_EQ holTheoryInst

theorem hol_num_INFINITE : 
  ¬Set.Finite (α := ℕ) Set.univ := @HolLightLean.hol_opam.thm_num_INFINITE holTheoryInst

theorem hol_string_INFINITE : 
  ¬Set.Finite (α := List CHAR) Set.univ := @HolLightLean.hol_opam.thm_string_INFINITE holTheoryInst

theorem hol_FINITE_REAL_INTERVAL : 
  (∀ (a : ℝ), ¬Set.Finite (α := ℝ) (id fun (GEN_PVAR_202 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | a < x ∧ GEN_PVAR_202 = x'} x)) ∧
    (∀ (a : ℝ), ¬Set.Finite (α := ℝ) (id fun (GEN_PVAR_203 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | a ≤ x ∧ GEN_PVAR_203 = x'} x)) ∧
      (∀ (b : ℝ),
          ¬Set.Finite (α := ℝ) (id fun (GEN_PVAR_204 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | x < b ∧ GEN_PVAR_204 = x'} x)) ∧
        (∀ (b : ℝ),
            ¬Set.Finite (α := ℝ) (id fun (GEN_PVAR_205 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | x ≤ b ∧ GEN_PVAR_205 = x'} x)) ∧
          (∀ (a b : ℝ),
              Set.Finite (α := ℝ)
                  (id fun (GEN_PVAR_206 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | (a < x ∧ x < b) ∧ GEN_PVAR_206 = x'} x) =
                (b ≤ a)) ∧
            (∀ (a b : ℝ),
                Set.Finite (α := ℝ)
                    (id fun (GEN_PVAR_207 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | (a ≤ x ∧ x < b) ∧ GEN_PVAR_207 = x'} x) =
                  (b ≤ a)) ∧
              (∀ (a b : ℝ),
                  Set.Finite (α := ℝ)
                      (id fun (GEN_PVAR_208 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | (a < x ∧ x ≤ b) ∧ GEN_PVAR_208 = x'} x) =
                    (b ≤ a)) ∧
                ∀ (a b : ℝ),
                  Set.Finite (α := ℝ)
                      (id fun (GEN_PVAR_209 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | (a ≤ x ∧ x ≤ b) ∧ GEN_PVAR_209 = x'} x) =
                    (b ≤ a) := @HolLightLean.hol_opam.thm_FINITE_REAL_INTERVAL holTheoryInst

theorem hol_real_INFINITE : 
  ¬Set.Finite (α := ℝ) Set.univ := @HolLightLean.hol_opam.thm_real_INFINITE holTheoryInst

theorem hol_HAS_SIZE_INDEX : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (n : ℕ),
    s.Finite ∧ s.ncard = n → ∃ (f : ℕ → A), (∀ m < n, f m ∈ s) ∧ ∀ x ∈ s, ∃! m : ℕ, m < n ∧ f m = x := @HolLightLean.hol_opam.thm_HAS_SIZE_INDEX holTheoryInst

theorem hol_INFINITE_ENUMERATE : 
  ∀ (s : Set ℕ), ¬s.Finite → ∃ (r : ℕ → ℕ), (∀ (m n : ℕ), m < n → r m < r n) ∧ r '' Set.univ = s := @HolLightLean.hol_opam.thm_INFINITE_ENUMERATE holTheoryInst

theorem hol_INFINITE_ENUMERATE_EQ : 
  ∀ (s : Set ℕ), (¬s.Finite) = ∃ (r : ℕ → ℕ), (∀ (m n : ℕ), m < n → r m < r n) ∧ r '' Set.univ = s := @HolLightLean.hol_opam.thm_INFINITE_ENUMERATE_EQ holTheoryInst

theorem hol_INFINITE_ENUMERATE_SUBSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    (¬s.Finite) = ∃ (f : ℕ → A), (∀ (x : ℕ), f x ∈ s) ∧ ∀ (x y : ℕ), f x = f y → x = y := @HolLightLean.hol_opam.thm_INFINITE_ENUMERATE_SUBSET holTheoryInst

theorem hol_set_of_list : 
  ∀ {A : Type} [Nonempty A] (h : A) (t : List A),
    And
      (@Eq (Set A)
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
          (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) (@List.nil A)))
        (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
      (@Eq (Set A)
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
          (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) (@List.cons A h t)))
        (@insert A (Set A) (@Set.instInsert A) h
          (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
            (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) t)))) := @HolLightLean.hol_opam.thm_set_of_list holTheoryInst

theorem hol_list_of_set : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    list_of_set s = Classical.epsilon fun (l : List A) ↦ ↑l.toFinset = s ∧ l.length = CARD s := @HolLightLean.hol_opam.thm_list_of_set holTheoryInst

theorem hol_LIST_OF_SET_PROPERTIES : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    s.Finite → ↑(list_of_set s).toFinset = s ∧ (list_of_set s).length = CARD s := @HolLightLean.hol_opam.thm_LIST_OF_SET_PROPERTIES holTheoryInst

theorem hol_SET_OF_LIST_OF_SET : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s.Finite → ↑(list_of_set s).toFinset = s := @HolLightLean.hol_opam.thm_SET_OF_LIST_OF_SET holTheoryInst

theorem hol_LENGTH_LIST_OF_SET : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s.Finite → (list_of_set s).length = CARD s := @HolLightLean.hol_opam.thm_LENGTH_LIST_OF_SET holTheoryInst

theorem hol_MEM_LIST_OF_SET : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A), s.Finite → ∀ (x : A), (x ∈ list_of_set s) = (x ∈ s) := @HolLightLean.hol_opam.thm_MEM_LIST_OF_SET holTheoryInst

theorem hol_FINITE_SET_OF_LIST : 
  ∀ {A : Type} [Nonempty A] (l : List A),
    @Set.Finite A
      (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
        (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l)) := @HolLightLean.hol_opam.thm_FINITE_SET_OF_LIST holTheoryInst

theorem hol_IN_SET_OF_LIST : 
  ∀ {A : Type} [Nonempty A] (x : A) (l : List A), (x ∈ ↑l.toFinset) = (x ∈ l) := @HolLightLean.hol_opam.thm_IN_SET_OF_LIST holTheoryInst

theorem hol_SET_OF_LIST_APPEND : 
  ∀ {A : Type} [Nonempty A] (l1 l2 : List A),
    @Eq (Set A)
      (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
        (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) (@List.append A l1 l2)))
      (@Union.union (Set A) (@Set.instUnion A)
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
          (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l1))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
          (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l2))) := @HolLightLean.hol_opam.thm_SET_OF_LIST_APPEND holTheoryInst

theorem hol_SET_OF_LIST_MAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (l : List A), ↑(List.map f l).toFinset = f '' ↑l.toFinset := @HolLightLean.hol_opam.thm_SET_OF_LIST_MAP holTheoryInst

theorem hol_SET_OF_LIST_EQ_EMPTY : 
  ∀ {A : Type} [Nonempty A] (l : List A),
    @Eq Prop
      (@Eq (Set A)
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
          (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l))
        (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
      (@Eq (List A) l (@List.nil A)) := @HolLightLean.hol_opam.thm_SET_OF_LIST_EQ_EMPTY holTheoryInst

theorem hol_LIST_OF_SET_EMPTY : 
  ∀ {A : Type} [inst : Nonempty A],
    @Eq (List A) (@list_of_set A inst (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
      (@List.nil A) := @HolLightLean.hol_opam.thm_LIST_OF_SET_EMPTY holTheoryInst

theorem hol_LIST_OF_SET_SING : 
  ∀ {A : Type} [inst : Nonempty A] (a : A),
    @Eq (List A)
      (@list_of_set A inst
        (@insert A (Set A) (@Set.instInsert A) a
          (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
      (@List.cons A a (@List.nil A)) := @HolLightLean.hol_opam.thm_LIST_OF_SET_SING holTheoryInst

theorem hol_pairwise : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (r : A → A → Prop),
    Eq (α := Prop) (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → r x y) (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → r x y) := @HolLightLean.hol_opam.thm_pairwise holTheoryInst

theorem hol_PAIRWISE_EMPTY : 
  ∀ {A : Type} [Nonempty A] (r : A → A → Prop),
    (∀ (x y : A), Membership.mem (γ := Set A) ∅ x ∧ Membership.mem (γ := Set A) ∅ y ∧ ¬x = y → r x y) = True := @HolLightLean.hol_opam.thm_PAIRWISE_EMPTY holTheoryInst

theorem hol_PAIRWISE_SING : 
  ∀ {A : Type} [Nonempty A] (r : A → A → Prop) (x : A),
    (∀ (x_1 y : A),
        Membership.mem (γ := Set A) (insert x ∅) x_1 ∧ Membership.mem (γ := Set A) (insert x ∅) y ∧ ¬x_1 = y →
          r x_1 y) =
      True := @HolLightLean.hol_opam.thm_PAIRWISE_SING holTheoryInst

theorem hol_PAIRWISE_IMP : 
  ∀ {A : Type} [Nonempty A] (P Q : A → A → Prop) (s : Set A),
    ((∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → P x y) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ P x y ∧ ¬x = y → Q x y) →
      ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → Q x y := @HolLightLean.hol_opam.thm_PAIRWISE_IMP holTheoryInst

theorem hol_PAIRWISE_MONO : 
  ∀ {A : Type} [Nonempty A] (r : A → A → Prop) (s t : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → r x y) ∧ t ⊆ s → ∀ (x y : A), x ∈ t ∧ y ∈ t ∧ ¬x = y → r x y := @HolLightLean.hol_opam.thm_PAIRWISE_MONO holTheoryInst

theorem hol_PAIRWISE_AND : 
  ∀ {A : Type} [Nonempty A] (R' R'' : A → A → Prop) (s : Set A),
    ((∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → R' x y) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → R'' x y) =
      ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → (fun (x y : A) ↦ R' x y ∧ R'' x y) x y := @HolLightLean.hol_opam.thm_PAIRWISE_AND holTheoryInst

theorem hol_PAIRWISE_INSERT : 
  ∀ {A : Type} [Nonempty A] (r : A → A → Prop) (x : A) (s : Set A),
    (∀ (x_1 y : A), x_1 ∈ insert x s ∧ y ∈ insert x s ∧ ¬x_1 = y → r x_1 y) =
      ((∀ (y : A), y ∈ s ∧ ¬y = x → r x y ∧ r y x) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → r x y) := @HolLightLean.hol_opam.thm_PAIRWISE_INSERT holTheoryInst

theorem hol_PAIRWISE_INSERT_SYMMETRIC : 
  ∀ {A : Type} [Nonempty A] (r : A → A → Prop) (x : A) (s : Set A),
    (∀ y ∈ s, r x y = r y x) →
      (∀ (x_1 y : A), x_1 ∈ insert x s ∧ y ∈ insert x s ∧ ¬x_1 = y → r x_1 y) =
        ((∀ (y : A), y ∈ s ∧ ¬y = x → r x y) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → r x y) := @HolLightLean.hol_opam.thm_PAIRWISE_INSERT_SYMMETRIC holTheoryInst

theorem hol_PAIRWISE_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (r : B → B → Prop) (f : A → B),
    Eq (α := Prop) (∀ (x y : B), x ∈ f '' s ∧ y ∈ f '' s ∧ ¬x = y → r x y)
      (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → (fun (x y : A) ↦ ¬f x = f y → r (f x) (f y)) x y) := @HolLightLean.hol_opam.thm_PAIRWISE_IMAGE holTheoryInst

theorem hol_PAIRWISE_UNION : 
  ∀ {A : Type} [Nonempty A] (R' : A → A → Prop) (s t : Set A),
    (∀ (x y : A), x ∈ s ∪ t ∧ y ∈ s ∪ t ∧ ¬x = y → R' x y) =
      ((∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → R' x y) ∧
        (∀ (x y : A), x ∈ t ∧ y ∈ t ∧ ¬x = y → R' x y) ∧ ∀ (x y : A), x ∈ s \ t ∧ y ∈ t \ s → R' x y ∧ R' y x) := @HolLightLean.hol_opam.thm_PAIRWISE_UNION holTheoryInst

theorem hol_PAIRWISE_CHAIN_UNIONS : 
  ∀ {A : Type} [Nonempty A] (R' : A → A → Prop) (c : Set (Set A)),
    ((∀ s ∈ c, ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y → R' x y) ∧ ∀ (s t : Set A), s ∈ c ∧ t ∈ c → s ⊆ t ∨ t ⊆ s) →
      ∀ (x y : A), x ∈ ⋃₀ c ∧ y ∈ ⋃₀ c ∧ ¬x = y → R' x y := @HolLightLean.hol_opam.thm_PAIRWISE_CHAIN_UNIONS holTheoryInst

theorem hol_DIFF_UNIONS_PAIRWISE_DISJOINT : 
  ∀ {A : Type} [Nonempty A] (s t : Set (Set A)),
    (∀ (x y : Set A), x ∈ s ∧ y ∈ s ∧ ¬x = y → Disjoint x y) ∧ t ⊆ s → ⋃₀ s \ ⋃₀ t = ⋃₀ (s \ t) := @HolLightLean.hol_opam.thm_DIFF_UNIONS_PAIRWISE_DISJOINT holTheoryInst

theorem hol_INTER_UNIONS_PAIRWISE_DISJOINT : 
  ∀ {A : Type} [Nonempty A] (s t : Set (Set A)),
    (∀ (x y : Set A), x ∈ s ∪ t ∧ y ∈ s ∪ t ∧ ¬x = y → Disjoint x y) → ⋃₀ s ∩ ⋃₀ t = ⋃₀ (s ∩ t) := @HolLightLean.hol_opam.thm_INTER_UNIONS_PAIRWISE_DISJOINT holTheoryInst

theorem hol_PSUBSET_UNIONS_PAIRWISE_DISJOINT : 
  ∀ {A : Type} [Nonempty A] (u v : Set (Set A)),
    (∀ (x y : Set A), x ∈ v ∧ y ∈ v ∧ ¬x = y → Disjoint x y) ∧ u ⊂ v \ {∅} → ⋃₀ u ⊂ ⋃₀ v := @HolLightLean.hol_opam.thm_PSUBSET_UNIONS_PAIRWISE_DISJOINT holTheoryInst

theorem hol_UNION_OF : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q : Set (Set A)),
    Eq (α := Set (Set A)) {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋃₀ u = s} fun (s : Set A) ↦
      ∃ (u : Set (Set A)), P u ∧ (∀ c ∈ u, Q c) ∧ ⋃₀ u = s := @HolLightLean.hol_opam.thm_UNION_OF holTheoryInst

theorem hol_INTERSECTION_OF : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q : Set (Set A)),
    Eq (α := Set (Set A)) {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋂₀ u = s} fun (s : Set A) ↦
      ∃ (u : Set (Set A)), P u ∧ (∀ c ∈ u, Q c) ∧ ⋂₀ u = s := @HolLightLean.hol_opam.thm_INTERSECTION_OF holTheoryInst

theorem hol_UNION_OF_INC : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q : Set (Set A)) (s : Set A),
    P (insert s ∅) ∧ Q s → {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋃₀ u = s} s := @HolLightLean.hol_opam.thm_UNION_OF_INC holTheoryInst

theorem hol_INTERSECTION_OF_INC : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q : Set (Set A)) (s : Set A),
    P (insert s ∅) ∧ Q s → {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋂₀ u = s} s := @HolLightLean.hol_opam.thm_INTERSECTION_OF_INC holTheoryInst

theorem hol_UNION_OF_MONO : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q Q' : Set (Set A)) (s : Set A),
    ({s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋃₀ u = s} s ∧ ∀ (x : Set A), Q x → Q' x) → {s : Set A | ∃ u ∈ P, u ⊆ Q' ∧ ⋃₀ u = s} s := @HolLightLean.hol_opam.thm_UNION_OF_MONO holTheoryInst

theorem hol_INTERSECTION_OF_MONO : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q Q' : Set (Set A)) (s : Set A),
    ({s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋂₀ u = s} s ∧ ∀ (x : Set A), Q x → Q' x) → {s : Set A | ∃ u ∈ P, u ⊆ Q' ∧ ⋂₀ u = s} s := @HolLightLean.hol_opam.thm_INTERSECTION_OF_MONO holTheoryInst

theorem hol_FORALL_UNION_OF : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q R' : Set (Set A)),
    Eq (α := Prop) (∀ (s : Set A), {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋃₀ u = s} s → R' s)
      (∀ (t : Set (Set A)), (P t ∧ ∀ c ∈ t, Q c) → R' (⋃₀ t)) := @HolLightLean.hol_opam.thm_FORALL_UNION_OF holTheoryInst

theorem hol_FORALL_INTERSECTION_OF : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q R' : Set (Set A)),
    Eq (α := Prop) (∀ (s : Set A), {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋂₀ u = s} s → R' s)
      (∀ (t : Set (Set A)), (P t ∧ ∀ c ∈ t, Q c) → R' (⋂₀ t)) := @HolLightLean.hol_opam.thm_FORALL_INTERSECTION_OF holTheoryInst

theorem hol_UNION_OF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q : Set (Set A)), P ∅ → {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋃₀ u = s} ∅ := @HolLightLean.hol_opam.thm_UNION_OF_EMPTY holTheoryInst

theorem hol_INTERSECTION_OF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set (Set A))) (Q : Set (Set A)),
    P ∅ → {s : Set A | ∃ u ∈ P, u ⊆ Q ∧ ⋂₀ u = s} Set.univ := @HolLightLean.hol_opam.thm_INTERSECTION_OF_EMPTY holTheoryInst

theorem hol_ARBITRARY : 
  ∀ {A : Type} [Nonempty A] (s : Set (Set A)), True = True := @HolLightLean.hol_opam.thm_ARBITRARY holTheoryInst

theorem hol_ARBITRARY_UNION_OF_ALT : 
  ∀ {A : Type} [Nonempty A] (B : Set (Set A)) (s : Set A),
    {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ B ∧ ⋃₀ u = s}
        s =
      ∀ x ∈ s, ∃ u ∈ B, x ∈ u ∧ u ⊆ s := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_ALT holTheoryInst

theorem hol_ARBITRARY_UNION_OF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
      ∅ := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_EMPTY holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
      Set.univ := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_EMPTY holTheoryInst

theorem hol_ARBITRARY_UNION_OF_INC : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    P s →
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
        s := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_INC holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_INC : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    P s →
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
        s := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_INC holTheoryInst

theorem hol_ARBITRARY_UNION_OF_COMPLEMENT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
        s =
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧
              (u ⊆ fun (s' : Set A) ↦ P (Set.univ \ s')) ∧ ⋂₀ u = s}
        (Set.univ \ s) := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_COMPLEMENT holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_COMPLEMENT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
        s =
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧
              (u ⊆ fun (s' : Set A) ↦ P (Set.univ \ s')) ∧ ⋃₀ u = s}
        (Set.univ \ s) := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_COMPLEMENT holTheoryInst

theorem hol_ARBITRARY_UNION_OF_IDEMPOT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Set (Set A))
      {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧
            u ⊆
                {s : Set A |
                  ∃ (u : Set (Set A)),
                    Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s} ∧
              ⋃₀ u = s}
      {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s} := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_IDEMPOT holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_IDEMPOT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Set (Set A))
      {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧
            u ⊆
                {s : Set A |
                  ∃ (u : Set (Set A)),
                    Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s} ∧
              ⋂₀ u = s}
      {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s} := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_IDEMPOT holTheoryInst

theorem hol_ARBITRARY_UNION_OF_UNIONS : 
  ∀ {A : Type} [Nonempty A] (P u : Set (Set A)),
    (∀ s ∈ u,
        {s : Set A |
            ∃ (u : Set (Set A)),
              Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
          s) →
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
        (⋃₀ u) := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_UNIONS holTheoryInst

theorem hol_ARBITRARY_UNION_OF_UNION : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s t : Set A),
    {s : Set A |
            ∃ (u : Set (Set A)),
              Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
          s ∧
        {s : Set A |
            ∃ (u : Set (Set A)),
              Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
          t →
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
        (s ∪ t) := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_UNION holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_INTERS : 
  ∀ {A : Type} [Nonempty A] (P u : Set (Set A)),
    (∀ s ∈ u,
        {s : Set A |
            ∃ (u : Set (Set A)),
              Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
          s) →
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
        (⋂₀ u) := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_INTERS holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_INTER : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s t : Set A),
    {s : Set A |
            ∃ (u : Set (Set A)),
              Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
          s ∧
        {s : Set A |
            ∃ (u : Set (Set A)),
              Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
          t →
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
        (s ∩ t) := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_INTER holTheoryInst

theorem hol_ARBITRARY_UNION_OF_INTER_EQ : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Prop)
      (∀ (s t : Set A),
        {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
              s ∧
            {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
              t →
          {s : Set A |
              ∃ (u : Set (Set A)),
                Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
            (s ∩ t))
      (∀ (s t : Set A),
        P s ∧ P t →
          {s : Set A |
              ∃ (u : Set (Set A)),
                Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
            (s ∩ t)) := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_INTER_EQ holTheoryInst

theorem hol_ARBITRARY_UNION_OF_INTER : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (∀ (s t : Set A), P s ∧ P t → P (s ∩ t)) →
      ∀ (s t : Set A),
        {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
              s ∧
            {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
              t →
          {s : Set A |
              ∃ (u : Set (Set A)),
                Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋃₀ u = s}
            (s ∩ t) := @HolLightLean.hol_opam.thm_ARBITRARY_UNION_OF_INTER holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_UNION_EQ : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Prop)
      (∀ (s t : Set A),
        {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
              s ∧
            {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
              t →
          {s : Set A |
              ∃ (u : Set (Set A)),
                Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
            (s ∪ t))
      (∀ (s t : Set A),
        P s ∧ P t →
          {s : Set A |
              ∃ (u : Set (Set A)),
                Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
            (s ∪ t)) := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_UNION_EQ holTheoryInst

theorem hol_ARBITRARY_INTERSECTION_OF_UNION : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (∀ (s t : Set A), P s ∧ P t → P (s ∪ t)) →
      ∀ (s t : Set A),
        {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
              s ∧
            {s : Set A |
                ∃ (u : Set (Set A)),
                  Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
              t →
          {s : Set A |
              ∃ (u : Set (Set A)),
                Membership.mem (γ := Set (Set (Set A))) (fun (x : Set (Set A)) ↦ True) u ∧ u ⊆ P ∧ ⋂₀ u = s}
            (s ∪ t) := @HolLightLean.hol_opam.thm_ARBITRARY_INTERSECTION_OF_UNION holTheoryInst

theorem hol_FINITE_UNION_OF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} ∅ := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_EMPTY holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_EMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} Set.univ := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_EMPTY holTheoryInst

theorem hol_FINITE_UNION_OF_INC : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    P s → {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} s := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_INC holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_INC : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    P s → {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} s := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_INC holTheoryInst

theorem hol_FINITE_UNION_OF_COMPLEMENT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} s =
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧
              (u ⊆ fun (s' : Set A) ↦ P (Set.univ \ s')) ∧ ⋂₀ u = s}
        (Set.univ \ s) := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_COMPLEMENT holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_COMPLEMENT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s : Set A),
    {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} s =
      {s : Set A |
          ∃ (u : Set (Set A)),
            Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧
              (u ⊆ fun (s' : Set A) ↦ P (Set.univ \ s')) ∧ ⋃₀ u = s}
        (Set.univ \ s) := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_COMPLEMENT holTheoryInst

theorem hol_FINITE_UNION_OF_IDEMPOT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Set (Set A))
      {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧
            u ⊆
                {s : Set A |
                  ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} ∧
              ⋃₀ u = s}
      {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_IDEMPOT holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_IDEMPOT : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Set (Set A))
      {s : Set A |
        ∃ (u : Set (Set A)),
          Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧
            u ⊆
                {s : Set A |
                  ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} ∧
              ⋂₀ u = s}
      {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_IDEMPOT holTheoryInst

theorem hol_FINITE_UNION_OF_UNIONS : 
  ∀ {A : Type} [Nonempty A] (P u : Set (Set A)),
    (u.Finite ∧
        ∀ s ∈ u,
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s}
            s) →
      {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} (⋃₀ u) := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_UNIONS holTheoryInst

theorem hol_FINITE_UNION_OF_UNION : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s t : Set A),
    {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} s ∧
        {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} t →
      {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} (s ∪ t) := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_UNION holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_INTERS : 
  ∀ {A : Type} [Nonempty A] (P u : Set (Set A)),
    (u.Finite ∧
        ∀ s ∈ u,
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s}
            s) →
      {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} (⋂₀ u) := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_INTERS holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_INTER : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)) (s t : Set A),
    {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} s ∧
        {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} t →
      {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} (s ∩ t) := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_INTER holTheoryInst

theorem hol_FINITE_UNION_OF_INTER_EQ : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Prop)
      (∀ (s t : Set A),
        {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} s ∧
            {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s}
              t →
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s}
            (s ∩ t))
      (∀ (s t : Set A),
        P s ∧ P t →
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s}
            (s ∩ t)) := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_INTER_EQ holTheoryInst

theorem hol_FINITE_UNION_OF_INTER : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (∀ (s t : Set A), P s ∧ P t → P (s ∩ t)) →
      ∀ (s t : Set A),
        {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s} s ∧
            {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s}
              t →
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋃₀ u = s}
            (s ∩ t) := @HolLightLean.hol_opam.thm_FINITE_UNION_OF_INTER holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_UNION_EQ : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    Eq (α := Prop)
      (∀ (s t : Set A),
        {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} s ∧
            {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s}
              t →
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s}
            (s ∪ t))
      (∀ (s t : Set A),
        P s ∧ P t →
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s}
            (s ∪ t)) := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_UNION_EQ holTheoryInst

theorem hol_FINITE_INTERSECTION_OF_UNION : 
  ∀ {A : Type} [Nonempty A] (P : Set (Set A)),
    (∀ (s t : Set A), P s ∧ P t → P (s ∪ t)) →
      ∀ (s t : Set A),
        {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s} s ∧
            {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s}
              t →
          {s : Set A | ∃ (u : Set (Set A)), Membership.mem (γ := Set (Set (Set A))) Set.Finite u ∧ u ⊆ P ∧ ⋂₀ u = s}
            (s ∪ t) := @HolLightLean.hol_opam.thm_FINITE_INTERSECTION_OF_UNION holTheoryInst

theorem hol_CARD_SET_OF_LIST_LE : 
  ∀ {A : Type} [inst : Nonempty A] (l : List A),
    @LE.le Nat instLENat
      (@CARD A inst
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
          (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l)))
      (@List.length A l) := @HolLightLean.hol_opam.thm_CARD_SET_OF_LIST_LE holTheoryInst

theorem hol_HAS_SIZE_SET_OF_LIST : 
  ∀ {A : Type} [Nonempty A] (l : List A),
    @Eq Prop
      (And
        (@Set.Finite A
          (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
            (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l)))
        (@Eq Nat
          (@Set.ncard A
            (@SetLike.coe (Finset A) A (@Finset.instSetLike A)
              (@List.toFinset A (fun (a b : A) ↦ Classical.propDecidable (@Eq A a b)) l)))
          (@List.length A l)))
      (@List.Pairwise A (fun (x y : A) ↦ Not (@Eq A x y)) l) := @HolLightLean.hol_opam.thm_HAS_SIZE_SET_OF_LIST holTheoryInst

theorem hol_SURJECTIVE_IFF_INJECTIVE_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B) (f : A → B),
    s.Finite ∧ t.Finite ∧ CARD s = CARD t ∧ f '' s ⊆ t →
      Eq (α := Prop) (∀ y ∈ t, ∃ x ∈ s, f x = y) (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_IFF_INJECTIVE_GEN holTheoryInst

theorem hol_SURJECTIVE_IFF_INJECTIVE : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (f : A → A),
    s.Finite ∧ f '' s ⊆ s → Eq (α := Prop) (∀ y ∈ s, ∃ x ∈ s, f x = y) (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_IFF_INJECTIVE holTheoryInst

theorem hol_IMAGE_IMP_INJECTIVE_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B) (f : A → B),
    s.Finite ∧ CARD s = CARD t ∧ f '' s = t → ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_IMAGE_IMP_INJECTIVE_GEN holTheoryInst

theorem hol_IMAGE_IMP_INJECTIVE : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (f : A → A),
    s.Finite ∧ f '' s = s → ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_IMAGE_IMP_INJECTIVE holTheoryInst

theorem hol_HAS_SIZE_IMAGE_INJ_RESTRICT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A) (t P : Set B) (n : ℕ),
    s.Finite ∧
        t.Finite ∧
          CARD s = CARD t ∧
            f '' s ⊆ t ∧
              (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) ∧
                Set.Finite (α := A)
                    (id fun (GEN_PVAR_219 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P (f x)) ∧ GEN_PVAR_219 = x'} x) ∧
                  Set.ncard (α := A)
                      (id fun (GEN_PVAR_219 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P (f x)) ∧ GEN_PVAR_219 = x'} x) =
                    n →
      Set.Finite (α := B) (id fun (GEN_PVAR_220 : B) ↦ ∃ (x : B), {x' : B | (x ∈ t ∧ P x) ∧ GEN_PVAR_220 = x'} x) ∧
        Set.ncard (α := B) (id fun (GEN_PVAR_220 : B) ↦ ∃ (x : B), {x' : B | (x ∈ t ∧ P x) ∧ GEN_PVAR_220 = x'} x) = n := @HolLightLean.hol_opam.thm_HAS_SIZE_IMAGE_INJ_RESTRICT holTheoryInst

theorem hol_CARD_LE_INJ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite ∧ CARD s ≤ CARD t → ∃ (f : A → B), f '' s ⊆ t ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_CARD_LE_INJ holTheoryInst

theorem hol_FORALL_IN_CLAUSES : 
  ∀ {A : Type} [Nonempty A],
    (∀ (P : Set A), (∀ (x : A), Membership.mem (γ := Set A) ∅ x → P x) = True) ∧
      ∀ (P : Set A) (a : A) (s : Set A), (∀ x ∈ insert a s, P x) = (P a ∧ ∀ x ∈ s, P x) := @HolLightLean.hol_opam.thm_FORALL_IN_CLAUSES holTheoryInst

theorem hol_EXISTS_IN_CLAUSES : 
  ∀ {A : Type} [Nonempty A],
    (∀ (P : Set A), (∃ (x : A), Membership.mem (γ := Set A) ∅ x ∧ P x) = False) ∧
      ∀ (P : Set A) (a : A) (s : Set A), (∃ x ∈ insert a s, P x) = (P a ∨ ∃ x ∈ s, P x) := @HolLightLean.hol_opam.thm_EXISTS_IN_CLAUSES holTheoryInst

theorem hol_INJECTIVE_ON_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (u : Set A),
    Eq (α := Prop) (∀ (s t : Set A), s ⊆ u ∧ t ⊆ u ∧ f '' s = f '' t → s = t)
      (∀ (x y : A), x ∈ u ∧ y ∈ u ∧ f x = f y → x = y) := @HolLightLean.hol_opam.thm_INJECTIVE_ON_IMAGE holTheoryInst

theorem hol_INJECTIVE_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (s t : Set A), f '' s = f '' t → s = t) (∀ (x y : A), f x = f y → x = y) := @HolLightLean.hol_opam.thm_INJECTIVE_IMAGE holTheoryInst

theorem hol_SURJECTIVE_ON_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (u : Set A) (v : Set B),
    Eq (α := Prop) (∀ t ⊆ v, ∃ s ⊆ u, f '' s = t) (∀ y ∈ v, ∃ x ∈ u, f x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_ON_IMAGE holTheoryInst

theorem hol_SURJECTIVE_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop) (∀ (t : Set B), ∃ (s : Set A), f '' s = t) (∀ (y : B), ∃ (x : A), f x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_IMAGE holTheoryInst

theorem hol_INJECTIVE_ON_PREIMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (u : Set B),
    (∀ (t t' : Set B),
        t ⊆ u ∧
            t' ⊆ u ∧
              Eq (α := Set A)
                (id fun (GEN_PVAR_222 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x ∈ t) ∧ GEN_PVAR_222 = x'} x)
                (id fun (GEN_PVAR_223 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x ∈ t') ∧ GEN_PVAR_223 = x'} x) →
          t = t') =
      (u ⊆ f '' s) := @HolLightLean.hol_opam.thm_INJECTIVE_ON_PREIMAGE holTheoryInst

theorem hol_SURJECTIVE_ON_PREIMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (s : Set A) (u : Set B),
    (∀ k ⊆ s,
        ∃ t ⊆ u, (id fun (GEN_PVAR_224 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x ∈ t) ∧ GEN_PVAR_224 = x'} x) = k) =
      (f '' s ⊆ u ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_ON_PREIMAGE holTheoryInst

theorem hol_INJECTIVE_PREIMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    (∀ (t t' : Set B),
        Eq (α := Set A) (id fun (GEN_PVAR_225 : A) ↦ ∃ (x : A), {x' : A | f x ∈ t ∧ GEN_PVAR_225 = x'} x)
            (id fun (GEN_PVAR_226 : A) ↦ ∃ (x : A), {x' : A | f x ∈ t' ∧ GEN_PVAR_226 = x'} x) →
          t = t') =
      (f '' Set.univ = Set.univ) := @HolLightLean.hol_opam.thm_INJECTIVE_PREIMAGE holTheoryInst

theorem hol_SURJECTIVE_PREIMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B),
    Eq (α := Prop)
      (∀ (k : Set A),
        ∃ (t : Set B), (id fun (GEN_PVAR_227 : A) ↦ ∃ (x : A), {x' : A | f x ∈ t ∧ GEN_PVAR_227 = x'} x) = k)
      (∀ (x y : A), f x = f y → x = y) := @HolLightLean.hol_opam.thm_SURJECTIVE_PREIMAGE holTheoryInst

theorem hol_CARD_EQ_BIJECTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite ∧ CARD s = CARD t →
      ∃ (f : A → B), (∀ x ∈ s, f x ∈ t) ∧ (∀ y ∈ t, ∃ x ∈ s, f x = y) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_CARD_EQ_BIJECTION holTheoryInst

theorem hol_CARD_EQ_BIJECTIONS : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite ∧ CARD s = CARD t →
      ∃ (f : A → B) (g : B → A), (∀ x ∈ s, f x ∈ t ∧ g (f x) = x) ∧ ∀ y ∈ t, g y ∈ s ∧ f (g y) = y := @HolLightLean.hol_opam.thm_CARD_EQ_BIJECTIONS holTheoryInst

theorem hol_CARD_EQ_BIJECTIONS_SPECIAL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B) (a : A) (b : B),
    s.Finite ∧ t.Finite ∧ CARD s = CARD t ∧ a ∈ s ∧ b ∈ t →
      ∃ (f : A → B) (g : B → A), f a = b ∧ g b = a ∧ (∀ x ∈ s, f x ∈ t ∧ g (f x) = x) ∧ ∀ y ∈ t, g y ∈ s ∧ f (g y) = y := @HolLightLean.hol_opam.thm_CARD_EQ_BIJECTIONS_SPECIAL holTheoryInst

theorem hol_BIJECTIONS_HAS_SIZE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (n : ℕ) (s : Set A) (t : Set B) (f : A → B) (g : B → A),
    (∀ x ∈ s, f x ∈ t ∧ g (f x) = x) ∧ (∀ y ∈ t, g y ∈ s ∧ f (g y) = y) ∧ s.Finite ∧ s.ncard = n →
      t.Finite ∧ t.ncard = n := @HolLightLean.hol_opam.thm_BIJECTIONS_HAS_SIZE holTheoryInst

theorem hol_BIJECTIONS_HAS_SIZE_EQ : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (f : A → B) (g : B → A),
    ((∀ x ∈ s, f x ∈ t ∧ g (f x) = x) ∧ ∀ y ∈ t, g y ∈ s ∧ f (g y) = y) →
      ∀ (n : ℕ), (s.Finite ∧ s.ncard = n) = (t.Finite ∧ t.ncard = n) := @HolLightLean.hol_opam.thm_BIJECTIONS_HAS_SIZE_EQ holTheoryInst

theorem hol_BIJECTIONS_CARD_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (t : Set B) (f : A → B) (g : B → A),
    ((s.Finite ∨ t.Finite) ∧ (∀ x ∈ s, f x ∈ t ∧ g (f x) = x) ∧ ∀ y ∈ t, g y ∈ s ∧ f (g y) = y) → CARD s = CARD t := @HolLightLean.hol_opam.thm_BIJECTIONS_CARD_EQ holTheoryInst

theorem hol_WF_FINITE : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    ((∀ (x : A), ¬lt2 x x) ∧
        (∀ (x y z : A), lt2 x y ∧ lt2 y z → lt2 x z) ∧
          ∀ (x : A),
            Set.Finite (α := A) (id fun (GEN_PVAR_229 : A) ↦ ∃ (y : A), {x' : A | lt2 y x ∧ GEN_PVAR_229 = x'} y)) →
      WellFounded lt2 := @HolLightLean.hol_opam.thm_WF_FINITE holTheoryInst

theorem hol_WF_PSUBSET : 
  ∀ {A : Type} [Nonempty A] (s : Set A), s.Finite → WellFounded fun (t1 t2 : Set A) ↦ t1 ⊂ t2 ∧ t2 ⊆ s := @HolLightLean.hol_opam.thm_WF_PSUBSET holTheoryInst

theorem hol_le_c : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑s) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑t)) =
      ∃ (f : A → B), (∀ x ∈ s, f x ∈ t) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y := @HolLightLean.hol_opam.thm_le_c holTheoryInst

theorem hol_lt_c : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑s) < Cardinal.lift.{0, 0} (Cardinal.mk ↑t)) =
      (Cardinal.lift.{0, 0} (Cardinal.mk ↑s) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑t) ∧
        ¬Cardinal.lift.{0, 0} (Cardinal.mk ↑t) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑s)) := @HolLightLean.hol_opam.thm_lt_c holTheoryInst

theorem hol_eq_c : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑s) = Cardinal.lift.{0, 0} (Cardinal.mk ↑t)) =
      ∃ (f : A → B), (∀ x ∈ s, f x ∈ t) ∧ ∀ y ∈ t, ∃! x : A, x ∈ s ∧ f x = y := @HolLightLean.hol_opam.thm_eq_c holTheoryInst

theorem hol_ge_c : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑t) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑s)) =
      (Cardinal.lift.{0, 0} (Cardinal.mk ↑t) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑s)) := @HolLightLean.hol_opam.thm_ge_c holTheoryInst

theorem hol_gt_c : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (t : Set B) (s : Set A),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑t) < Cardinal.lift.{0, 0} (Cardinal.mk ↑s)) =
      (Cardinal.lift.{0, 0} (Cardinal.mk ↑t) < Cardinal.lift.{0, 0} (Cardinal.mk ↑s)) := @HolLightLean.hol_opam.thm_gt_c holTheoryInst

theorem hol_LE_C : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set B) (t : Set A),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑s) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑t)) =
      ∃ (g : A → B), ∀ x ∈ s, ∃ y ∈ t, g y = x := @HolLightLean.hol_opam.thm_LE_C holTheoryInst

theorem hol_GE_C : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B),
    (Cardinal.lift.{0, 0} (Cardinal.mk ↑t) ≤ Cardinal.lift.{0, 0} (Cardinal.mk ↑s)) =
      ∃ (f : A → B), ∀ y ∈ t, ∃ x ∈ s, y = f x := @HolLightLean.hol_opam.thm_GE_C holTheoryInst

theorem hol_COUNTABLE : 
  ∀ {A : Type} [Nonempty A] (t : Set A),
    @Eq Prop (@Set.Countable A t)
      (@LE.le Cardinal.{0} Cardinal.instLE (Cardinal.mk (@Set.Elem A t)).lift
        (Cardinal.mk (@Set.Elem Nat (@Set.univ Nat))).lift) := @HolLightLean.hol_opam.thm_COUNTABLE holTheoryInst

theorem hol_sup : 
  ∀ (s : Set ℝ), sup s = Classical.epsilon fun (a : ℝ) ↦ (∀ x ∈ s, x ≤ a) ∧ ∀ (b : ℝ), (∀ x ∈ s, x ≤ b) → a ≤ b := @HolLightLean.hol_opam.thm_sup holTheoryInst

theorem hol_SUP_EQ : 
  ∀ (s t : Set ℝ), (∀ (b : ℝ), Eq (α := Prop) (∀ x ∈ s, x ≤ b) (∀ x ∈ t, x ≤ b)) → sup s = sup t := @HolLightLean.hol_opam.thm_SUP_EQ holTheoryInst

theorem hol_SUP : 
  ∀ (s : Set ℝ), (¬s = ∅ ∧ ∃ (b : ℝ), ∀ x ∈ s, x ≤ b) → (∀ x ∈ s, x ≤ sup s) ∧ ∀ (b : ℝ), (∀ x ∈ s, x ≤ b) → sup s ≤ b := @HolLightLean.hol_opam.thm_SUP holTheoryInst

theorem hol_SUP_FINITE_LEMMA : 
  ∀ (s : Set ℝ), s.Finite ∧ ¬s = ∅ → ∃ b ∈ s, ∀ x ∈ s, x ≤ b := @HolLightLean.hol_opam.thm_SUP_FINITE_LEMMA holTheoryInst

theorem hol_SUP_FINITE : 
  ∀ (s : Set ℝ), s.Finite ∧ ¬s = ∅ → sup s ∈ s ∧ ∀ x ∈ s, x ≤ sup s := @HolLightLean.hol_opam.thm_SUP_FINITE holTheoryInst

theorem hol_REAL_LE_SUP_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (a ≤ sup s) = ∃ x ∈ s, a ≤ x := @HolLightLean.hol_opam.thm_REAL_LE_SUP_FINITE holTheoryInst

theorem hol_REAL_SUP_LE_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (sup s ≤ a) = ∀ x ∈ s, x ≤ a := @HolLightLean.hol_opam.thm_REAL_SUP_LE_FINITE holTheoryInst

theorem hol_REAL_LT_SUP_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (a < sup s) = ∃ x ∈ s, a < x := @HolLightLean.hol_opam.thm_REAL_LT_SUP_FINITE holTheoryInst

theorem hol_REAL_SUP_LT_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (sup s < a) = ∀ x ∈ s, x < a := @HolLightLean.hol_opam.thm_REAL_SUP_LT_FINITE holTheoryInst

theorem hol_REAL_SUP_UNIQUE : 
  ∀ (s : Set ℝ) (b : ℝ), ((∀ x ∈ s, x ≤ b) ∧ ∀ b' < b, ∃ x ∈ s, b' < x) → sup s = b := @HolLightLean.hol_opam.thm_REAL_SUP_UNIQUE holTheoryInst

theorem hol_REAL_SUP_LE : 
  ∀ (s : Set ℝ) (b : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, x ≤ b) → sup s ≤ b := @HolLightLean.hol_opam.thm_REAL_SUP_LE holTheoryInst

theorem hol_REAL_SUP_LE_SUBSET : 
  ∀ (s t : Set ℝ), (¬s = ∅ ∧ s ⊆ t ∧ ∃ (b : ℝ), ∀ x ∈ t, x ≤ b) → sup s ≤ sup t := @HolLightLean.hol_opam.thm_REAL_SUP_LE_SUBSET holTheoryInst

theorem hol_REAL_SUP_BOUNDS : 
  ∀ (s : Set ℝ) (a b : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, a ≤ x ∧ x ≤ b) → a ≤ sup s ∧ sup s ≤ b := @HolLightLean.hol_opam.thm_REAL_SUP_BOUNDS holTheoryInst

theorem hol_REAL_ABS_SUP_LE : 
  ∀ (s : Set ℝ) (a : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, |x| ≤ a) → |sup s| ≤ a := @HolLightLean.hol_opam.thm_REAL_ABS_SUP_LE holTheoryInst

theorem hol_REAL_SUP_ASCLOSE : 
  ∀ (s : Set ℝ) (l e : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, |x - l| ≤ e) → |sup s - l| ≤ e := @HolLightLean.hol_opam.thm_REAL_SUP_ASCLOSE holTheoryInst

theorem hol_SUP_UNIQUE_FINITE : 
  ∀ (a : ℝ) (s : Set ℝ), s.Finite ∧ ¬s = ∅ → (sup s = a) = (a ∈ s ∧ ∀ y ∈ s, y ≤ a) := @HolLightLean.hol_opam.thm_SUP_UNIQUE_FINITE holTheoryInst

theorem hol_SUP_INSERT_FINITE : 
  ∀ (x : Real) (s : Set Real),
    @Set.Finite Real s →
      @Eq Real (sup (@insert Real (Set Real) (@Set.instInsert Real) x s))
        (@ite Real (@Eq (Set Real) s (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real)))
          (Classical.propDecidable
            (@Eq (Set Real) s (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
          x (@max Real Real.instMax x (sup s))) := @HolLightLean.hol_opam.thm_SUP_INSERT_FINITE holTheoryInst

theorem hol_SUP_SING : 
  ∀ (a : Real),
    @Eq Real
      (sup
        (@insert Real (Set Real) (@Set.instInsert Real) a
          (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
      a := @HolLightLean.hol_opam.thm_SUP_SING holTheoryInst

theorem hol_SUP_INSERT_INSERT : 
  ∀ (a b : Real) (s : Set Real),
    @Eq Real
      (sup (@insert Real (Set Real) (@Set.instInsert Real) b (@insert Real (Set Real) (@Set.instInsert Real) a s)))
      (sup (@insert Real (Set Real) (@Set.instInsert Real) (@max Real Real.instMax a b) s)) := @HolLightLean.hol_opam.thm_SUP_INSERT_INSERT holTheoryInst

theorem hol_REAL_LE_SUP : 
  ∀ (s : Set ℝ) (a b y : ℝ), (y ∈ s ∧ a ≤ y ∧ ∀ x ∈ s, x ≤ b) → a ≤ sup s := @HolLightLean.hol_opam.thm_REAL_LE_SUP holTheoryInst

theorem hol_REAL_SUP_LE_EQ : 
  ∀ (s : Set ℝ) (y : ℝ), (¬s = ∅ ∧ ∃ (b : ℝ), ∀ x ∈ s, x ≤ b) → (sup s ≤ y) = ∀ x ∈ s, x ≤ y := @HolLightLean.hol_opam.thm_REAL_SUP_LE_EQ holTheoryInst

theorem hol_SUP_UNIQUE : 
  ∀ (s : Set ℝ) (b : ℝ), (∀ (c : ℝ), (∀ x ∈ s, x ≤ c) = (b ≤ c)) → sup s = b := @HolLightLean.hol_opam.thm_SUP_UNIQUE holTheoryInst

theorem hol_SUP_UNION : 
  ∀ (s t : Set Real),
    And (Not (@Eq (Set Real) s (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
        (And (Not (@Eq (Set Real) t (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
          (And
            (∃ (b : Real),
              ∀ (x : Real),
                @Membership.mem Real (Set Real) (@Set.instMembership Real) s x → @LE.le Real Real.instLE x b)
            (∃ (c : Real),
              ∀ (x : Real),
                @Membership.mem Real (Set Real) (@Set.instMembership Real) t x → @LE.le Real Real.instLE x c))) →
      @Eq Real (sup (@Union.union (Set Real) (@Set.instUnion Real) s t)) (@max Real Real.instMax (sup s) (sup t)) := @HolLightLean.hol_opam.thm_SUP_UNION holTheoryInst

theorem hol_ELEMENT_LE_SUP : 
  ∀ (s : Set ℝ) (a : ℝ), (∃ (b : ℝ), ∀ x ∈ s, x ≤ b) ∧ a ∈ s → a ≤ sup s := @HolLightLean.hol_opam.thm_ELEMENT_LE_SUP holTheoryInst

theorem hol_SUP_APPROACH : 
  ∀ (s : Set ℝ) (c : ℝ), ¬s = ∅ ∧ (∃ (b : ℝ), ∀ x ∈ s, x ≤ b) ∧ c < sup s → ∃ x ∈ s, c < x := @HolLightLean.hol_opam.thm_SUP_APPROACH holTheoryInst

theorem hol_REAL_MAX_SUP : 
  ∀ (x y : Real),
    @Eq Real (@max Real Real.instMax x y)
      (sup
        (@insert Real (Set Real) (@Set.instInsert Real) x
          (@insert Real (Set Real) (@Set.instInsert Real) y
            (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))) := @HolLightLean.hol_opam.thm_REAL_MAX_SUP holTheoryInst

theorem hol_inf : 
  ∀ (s : Set ℝ), inf s = Classical.epsilon fun (a : ℝ) ↦ (∀ x ∈ s, a ≤ x) ∧ ∀ (b : ℝ), (∀ x ∈ s, b ≤ x) → b ≤ a := @HolLightLean.hol_opam.thm_inf holTheoryInst

theorem hol_INF_EQ : 
  ∀ (s t : Set ℝ), (∀ (a : ℝ), Eq (α := Prop) (∀ x ∈ s, a ≤ x) (∀ x ∈ t, a ≤ x)) → inf s = inf t := @HolLightLean.hol_opam.thm_INF_EQ holTheoryInst

theorem hol_INF : 
  ∀ (s : Set ℝ), (¬s = ∅ ∧ ∃ (b : ℝ), ∀ x ∈ s, b ≤ x) → (∀ x ∈ s, inf s ≤ x) ∧ ∀ (b : ℝ), (∀ x ∈ s, b ≤ x) → b ≤ inf s := @HolLightLean.hol_opam.thm_INF holTheoryInst

theorem hol_INF_FINITE_LEMMA : 
  ∀ (s : Set ℝ), s.Finite ∧ ¬s = ∅ → ∃ b ∈ s, ∀ x ∈ s, b ≤ x := @HolLightLean.hol_opam.thm_INF_FINITE_LEMMA holTheoryInst

theorem hol_INF_FINITE : 
  ∀ (s : Set ℝ), s.Finite ∧ ¬s = ∅ → inf s ∈ s ∧ ∀ x ∈ s, inf s ≤ x := @HolLightLean.hol_opam.thm_INF_FINITE holTheoryInst

theorem hol_REAL_LE_INF_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (a ≤ inf s) = ∀ x ∈ s, a ≤ x := @HolLightLean.hol_opam.thm_REAL_LE_INF_FINITE holTheoryInst

theorem hol_REAL_INF_LE_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (inf s ≤ a) = ∃ x ∈ s, x ≤ a := @HolLightLean.hol_opam.thm_REAL_INF_LE_FINITE holTheoryInst

theorem hol_REAL_LT_INF_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (a < inf s) = ∀ x ∈ s, a < x := @HolLightLean.hol_opam.thm_REAL_LT_INF_FINITE holTheoryInst

theorem hol_REAL_INF_LT_FINITE : 
  ∀ (s : Set ℝ) (a : ℝ), s.Finite ∧ ¬s = ∅ → (inf s < a) = ∃ x ∈ s, x < a := @HolLightLean.hol_opam.thm_REAL_INF_LT_FINITE holTheoryInst

theorem hol_REAL_INF_UNIQUE : 
  ∀ (s : Set ℝ) (b : ℝ), ((∀ x ∈ s, b ≤ x) ∧ ∀ (b' : ℝ), b < b' → ∃ x ∈ s, x < b') → inf s = b := @HolLightLean.hol_opam.thm_REAL_INF_UNIQUE holTheoryInst

theorem hol_REAL_LE_INF : 
  ∀ (s : Set ℝ) (b : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, b ≤ x) → b ≤ inf s := @HolLightLean.hol_opam.thm_REAL_LE_INF holTheoryInst

theorem hol_REAL_LE_INF_SUBSET : 
  ∀ (s t : Set ℝ), (¬t = ∅ ∧ t ⊆ s ∧ ∃ (b : ℝ), ∀ x ∈ s, b ≤ x) → inf s ≤ inf t := @HolLightLean.hol_opam.thm_REAL_LE_INF_SUBSET holTheoryInst

theorem hol_REAL_INF_BOUNDS : 
  ∀ (s : Set ℝ) (a b : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, a ≤ x ∧ x ≤ b) → a ≤ inf s ∧ inf s ≤ b := @HolLightLean.hol_opam.thm_REAL_INF_BOUNDS holTheoryInst

theorem hol_REAL_ABS_INF_LE : 
  ∀ (s : Set ℝ) (a : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, |x| ≤ a) → |inf s| ≤ a := @HolLightLean.hol_opam.thm_REAL_ABS_INF_LE holTheoryInst

theorem hol_REAL_INF_ASCLOSE : 
  ∀ (s : Set ℝ) (l e : ℝ), (¬s = ∅ ∧ ∀ x ∈ s, |x - l| ≤ e) → |inf s - l| ≤ e := @HolLightLean.hol_opam.thm_REAL_INF_ASCLOSE holTheoryInst

theorem hol_INF_UNIQUE_FINITE : 
  ∀ (a : ℝ) (s : Set ℝ), s.Finite ∧ ¬s = ∅ → (inf s = a) = (a ∈ s ∧ ∀ y ∈ s, a ≤ y) := @HolLightLean.hol_opam.thm_INF_UNIQUE_FINITE holTheoryInst

theorem hol_INF_INSERT_FINITE : 
  ∀ (x : Real) (s : Set Real),
    @Set.Finite Real s →
      @Eq Real (inf (@insert Real (Set Real) (@Set.instInsert Real) x s))
        (@ite Real (@Eq (Set Real) s (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real)))
          (Classical.propDecidable
            (@Eq (Set Real) s (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
          x (@min Real Real.instMin x (inf s))) := @HolLightLean.hol_opam.thm_INF_INSERT_FINITE holTheoryInst

theorem hol_INF_SING : 
  ∀ (a : Real),
    @Eq Real
      (inf
        (@insert Real (Set Real) (@Set.instInsert Real) a
          (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
      a := @HolLightLean.hol_opam.thm_INF_SING holTheoryInst

theorem hol_INF_INSERT_INSERT : 
  ∀ (a b : Real) (s : Set Real),
    @Eq Real
      (inf (@insert Real (Set Real) (@Set.instInsert Real) b (@insert Real (Set Real) (@Set.instInsert Real) a s)))
      (inf (@insert Real (Set Real) (@Set.instInsert Real) (@min Real Real.instMin a b) s)) := @HolLightLean.hol_opam.thm_INF_INSERT_INSERT holTheoryInst

theorem hol_REAL_SUP_EQ_INF : 
  ∀ (s : Set ℝ), (¬s = ∅ ∧ ∃ (B : ℝ), ∀ x ∈ s, |x| ≤ B) → (sup s = inf s) = ∃ (a : ℝ), s = insert a ∅ := @HolLightLean.hol_opam.thm_REAL_SUP_EQ_INF holTheoryInst

theorem hol_REAL_INF_LE : 
  ∀ (s : Set ℝ) (a b y : ℝ), (y ∈ s ∧ y ≤ b ∧ ∀ x ∈ s, a ≤ x) → inf s ≤ b := @HolLightLean.hol_opam.thm_REAL_INF_LE holTheoryInst

theorem hol_REAL_LE_INF_EQ : 
  ∀ (s : Set ℝ) (y : ℝ), (¬s = ∅ ∧ ∃ (b : ℝ), ∀ x ∈ s, b ≤ x) → (y ≤ inf s) = ∀ x ∈ s, y ≤ x := @HolLightLean.hol_opam.thm_REAL_LE_INF_EQ holTheoryInst

theorem hol_INF_UNIQUE : 
  ∀ (s : Set ℝ) (b : ℝ), (∀ (c : ℝ), (∀ x ∈ s, c ≤ x) = (c ≤ b)) → inf s = b := @HolLightLean.hol_opam.thm_INF_UNIQUE holTheoryInst

theorem hol_INF_UNION : 
  ∀ (s t : Set Real),
    And (Not (@Eq (Set Real) s (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
        (And (Not (@Eq (Set Real) t (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))
          (And
            (∃ (b : Real),
              ∀ (x : Real),
                @Membership.mem Real (Set Real) (@Set.instMembership Real) s x → @LE.le Real Real.instLE b x)
            (∃ (c : Real),
              ∀ (x : Real),
                @Membership.mem Real (Set Real) (@Set.instMembership Real) t x → @LE.le Real Real.instLE c x))) →
      @Eq Real (inf (@Union.union (Set Real) (@Set.instUnion Real) s t)) (@min Real Real.instMin (inf s) (inf t)) := @HolLightLean.hol_opam.thm_INF_UNION holTheoryInst

theorem hol_INF_LE_ELEMENT : 
  ∀ (s : Set ℝ) (a : ℝ), (∃ (b : ℝ), ∀ x ∈ s, b ≤ x) ∧ a ∈ s → inf s ≤ a := @HolLightLean.hol_opam.thm_INF_LE_ELEMENT holTheoryInst

theorem hol_INF_APPROACH : 
  ∀ (s : Set ℝ) (c : ℝ), ¬s = ∅ ∧ (∃ (b : ℝ), ∀ x ∈ s, b ≤ x) ∧ inf s < c → ∃ x ∈ s, x < c := @HolLightLean.hol_opam.thm_INF_APPROACH holTheoryInst

theorem hol_REAL_MIN_INF : 
  ∀ (x y : Real),
    @Eq Real (@min Real Real.instMin x y)
      (inf
        (@insert Real (Set Real) (@Set.instInsert Real) x
          (@insert Real (Set Real) (@Set.instInsert Real) y
            (@EmptyCollection.emptyCollection (Set Real) (@Set.instEmptyCollection Real))))) := @HolLightLean.hol_opam.thm_REAL_MIN_INF holTheoryInst

theorem hol_has_inf : 
  ∀ (s : Set ℝ) (b : ℝ), IsGLB s b = ∀ (c : ℝ), (∀ x ∈ s, c ≤ x) = (c ≤ b) := @HolLightLean.hol_opam.thm_has_inf holTheoryInst

theorem hol_has_sup : 
  ∀ (s : Set ℝ) (b : ℝ), IsLUB s b = ∀ (c : ℝ), (∀ x ∈ s, x ≤ c) = (b ≤ c) := @HolLightLean.hol_opam.thm_has_sup holTheoryInst

theorem hol_HAS_INF_LBOUND : 
  ∀ (s : Set ℝ) (b x : ℝ), IsGLB s b ∧ x ∈ s → b ≤ x := @HolLightLean.hol_opam.thm_HAS_INF_LBOUND holTheoryInst

theorem hol_HAS_SUP_UBOUND : 
  ∀ (s : Set ℝ) (b x : ℝ), IsLUB s b ∧ x ∈ s → x ≤ b := @HolLightLean.hol_opam.thm_HAS_SUP_UBOUND holTheoryInst

theorem hol_HAS_INF_INF : 
  ∀ (s : Set ℝ) (l : ℝ), IsGLB s l = (¬s = ∅ ∧ (∃ (b : ℝ), ∀ x ∈ s, b ≤ x) ∧ inf s = l) := @HolLightLean.hol_opam.thm_HAS_INF_INF holTheoryInst

theorem hol_HAS_SUP_SUP : 
  ∀ (s : Set ℝ) (l : ℝ), IsLUB s l = (¬s = ∅ ∧ (∃ (b : ℝ), ∀ x ∈ s, x ≤ b) ∧ sup s = l) := @HolLightLean.hol_opam.thm_HAS_SUP_SUP holTheoryInst

theorem hol_INF_EXISTS : 
  ∀ (s : Set ℝ), (∃ (l : ℝ), IsGLB s l) = (¬s = ∅ ∧ ∃ (b : ℝ), ∀ x ∈ s, b ≤ x) := @HolLightLean.hol_opam.thm_INF_EXISTS holTheoryInst

theorem hol_SUP_EXISTS : 
  ∀ (s : Set ℝ), (∃ (l : ℝ), IsLUB s l) = (¬s = ∅ ∧ ∃ (b : ℝ), ∀ x ∈ s, x ≤ b) := @HolLightLean.hol_opam.thm_SUP_EXISTS holTheoryInst

theorem hol_HAS_INF_APPROACH : 
  ∀ (s : Set ℝ) (l c : ℝ), IsGLB s l ∧ l < c → ∃ x ∈ s, x < c := @HolLightLean.hol_opam.thm_HAS_INF_APPROACH holTheoryInst

theorem hol_HAS_SUP_APPROACH : 
  ∀ (s : Set ℝ) (l c : ℝ), IsLUB s l ∧ c < l → ∃ x ∈ s, c < x := @HolLightLean.hol_opam.thm_HAS_SUP_APPROACH holTheoryInst

theorem hol_HAS_INF : 
  ∀ (s : Set ℝ) (l : ℝ), IsGLB s l = (¬s = ∅ ∧ (∀ x ∈ s, l ≤ x) ∧ ∀ (c : ℝ), l < c → ∃ x ∈ s, x < c) := @HolLightLean.hol_opam.thm_HAS_INF holTheoryInst

theorem hol_HAS_SUP : 
  ∀ (s : Set ℝ) (l : ℝ), IsLUB s l = (¬s = ∅ ∧ (∀ x ∈ s, x ≤ l) ∧ ∀ c < l, ∃ x ∈ s, c < x) := @HolLightLean.hol_opam.thm_HAS_SUP holTheoryInst

theorem hol_HAS_INF_LE : 
  ∀ (s t : Set ℝ) (l m : ℝ), (IsGLB s l ∧ IsGLB t m ∧ ∀ y ∈ t, ∃ x ∈ s, x ≤ y) → l ≤ m := @HolLightLean.hol_opam.thm_HAS_INF_LE holTheoryInst

theorem hol_HAS_SUP_LE : 
  ∀ (s t : Set ℝ) (l m : ℝ), (IsLUB s l ∧ IsLUB t m ∧ ∀ y ∈ t, ∃ x ∈ s, y ≤ x) → m ≤ l := @HolLightLean.hol_opam.thm_HAS_SUP_LE holTheoryInst

theorem hol_numseg : 
  ∀ (m n : ℕ), Set.Icc m n = id fun (GEN_PVAR_231 : ℕ) ↦ ∃ (x : ℕ), {x' : ℕ | (m ≤ x ∧ x ≤ n) ∧ GEN_PVAR_231 = x'} x := @HolLightLean.hol_opam.thm_numseg holTheoryInst

theorem hol_FINITE_NUMSEG : 
  ∀ (m n : ℕ), (Set.Icc m n).Finite := @HolLightLean.hol_opam.thm_FINITE_NUMSEG holTheoryInst

theorem hol_NUMSEG_COMBINE_R : 
  ∀ (m p n : ℕ),
    m ≤ p + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ p ≤ n →
      Set.Icc m p ∪ Set.Icc (p + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n = Set.Icc m n := @HolLightLean.hol_opam.thm_NUMSEG_COMBINE_R holTheoryInst

theorem hol_NUMSEG_COMBINE_L : 
  ∀ (m p n : ℕ),
    m ≤ p ∧ p ≤ n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      Set.Icc m (p - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∪ Set.Icc p n = Set.Icc m n := @HolLightLean.hol_opam.thm_NUMSEG_COMBINE_L holTheoryInst

theorem hol_NUMSEG_LREC : 
  ∀ (m n : ℕ), m ≤ n → insert m (Set.Icc (m + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n) = Set.Icc m n := @HolLightLean.hol_opam.thm_NUMSEG_LREC holTheoryInst

theorem hol_NUMSEG_RREC : 
  ∀ (m n : ℕ), m ≤ n → insert n (Set.Icc m (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) = Set.Icc m n := @HolLightLean.hol_opam.thm_NUMSEG_RREC holTheoryInst

theorem hol_NUMSEG_REC : 
  ∀ (m n : ℕ), m ≤ n + (1 : ℕ) → Set.Icc m (n + (1 : ℕ)) = insert (n + (1 : ℕ)) (Set.Icc m n) := @HolLightLean.hol_opam.thm_NUMSEG_REC holTheoryInst

theorem hol_IN_NUMSEG : 
  ∀ (m n p : ℕ), (p ∈ Set.Icc m n) = (m ≤ p ∧ p ≤ n) := @HolLightLean.hol_opam.thm_IN_NUMSEG holTheoryInst

theorem hol_IN_NUMSEG_0 : 
  ∀ (m n : ℕ), (m ∈ Set.Icc (0 : ℕ) n) = (m ≤ n) := @HolLightLean.hol_opam.thm_IN_NUMSEG_0 holTheoryInst

theorem hol_NUMSEG_SING : 
  ∀ (n : ℕ), Set.Icc n n = insert n ∅ := @HolLightLean.hol_opam.thm_NUMSEG_SING holTheoryInst

theorem hol_NUMSEG_EMPTY : 
  ∀ (m n : ℕ), (Set.Icc m n = ∅) = (n < m) := @HolLightLean.hol_opam.thm_NUMSEG_EMPTY holTheoryInst

theorem hol_EMPTY_NUMSEG : 
  ∀ (m n : ℕ), n < m → Set.Icc m n = ∅ := @HolLightLean.hol_opam.thm_EMPTY_NUMSEG holTheoryInst

theorem hol_FINITE_SUBSET_NUMSEG : 
  ∀ (s : Set ℕ), s.Finite = ∃ (n : ℕ), s ⊆ Set.Icc (0 : ℕ) n := @HolLightLean.hol_opam.thm_FINITE_SUBSET_NUMSEG holTheoryInst

theorem hol_CARD_NUMSEG_LEMMA : 
  ∀ (m d : ℕ), CARD (Set.Icc m (m + d)) = d + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_CARD_NUMSEG_LEMMA holTheoryInst

theorem hol_CARD_NUMSEG : 
  ∀ (m n : ℕ), CARD (Set.Icc m n) = n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - m := @HolLightLean.hol_opam.thm_CARD_NUMSEG holTheoryInst

theorem hol_HAS_SIZE_NUMSEG : 
  ∀ (m n : ℕ), (Set.Icc m n).Finite ∧ (Set.Icc m n).ncard = n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - m := @HolLightLean.hol_opam.thm_HAS_SIZE_NUMSEG holTheoryInst

theorem hol_CARD_NUMSEG_1 : 
  ∀ (n : ℕ), CARD (Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n) = n := @HolLightLean.hol_opam.thm_CARD_NUMSEG_1 holTheoryInst

theorem hol_HAS_SIZE_NUMSEG_1 : 
  ∀ (n : ℕ), (Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n).Finite ∧ (Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n).ncard = n := @HolLightLean.hol_opam.thm_HAS_SIZE_NUMSEG_1 holTheoryInst

theorem hol_NUMSEG_CLAUSES : 
  (∀ (m : ℕ), Set.Icc m (0 : ℕ) = if m = (0 : ℕ) then insert (0 : ℕ) ∅ else ∅) ∧
    ∀ (m n : ℕ), Set.Icc m (n + (1 : ℕ)) = if m ≤ n + (1 : ℕ) then insert (n + (1 : ℕ)) (Set.Icc m n) else Set.Icc m n := @HolLightLean.hol_opam.thm_NUMSEG_CLAUSES holTheoryInst

theorem hol_FINITE_INDEX_NUMSEG : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    s.Finite =
      ∃ (f : ℕ → A),
        (∀ (i j : ℕ),
            i ∈ Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) (CARD s) ∧
                j ∈ Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) (CARD s) ∧ f i = f j →
              i = j) ∧
          s = f '' Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) (CARD s) := @HolLightLean.hol_opam.thm_FINITE_INDEX_NUMSEG holTheoryInst

theorem hol_FINITE_INDEX_NUMBERS : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    s.Finite = ∃ (k : Set ℕ) (f : ℕ → A), (∀ (i j : ℕ), i ∈ k ∧ j ∈ k ∧ f i = f j → i = j) ∧ k.Finite ∧ s = f '' k := @HolLightLean.hol_opam.thm_FINITE_INDEX_NUMBERS holTheoryInst

theorem hol_INTER_NUMSEG : 
  ∀ (m n p q : ℕ), Set.Icc m n ∩ Set.Icc p q = Set.Icc (max m p) (min n q) := @HolLightLean.hol_opam.thm_INTER_NUMSEG holTheoryInst

theorem hol_DISJOINT_NUMSEG : 
  ∀ (m n p q : ℕ), Disjoint (Set.Icc m n) (Set.Icc p q) = (n < p ∨ q < m ∨ n < m ∨ q < p) := @HolLightLean.hol_opam.thm_DISJOINT_NUMSEG holTheoryInst

theorem hol_NUMSEG_ADD_SPLIT : 
  ∀ (m n p : ℕ),
    m ≤ n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      Set.Icc m (n + p) = Set.Icc m n ∪ Set.Icc (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) (n + p) := @HolLightLean.hol_opam.thm_NUMSEG_ADD_SPLIT holTheoryInst

theorem hol_NUMSEG_OFFSET_IMAGE : 
  ∀ (m n p : ℕ), Set.Icc (m + p) (n + p) = (fun (i : ℕ) ↦ i + p) '' Set.Icc m n := @HolLightLean.hol_opam.thm_NUMSEG_OFFSET_IMAGE holTheoryInst

theorem hol_SUBSET_NUMSEG : 
  ∀ (m n p q : ℕ), (Set.Icc m n ⊆ Set.Icc p q) = (n < m ∨ p ≤ m ∧ n ≤ q) := @HolLightLean.hol_opam.thm_SUBSET_NUMSEG holTheoryInst

theorem hol_NUMSEG_LE : 
  ∀ (n : ℕ), (id fun (GEN_PVAR_233 : ℕ) ↦ ∃ (x : ℕ), {x' : ℕ | x ≤ n ∧ GEN_PVAR_233 = x'} x) = Set.Icc (0 : ℕ) n := @HolLightLean.hol_opam.thm_NUMSEG_LE holTheoryInst

theorem hol_NUMSEG_LT : 
  ∀ (n : ℕ),
    (id fun (GEN_PVAR_234 : ℕ) ↦ ∃ (x : ℕ), {x' : ℕ | x < n ∧ GEN_PVAR_234 = x'} x) =
      if n = (0 : ℕ) then ∅ else Set.Icc (0 : ℕ) (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_NUMSEG_LT holTheoryInst

theorem hol_TOPOLOGICAL_SORT : 
  ∀ {A : Type} [Nonempty A] (lt2 : A → A → Prop),
    ((∀ (x y : A), lt2 x y ∧ lt2 y x → x = y) ∧ ∀ (x y z : A), lt2 x y ∧ lt2 y z → lt2 x z) →
      ∀ (n : ℕ) (s : Set A),
        s.Finite ∧ s.ncard = n →
          ∃ (f : ℕ → A),
            s = f '' Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n ∧
              ∀ (j k : ℕ),
                j ∈ Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n ∧ k ∈ Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n ∧ j < k →
                  ¬lt2 (f k) (f j) := @HolLightLean.hol_opam.thm_TOPOLOGICAL_SORT holTheoryInst

theorem hol_FINITE_INT_SEG : 
  (∀ (l r : ℤ),
      Set.Finite (α := ℤ) (id fun (GEN_PVAR_235 : ℤ) ↦ ∃ (x : ℤ), {x' : ℤ | (l ≤ x ∧ x ≤ r) ∧ GEN_PVAR_235 = x'} x)) ∧
    (∀ (l r : ℤ),
        Set.Finite (α := ℤ) (id fun (GEN_PVAR_236 : ℤ) ↦ ∃ (x : ℤ), {x' : ℤ | (l ≤ x ∧ x < r) ∧ GEN_PVAR_236 = x'} x)) ∧
      (∀ (l r : ℤ),
          Set.Finite (α := ℤ)
            (id fun (GEN_PVAR_237 : ℤ) ↦ ∃ (x : ℤ), {x' : ℤ | (l < x ∧ x ≤ r) ∧ GEN_PVAR_237 = x'} x)) ∧
        ∀ (l r : ℤ),
          Set.Finite (α := ℤ) (id fun (GEN_PVAR_238 : ℤ) ↦ ∃ (x : ℤ), {x' : ℤ | (l < x ∧ x < r) ∧ GEN_PVAR_238 = x'} x) := @HolLightLean.hol_opam.thm_FINITE_INT_SEG holTheoryInst

theorem hol_neutral : 
  ∀ {A : Type} [inst : Nonempty A] (op : A → A → A),
    neutral op = Classical.epsilon fun (x : A) ↦ ∀ (y : A), op x y = y ∧ op y x = y := @HolLightLean.hol_opam.thm_neutral holTheoryInst

theorem hol_monoidal : 
  ∀ {A : Type} [inst : Nonempty A] (op : A → A → A),
    monoidal op =
      ((∀ (x y : A), op x y = op y x) ∧
        (∀ (x y z : A), op x (op y z) = op (op x y) z) ∧ ∀ (x : A), op (neutral op) x = x) := @HolLightLean.hol_opam.thm_monoidal holTheoryInst

theorem hol_MONOIDAL_AC : 
  ∀ {A : Type} [inst : Nonempty A] (op : A → A → A),
    monoidal op →
      (∀ (a : A), op (neutral op) a = a) ∧
        (∀ (a : A), op a (neutral op) = a) ∧
          (∀ (a b : A), op a b = op b a) ∧
            (∀ (a b c : A), op (op a b) c = op a (op b c)) ∧ ∀ (a b c : A), op a (op b c) = op b (op a c) := @HolLightLean.hol_opam.thm_MONOIDAL_AC holTheoryInst

theorem hol_support : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (f : A → B) (op : B → B → B),
    support op f s = id fun (GEN_PVAR_239 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬f x = neutral op) ∧ GEN_PVAR_239 = x'} x := @HolLightLean.hol_opam.thm_support holTheoryInst

theorem hol_iterate : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : A → B) (s : Set A) (op : B → B → B),
    iterate op s f =
      if Set.Finite (support op f s) then ITSET (fun (x : A) (a : B) ↦ op (f x) a) (support op f s) (neutral op)
      else neutral op := @HolLightLean.hol_opam.thm_iterate holTheoryInst

theorem hol_IN_SUPPORT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (x : A) (s : Set A),
    @Eq Prop (@Membership.mem A (Set A) (@Set.instMembership A) (@support A B inst inst_1 op f s) x)
      (And (@Membership.mem A (Set A) (@Set.instMembership A) s x) (Not (@Eq B (f x) (@neutral B inst_1 op)))) := @HolLightLean.hol_opam.thm_IN_SUPPORT holTheoryInst

theorem hol_SUPPORT_SUPPORT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (s : Set A),
    support op f (support op f s) = support op f s := @HolLightLean.hol_opam.thm_SUPPORT_SUPPORT holTheoryInst

theorem hol_SUPPORT_EMPTY : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (s : Set A),
    @Eq Prop (∀ (x : A), @Membership.mem A (Set A) (@Set.instMembership A) s x → @Eq B (f x) (@neutral B inst_1 op))
      (@Eq (Set A) (@support A B inst inst_1 op f s)
        (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))) := @HolLightLean.hol_opam.thm_SUPPORT_EMPTY holTheoryInst

theorem hol_SUPPORT_SUBSET : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (s : Set A),
    @Subset (Set A) (@Set.instHasSubset A) (@support A B inst inst_1 op f s) s := @HolLightLean.hol_opam.thm_SUPPORT_SUBSET holTheoryInst

theorem hol_FINITE_SUPPORT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (s : Set A),
    s.Finite → Set.Finite (support op f s) := @HolLightLean.hol_opam.thm_FINITE_SUPPORT holTheoryInst

theorem hol_SUPPORT_CLAUSES : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    And
      (∀ (f : A → C),
        @Eq (Set A)
          (@support A C inst inst_2 op f (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
          (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
      (And
        (∀ (f : A → C) (x : A) (s : Set A),
          @Eq (Set A) (@support A C inst inst_2 op f (@insert A (Set A) (@Set.instInsert A) x s))
            (@ite (Set A) (@Eq C (f x) (@neutral C inst_2 op))
              (Classical.propDecidable (@Eq C (f x) (@neutral C inst_2 op))) (@support A C inst inst_2 op f s)
              (@insert A (Set A) (@Set.instInsert A) x (@support A C inst inst_2 op f s))))
        (And
          (∀ (f : A → C) (x : A) (s : Set A),
            @Eq (Set A)
              (@support A C inst inst_2 op f
                (@sdiff (Set A)
                  (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦
                    @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                  s (@singleton A (Set A) (@Set.instSingletonSet A) x)))
              (@sdiff (Set A)
                (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦ @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                (@support A C inst inst_2 op f s) (@singleton A (Set A) (@Set.instSingletonSet A) x)))
          (And
            (∀ (f : A → C) (s t : Set A),
              @Eq (Set A) (@support A C inst inst_2 op f (@Union.union (Set A) (@Set.instUnion A) s t))
                (@Union.union (Set A) (@Set.instUnion A) (@support A C inst inst_2 op f s)
                  (@support A C inst inst_2 op f t)))
            (And
              (∀ (f : A → C) (s t : Set A),
                @Eq (Set A) (@support A C inst inst_2 op f (@Inter.inter (Set A) (@Set.instInter A) s t))
                  (@Inter.inter (Set A) (@Set.instInter A) (@support A C inst inst_2 op f s)
                    (@support A C inst inst_2 op f t)))
              (And
                (∀ (f : A → C) (s t : Set A),
                  @Eq (Set A) (@support A C inst inst_2 op f (@sdiff (Set A) (@Set.instSDiff A) s t))
                    (@sdiff (Set A) (@Set.instSDiff A) (@support A C inst inst_2 op f s)
                      (@support A C inst inst_2 op f t)))
                (∀ (f : A → B) (g : B → C) (s : Set A),
                  @Eq (Set B) (@support B C inst_1 inst_2 op g (@Set.image A B f s))
                    (@Set.image A B f (@support A C inst inst_2 op (@Function.comp A B C g f) s)))))))) := @HolLightLean.hol_opam.thm_SUPPORT_CLAUSES holTheoryInst

theorem hol_SUPPORT_DELTA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (s : Set A) (f : A → B) (a : A),
    @Eq (Set A)
      (@support A B inst inst_1 op
        (fun (x : A) ↦ @ite B (@Eq A x a) (Classical.propDecidable (@Eq A x a)) (f x) (@neutral B inst_1 op)) s)
      (@ite (Set A) (@Membership.mem A (Set A) (@Set.instMembership A) s a)
        (Classical.propDecidable (@Membership.mem A (Set A) (@Set.instMembership A) s a))
        (@support A B inst inst_1 op f
          (@insert A (Set A) (@Set.instInsert A) a
            (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
        (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))) := @HolLightLean.hol_opam.thm_SUPPORT_DELTA holTheoryInst

theorem hol_FINITE_SUPPORT_DELTA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (s : Set A) (op : B → B → B) (f : A → B) (a : A),
    Set.Finite (support op (fun (x : A) ↦ if x = a then f x else neutral op) s) := @HolLightLean.hol_opam.thm_FINITE_SUPPORT_DELTA holTheoryInst

theorem hol_ITERATE_SUPPORT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (s : Set A),
    iterate op (support op f s) f = iterate op s f := @HolLightLean.hol_opam.thm_ITERATE_SUPPORT holTheoryInst

theorem hol_ITERATE_EXPAND_CASES : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B) (f : A → B) (s : Set A),
    iterate op s f = if Set.Finite (support op f s) then iterate op (support op f s) f else neutral op := @HolLightLean.hol_opam.thm_ITERATE_EXPAND_CASES holTheoryInst

theorem hol_ITERATE_CLAUSES_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      And
        (∀ (f : A → B),
          @Eq B (@iterate A B inst inst_1 op (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)) f)
            (@neutral B inst_1 op))
        (∀ (f : A → B) (x : A) (s : Set A),
          @Set.Finite A (@support A B inst inst_1 op f s) →
            @Eq B (@iterate A B inst inst_1 op (@insert A (Set A) (@Set.instInsert A) x s) f)
              (@ite B (@Membership.mem A (Set A) (@Set.instMembership A) s x)
                (Classical.propDecidable (@Membership.mem A (Set A) (@Set.instMembership A) s x))
                (@iterate A B inst inst_1 op s f) (op (f x) (@iterate A B inst inst_1 op s f)))) := @HolLightLean.hol_opam.thm_ITERATE_CLAUSES_GEN holTheoryInst

theorem hol_ITERATE_CLAUSES : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    @monoidal C inst_2 op →
      And
        (∀ (f : A → C),
          @Eq C (@iterate A C inst inst_2 op (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)) f)
            (@neutral C inst_2 op))
        (∀ (f : B → C) (x : B) (s : Set B),
          @Set.Finite B s →
            @Eq C (@iterate B C inst_1 inst_2 op (@insert B (Set B) (@Set.instInsert B) x s) f)
              (@ite C (@Membership.mem B (Set B) (@Set.instMembership B) s x)
                (Classical.propDecidable (@Membership.mem B (Set B) (@Set.instMembership B) s x))
                (@iterate B C inst_1 inst_2 op s f) (op (f x) (@iterate B C inst_1 inst_2 op s f)))) := @HolLightLean.hol_opam.thm_ITERATE_CLAUSES holTheoryInst

theorem hol_ITERATE_UNION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (s t : Set A),
        And (@Set.Finite A s)
            (And (@Set.Finite A t)
              (@Disjoint (Set A)
                (@ChainCompletePartialOrder.toPartialOrder (Set A)
                  (@ChainCompletePartialOrder.instOfCompleteLattice (Set A)
                    (@CompleteBooleanAlgebra.toCompleteLattice (Set A)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set A)
                        (@Set.instCompleteAtomicBooleanAlgebra A)))))
                (@HeytingAlgebra.toOrderBot (Set A)
                  (@Order.Frame.toHeytingAlgebra (Set A)
                    (@CompleteDistribLattice.toFrame (Set A)
                      (@CompleteBooleanAlgebra.toCompleteDistribLattice (Set A)
                        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set A)
                          (@Set.instCompleteAtomicBooleanAlgebra A))))))
                s t)) →
          @Eq B (@iterate A B inst inst_1 op (@Union.union (Set A) (@Set.instUnion A) s t) f)
            (op (@iterate A B inst inst_1 op s f) (@iterate A B inst inst_1 op t f)) := @HolLightLean.hol_opam.thm_ITERATE_UNION holTheoryInst

theorem hol_ITERATE_UNION_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (s t : Set A),
        And (@Set.Finite A (@support A B inst inst_1 op f s))
            (And (@Set.Finite A (@support A B inst inst_1 op f t))
              (@Disjoint (Set A)
                (@ChainCompletePartialOrder.toPartialOrder (Set A)
                  (@ChainCompletePartialOrder.instOfCompleteLattice (Set A)
                    (@CompleteBooleanAlgebra.toCompleteLattice (Set A)
                      (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set A)
                        (@Set.instCompleteAtomicBooleanAlgebra A)))))
                (@HeytingAlgebra.toOrderBot (Set A)
                  (@Order.Frame.toHeytingAlgebra (Set A)
                    (@CompleteDistribLattice.toFrame (Set A)
                      (@CompleteBooleanAlgebra.toCompleteDistribLattice (Set A)
                        (@CompleteAtomicBooleanAlgebra.toCompleteBooleanAlgebra (Set A)
                          (@Set.instCompleteAtomicBooleanAlgebra A))))))
                (@support A B inst inst_1 op f s) (@support A B inst inst_1 op f t))) →
          @Eq B (@iterate A B inst inst_1 op (@Union.union (Set A) (@Set.instUnion A) s t) f)
            (op (@iterate A B inst inst_1 op s f) (@iterate A B inst inst_1 op t f)) := @HolLightLean.hol_opam.thm_ITERATE_UNION_GEN holTheoryInst

theorem hol_ITERATE_DIFF : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f : A → B) (s t : Set A), s.Finite ∧ t ⊆ s → op (iterate op (s \ t) f) (iterate op t f) = iterate op s f := @HolLightLean.hol_opam.thm_ITERATE_DIFF holTheoryInst

theorem hol_ITERATE_DIFF_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (s t : Set A),
        And (@Set.Finite A (@support A B inst inst_1 op f s))
            (@Subset (Set A) (@Set.instHasSubset A) (@support A B inst inst_1 op f t)
              (@support A B inst inst_1 op f s)) →
          @Eq B
            (op (@iterate A B inst inst_1 op (@sdiff (Set A) (@Set.instSDiff A) s t) f)
              (@iterate A B inst inst_1 op t f))
            (@iterate A B inst inst_1 op s f) := @HolLightLean.hol_opam.thm_ITERATE_DIFF_GEN holTheoryInst

theorem hol_ITERATE_INCL_EXCL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (s t : Set A) (f : A → B),
        And (@Set.Finite A s) (@Set.Finite A t) →
          @Eq B (op (@iterate A B inst inst_1 op s f) (@iterate A B inst inst_1 op t f))
            (op (@iterate A B inst inst_1 op (@Union.union (Set A) (@Set.instUnion A) s t) f)
              (@iterate A B inst inst_1 op (@Inter.inter (Set A) (@Set.instInter A) s t) f)) := @HolLightLean.hol_opam.thm_ITERATE_INCL_EXCL holTheoryInst

theorem hol_ITERATE_CLOSED : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (P : Set B),
        (P (neutral op) ∧ ∀ (x y : B), P x ∧ P y → P (op x y)) →
          ∀ (f : A → B) (s : Set A), (∀ (x : A), x ∈ s ∧ ¬f x = neutral op → P (f x)) → P (iterate op s f) := @HolLightLean.hol_opam.thm_ITERATE_CLOSED holTheoryInst

theorem hol_ITERATE_RELATED : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (R' : B → B → Prop),
        (R' (neutral op) (neutral op) ∧ ∀ (x1 y1 x2 y2 : B), R' x1 x2 ∧ R' y1 y2 → R' (op x1 y1) (op x2 y2)) →
          ∀ (f g : A → B) (s : Set A), (s.Finite ∧ ∀ x ∈ s, R' (f x) (g x)) → R' (iterate op s f) (iterate op s g) := @HolLightLean.hol_opam.thm_ITERATE_RELATED holTheoryInst

theorem hol_ITERATE_EQ_NEUTRAL : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op → ∀ (f : A → B) (s : Set A), (∀ x ∈ s, f x = neutral op) → iterate op s f = neutral op := @HolLightLean.hol_opam.thm_ITERATE_EQ_NEUTRAL holTheoryInst

theorem hol_ITERATE_SING : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (x : A),
        @Eq B
          (@iterate A B inst inst_1 op
            (@insert A (Set A) (@Set.instInsert A) x
              (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A)))
            f)
          (f x) := @HolLightLean.hol_opam.thm_ITERATE_SING holTheoryInst

theorem hol_ITERATE_CLOSED_NONEMPTY : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (P : Set B),
        (∀ (x y : B), P x ∧ P y → P (op x y)) →
          ∀ (f : A → B) (s : Set A), (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, P (f x)) → P (iterate op s f) := @HolLightLean.hol_opam.thm_ITERATE_CLOSED_NONEMPTY holTheoryInst

theorem hol_ITERATE_RELATED_NONEMPTY : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (R' : B → B → Prop),
        (∀ (x1 y1 x2 y2 : B), R' x1 x2 ∧ R' y1 y2 → R' (op x1 y1) (op x2 y2)) →
          ∀ (f g : A → B) (s : Set A),
            (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, R' (f x) (g x)) → R' (iterate op s f) (iterate op s g) := @HolLightLean.hol_opam.thm_ITERATE_RELATED_NONEMPTY holTheoryInst

theorem hol_ITERATE_DELETE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (s : Set A) (a : A),
        And (@Set.Finite A s) (@Membership.mem A (Set A) (@Set.instMembership A) s a) →
          @Eq B
            (op (f a)
              (@iterate A B inst inst_1 op
                (@sdiff (Set A)
                  (@Pi.sdiff A (fun (a : A) ↦ Prop) fun (i : A) ↦
                    @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                  s (@singleton A (Set A) (@Set.instSingletonSet A) a))
                f))
            (@iterate A B inst inst_1 op s f) := @HolLightLean.hol_opam.thm_ITERATE_DELETE holTheoryInst

theorem hol_ITERATE_DELTA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f : A → B) (a : A) (s : Set A),
        (iterate op s fun (x : A) ↦ if x = a then f x else neutral op) = if a ∈ s then f a else neutral op := @HolLightLean.hol_opam.thm_ITERATE_DELTA holTheoryInst

theorem hol_ITERATE_IMAGE : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    monoidal op →
      ∀ (f : A → B) (g : B → C) (s : Set A),
        (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) → iterate op (f '' s) g = iterate op s (g ∘ f) := @HolLightLean.hol_opam.thm_ITERATE_IMAGE holTheoryInst

theorem hol_ITERATE_BIJECTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f : A → B) (p : A → A) (s : Set A),
        ((∀ x ∈ s, p x ∈ s) ∧ ∀ y ∈ s, ∃! x : A, x ∈ s ∧ p x = y) → iterate op s f = iterate op s (f ∘ p) := @HolLightLean.hol_opam.thm_ITERATE_BIJECTION holTheoryInst

theorem hol_ITERATE_ITERATE_PRODUCT : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    @monoidal C inst_2 op →
      ∀ (s : Set A) (t : A → B → Prop) (x : A → B → C),
        And (@Set.Finite A s) (∀ (i : A), @Membership.mem A (Set A) (@Set.instMembership A) s i → @Set.Finite B (t i)) →
          @Eq C (@iterate A C inst inst_2 op s fun (i : A) ↦ @iterate B C inst_1 inst_2 op (t i) (x i))
            (@iterate (Prod A B) C (@instNeProd holTheoryInst A B inst inst_1) inst_2 op
              (@id (Set (Prod A B)) fun (GEN_PVAR_243 : Prod A B) ↦
                ∃ (i : A) (j : B),
                  @setOf (Prod A B)
                    (fun (x' : Prod A B) ↦
                      And
                        (And (@Membership.mem A (Set A) (@Set.instMembership A) s i)
                          (@Membership.mem B (Set B) (@Set.instMembership B) (t i) j))
                        (@Eq (Prod A B) GEN_PVAR_243 x'))
                    (@Prod.mk A B i j))
              (@Classical.epsilon (Prod A B → C) (@instNonemptyForall_holLightLean (Prod A B) C inst_2)
                fun (f : Prod A B → C) ↦ ∀ (i : A) (j : B), @Eq C (f (@Prod.mk A B i j)) (x i j))) := @HolLightLean.hol_opam.thm_ITERATE_ITERATE_PRODUCT holTheoryInst

theorem hol_ITERATE_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op → ∀ (f g : A → B) (s : Set A), (∀ x ∈ s, f x = g x) → iterate op s f = iterate op s g := @HolLightLean.hol_opam.thm_ITERATE_EQ holTheoryInst

theorem hol_ITERATE_RESTRICT_SET : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (P s : Set A) (f : A → B),
        iterate op (id fun (GEN_PVAR_244 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_244 = x'} x) f =
          iterate op s fun (x : A) ↦ if P x then f x else neutral op := @HolLightLean.hol_opam.thm_ITERATE_RESTRICT_SET holTheoryInst

theorem hol_ITERATE_EQ_GENERAL : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    monoidal op →
      ∀ (s : Set A) (t : Set B) (f : A → C) (g : B → C) (h : A → B),
        ((∀ y ∈ t, ∃! x : A, x ∈ s ∧ h x = y) ∧ ∀ x ∈ s, h x ∈ t ∧ g (h x) = f x) → iterate op s f = iterate op t g := @HolLightLean.hol_opam.thm_ITERATE_EQ_GENERAL holTheoryInst

theorem hol_ITERATE_EQ_GENERAL_INVERSES : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    monoidal op →
      ∀ (s : Set A) (t : Set B) (f : A → C) (g : B → C) (h : A → B) (k : B → A),
        ((∀ y ∈ t, k y ∈ s ∧ h (k y) = y) ∧ ∀ x ∈ s, h x ∈ t ∧ k (h x) = x ∧ g (h x) = f x) →
          iterate op s f = iterate op t g := @HolLightLean.hol_opam.thm_ITERATE_EQ_GENERAL_INVERSES holTheoryInst

theorem hol_ITERATE_INJECTION : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f : A → B) (p : A → A) (s : Set A),
        (s.Finite ∧ (∀ x ∈ s, p x ∈ s) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ p x = p y → x = y) →
          iterate op s (f ∘ p) = iterate op s f := @HolLightLean.hol_opam.thm_ITERATE_INJECTION holTheoryInst

theorem hol_ITERATE_UNION_NONZERO : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (s t : Set A),
        And (@Set.Finite A s)
            (And (@Set.Finite A t)
              (∀ (x : A),
                @Membership.mem A (Set A) (@Set.instMembership A) (@Inter.inter (Set A) (@Set.instInter A) s t) x →
                  @Eq B (f x) (@neutral B inst_1 op))) →
          @Eq B (@iterate A B inst inst_1 op (@Union.union (Set A) (@Set.instUnion A) s t) f)
            (op (@iterate A B inst inst_1 op s f) (@iterate A B inst inst_1 op t f)) := @HolLightLean.hol_opam.thm_ITERATE_UNION_NONZERO holTheoryInst

theorem hol_ITERATE_OP : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f g : A → B) (s : Set A),
        s.Finite → (iterate op s fun (x : A) ↦ op (f x) (g x)) = op (iterate op s f) (iterate op s g) := @HolLightLean.hol_opam.thm_ITERATE_OP holTheoryInst

theorem hol_ITERATE_SUPERSET : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f : A → B) (u v : Set A),
        (u ⊆ v ∧ ∀ (x : A), x ∈ v ∧ x ∉ u → f x = neutral op) → iterate op v f = iterate op u f := @HolLightLean.hol_opam.thm_ITERATE_SUPERSET holTheoryInst

theorem hol_ITERATE_UNIV : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    @monoidal B inst_1 op →
      ∀ (f : A → B) (s : Set A),
        @Subset (Set A) (@Set.instHasSubset A) (@support A B inst inst_1 op f (@Set.univ A)) s →
          @Eq B (@iterate A B inst inst_1 op s f) (@iterate A B inst inst_1 op (@Set.univ A) f) := @HolLightLean.hol_opam.thm_ITERATE_UNIV holTheoryInst

theorem hol_ITERATE_SWAP : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    monoidal op →
      ∀ (f : A → B → C) (s : Set A) (t : Set B),
        s.Finite ∧ t.Finite →
          (iterate op s fun (i : A) ↦ iterate op t (f i)) = iterate op t fun (j : B) ↦ iterate op s fun (i : A) ↦ f i j := @HolLightLean.hol_opam.thm_ITERATE_SWAP holTheoryInst

theorem hol_ITERATE_IMAGE_NONZERO : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    monoidal op →
      ∀ (g : B → C) (f : A → B) (s : Set A),
        (s.Finite ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y ∧ f x = f y → g (f x) = neutral op) →
          iterate op (f '' s) g = iterate op s (g ∘ f) := @HolLightLean.hol_opam.thm_ITERATE_IMAGE_NONZERO holTheoryInst

theorem hol_ITERATE_IMAGE_GEN : 
  ∀ {A B C : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] (op : C → C → C),
    monoidal op →
      ∀ (f : A → B) (g : A → C) (s : Set A),
        s.Finite →
          iterate op s g =
            iterate op (f '' s) fun (y : B) ↦
              iterate op (id fun (GEN_PVAR_247 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = y) ∧ GEN_PVAR_247 = x'} x) g := @HolLightLean.hol_opam.thm_ITERATE_IMAGE_GEN holTheoryInst

theorem hol_ITERATE_CASES : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (s P : Set A) (f g : A → B),
        s.Finite →
          (iterate op s fun (x : A) ↦ if P x then f x else g x) =
            op (iterate op (id fun (GEN_PVAR_250 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_250 = x'} x) f)
              (iterate op (id fun (GEN_PVAR_251 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬P x) ∧ GEN_PVAR_251 = x'} x) g) := @HolLightLean.hol_opam.thm_ITERATE_CASES holTheoryInst

theorem hol_ITERATE_OP_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (op : B → B → B),
    monoidal op →
      ∀ (f g : A → B) (s : Set A),
        Set.Finite (support op f s) ∧ Set.Finite (support op g s) →
          (iterate op s fun (x : A) ↦ op (f x) (g x)) = op (iterate op s f) (iterate op s g) := @HolLightLean.hol_opam.thm_ITERATE_OP_GEN holTheoryInst

theorem hol_ITERATE_CLAUSES_NUMSEG : 
  ∀ {A : Type} [inst : Nonempty A] (f : ℕ → A) (op : A → A → A),
    monoidal op →
      (∀ (m : ℕ), iterate op (Set.Icc m (0 : ℕ)) f = if m = (0 : ℕ) then f (0 : ℕ) else neutral op) ∧
        ∀ (m n : ℕ),
          iterate op (Set.Icc m (n + (1 : ℕ))) f =
            if m ≤ n + (1 : ℕ) then op (iterate op (Set.Icc m n) f) (f (n + (1 : ℕ))) else iterate op (Set.Icc m n) f := @HolLightLean.hol_opam.thm_ITERATE_CLAUSES_NUMSEG holTheoryInst

theorem hol_ITERATE_CLAUSES_NUMSEG_LT : 
  ∀ {A : Type} [inst : Nonempty A] (f : ℕ → A) (op : A → A → A),
    monoidal op →
      iterate op (id fun (GEN_PVAR_256 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < (0 : ℕ) ∧ GEN_PVAR_256 = x'} i) f = neutral op ∧
        ∀ (k : ℕ),
          iterate op (id fun (GEN_PVAR_257 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k + (1 : ℕ) ∧ GEN_PVAR_257 = x'} i) f =
            op (iterate op (id fun (GEN_PVAR_258 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k ∧ GEN_PVAR_258 = x'} i) f) (f k) := @HolLightLean.hol_opam.thm_ITERATE_CLAUSES_NUMSEG_LT holTheoryInst

theorem hol_ITERATE_CLAUSES_NUMSEG_LE : 
  ∀ {A : Type} [inst : Nonempty A] (f : ℕ → A) (op : A → A → A),
    monoidal op →
      iterate op (id fun (GEN_PVAR_259 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ (0 : ℕ) ∧ GEN_PVAR_259 = x'} i) f = f (0 : ℕ) ∧
        ∀ (k : ℕ),
          iterate op (id fun (GEN_PVAR_260 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k + (1 : ℕ) ∧ GEN_PVAR_260 = x'} i) f =
            op (iterate op (id fun (GEN_PVAR_261 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k ∧ GEN_PVAR_261 = x'} i) f)
              (f (k + (1 : ℕ))) := @HolLightLean.hol_opam.thm_ITERATE_CLAUSES_NUMSEG_LE holTheoryInst

theorem hol_ITERATE_PAIR : 
  ∀ {A : Type} [inst : Nonempty A] (op : A → A → A),
    monoidal op →
      ∀ (f : ℕ → A) (m n : ℕ),
        iterate op
            (Set.Icc (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m)
              (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))))
            f =
          iterate op (Set.Icc m n) fun (i : ℕ) ↦
            op (f (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * i))
              (f (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * i + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) := @HolLightLean.hol_opam.thm_ITERATE_PAIR holTheoryInst

theorem hol_ITERATE_REFLECT : 
  ∀ {A : Type} [inst : Nonempty A] (op : A → A → A),
    monoidal op →
      ∀ (x : ℕ → A) (m n : ℕ),
        iterate op (Set.Icc m n) x =
          if n < m then neutral op else iterate op (Set.Icc (0 : ℕ) (n - m)) fun (i : ℕ) ↦ x (n - i) := @HolLightLean.hol_opam.thm_ITERATE_REFLECT holTheoryInst

theorem hol_ITERATO_SUPPORT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (k : Set K) (f : K → A),
    iterato dom neut op ltle
        (id fun (GEN_PVAR_270 : K) ↦ ∃ (i : K), {x' : K | (i ∈ k ∧ f i ∈ dom \ insert neut ∅) ∧ GEN_PVAR_270 = x'} i)
        f =
      iterato dom neut op ltle k f := @HolLightLean.hol_opam.thm_ITERATO_SUPPORT holTheoryInst

theorem hol_ITERATO_EXPAND_CASES : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (k : Set K) (f : K → A),
    iterato dom neut op ltle k f =
      if
          Set.Finite (α := K)
            (id fun (GEN_PVAR_271 : K) ↦
              ∃ (i : K), {x' : K | (i ∈ k ∧ f i ∈ dom \ insert neut ∅) ∧ GEN_PVAR_271 = x'} i) then
        iterato dom neut op ltle
          (id fun (GEN_PVAR_272 : K) ↦ ∃ (i : K), {x' : K | (i ∈ k ∧ f i ∈ dom \ insert neut ∅) ∧ GEN_PVAR_272 = x'} i)
          f
      else neut := @HolLightLean.hol_opam.thm_ITERATO_EXPAND_CASES holTheoryInst

theorem hol_ITERATO_CLAUSES_GEN : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (f : K → A),
    And
      (@Eq A
        (@iterato A K inst inst_1 dom neut op ltle
          (@EmptyCollection.emptyCollection (Set K) (@Set.instEmptyCollection K)) f)
        neut)
      (∀ (i : K) (k : Set K),
        And
            (@Set.Finite K
              (@id (Set K) fun (GEN_PVAR_274 : K) ↦
                ∃ (j : K),
                  @setOf K
                    (fun (x' : K) ↦
                      And
                        (And (@Membership.mem K (Set K) (@Set.instMembership K) k j)
                          (@Membership.mem A (Set A) (@Set.instMembership A)
                            (@sdiff (Set A) (@Set.instSDiff A) dom
                              (@insert A (Set A) (@Set.instInsert A) neut
                                (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                            (f j)))
                        (@Eq K GEN_PVAR_274 x'))
                    j))
            (And
              (∀ (j : K),
                @Membership.mem K (Set K) (@Set.instMembership K) k j → Or (@Eq K i j) (Or (ltle i j) (ltle j i)))
              (∀ (j : K),
                And (ltle j i)
                    (And (@Membership.mem K (Set K) (@Set.instMembership K) k j)
                      (@Membership.mem A (Set A) (@Set.instMembership A)
                        (@sdiff (Set A) (@Set.instSDiff A) dom
                          (@insert A (Set A) (@Set.instInsert A) neut
                            (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                        (f j))) →
                  @Eq K j i)) →
          @Eq A (@iterato A K inst inst_1 dom neut op ltle (@insert K (Set K) (@Set.instInsert K) i k) f)
            (@ite A
              (@Membership.mem A (Set A) (@Set.instMembership A) dom (f i) →
                Or (@Eq A (f i) neut) (@Membership.mem K (Set K) (@Set.instMembership K) k i))
              (Classical.propDecidable
                (@Membership.mem A (Set A) (@Set.instMembership A) dom (f i) →
                  Or (@Eq A (f i) neut) (@Membership.mem K (Set K) (@Set.instMembership K) k i)))
              (@iterato A K inst inst_1 dom neut op ltle k f)
              (op (f i) (@iterato A K inst inst_1 dom neut op ltle k f)))) := @HolLightLean.hol_opam.thm_ITERATO_CLAUSES_GEN holTheoryInst

theorem hol_ITERATO_CLAUSES : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (f : K → A),
    And
      (@Eq A
        (@iterato A K inst inst_1 dom neut op ltle
          (@EmptyCollection.emptyCollection (Set K) (@Set.instEmptyCollection K)) f)
        neut)
      (∀ (i : K) (k : Set K),
        And
            (@Set.Finite K
              (@id (Set K) fun (GEN_PVAR_275 : K) ↦
                ∃ (i' : K),
                  @setOf K
                    (fun (x' : K) ↦
                      And
                        (And (@Membership.mem K (Set K) (@Set.instMembership K) k i')
                          (@Membership.mem A (Set A) (@Set.instMembership A)
                            (@sdiff (Set A) (@Set.instSDiff A) dom
                              (@insert A (Set A) (@Set.instInsert A) neut
                                (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                            (f i')))
                        (@Eq K GEN_PVAR_275 x'))
                    i'))
            (∀ (j : K), @Membership.mem K (Set K) (@Set.instMembership K) k j → And (ltle i j) (Not (ltle j i))) →
          @Eq A (@iterato A K inst inst_1 dom neut op ltle (@insert K (Set K) (@Set.instInsert K) i k) f)
            (@ite A
              (@Membership.mem A (Set A) (@Set.instMembership A) dom (f i) →
                Or (@Eq A (f i) neut) (@Membership.mem K (Set K) (@Set.instMembership K) k i))
              (Classical.propDecidable
                (@Membership.mem A (Set A) (@Set.instMembership A) dom (f i) →
                  Or (@Eq A (f i) neut) (@Membership.mem K (Set K) (@Set.instMembership K) k i)))
              (@iterato A K inst inst_1 dom neut op ltle k f)
              (op (f i) (@iterato A K inst inst_1 dom neut op ltle k f)))) := @HolLightLean.hol_opam.thm_ITERATO_CLAUSES holTheoryInst

theorem hol_ITERATO_CLAUSES_EXISTS : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (f : K → A),
    And
      (@Eq A
        (@iterato A K inst inst_1 dom neut op ltle
          (@EmptyCollection.emptyCollection (Set K) (@Set.instEmptyCollection K)) f)
        neut)
      (∀ (k : Set K),
        And
            (@Set.Finite K
              (@id (Set K) fun (GEN_PVAR_276 : K) ↦
                ∃ (i : K),
                  @setOf K
                    (fun (x' : K) ↦
                      And
                        (And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
                          (@Membership.mem A (Set A) (@Set.instMembership A)
                            (@sdiff (Set A) (@Set.instSDiff A) dom
                              (@insert A (Set A) (@Set.instInsert A) neut
                                (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                            (f i)))
                        (@Eq K GEN_PVAR_276 x'))
                    i))
            (Not
              (@Eq (Set K)
                (@id (Set K) fun (GEN_PVAR_277 : K) ↦
                  ∃ (i : K),
                    @setOf K
                      (fun (x' : K) ↦
                        And
                          (And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
                            (@Membership.mem A (Set A) (@Set.instMembership A)
                              (@sdiff (Set A) (@Set.instSDiff A) dom
                                (@insert A (Set A) (@Set.instInsert A) neut
                                  (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                              (f i)))
                          (@Eq K GEN_PVAR_277 x'))
                      i)
                (@EmptyCollection.emptyCollection (Set K) (@Set.instEmptyCollection K)))) →
          ∃ (i : K),
            And (@Membership.mem K (Set K) (@Set.instMembership K) k i)
              (And
                (@Membership.mem A (Set A) (@Set.instMembership A)
                  (@sdiff (Set A) (@Set.instSDiff A) dom
                    (@insert A (Set A) (@Set.instInsert A) neut
                      (@EmptyCollection.emptyCollection (Set A) (@Set.instEmptyCollection A))))
                  (f i))
                (@Eq A (@iterato A K inst inst_1 dom neut op ltle k f)
                  (op (f i)
                    (@iterato A K inst inst_1 dom neut op ltle
                      (@sdiff (Set K)
                        (@Pi.sdiff K (fun (a : K) ↦ Prop) fun (i : K) ↦
                          @BooleanAlgebra.toSDiff Prop «Prop».instBooleanAlgebra)
                        k (@singleton K (Set K) (@Set.instSingletonSet K) i))
                      f))))) := @HolLightLean.hol_opam.thm_ITERATO_CLAUSES_EXISTS holTheoryInst

theorem hol_ITERATO_EQ : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (k : Set K) (f g : K → A),
    (∀ i ∈ k, f i = g i) → iterato dom neut op ltle k f = iterato dom neut op ltle k g := @HolLightLean.hol_opam.thm_ITERATO_EQ holTheoryInst

theorem hol_ITERATO_INDUCT : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (k : Set K) (f : K → A) (P : Set A),
    (P neut ∧ ∀ (i : K) (x : A), i ∈ k ∧ f i ∈ dom ∧ ¬f i = neut ∧ P x → P (op (f i) x)) →
      P (iterato dom neut op ltle k f) := @HolLightLean.hol_opam.thm_ITERATO_INDUCT holTheoryInst

theorem hol_ITERATO_CLOSED : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (dom : Set A) (neut : A) (op : A → A → A)
    (ltle : K → K → Prop) (k : Set K) (f : K → A) (P : Set A),
    (P neut ∧ (∀ (x y : A), P x ∧ P y → P (op x y)) ∧ ∀ (i : K), i ∈ k ∧ f i ∈ dom ∧ ¬f i = neut → P (f i)) →
      P (iterato dom neut op ltle k f) := @HolLightLean.hol_opam.thm_ITERATO_CLOSED holTheoryInst

theorem hol_ITERATO_ITERATE : 
  ∀ {A K : Type} [inst : Nonempty A] [inst_1 : Nonempty K] (op : A → A → A) (ltle : K → K → Prop),
    monoidal op → iterato Set.univ (neutral op) op ltle = iterate op := @HolLightLean.hol_opam.thm_ITERATO_ITERATE holTheoryInst

theorem hol_ITERATO_CLAUSES_NUMSEG_LEFT : 
  ∀ {A : Type} [inst : Nonempty A] (dom : Set A) (neut : A) (op : A → A → A) (f : ℕ → A) (m n : ℕ),
    iterato dom neut op (fun (x1 x2 : ℕ) ↦ x1 ≤ x2) (Set.Icc m n) f =
      if m ≤ n then
        if f m ∈ dom → f m = neut then
          iterato dom neut op (fun (x1 x2 : ℕ) ↦ x1 ≤ x2) (Set.Icc (m + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n) f
        else
          op (f m) (iterato dom neut op (fun (x1 x2 : ℕ) ↦ x1 ≤ x2) (Set.Icc (m + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n) f)
      else neut := @HolLightLean.hol_opam.thm_ITERATO_CLAUSES_NUMSEG_LEFT holTheoryInst

theorem hol_nproduct : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set A → (A → ℕ) → ℕ) (fun (s : Set A) (f : A → ℕ) ↦ ∏ᶠ (i : A) (_ : i ∈ s), f i)
      (iterate fun (x1 x2 : ℕ) ↦ x1 * x2) := @HolLightLean.hol_opam.thm_nproduct holTheoryInst

theorem hol_NEUTRAL_MUL : 
  (neutral fun (x1 x2 : ℕ) ↦ x1 * x2) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_NEUTRAL_MUL holTheoryInst

theorem hol_MONOIDAL_MUL : 
  monoidal fun (x1 x2 : ℕ) ↦ x1 * x2 := @HolLightLean.hol_opam.thm_MONOIDAL_MUL holTheoryInst

theorem hol_NPRODUCT_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → ℕ), ∏ᶠ (i : A) (_ : Membership.mem (γ := Set A) ∅ i), f i = (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧
      ∀ (x : B) (f : B → ℕ) (s : Set B),
        s.Finite →
          ∏ᶠ (i : B) (_ : i ∈ insert x s), f i =
            if x ∈ s then ∏ᶠ (i : B) (_ : i ∈ s), f i else f x * ∏ᶠ (i : B) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_NPRODUCT_CLAUSES holTheoryInst

theorem hol_iproduct : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set A → (A → ℤ) → ℤ) (fun (s : Set A) (f : A → ℤ) ↦ ∏ᶠ (i : A) (_ : i ∈ s), f i)
      (iterate fun (x1 x2 : ℤ) ↦ x1 * x2) := @HolLightLean.hol_opam.thm_iproduct holTheoryInst

theorem hol_NEUTRAL_INT_MUL : 
  Eq (α := ℤ) (neutral fun (x1 x2 : ℤ) ↦ x1 * x2) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_NEUTRAL_INT_MUL holTheoryInst

theorem hol_MONOIDAL_INT_MUL : 
  monoidal fun (x1 x2 : ℤ) ↦ x1 * x2 := @HolLightLean.hol_opam.thm_MONOIDAL_INT_MUL holTheoryInst

theorem hol_IPRODUCT_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → ℤ),
        Eq (α := ℤ) (∏ᶠ (i : A) (_ : Membership.mem (γ := Set A) ∅ i), f i) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∧
      ∀ (x : B) (f : B → ℤ) (s : Set B),
        s.Finite →
          ∏ᶠ (i : B) (_ : i ∈ insert x s), f i =
            if x ∈ s then ∏ᶠ (i : B) (_ : i ∈ s), f i else f x * ∏ᶠ (i : B) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_IPRODUCT_CLAUSES holTheoryInst

theorem hol_product : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set A → (A → ℝ) → ℝ) (fun (s : Set A) (f : A → ℝ) ↦ ∏ᶠ (i : A) (_ : i ∈ s), f i)
      (iterate fun (x1 x2 : ℝ) ↦ x1 * x2) := @HolLightLean.hol_opam.thm_product holTheoryInst

theorem hol_NEUTRAL_REAL_MUL : 
  Eq (α := ℝ) (neutral fun (x1 x2 : ℝ) ↦ x1 * x2) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_NEUTRAL_REAL_MUL holTheoryInst

theorem hol_MONOIDAL_REAL_MUL : 
  monoidal fun (x1 x2 : ℝ) ↦ x1 * x2 := @HolLightLean.hol_opam.thm_MONOIDAL_REAL_MUL holTheoryInst

theorem hol_PRODUCT_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → ℝ),
        Eq (α := ℝ) (∏ᶠ (i : A) (_ : Membership.mem (γ := Set A) ∅ i), f i) ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) ∧
      ∀ (x : B) (f : B → ℝ) (s : Set B),
        s.Finite →
          ∏ᶠ (i : B) (_ : i ∈ insert x s), f i =
            if x ∈ s then ∏ᶠ (i : B) (_ : i ∈ s), f i else f x * ∏ᶠ (i : B) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_PRODUCT_CLAUSES holTheoryInst

theorem hol_isum : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set A → (A → ℤ) → ℤ) (fun (s : Set A) (f : A → ℤ) ↦ ∑ᶠ (i : A) (_ : i ∈ s), f i)
      (iterate fun (x1 x2 : ℤ) ↦ x1 + x2) := @HolLightLean.hol_opam.thm_isum holTheoryInst

theorem hol_NEUTRAL_INT_ADD : 
  Eq (α := ℤ) (neutral fun (x1 x2 : ℤ) ↦ x1 + x2) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_NEUTRAL_INT_ADD holTheoryInst

theorem hol_MONOIDAL_INT_ADD : 
  monoidal fun (x1 x2 : ℤ) ↦ x1 + x2 := @HolLightLean.hol_opam.thm_MONOIDAL_INT_ADD holTheoryInst

theorem hol_ISUM_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → ℤ), Eq (α := ℤ) (∑ᶠ (i : A) (_ : Membership.mem (γ := Set A) ∅ i), f i) ↑(0 : ℕ)) ∧
      ∀ (x : B) (f : B → ℤ) (s : Set B),
        s.Finite →
          ∑ᶠ (i : B) (_ : i ∈ insert x s), f i =
            if x ∈ s then ∑ᶠ (i : B) (_ : i ∈ s), f i else f x + ∑ᶠ (i : B) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_ISUM_CLAUSES holTheoryInst

theorem hol_nsum : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set A → (A → ℕ) → ℕ) (fun (s : Set A) (f : A → ℕ) ↦ ∑ᶠ (i : A) (_ : i ∈ s), f i)
      (iterate fun (x1 x2 : ℕ) ↦ x1 + x2) := @HolLightLean.hol_opam.thm_nsum holTheoryInst

theorem hol_NEUTRAL_ADD : 
  (neutral fun (x1 x2 : ℕ) ↦ x1 + x2) = (0 : ℕ) := @HolLightLean.hol_opam.thm_NEUTRAL_ADD holTheoryInst

theorem hol_MONOIDAL_ADD : 
  monoidal fun (x1 x2 : ℕ) ↦ x1 + x2 := @HolLightLean.hol_opam.thm_MONOIDAL_ADD holTheoryInst

theorem hol_NSUM_DEGENERATE : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A),
    ¬Set.Finite (α := A)
          (id fun (GEN_PVAR_286 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬f x = (0 : ℕ)) ∧ GEN_PVAR_286 = x'} x) →
      ∑ᶠ (i : A) (_ : i ∈ s), f i = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_DEGENERATE holTheoryInst

theorem hol_NSUM_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → ℕ), ∑ᶠ (i : A) (_ : Membership.mem (γ := Set A) ∅ i), f i = (0 : ℕ)) ∧
      ∀ (x : B) (f : B → ℕ) (s : Set B),
        s.Finite →
          ∑ᶠ (i : B) (_ : i ∈ insert x s), f i =
            if x ∈ s then ∑ᶠ (i : B) (_ : i ∈ s), f i else f x + ∑ᶠ (i : B) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_NSUM_CLAUSES holTheoryInst

theorem hol_NSUM_UNION : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s t : Set A),
    s.Finite ∧ t.Finite ∧ Disjoint s t →
      ∑ᶠ (i : A) (_ : i ∈ s ∪ t), f i = HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) := @HolLightLean.hol_opam.thm_NSUM_UNION holTheoryInst

theorem hol_NSUM_DIFF : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s t : Set A),
    s.Finite ∧ t ⊆ s →
      ∑ᶠ (i : A) (_ : i ∈ s \ t), f i = HSub.hSub (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) := @HolLightLean.hol_opam.thm_NSUM_DIFF holTheoryInst

theorem hol_NSUM_INCL_EXCL : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (f : A → ℕ),
    s.Finite ∧ t.Finite →
      HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) =
        HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s ∪ t), f i) (∑ᶠ (i : A) (_ : i ∈ s ∩ t), f i) := @HolLightLean.hol_opam.thm_NSUM_INCL_EXCL holTheoryInst

theorem hol_NSUM_SUPPORT : 
  ∀ {A : Type} [inst : Nonempty A] (f : A → Nat) (s : Set A),
    @Eq Nat
      (@finsum Nat A Nat.instAddCommMonoid fun (i : A) ↦
        @finsum Nat
          (@Membership.mem A (Set A) (@Set.instMembership A)
            (@support A Nat inst (@instNeNum holTheoryInst)
              (fun (x1 x2 : Nat) ↦ @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x1 x2) f s)
            i)
          Nat.instAddCommMonoid
          fun
            (h :
              @Membership.mem A (Set A) (@Set.instMembership A)
                (@support A Nat inst (@instNeNum holTheoryInst)
                  (fun (x1 x2 : Nat) ↦ @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x1 x2) f s)
                i) ↦
          f i)
      (@finsum Nat A Nat.instAddCommMonoid fun (i : A) ↦
        @finsum Nat (@Membership.mem A (Set A) (@Set.instMembership A) s i) Nat.instAddCommMonoid
          fun (h : @Membership.mem A (Set A) (@Set.instMembership A) s i) ↦ f i) := @HolLightLean.hol_opam.thm_NSUM_SUPPORT holTheoryInst

theorem hol_NSUM_ADD : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x + g x) i =
        HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_ADD holTheoryInst

theorem hol_NSUM_ADD_GEN : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    Set.Finite (α := A)
          (id fun (GEN_PVAR_287 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬f x = (0 : ℕ)) ∧ GEN_PVAR_287 = x'} x) ∧
        Set.Finite (α := A)
          (id fun (GEN_PVAR_288 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬g x = (0 : ℕ)) ∧ GEN_PVAR_288 = x'} x) →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x + g x) i =
        HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_ADD_GEN holTheoryInst

theorem hol_NSUM_EQ_0 : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A), (∀ x ∈ s, f x = (0 : ℕ)) → ∑ᶠ (i : A) (_ : i ∈ s), f i = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_EQ_0 holTheoryInst

theorem hol_NSUM_0 : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ∑ᶠ (i : A) (_ : i ∈ s), (fun (n : A) ↦ (0 : ℕ)) i = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_0 holTheoryInst

theorem hol_NSUM_LMUL : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (c : ℕ) (s : Set A),
    ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ c * f x) i = c * ∑ᶠ (i : A) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_NSUM_LMUL holTheoryInst

theorem hol_NSUM_RMUL : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (c : ℕ) (s : Set A),
    ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x * c) i = (∑ᶠ (i : A) (_ : i ∈ s), f i) * c := @HolLightLean.hol_opam.thm_NSUM_RMUL holTheoryInst

theorem hol_NSUM_LE : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, f x ≤ g x) → LE.le (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_LE holTheoryInst

theorem hol_NSUM_LT : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    (s.Finite ∧ (∀ x ∈ s, f x ≤ g x) ∧ ∃ x ∈ s, f x < g x) →
      LT.lt (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_LT holTheoryInst

theorem hol_NSUM_LT_ALL : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x < g x) →
      LT.lt (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_LT_ALL holTheoryInst

theorem hol_NSUM_EQ : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    (∀ x ∈ s, f x = g x) → Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_EQ holTheoryInst

theorem hol_NSUM_CONST : 
  ∀ {A : Type} [inst : Nonempty A] (c : ℕ) (s : Set A),
    s.Finite → ∑ᶠ (i : A) (_ : i ∈ s), (fun (n : A) ↦ c) i = CARD s * c := @HolLightLean.hol_opam.thm_NSUM_CONST holTheoryInst

theorem hol_NSUM_POS_BOUND : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (b : ℕ) (s : Set A),
    s.Finite ∧ ∑ᶠ (i : A) (_ : i ∈ s), f i ≤ b → ∀ x ∈ s, f x ≤ b := @HolLightLean.hol_opam.thm_NSUM_POS_BOUND holTheoryInst

theorem hol_NSUM_EQ_0_IFF : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A),
    s.Finite → (∑ᶠ (i : A) (_ : i ∈ s), f i = (0 : ℕ)) = ∀ x ∈ s, f x = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_EQ_0_IFF holTheoryInst

theorem hol_NSUM_POS_LT : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A),
    (s.Finite ∧ ∃ x ∈ s, (0 : ℕ) < f x) → (0 : ℕ) < ∑ᶠ (i : A) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_NSUM_POS_LT holTheoryInst

theorem hol_NSUM_POS_LT_ALL : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (f : A → ℕ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ i ∈ s, (0 : ℕ) < f i) → (0 : ℕ) < ∑ᶠ (i : A) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_NSUM_POS_LT_ALL holTheoryInst

theorem hol_NSUM_DELETE : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A) (a : A),
    s.Finite ∧ a ∈ s → f a + ∑ᶠ (i : A) (_ : i ∈ s \ {a}), f i = ∑ᶠ (i : A) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_NSUM_DELETE holTheoryInst

theorem hol_NSUM_SING : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (x : A), ∑ᶠ (i : A) (_ : Membership.mem (γ := Set A) (insert x ∅) i), f i = f x := @HolLightLean.hol_opam.thm_NSUM_SING holTheoryInst

theorem hol_NSUM_DELTA : 
  ∀ {A : Type} [Nonempty A] (b : ℕ) (s : Set A) (a : A),
    ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if x = a then b else (0 : ℕ)) i = if a ∈ s then b else (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_DELTA holTheoryInst

theorem hol_NSUM_SWAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → ℕ) (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ (∑ᶠ (i_1 : B) (_ : i_1 ∈ t), f i i_1 : ℕ)) i)
        (∑ᶠ (i : B) (_ : i ∈ t), (fun (j : B) ↦ (∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ f i j) i : ℕ)) i) := @HolLightLean.hol_opam.thm_NSUM_SWAP holTheoryInst

theorem hol_NSUM_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : B → ℕ) (s : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) →
      Eq (α := ℕ) (∑ᶠ (i : B) (_ : i ∈ f '' s), g i) (∑ᶠ (i : A) (_ : i ∈ s), (g ∘ f) i) := @HolLightLean.hol_opam.thm_NSUM_IMAGE holTheoryInst

theorem hol_NSUM_SUPERSET : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (u v : Set A),
    (u ⊆ v ∧ ∀ (x : A), x ∈ v ∧ x ∉ u → f x = (0 : ℕ)) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ v), f i) (∑ᶠ (i : A) (_ : i ∈ u), f i) := @HolLightLean.hol_opam.thm_NSUM_SUPERSET holTheoryInst

theorem hol_NSUM_UNIV : 
  ∀ {A : Type} [inst : Nonempty A] (f : A → Nat) (s : Set A),
    @Subset (Set A) (@Set.instHasSubset A)
        (@support A Nat inst (@instNeNum holTheoryInst)
          (fun (x1 x2 : Nat) ↦ @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x1 x2) f (@Set.univ A))
        s →
      @Eq Nat
        (@finsum Nat A Nat.instAddCommMonoid fun (i : A) ↦
          @finsum Nat (@Membership.mem A (Set A) (@Set.instMembership A) s i) Nat.instAddCommMonoid
            fun (h : @Membership.mem A (Set A) (@Set.instMembership A) s i) ↦ f i)
        (@finsum Nat A Nat.instAddCommMonoid fun (i : A) ↦
          @finsum Nat (@Membership.mem A (Set A) (@Set.instMembership A) (@Set.univ A) i) Nat.instAddCommMonoid
            fun (h : @Membership.mem A (Set A) (@Set.instMembership A) (@Set.univ A) i) ↦ f i) := @HolLightLean.hol_opam.thm_NSUM_UNIV holTheoryInst

theorem hol_NSUM_UNION_RZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (u v : Set A),
    (u.Finite ∧ ∀ (x : A), x ∈ v ∧ x ∉ u → f x = (0 : ℕ)) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ u ∪ v), f i) (∑ᶠ (i : A) (_ : i ∈ u), f i) := @HolLightLean.hol_opam.thm_NSUM_UNION_RZERO holTheoryInst

theorem hol_NSUM_UNION_LZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (u v : Set A),
    (v.Finite ∧ ∀ (x : A), x ∈ u ∧ x ∉ v → f x = (0 : ℕ)) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ u ∪ v), f i) (∑ᶠ (i : A) (_ : i ∈ v), f i) := @HolLightLean.hol_opam.thm_NSUM_UNION_LZERO holTheoryInst

theorem hol_NSUM_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A),
    s.Finite →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if x ∈ s then f x else (0 : ℕ)) i)
        (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_NSUM_RESTRICT holTheoryInst

theorem hol_NSUM_BOUND : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℕ) (b : ℕ),
    (s.Finite ∧ ∀ x ∈ s, f x ≤ b) → ∑ᶠ (i : A) (_ : i ∈ s), f i ≤ CARD s * b := @HolLightLean.hol_opam.thm_NSUM_BOUND holTheoryInst

theorem hol_NSUM_BOUND_GEN : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℕ) (b : ℕ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x ≤ b / CARD s) → ∑ᶠ (i : A) (_ : i ∈ s), f i ≤ b := @HolLightLean.hol_opam.thm_NSUM_BOUND_GEN holTheoryInst

theorem hol_NSUM_BOUND_LT : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℕ) (b : ℕ),
    (s.Finite ∧ (∀ x ∈ s, f x ≤ b) ∧ ∃ x ∈ s, f x < b) → ∑ᶠ (i : A) (_ : i ∈ s), f i < CARD s * b := @HolLightLean.hol_opam.thm_NSUM_BOUND_LT holTheoryInst

theorem hol_NSUM_BOUND_LT_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℕ) (b : ℕ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x < b) → ∑ᶠ (i : A) (_ : i ∈ s), f i < CARD s * b := @HolLightLean.hol_opam.thm_NSUM_BOUND_LT_ALL holTheoryInst

theorem hol_NSUM_BOUND_LT_GEN : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℕ) (b : ℕ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x < b / CARD s) → ∑ᶠ (i : A) (_ : i ∈ s), f i < b := @HolLightLean.hol_opam.thm_NSUM_BOUND_LT_GEN holTheoryInst

theorem hol_NSUM_UNION_EQ : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s t u : Set A),
    u.Finite ∧ s ∩ t = ∅ ∧ s ∪ t = u →
      HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) = ∑ᶠ (i : A) (_ : i ∈ u), f i := @HolLightLean.hol_opam.thm_NSUM_UNION_EQ holTheoryInst

theorem hol_NSUM_EQ_SUPERSET : 
  ∀ {A : Type} [Nonempty A] (g f : A → ℕ) (s t : Set A),
    (t.Finite ∧ t ⊆ s ∧ (∀ x ∈ t, f x = g x) ∧ ∀ (x : A), x ∈ s ∧ x ∉ t → f x = (0 : ℕ)) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_NSUM_EQ_SUPERSET holTheoryInst

theorem hol_NSUM_RESTRICT_SET : 
  ∀ {A : Type} [Nonempty A] (P s : Set A) (f : A → ℕ),
    Eq (α := ℕ)
      (∑ᶠ (i : A) (_ :
        Membership.mem (γ := Set A)
          (id fun (GEN_PVAR_289 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_289 = x'} x) i),
        f i)
      (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if P x then f x else (0 : ℕ)) i) := @HolLightLean.hol_opam.thm_NSUM_RESTRICT_SET holTheoryInst

theorem hol_NSUM_NSUM_RESTRICT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : A → B → Prop) (f : A → B → ℕ) (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      Eq (α := ℕ)
        (∑ᶠ (i : A) (_ : i ∈ s),
          (fun (x : A) ↦
              (∑ᶠ (i : B) (_ :
                  Membership.mem (γ := Set B)
                    (id fun (GEN_PVAR_290 : B) ↦ ∃ (y : B), {x' : B | (y ∈ t ∧ R' x y) ∧ GEN_PVAR_290 = x'} y) i),
                  (fun (y : B) ↦ f x y) i :
                ℕ))
            i)
        (∑ᶠ (i : B) (_ : i ∈ t),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_291 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ R' x y) ∧ GEN_PVAR_291 = x'} x) i),
                  (fun (x : A) ↦ f x y) i :
                ℕ))
            i) := @HolLightLean.hol_opam.thm_NSUM_NSUM_RESTRICT holTheoryInst

theorem hol_CARD_EQ_NSUM : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    s.Finite → CARD s = ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ (0 : ℕ) + (0 : ℕ) + (1 : ℕ)) i := @HolLightLean.hol_opam.thm_CARD_EQ_NSUM holTheoryInst

theorem hol_NSUM_MULTICOUNT_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (R' : A → B → Prop) (s : Set A) (t : Set B) (k : B → ℕ),
    (s.Finite ∧
        t.Finite ∧
          ∀ j ∈ t,
            CARD (A := A) (id fun (GEN_PVAR_293 : A) ↦ ∃ (i : A), {x' : A | (i ∈ s ∧ R' i j) ∧ GEN_PVAR_293 = x'} i) =
              k j) →
      Eq (α := ℕ)
        (∑ᶠ (i : A) (_ : i ∈ s),
          (fun (i : A) ↦
              CARD (A := B) (id fun (GEN_PVAR_294 : B) ↦ ∃ (j : B), {x' : B | (j ∈ t ∧ R' i j) ∧ GEN_PVAR_294 = x'} j))
            i)
        (∑ᶠ (i : B) (_ : i ∈ t), (fun (i : B) ↦ k i) i) := @HolLightLean.hol_opam.thm_NSUM_MULTICOUNT_GEN holTheoryInst

theorem hol_NSUM_MULTICOUNT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (R' : A → B → Prop) (s : Set A) (t : Set B) (k : ℕ),
    (s.Finite ∧
        t.Finite ∧
          ∀ j ∈ t,
            CARD (A := A) (id fun (GEN_PVAR_295 : A) ↦ ∃ (i : A), {x' : A | (i ∈ s ∧ R' i j) ∧ GEN_PVAR_295 = x'} i) =
              k) →
      ∑ᶠ (i : A) (_ : i ∈ s),
          (fun (i : A) ↦
              CARD (A := B) (id fun (GEN_PVAR_296 : B) ↦ ∃ (j : B), {x' : B | (j ∈ t ∧ R' i j) ∧ GEN_PVAR_296 = x'} j))
            i =
        k * CARD t := @HolLightLean.hol_opam.thm_NSUM_MULTICOUNT holTheoryInst

theorem hol_NSUM_IMAGE_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : A → ℕ) (s : Set A),
    s.Finite →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), g i)
        (∑ᶠ (i : B) (_ : i ∈ f '' s),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_297 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = y) ∧ GEN_PVAR_297 = x'} x) i),
                  g i :
                ℕ))
            i) := @HolLightLean.hol_opam.thm_NSUM_IMAGE_GEN holTheoryInst

theorem hol_NSUM_GROUP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : A → ℕ) (s : Set A) (t : Set B),
    s.Finite ∧ f '' s ⊆ t →
      Eq (α := ℕ)
        (∑ᶠ (i : B) (_ : i ∈ t),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_298 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = y) ∧ GEN_PVAR_298 = x'} x) i),
                  g i :
                ℕ))
            i)
        (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_GROUP holTheoryInst

theorem hol_NSUM_GROUP_RELATION : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : A → B → Prop) (g : A → ℕ) (s : Set A) (t : Set B),
    (s.Finite ∧ ∀ x ∈ s, ∃! y : B, y ∈ t ∧ R' x y) →
      Eq (α := ℕ)
        (∑ᶠ (i : B) (_ : i ∈ t),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_299 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ R' x y) ∧ GEN_PVAR_299 = x'} x) i),
                  g i :
                ℕ))
            i)
        (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_GROUP_RELATION holTheoryInst

theorem hol_NSUM_SUBSET : 
  ∀ {A : Type} [Nonempty A] (u v : Set A) (f : A → ℕ),
    (u.Finite ∧ v.Finite ∧ ∀ x ∈ u \ v, f x = (0 : ℕ)) →
      LE.le (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ u), f i) (∑ᶠ (i : A) (_ : i ∈ v), f i) := @HolLightLean.hol_opam.thm_NSUM_SUBSET holTheoryInst

theorem hol_NSUM_SUBSET_SIMPLE : 
  ∀ {A : Type} [Nonempty A] (u v : Set A) (f : A → ℕ),
    v.Finite ∧ u ⊆ v → LE.le (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ u), f i) (∑ᶠ (i : A) (_ : i ∈ v), f i) := @HolLightLean.hol_opam.thm_NSUM_SUBSET_SIMPLE holTheoryInst

theorem hol_NSUM_LE_GEN : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℕ) (s : Set A),
    (∀ x ∈ s, f x ≤ g x) ∧
        Set.Finite (α := A)
          (id fun (GEN_PVAR_301 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬g x = (0 : ℕ)) ∧ GEN_PVAR_301 = x'} x) →
      LE.le (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_LE_GEN holTheoryInst

theorem hol_NSUM_MUL_BOUND : 
  ∀ {A : Type} [Nonempty A] (a b : A → ℕ) (s : Set A),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ a i * b i) i ≤
        HMul.hMul (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), a i) (∑ᶠ (i : A) (_ : i ∈ s), b i) := @HolLightLean.hol_opam.thm_NSUM_MUL_BOUND holTheoryInst

theorem hol_NSUM_IMAGE_NONZERO : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (d : B → ℕ) (i : A → B) (s : Set A),
    (s.Finite ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y ∧ i x = i y → d (i x) = (0 : ℕ)) →
      Eq (α := ℕ) (∑ᶠ (i_1 : B) (_ : i_1 ∈ i '' s), d i_1) (∑ᶠ (i_1 : A) (_ : i_1 ∈ s), (d ∘ i) i_1) := @HolLightLean.hol_opam.thm_NSUM_IMAGE_NONZERO holTheoryInst

theorem hol_NSUM_BIJECTION : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (p : A → A) (s : Set A),
    ((∀ x ∈ s, p x ∈ s) ∧ ∀ y ∈ s, ∃! x : A, x ∈ s ∧ p x = y) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), (f ∘ p) i) := @HolLightLean.hol_opam.thm_NSUM_BIJECTION holTheoryInst

theorem hol_NSUM_NSUM_PRODUCT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : A → B → Prop) (x : A → B → Nat),
    And (@Set.Finite A s) (∀ (i : A), @Membership.mem A (Set A) (@Set.instMembership A) s i → @Set.Finite B (t i)) →
      @Eq Nat
        (@finsum Nat A Nat.instAddCommMonoid fun (i : A) ↦
          @finsum Nat (@Membership.mem A (Set A) (@Set.instMembership A) s i) Nat.instAddCommMonoid
            fun (h : @Membership.mem A (Set A) (@Set.instMembership A) s i) ↦
            (fun (i : A) ↦
                @finsum Nat B Nat.instAddCommMonoid fun (i_1 : B) ↦
                  @finsum Nat (@Membership.mem B (Set B) (@Set.instMembership B) (t i) i_1) Nat.instAddCommMonoid
                    fun (h : @Membership.mem B (Set B) (@Set.instMembership B) (t i) i_1) ↦ x i i_1)
              i)
        (@finsum Nat (Prod A B) Nat.instAddCommMonoid fun (i : Prod A B) ↦
          @finsum Nat
            (@Membership.mem (Prod A B) (Set (Prod A B)) (@Set.instMembership (Prod A B))
              (@id (Set (Prod A B)) fun (GEN_PVAR_302 : Prod A B) ↦
                ∃ (i : A) (j : B),
                  @setOf (Prod A B)
                    (fun (x' : Prod A B) ↦
                      And
                        (And (@Membership.mem A (Set A) (@Set.instMembership A) s i)
                          (@Membership.mem B (Set B) (@Set.instMembership B) (t i) j))
                        (@Eq (Prod A B) GEN_PVAR_302 x'))
                    (@Prod.mk A B i j))
              i)
            Nat.instAddCommMonoid
            fun
              (h :
                @Membership.mem (Prod A B) (Set (Prod A B)) (@Set.instMembership (Prod A B))
                  (@id (Set (Prod A B)) fun (GEN_PVAR_302 : Prod A B) ↦
                    ∃ (i : A) (j : B),
                      @setOf (Prod A B)
                        (fun (x' : Prod A B) ↦
                          And
                            (And (@Membership.mem A (Set A) (@Set.instMembership A) s i)
                              (@Membership.mem B (Set B) (@Set.instMembership B) (t i) j))
                            (@Eq (Prod A B) GEN_PVAR_302 x'))
                        (@Prod.mk A B i j))
                  i) ↦
            @Classical.epsilon (Prod A B → Nat)
              (@instNonemptyForall_holLightLean (Prod A B) Nat (@instNeNum holTheoryInst))
              (fun (f : Prod A B → Nat) ↦ ∀ (i : A) (j : B), @Eq Nat (f (@Prod.mk A B i j)) (x i j)) i) := @HolLightLean.hol_opam.thm_NSUM_NSUM_PRODUCT holTheoryInst

theorem hol_NSUM_EQ_GENERAL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (f : A → ℕ) (g : B → ℕ) (h : A → B),
    ((∀ y ∈ t, ∃! x : A, x ∈ s ∧ h x = y) ∧ ∀ x ∈ s, h x ∈ t ∧ g (h x) = f x) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : B) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_NSUM_EQ_GENERAL holTheoryInst

theorem hol_NSUM_EQ_GENERAL_INVERSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (f : A → ℕ) (g : B → ℕ) (h : A → B) (k : B → A),
    ((∀ y ∈ t, k y ∈ s ∧ h (k y) = y) ∧ ∀ x ∈ s, h x ∈ t ∧ k (h x) = x ∧ g (h x) = f x) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : B) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_NSUM_EQ_GENERAL_INVERSES holTheoryInst

theorem hol_NSUM_INJECTION : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (p : A → A) (s : Set A),
    (s.Finite ∧ (∀ x ∈ s, p x ∈ s) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ p x = p y → x = y) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), (f ∘ p) i) (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_NSUM_INJECTION holTheoryInst

theorem hol_NSUM_UNION_NONZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s t : Set A),
    (s.Finite ∧ t.Finite ∧ ∀ x ∈ s ∩ t, f x = (0 : ℕ)) →
      ∑ᶠ (i : A) (_ : i ∈ s ∪ t), f i = HAdd.hAdd (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) := @HolLightLean.hol_opam.thm_NSUM_UNION_NONZERO holTheoryInst

theorem hol_NSUM_UNIONS_NONZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set (Set A)),
    (s.Finite ∧
        (∀ t ∈ s, t.Finite) ∧ ∀ (t1 t2 : Set A) (x : A), t1 ∈ s ∧ t2 ∈ s ∧ ¬t1 = t2 ∧ x ∈ t1 ∧ x ∈ t2 → f x = (0 : ℕ)) →
      Eq (α := ℕ) (∑ᶠ (i : A) (_ : i ∈ ⋃₀ s), f i)
        (∑ᶠ (i : Set A) (_ : i ∈ s), (fun (t : Set A) ↦ (∑ᶠ (i : A) (_ : i ∈ t), f i : ℕ)) i) := @HolLightLean.hol_opam.thm_NSUM_UNIONS_NONZERO holTheoryInst

theorem hol_NSUM_CASES : 
  ∀ {A : Type} [Nonempty A] (s P : Set A) (f g : A → ℕ),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if P x then f x else g x) i =
        HAdd.hAdd (α := ℕ)
          (∑ᶠ (i : A) (_ :
            Membership.mem (γ := Set A)
              (id fun (GEN_PVAR_303 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_303 = x'} x) i),
            f i)
          (∑ᶠ (i : A) (_ :
            Membership.mem (γ := Set A)
              (id fun (GEN_PVAR_304 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬P x) ∧ GEN_PVAR_304 = x'} x) i),
            g i) := @HolLightLean.hol_opam.thm_NSUM_CASES holTheoryInst

theorem hol_NSUM_CLOSED : 
  ∀ {A : Type} [Nonempty A] (P : Set ℕ) (f : A → ℕ) (s : Set A),
    (P (0 : ℕ) ∧ (∀ (x y : ℕ), P x ∧ P y → P (x + y)) ∧ ∀ a ∈ s, P (f a)) → P (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_NSUM_CLOSED holTheoryInst

theorem hol_NSUM_RELATED : 
  ∀ {A : Type} [Nonempty A] (R' : ℕ → ℕ → Prop) (f g : A → ℕ) (s : Set A),
    (R' (0 : ℕ) (0 : ℕ) ∧
        (∀ (m n m' n' : ℕ), R' m n ∧ R' m' n' → R' (m + m') (n + n')) ∧ s.Finite ∧ ∀ x ∈ s, R' (f x) (g x)) →
      R' (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_RELATED holTheoryInst

theorem hol_NSUM_CLOSED_NONEMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set ℕ) (f : A → ℕ) (s : Set A),
    (s.Finite ∧ ¬s = ∅ ∧ (∀ (x y : ℕ), P x ∧ P y → P (x + y)) ∧ ∀ a ∈ s, P (f a)) → P (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_NSUM_CLOSED_NONEMPTY holTheoryInst

theorem hol_NSUM_RELATED_NONEMPTY : 
  ∀ {A : Type} [Nonempty A] (R' : ℕ → ℕ → Prop) (f g : A → ℕ) (s : Set A),
    ((∀ (m n m' n' : ℕ), R' m n ∧ R' m' n' → R' (m + m') (n + n')) ∧ s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, R' (f x) (g x)) →
      R' (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_NSUM_RELATED_NONEMPTY holTheoryInst

theorem hol_NSUM_ADD_NUMSEG : 
  ∀ (f g : ℕ → ℕ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ f i + g i) i =
      HAdd.hAdd (α := ℕ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_NSUM_ADD_NUMSEG holTheoryInst

theorem hol_NSUM_LE_NUMSEG : 
  ∀ (f g : ℕ → ℕ) (m n : ℕ),
    (∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i ≤ g i) →
      LE.le (α := ℕ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_NSUM_LE_NUMSEG holTheoryInst

theorem hol_NSUM_EQ_NUMSEG : 
  ∀ (f g : ℕ → ℕ) (m n : ℕ),
    (∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i = g i) →
      Eq (α := ℕ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_NSUM_EQ_NUMSEG holTheoryInst

theorem hol_NSUM_CONST_NUMSEG : 
  ∀ (c m n : ℕ), ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (n' : ℕ) ↦ c) i = (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - m) * c := @HolLightLean.hol_opam.thm_NSUM_CONST_NUMSEG holTheoryInst

theorem hol_NSUM_EQ_0_NUMSEG : 
  ∀ (f : ℕ → ℕ) (m n : ℕ), (∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i = (0 : ℕ)) → ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_EQ_0_NUMSEG holTheoryInst

theorem hol_NSUM_EQ_0_IFF_NUMSEG : 
  ∀ (f : ℕ → ℕ) (m n : ℕ), (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i = (0 : ℕ)) = ∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_EQ_0_IFF_NUMSEG holTheoryInst

theorem hol_NSUM_TRIV_NUMSEG : 
  ∀ (f : ℕ → ℕ) (m n : ℕ), n < m → ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i = (0 : ℕ) := @HolLightLean.hol_opam.thm_NSUM_TRIV_NUMSEG holTheoryInst

theorem hol_NSUM_SING_NUMSEG : 
  ∀ (f : ℕ → ℕ) (n : ℕ), ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc n n), f i = f n := @HolLightLean.hol_opam.thm_NSUM_SING_NUMSEG holTheoryInst

theorem hol_NSUM_CLAUSES_NUMSEG : 
  ∀ (f : ℕ → ℕ),
    (∀ (m : ℕ), ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (0 : ℕ)), f i = if m = (0 : ℕ) then f (0 : ℕ) else (0 : ℕ)) ∧
      ∀ (m n : ℕ),
        ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n + (1 : ℕ))), f i =
          if m ≤ n + (1 : ℕ) then ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i + f (n + (1 : ℕ))
          else ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i := @HolLightLean.hol_opam.thm_NSUM_CLAUSES_NUMSEG holTheoryInst

theorem hol_NSUM_CLAUSES_NUMSEG_LT : 
  ∀ (f : ℕ → ℕ),
    ∑ᶠ (i : ℕ) (_ :
          Membership.mem (γ := Set ℕ)
            (id fun (GEN_PVAR_305 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < (0 : ℕ) ∧ GEN_PVAR_305 = x'} i) i),
          f i =
        (0 : ℕ) ∧
      ∀ (k : ℕ),
        ∑ᶠ (i : ℕ) (_ :
            Membership.mem (γ := Set ℕ)
              (id fun (GEN_PVAR_306 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k + (1 : ℕ) ∧ GEN_PVAR_306 = x'} i) i),
            f i =
          ∑ᶠ (i : ℕ) (_ :
              Membership.mem (γ := Set ℕ)
                (id fun (GEN_PVAR_307 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k ∧ GEN_PVAR_307 = x'} i) i),
              f i +
            f k := @HolLightLean.hol_opam.thm_NSUM_CLAUSES_NUMSEG_LT holTheoryInst

theorem hol_NSUM_CLAUSES_NUMSEG_LE : 
  ∀ (f : ℕ → ℕ),
    ∑ᶠ (i : ℕ) (_ :
          Membership.mem (γ := Set ℕ)
            (id fun (GEN_PVAR_308 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ (0 : ℕ) ∧ GEN_PVAR_308 = x'} i) i),
          f i =
        f (0 : ℕ) ∧
      ∀ (k : ℕ),
        ∑ᶠ (i : ℕ) (_ :
            Membership.mem (γ := Set ℕ)
              (id fun (GEN_PVAR_309 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k + (1 : ℕ) ∧ GEN_PVAR_309 = x'} i) i),
            f i =
          ∑ᶠ (i : ℕ) (_ :
              Membership.mem (γ := Set ℕ)
                (id fun (GEN_PVAR_310 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k ∧ GEN_PVAR_310 = x'} i) i),
              f i +
            f (k + (1 : ℕ)) := @HolLightLean.hol_opam.thm_NSUM_CLAUSES_NUMSEG_LE holTheoryInst

theorem hol_NSUM_SWAP_NUMSEG : 
  ∀ (a b c d : ℕ) (f : ℕ → ℕ → ℕ),
    Eq (α := ℕ)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc a b), (fun (i : ℕ) ↦ (∑ᶠ (i_1 : ℕ) (_ : i_1 ∈ Set.Icc c d), f i i_1 : ℕ)) i)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc c d),
        (fun (j : ℕ) ↦ (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc a b), (fun (i : ℕ) ↦ f i j) i : ℕ)) i) := @HolLightLean.hol_opam.thm_NSUM_SWAP_NUMSEG holTheoryInst

theorem hol_NSUM_ADD_SPLIT : 
  ∀ (f : ℕ → ℕ) (m n p : ℕ),
    m ≤ n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n + p)), f i =
        HAdd.hAdd (α := ℕ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i)
          (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) (n + p)), f i) := @HolLightLean.hol_opam.thm_NSUM_ADD_SPLIT holTheoryInst

theorem hol_NSUM_OFFSET : 
  ∀ (p : ℕ) (f : ℕ → ℕ) (m n : ℕ),
    Eq (α := ℕ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (m + p) (n + p)), f i)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ f (i + p)) i) := @HolLightLean.hol_opam.thm_NSUM_OFFSET holTheoryInst

theorem hol_NSUM_OFFSET_0 : 
  ∀ (f : ℕ → ℕ) (m n : ℕ),
    m ≤ n →
      Eq (α := ℕ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i)
        (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - m)), (fun (i : ℕ) ↦ f (i + m)) i) := @HolLightLean.hol_opam.thm_NSUM_OFFSET_0 holTheoryInst

theorem hol_NSUM_CLAUSES_LEFT : 
  ∀ (f : ℕ → ℕ) (m n : ℕ),
    m ≤ n →
      ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i =
        f m + ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (m + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n), f i := @HolLightLean.hol_opam.thm_NSUM_CLAUSES_LEFT holTheoryInst

theorem hol_NSUM_CLAUSES_RIGHT : 
  ∀ (f : ℕ → ℕ) (m n : ℕ),
    (0 : ℕ) < n ∧ m ≤ n →
      ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i =
        ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))), f i + f n := @HolLightLean.hol_opam.thm_NSUM_CLAUSES_RIGHT holTheoryInst

theorem hol_NSUM_PAIR : 
  ∀ (f : ℕ → ℕ) (m n : ℕ),
    Eq (α := ℕ)
      (∑ᶠ (i : ℕ) (_ :
        i ∈
          Set.Icc (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m)
            (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))),
        f i)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n),
        (fun (i : ℕ) ↦
            f (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * i) +
              f (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * i + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))))
          i) := @HolLightLean.hol_opam.thm_NSUM_PAIR holTheoryInst

theorem hol_NSUM_REFLECT : 
  ∀ (x : ℕ → ℕ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), x i =
      if n < m then (0 : ℕ) else ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - m)), (fun (i : ℕ) ↦ x (n - i)) i := @HolLightLean.hol_opam.thm_NSUM_REFLECT holTheoryInst

theorem hol_MOD_NSUM_MOD : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (n : ℕ) (s : Set A),
    s.Finite → (∑ᶠ (i : A) (_ : i ∈ s), f i) % n = (∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ f i % n) i) % n := @HolLightLean.hol_opam.thm_MOD_NSUM_MOD holTheoryInst

theorem hol_MOD_NSUM_MOD_NUMSEG : 
  ∀ (f : ℕ → ℕ) (a b n : ℕ),
    (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc a b), f i) % n = (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc a b), (fun (i : ℕ) ↦ f i % n) i) % n := @HolLightLean.hol_opam.thm_MOD_NSUM_MOD_NUMSEG holTheoryInst

theorem hol_CONG_NSUM : 
  ∀ {A : Type} [Nonempty A] (n : ℕ) (f g : A → ℕ) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, num_mod n (f x) (g x)) → num_mod n (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_CONG_NSUM holTheoryInst

theorem hol_CARD_UNIONS : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set (Set A)),
    (s.Finite ∧ (∀ t ∈ s, t.Finite) ∧ ∀ (t u : Set A), t ∈ s ∧ u ∈ s ∧ ¬t = u → t ∩ u = ∅) →
      CARD (⋃₀ s) = ∑ᶠ (i : Set A) (_ : i ∈ s), CARD i := @HolLightLean.hol_opam.thm_CARD_UNIONS holTheoryInst

theorem hol_sum : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set A → (A → ℝ) → ℝ) (fun (s : Set A) (f : A → ℝ) ↦ ∑ᶠ (i : A) (_ : i ∈ s), f i)
      (iterate fun (x1 x2 : ℝ) ↦ x1 + x2) := @HolLightLean.hol_opam.thm_sum holTheoryInst

theorem hol_NEUTRAL_REAL_ADD : 
  Eq (α := ℝ) (neutral fun (x1 x2 : ℝ) ↦ x1 + x2) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_NEUTRAL_REAL_ADD holTheoryInst

theorem hol_MONOIDAL_REAL_ADD : 
  monoidal fun (x1 x2 : ℝ) ↦ x1 + x2 := @HolLightLean.hol_opam.thm_MONOIDAL_REAL_ADD holTheoryInst

theorem hol_SUM_DEGENERATE : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    ¬Set.Finite (α := A)
          (id fun (GEN_PVAR_313 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬f x = ↑(0 : ℕ)) ∧ GEN_PVAR_313 = x'} x) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_DEGENERATE holTheoryInst

theorem hol_SUM_CLAUSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B],
    (∀ (f : A → ℝ), Eq (α := ℝ) (∑ᶠ (i : A) (_ : Membership.mem (γ := Set A) ∅ i), f i) ↑(0 : ℕ)) ∧
      ∀ (x : B) (f : B → ℝ) (s : Set B),
        s.Finite →
          ∑ᶠ (i : B) (_ : i ∈ insert x s), f i =
            if x ∈ s then ∑ᶠ (i : B) (_ : i ∈ s), f i else f x + ∑ᶠ (i : B) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_SUM_CLAUSES holTheoryInst

theorem hol_SUM_UNION : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s t : Set A),
    s.Finite ∧ t.Finite ∧ Disjoint s t →
      ∑ᶠ (i : A) (_ : i ∈ s ∪ t), f i = HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) := @HolLightLean.hol_opam.thm_SUM_UNION holTheoryInst

theorem hol_SUM_DIFF : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s t : Set A),
    s.Finite ∧ t ⊆ s →
      ∑ᶠ (i : A) (_ : i ∈ s \ t), f i = HSub.hSub (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) := @HolLightLean.hol_opam.thm_SUM_DIFF holTheoryInst

theorem hol_SUM_INCL_EXCL : 
  ∀ {A : Type} [Nonempty A] (s t : Set A) (f : A → ℝ),
    s.Finite ∧ t.Finite →
      HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) =
        HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s ∪ t), f i) (∑ᶠ (i : A) (_ : i ∈ s ∩ t), f i) := @HolLightLean.hol_opam.thm_SUM_INCL_EXCL holTheoryInst

theorem hol_SUM_SUPPORT : 
  ∀ {A : Type} [inst : Nonempty A] (f : A → Real) (s : Set A),
    @Eq Real
      (@finsum Real A Real.instAddCommMonoid fun (i : A) ↦
        @finsum Real
          (@Membership.mem A (Set A) (@Set.instMembership A)
            (@support A Real inst (@instNeReal holTheoryInst)
              (fun (x1 x2 : Real) ↦ @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) x1 x2) f s)
            i)
          Real.instAddCommMonoid
          fun
            (h :
              @Membership.mem A (Set A) (@Set.instMembership A)
                (@support A Real inst (@instNeReal holTheoryInst)
                  (fun (x1 x2 : Real) ↦ @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) x1 x2) f s)
                i) ↦
          f i)
      (@finsum Real A Real.instAddCommMonoid fun (i : A) ↦
        @finsum Real (@Membership.mem A (Set A) (@Set.instMembership A) s i) Real.instAddCommMonoid
          fun (h : @Membership.mem A (Set A) (@Set.instMembership A) s i) ↦ f i) := @HolLightLean.hol_opam.thm_SUM_SUPPORT holTheoryInst

theorem hol_SUM_ADD : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x + g x) i =
        HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_ADD holTheoryInst

theorem hol_SUM_ADD_GEN : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    Set.Finite (α := A)
          (id fun (GEN_PVAR_314 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬f x = ↑(0 : ℕ)) ∧ GEN_PVAR_314 = x'} x) ∧
        Set.Finite (α := A)
          (id fun (GEN_PVAR_315 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬g x = ↑(0 : ℕ)) ∧ GEN_PVAR_315 = x'} x) →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x + g x) i =
        HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_ADD_GEN holTheoryInst

theorem hol_SUM_EQ_0 : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    (∀ x ∈ s, f x = ↑(0 : ℕ)) → Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_EQ_0 holTheoryInst

theorem hol_SUM_0 : 
  ∀ {A : Type} [Nonempty A] (s : Set A), Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), (fun (n : A) ↦ (↑(0 : ℕ) : ℝ)) i) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_0 holTheoryInst

theorem hol_SUM_LMUL : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (c : ℝ) (s : Set A),
    ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ c * f x) i = c * ∑ᶠ (i : A) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_SUM_LMUL holTheoryInst

theorem hol_SUM_RMUL : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (c : ℝ) (s : Set A),
    ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x * c) i = (∑ᶠ (i : A) (_ : i ∈ s), f i) * c := @HolLightLean.hol_opam.thm_SUM_RMUL holTheoryInst

theorem hol_SUM_NEG : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ -f x) i) (-∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_NEG holTheoryInst

theorem hol_SUM_SUB : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ f x - g x) i =
        HSub.hSub (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_SUB holTheoryInst

theorem hol_SUM_LE : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, f x ≤ g x) → LE.le (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_LE holTheoryInst

theorem hol_SUM_LT : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    (s.Finite ∧ (∀ x ∈ s, f x ≤ g x) ∧ ∃ x ∈ s, f x < g x) →
      LT.lt (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_LT holTheoryInst

theorem hol_SUM_LT_ALL : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x < g x) →
      LT.lt (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_LT_ALL holTheoryInst

theorem hol_SUM_POS_LT : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    (s.Finite ∧ (∀ x ∈ s, ↑(0 : ℕ) ≤ f x) ∧ ∃ x ∈ s, ↑(0 : ℕ) < f x) →
      LT.lt (α := ℝ) (↑(0 : ℕ)) (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_POS_LT holTheoryInst

theorem hol_SUM_POS_LT_ALL : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (f : A → ℝ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ i ∈ s, ↑(0 : ℕ) < f i) → LT.lt (α := ℝ) (↑(0 : ℕ)) (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_POS_LT_ALL holTheoryInst

theorem hol_SUM_EQ : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    (∀ x ∈ s, f x = g x) → Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_EQ holTheoryInst

theorem hol_SUM_ABS : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    s.Finite → LE.le (α := ℝ) |∑ᶠ (i : A) (_ : i ∈ s), f i| (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ |f x|) i) := @HolLightLean.hol_opam.thm_SUM_ABS holTheoryInst

theorem hol_SUM_ABS_LE : 
  ∀ {A : Type} [Nonempty A] (f g : A → ℝ) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, |f x| ≤ g x) → LE.le (α := ℝ) |∑ᶠ (i : A) (_ : i ∈ s), f i| (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_ABS_LE holTheoryInst

theorem hol_SUM_CONST : 
  ∀ {A : Type} [inst : Nonempty A] (c : ℝ) (s : Set A),
    s.Finite → ∑ᶠ (i : A) (_ : i ∈ s), (fun (n : A) ↦ c) i = ↑(CARD s) * c := @HolLightLean.hol_opam.thm_SUM_CONST holTheoryInst

theorem hol_SUM_POS_LE : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    (∀ x ∈ s, ↑(0 : ℕ) ≤ f x) → LE.le (α := ℝ) (↑(0 : ℕ)) (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_POS_LE holTheoryInst

theorem hol_SUM_POS_BOUND : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (b : ℝ) (s : Set A),
    s.Finite ∧ (∀ x ∈ s, ↑(0 : ℕ) ≤ f x) ∧ ∑ᶠ (i : A) (_ : i ∈ s), f i ≤ b → ∀ x ∈ s, f x ≤ b := @HolLightLean.hol_opam.thm_SUM_POS_BOUND holTheoryInst

theorem hol_SUM_POS_EQ_0 : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    s.Finite ∧ (∀ x ∈ s, ↑(0 : ℕ) ≤ f x) ∧ Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) ↑(0 : ℕ) → ∀ x ∈ s, f x = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_POS_EQ_0 holTheoryInst

theorem hol_SUM_ZERO_EXISTS : 
  ∀ {A : Type} [Nonempty A] (u : A → ℝ) (s : Set A),
    s.Finite ∧ Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), u i) ↑(0 : ℕ) →
      (∀ i ∈ s, u i = ↑(0 : ℕ)) ∨ ∃ (j : A) (k : A), j ∈ s ∧ u j < ↑(0 : ℕ) ∧ k ∈ s ∧ u k > ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_ZERO_EXISTS holTheoryInst

theorem hol_SUM_DELETE : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A) (a : A),
    s.Finite ∧ a ∈ s → ∑ᶠ (i : A) (_ : i ∈ s \ {a}), f i = ∑ᶠ (i : A) (_ : i ∈ s), f i - f a := @HolLightLean.hol_opam.thm_SUM_DELETE holTheoryInst

theorem hol_SUM_DELETE_CASES : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A) (a : A),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s \ {a}), f i =
        if a ∈ s then ∑ᶠ (i : A) (_ : i ∈ s), f i - f a else ∑ᶠ (i : A) (_ : i ∈ s), f i := @HolLightLean.hol_opam.thm_SUM_DELETE_CASES holTheoryInst

theorem hol_SUM_SING : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (x : A), ∑ᶠ (i : A) (_ : Membership.mem (γ := Set A) (insert x ∅) i), f i = f x := @HolLightLean.hol_opam.thm_SUM_SING holTheoryInst

theorem hol_SUM_DELTA : 
  ∀ {A : Type} [Nonempty A] (b : ℝ) (s : Set A) (a : A),
    ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if x = a then b else ↑(0 : ℕ)) i = if a ∈ s then b else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_DELTA holTheoryInst

theorem hol_SUM_SWAP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B → ℝ) (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ (∑ᶠ (i_1 : B) (_ : i_1 ∈ t), f i i_1 : ℝ)) i)
        (∑ᶠ (i : B) (_ : i ∈ t), (fun (j : B) ↦ (∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ f i j) i : ℝ)) i) := @HolLightLean.hol_opam.thm_SUM_SWAP holTheoryInst

theorem hol_SUM_IMAGE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : B → ℝ) (s : Set A),
    (∀ (x y : A), x ∈ s ∧ y ∈ s ∧ f x = f y → x = y) →
      Eq (α := ℝ) (∑ᶠ (i : B) (_ : i ∈ f '' s), g i) (∑ᶠ (i : A) (_ : i ∈ s), (g ∘ f) i) := @HolLightLean.hol_opam.thm_SUM_IMAGE holTheoryInst

theorem hol_SUM_SUPERSET : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (u v : Set A),
    (u ⊆ v ∧ ∀ (x : A), x ∈ v ∧ x ∉ u → f x = ↑(0 : ℕ)) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ v), f i) (∑ᶠ (i : A) (_ : i ∈ u), f i) := @HolLightLean.hol_opam.thm_SUM_SUPERSET holTheoryInst

theorem hol_SUM_UNIV : 
  ∀ {A : Type} [inst : Nonempty A] (f : A → Real) (s : Set A),
    @Subset (Set A) (@Set.instHasSubset A)
        (@support A Real inst (@instNeReal holTheoryInst)
          (fun (x1 x2 : Real) ↦ @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) x1 x2) f (@Set.univ A))
        s →
      @Eq Real
        (@finsum Real A Real.instAddCommMonoid fun (i : A) ↦
          @finsum Real (@Membership.mem A (Set A) (@Set.instMembership A) s i) Real.instAddCommMonoid
            fun (h : @Membership.mem A (Set A) (@Set.instMembership A) s i) ↦ f i)
        (@finsum Real A Real.instAddCommMonoid fun (i : A) ↦
          @finsum Real (@Membership.mem A (Set A) (@Set.instMembership A) (@Set.univ A) i) Real.instAddCommMonoid
            fun (h : @Membership.mem A (Set A) (@Set.instMembership A) (@Set.univ A) i) ↦ f i) := @HolLightLean.hol_opam.thm_SUM_UNIV holTheoryInst

theorem hol_SUM_UNION_RZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (u v : Set A),
    (u.Finite ∧ ∀ (x : A), x ∈ v ∧ x ∉ u → f x = ↑(0 : ℕ)) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ u ∪ v), f i) (∑ᶠ (i : A) (_ : i ∈ u), f i) := @HolLightLean.hol_opam.thm_SUM_UNION_RZERO holTheoryInst

theorem hol_SUM_UNION_LZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (u v : Set A),
    (v.Finite ∧ ∀ (x : A), x ∈ u ∧ x ∉ v → f x = ↑(0 : ℕ)) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ u ∪ v), f i) (∑ᶠ (i : A) (_ : i ∈ v), f i) := @HolLightLean.hol_opam.thm_SUM_UNION_LZERO holTheoryInst

theorem hol_SUM_RESTRICT : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set A),
    s.Finite →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if x ∈ s then f x else ↑(0 : ℕ)) i)
        (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_RESTRICT holTheoryInst

theorem hol_SUM_BOUND : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℝ) (b : ℝ),
    (s.Finite ∧ ∀ x ∈ s, f x ≤ b) → ∑ᶠ (i : A) (_ : i ∈ s), f i ≤ ↑(CARD s) * b := @HolLightLean.hol_opam.thm_SUM_BOUND holTheoryInst

theorem hol_SUM_BOUND_GEN : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℝ) (b : ℝ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x ≤ b / ↑(CARD s)) → ∑ᶠ (i : A) (_ : i ∈ s), f i ≤ b := @HolLightLean.hol_opam.thm_SUM_BOUND_GEN holTheoryInst

theorem hol_SUM_ABS_BOUND : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℝ) (b : ℝ),
    (s.Finite ∧ ∀ x ∈ s, |f x| ≤ b) → |∑ᶠ (i : A) (_ : i ∈ s), f i| ≤ ↑(CARD s) * b := @HolLightLean.hol_opam.thm_SUM_ABS_BOUND holTheoryInst

theorem hol_SUM_BOUND_LT : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℝ) (b : ℝ),
    (s.Finite ∧ (∀ x ∈ s, f x ≤ b) ∧ ∃ x ∈ s, f x < b) → ∑ᶠ (i : A) (_ : i ∈ s), f i < ↑(CARD s) * b := @HolLightLean.hol_opam.thm_SUM_BOUND_LT holTheoryInst

theorem hol_SUM_BOUND_LT_ALL : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℝ) (b : ℝ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x < b) → ∑ᶠ (i : A) (_ : i ∈ s), f i < ↑(CARD s) * b := @HolLightLean.hol_opam.thm_SUM_BOUND_LT_ALL holTheoryInst

theorem hol_SUM_BOUND_LT_GEN : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A) (f : A → ℝ) (b : ℝ),
    (s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, f x < b / ↑(CARD s)) → ∑ᶠ (i : A) (_ : i ∈ s), f i < b := @HolLightLean.hol_opam.thm_SUM_BOUND_LT_GEN holTheoryInst

theorem hol_SUM_UNION_EQ : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s t u : Set A),
    u.Finite ∧ s ∩ t = ∅ ∧ s ∪ t = u →
      HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) = ∑ᶠ (i : A) (_ : i ∈ u), f i := @HolLightLean.hol_opam.thm_SUM_UNION_EQ holTheoryInst

theorem hol_SUM_EQ_SUPERSET : 
  ∀ {A : Type} [Nonempty A] (g f : A → ℝ) (s t : Set A),
    (t.Finite ∧ t ⊆ s ∧ (∀ x ∈ t, f x = g x) ∧ ∀ (x : A), x ∈ s ∧ x ∉ t → f x = ↑(0 : ℕ)) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_SUM_EQ_SUPERSET holTheoryInst

theorem hol_SUM_RESTRICT_SET : 
  ∀ {A : Type} [Nonempty A] (P s : Set A) (f : A → ℝ),
    Eq (α := ℝ)
      (∑ᶠ (i : A) (_ :
        Membership.mem (γ := Set A)
          (id fun (GEN_PVAR_318 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_318 = x'} x) i),
        f i)
      (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if P x then f x else ↑(0 : ℕ)) i) := @HolLightLean.hol_opam.thm_SUM_RESTRICT_SET holTheoryInst

theorem hol_SUM_SUM_RESTRICT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : A → B → Prop) (f : A → B → ℝ) (s : Set A) (t : Set B),
    s.Finite ∧ t.Finite →
      Eq (α := ℝ)
        (∑ᶠ (i : A) (_ : i ∈ s),
          (fun (x : A) ↦
              (∑ᶠ (i : B) (_ :
                  Membership.mem (γ := Set B)
                    (id fun (GEN_PVAR_319 : B) ↦ ∃ (y : B), {x' : B | (y ∈ t ∧ R' x y) ∧ GEN_PVAR_319 = x'} y) i),
                  (fun (y : B) ↦ f x y) i :
                ℝ))
            i)
        (∑ᶠ (i : B) (_ : i ∈ t),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_320 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ R' x y) ∧ GEN_PVAR_320 = x'} x) i),
                  (fun (x : A) ↦ f x y) i :
                ℝ))
            i) := @HolLightLean.hol_opam.thm_SUM_SUM_RESTRICT holTheoryInst

theorem hol_CARD_EQ_SUM : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    s.Finite → Eq (α := ℝ) (↑(CARD s)) (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) : ℝ)) i) := @HolLightLean.hol_opam.thm_CARD_EQ_SUM holTheoryInst

theorem hol_SUM_MULTICOUNT_GEN : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (R' : A → B → Prop) (s : Set A) (t : Set B) (k : B → ℕ),
    (s.Finite ∧
        t.Finite ∧
          ∀ j ∈ t,
            CARD (A := A) (id fun (GEN_PVAR_322 : A) ↦ ∃ (i : A), {x' : A | (i ∈ s ∧ R' i j) ∧ GEN_PVAR_322 = x'} i) =
              k j) →
      Eq (α := ℝ)
        (∑ᶠ (i : A) (_ : i ∈ s),
          (fun (i : A) ↦
              (↑(CARD (A := B)
                    (id fun (GEN_PVAR_323 : B) ↦ ∃ (j : B), {x' : B | (j ∈ t ∧ R' i j) ∧ GEN_PVAR_323 = x'} j)) :
                ℝ))
            i)
        (∑ᶠ (i : B) (_ : i ∈ t), (fun (i : B) ↦ (↑(k i) : ℝ)) i) := @HolLightLean.hol_opam.thm_SUM_MULTICOUNT_GEN holTheoryInst

theorem hol_SUM_MULTICOUNT : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (R' : A → B → Prop) (s : Set A) (t : Set B) (k : ℕ),
    (s.Finite ∧
        t.Finite ∧
          ∀ j ∈ t,
            CARD (A := A) (id fun (GEN_PVAR_324 : A) ↦ ∃ (i : A), {x' : A | (i ∈ s ∧ R' i j) ∧ GEN_PVAR_324 = x'} i) =
              k) →
      Eq (α := ℝ)
        (∑ᶠ (i : A) (_ : i ∈ s),
          (fun (i : A) ↦
              (↑(CARD (A := B)
                    (id fun (GEN_PVAR_325 : B) ↦ ∃ (j : B), {x' : B | (j ∈ t ∧ R' i j) ∧ GEN_PVAR_325 = x'} j)) :
                ℝ))
            i)
        ↑(k * CARD t) := @HolLightLean.hol_opam.thm_SUM_MULTICOUNT holTheoryInst

theorem hol_SUM_IMAGE_GEN : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : A → ℝ) (s : Set A),
    s.Finite →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), g i)
        (∑ᶠ (i : B) (_ : i ∈ f '' s),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_326 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = y) ∧ GEN_PVAR_326 = x'} x) i),
                  g i :
                ℝ))
            i) := @HolLightLean.hol_opam.thm_SUM_IMAGE_GEN holTheoryInst

theorem hol_SUM_GROUP : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : A → ℝ) (s : Set A) (t : Set B),
    s.Finite ∧ f '' s ⊆ t →
      Eq (α := ℝ)
        (∑ᶠ (i : B) (_ : i ∈ t),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_327 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ f x = y) ∧ GEN_PVAR_327 = x'} x) i),
                  g i :
                ℝ))
            i)
        (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_GROUP holTheoryInst

theorem hol_SUM_GROUP_RELATION : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (R' : A → B → Prop) (g : A → ℝ) (s : Set A) (t : Set B),
    (s.Finite ∧ ∀ x ∈ s, ∃! y : B, y ∈ t ∧ R' x y) →
      Eq (α := ℝ)
        (∑ᶠ (i : B) (_ : i ∈ t),
          (fun (y : B) ↦
              (∑ᶠ (i : A) (_ :
                  Membership.mem (γ := Set A)
                    (id fun (GEN_PVAR_328 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ R' x y) ∧ GEN_PVAR_328 = x'} x) i),
                  g i :
                ℝ))
            i)
        (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_GROUP_RELATION holTheoryInst

theorem hol_REAL_OF_NUM_SUM : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A),
    s.Finite → Eq (α := ℝ) (↑(∑ᶠ (i : A) (_ : i ∈ s), f i)) (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ (↑(f x) : ℝ)) i) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_SUM holTheoryInst

theorem hol_SUM_SUBSET : 
  ∀ {A : Type} [Nonempty A] (u v : Set A) (f : A → ℝ),
    (u.Finite ∧ v.Finite ∧ (∀ x ∈ u \ v, f x ≤ ↑(0 : ℕ)) ∧ ∀ x ∈ v \ u, ↑(0 : ℕ) ≤ f x) →
      LE.le (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ u), f i) (∑ᶠ (i : A) (_ : i ∈ v), f i) := @HolLightLean.hol_opam.thm_SUM_SUBSET holTheoryInst

theorem hol_SUM_SUBSET_SIMPLE : 
  ∀ {A : Type} [Nonempty A] (u v : Set A) (f : A → ℝ),
    (v.Finite ∧ u ⊆ v ∧ ∀ x ∈ v \ u, ↑(0 : ℕ) ≤ f x) →
      LE.le (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ u), f i) (∑ᶠ (i : A) (_ : i ∈ v), f i) := @HolLightLean.hol_opam.thm_SUM_SUBSET_SIMPLE holTheoryInst

theorem hol_SUM_MUL_BOUND : 
  ∀ {A : Type} [Nonempty A] (a b : A → ℝ) (s : Set A),
    (s.Finite ∧ ∀ i ∈ s, ↑(0 : ℕ) ≤ a i ∧ ↑(0 : ℕ) ≤ b i) →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (i : A) ↦ a i * b i) i ≤
        HMul.hMul (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), a i) (∑ᶠ (i : A) (_ : i ∈ s), b i) := @HolLightLean.hol_opam.thm_SUM_MUL_BOUND holTheoryInst

theorem hol_SUM_IMAGE_NONZERO : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (d : B → ℝ) (i : A → B) (s : Set A),
    (s.Finite ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ ¬x = y ∧ i x = i y → d (i x) = ↑(0 : ℕ)) →
      Eq (α := ℝ) (∑ᶠ (i_1 : B) (_ : i_1 ∈ i '' s), d i_1) (∑ᶠ (i_1 : A) (_ : i_1 ∈ s), (d ∘ i) i_1) := @HolLightLean.hol_opam.thm_SUM_IMAGE_NONZERO holTheoryInst

theorem hol_SUM_BIJECTION : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (p : A → A) (s : Set A),
    ((∀ x ∈ s, p x ∈ s) ∧ ∀ y ∈ s, ∃! x : A, x ∈ s ∧ p x = y) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), (f ∘ p) i) := @HolLightLean.hol_opam.thm_SUM_BIJECTION holTheoryInst

theorem hol_SUM_SUM_PRODUCT : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : A → B → Prop) (x : A → B → Real),
    And (@Set.Finite A s) (∀ (i : A), @Membership.mem A (Set A) (@Set.instMembership A) s i → @Set.Finite B (t i)) →
      @Eq Real
        (@finsum Real A Real.instAddCommMonoid fun (i : A) ↦
          @finsum Real (@Membership.mem A (Set A) (@Set.instMembership A) s i) Real.instAddCommMonoid
            fun (h : @Membership.mem A (Set A) (@Set.instMembership A) s i) ↦
            (fun (i : A) ↦
                @finsum Real B Real.instAddCommMonoid fun (i_1 : B) ↦
                  @finsum Real (@Membership.mem B (Set B) (@Set.instMembership B) (t i) i_1) Real.instAddCommMonoid
                    fun (h : @Membership.mem B (Set B) (@Set.instMembership B) (t i) i_1) ↦ x i i_1)
              i)
        (@finsum Real (Prod A B) Real.instAddCommMonoid fun (i : Prod A B) ↦
          @finsum Real
            (@Membership.mem (Prod A B) (Set (Prod A B)) (@Set.instMembership (Prod A B))
              (@id (Set (Prod A B)) fun (GEN_PVAR_329 : Prod A B) ↦
                ∃ (i : A) (j : B),
                  @setOf (Prod A B)
                    (fun (x' : Prod A B) ↦
                      And
                        (And (@Membership.mem A (Set A) (@Set.instMembership A) s i)
                          (@Membership.mem B (Set B) (@Set.instMembership B) (t i) j))
                        (@Eq (Prod A B) GEN_PVAR_329 x'))
                    (@Prod.mk A B i j))
              i)
            Real.instAddCommMonoid
            fun
              (h :
                @Membership.mem (Prod A B) (Set (Prod A B)) (@Set.instMembership (Prod A B))
                  (@id (Set (Prod A B)) fun (GEN_PVAR_329 : Prod A B) ↦
                    ∃ (i : A) (j : B),
                      @setOf (Prod A B)
                        (fun (x' : Prod A B) ↦
                          And
                            (And (@Membership.mem A (Set A) (@Set.instMembership A) s i)
                              (@Membership.mem B (Set B) (@Set.instMembership B) (t i) j))
                            (@Eq (Prod A B) GEN_PVAR_329 x'))
                        (@Prod.mk A B i j))
                  i) ↦
            @Classical.epsilon (Prod A B → Real)
              (@instNonemptyForall_holLightLean (Prod A B) Real (@instNeReal holTheoryInst))
              (fun (f : Prod A B → Real) ↦ ∀ (i : A) (j : B), @Eq Real (f (@Prod.mk A B i j)) (x i j)) i) := @HolLightLean.hol_opam.thm_SUM_SUM_PRODUCT holTheoryInst

theorem hol_SUM_EQ_GENERAL : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (f : A → ℝ) (g : B → ℝ) (h : A → B),
    ((∀ y ∈ t, ∃! x : A, x ∈ s ∧ h x = y) ∧ ∀ x ∈ s, h x ∈ t ∧ g (h x) = f x) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : B) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_SUM_EQ_GENERAL holTheoryInst

theorem hol_SUM_EQ_GENERAL_INVERSES : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (s : Set A) (t : Set B) (f : A → ℝ) (g : B → ℝ) (h : A → B) (k : B → A),
    ((∀ y ∈ t, k y ∈ s ∧ h (k y) = y) ∧ ∀ x ∈ s, h x ∈ t ∧ k (h x) = x ∧ g (h x) = f x) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : B) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_SUM_EQ_GENERAL_INVERSES holTheoryInst

theorem hol_SUM_INJECTION : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (p : A → A) (s : Set A),
    (s.Finite ∧ (∀ x ∈ s, p x ∈ s) ∧ ∀ (x y : A), x ∈ s ∧ y ∈ s ∧ p x = p y → x = y) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), (f ∘ p) i) (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_INJECTION holTheoryInst

theorem hol_SUM_UNION_NONZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s t : Set A),
    (s.Finite ∧ t.Finite ∧ ∀ x ∈ s ∩ t, f x = ↑(0 : ℕ)) →
      ∑ᶠ (i : A) (_ : i ∈ s ∪ t), f i = HAdd.hAdd (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ t), f i) := @HolLightLean.hol_opam.thm_SUM_UNION_NONZERO holTheoryInst

theorem hol_SUM_UNIONS_NONZERO : 
  ∀ {A : Type} [Nonempty A] (f : A → ℝ) (s : Set (Set A)),
    (s.Finite ∧
        (∀ t ∈ s, t.Finite) ∧
          ∀ (t1 t2 : Set A) (x : A), t1 ∈ s ∧ t2 ∈ s ∧ ¬t1 = t2 ∧ x ∈ t1 ∧ x ∈ t2 → f x = ↑(0 : ℕ)) →
      Eq (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ ⋃₀ s), f i)
        (∑ᶠ (i : Set A) (_ : i ∈ s), (fun (t : Set A) ↦ (∑ᶠ (i : A) (_ : i ∈ t), f i : ℝ)) i) := @HolLightLean.hol_opam.thm_SUM_UNIONS_NONZERO holTheoryInst

theorem hol_SUM_CASES : 
  ∀ {A : Type} [Nonempty A] (s P : Set A) (f g : A → ℝ),
    s.Finite →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if P x then f x else g x) i =
        HAdd.hAdd (α := ℝ)
          (∑ᶠ (i : A) (_ :
            Membership.mem (γ := Set A)
              (id fun (GEN_PVAR_330 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ P x) ∧ GEN_PVAR_330 = x'} x) i),
            f i)
          (∑ᶠ (i : A) (_ :
            Membership.mem (γ := Set A)
              (id fun (GEN_PVAR_331 : A) ↦ ∃ (x : A), {x' : A | (x ∈ s ∧ ¬P x) ∧ GEN_PVAR_331 = x'} x) i),
            g i) := @HolLightLean.hol_opam.thm_SUM_CASES holTheoryInst

theorem hol_SUM_CASES_1 : 
  ∀ {A : Type} [Nonempty A] (y : ℝ) (f : A → ℝ) (s : Set A) (a : A),
    s.Finite ∧ a ∈ s →
      ∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ if x = a then y else f x) i = ∑ᶠ (i : A) (_ : i ∈ s), f i + (y - f a) := @HolLightLean.hol_opam.thm_SUM_CASES_1 holTheoryInst

theorem hol_SUM_LE_INCLUDED : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → ℝ) (g : B → ℝ) (s : Set A) (t : Set B) (i : B → A),
    (s.Finite ∧ t.Finite ∧ (∀ y ∈ t, ↑(0 : ℕ) ≤ g y) ∧ ∀ x ∈ s, ∃ y ∈ t, i y = x ∧ f x ≤ g y) →
      LE.le (α := ℝ) (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : B) (_ : i ∈ t), g i) := @HolLightLean.hol_opam.thm_SUM_LE_INCLUDED holTheoryInst

theorem hol_SUM_IMAGE_LE : 
  ∀ {A B : Type} [Nonempty A] [Nonempty B] (f : A → B) (g : B → ℝ) (s : Set A),
    (s.Finite ∧ ∀ x ∈ s, ↑(0 : ℕ) ≤ g (f x)) →
      LE.le (α := ℝ) (∑ᶠ (i : B) (_ : i ∈ f '' s), g i) (∑ᶠ (i : A) (_ : i ∈ s), (g ∘ f) i) := @HolLightLean.hol_opam.thm_SUM_IMAGE_LE holTheoryInst

theorem hol_SUM_CLOSED : 
  ∀ {A : Type} [Nonempty A] (P : Set ℝ) (f : A → ℝ) (s : Set A),
    (P ↑(0 : ℕ) ∧ (∀ (x y : ℝ), P x ∧ P y → P (x + y)) ∧ ∀ a ∈ s, P (f a)) → P (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_CLOSED holTheoryInst

theorem hol_SUM_RELATED : 
  ∀ {A : Type} [Nonempty A] (R' : ℝ → ℝ → Prop) (f g : A → ℝ) (s : Set A),
    (R' ↑(0 : ℕ) ↑(0 : ℕ) ∧
        (∀ (m n m' n' : ℝ), R' m n ∧ R' m' n' → R' (m + m') (n + n')) ∧ s.Finite ∧ ∀ x ∈ s, R' (f x) (g x)) →
      R' (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_RELATED holTheoryInst

theorem hol_SUM_CLOSED_NONEMPTY : 
  ∀ {A : Type} [Nonempty A] (P : Set ℝ) (f : A → ℝ) (s : Set A),
    (s.Finite ∧ ¬s = ∅ ∧ (∀ (x y : ℝ), P x ∧ P y → P (x + y)) ∧ ∀ a ∈ s, P (f a)) → P (∑ᶠ (i : A) (_ : i ∈ s), f i) := @HolLightLean.hol_opam.thm_SUM_CLOSED_NONEMPTY holTheoryInst

theorem hol_SUM_RELATED_NONEMPTY : 
  ∀ {A : Type} [Nonempty A] (R' : ℝ → ℝ → Prop) (f g : A → ℝ) (s : Set A),
    ((∀ (m n m' n' : ℝ), R' m n ∧ R' m' n' → R' (m + m') (n + n')) ∧ s.Finite ∧ ¬s = ∅ ∧ ∀ x ∈ s, R' (f x) (g x)) →
      R' (∑ᶠ (i : A) (_ : i ∈ s), f i) (∑ᶠ (i : A) (_ : i ∈ s), g i) := @HolLightLean.hol_opam.thm_SUM_RELATED_NONEMPTY holTheoryInst

theorem hol_REAL_OF_NUM_SUM_GEN : 
  ∀ {A : Type} [Nonempty A] (f : A → ℕ) (s : Set A),
    Set.Finite (α := A)
        (id fun (GEN_PVAR_335 : A) ↦ ∃ (i : A), {x' : A | (i ∈ s ∧ ¬f i = (0 : ℕ)) ∧ GEN_PVAR_335 = x'} i) →
      Eq (α := ℝ) (↑(∑ᶠ (i : A) (_ : i ∈ s), f i)) (∑ᶠ (i : A) (_ : i ∈ s), (fun (x : A) ↦ (↑(f x) : ℝ)) i) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_SUM_GEN holTheoryInst

theorem hol_SUM_ADD_NUMSEG : 
  ∀ (f g : ℕ → ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ f i + g i) i =
      HAdd.hAdd (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_SUM_ADD_NUMSEG holTheoryInst

theorem hol_SUM_SUB_NUMSEG : 
  ∀ (f g : ℕ → ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ f i - g i) i =
      HSub.hSub (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_SUM_SUB_NUMSEG holTheoryInst

theorem hol_SUM_LE_NUMSEG : 
  ∀ (f g : ℕ → ℝ) (m n : ℕ),
    (∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i ≤ g i) →
      LE.le (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_SUM_LE_NUMSEG holTheoryInst

theorem hol_SUM_EQ_NUMSEG : 
  ∀ (f g : ℕ → ℝ) (m n : ℕ),
    (∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i = g i) →
      Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), g i) := @HolLightLean.hol_opam.thm_SUM_EQ_NUMSEG holTheoryInst

theorem hol_SUM_ABS_NUMSEG : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    LE.le (α := ℝ) |∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i| (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ |f i|) i) := @HolLightLean.hol_opam.thm_SUM_ABS_NUMSEG holTheoryInst

theorem hol_SUM_CONST_NUMSEG : 
  ∀ (c : ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (n' : ℕ) ↦ c) i = ↑(n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - m) * c := @HolLightLean.hol_opam.thm_SUM_CONST_NUMSEG holTheoryInst

theorem hol_SUM_EQ_0_NUMSEG : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    (∀ (i : ℕ), m ≤ i ∧ i ≤ n → f i = ↑(0 : ℕ)) → Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_EQ_0_NUMSEG holTheoryInst

theorem hol_SUM_TRIV_NUMSEG : 
  ∀ (f : ℕ → ℝ) (m n : ℕ), n < m → Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_TRIV_NUMSEG holTheoryInst

theorem hol_SUM_POS_LE_NUMSEG : 
  ∀ (m n : ℕ) (f : ℕ → ℝ),
    (∀ (p : ℕ), m ≤ p ∧ p ≤ n → ↑(0 : ℕ) ≤ f p) → LE.le (α := ℝ) (↑(0 : ℕ)) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) := @HolLightLean.hol_opam.thm_SUM_POS_LE_NUMSEG holTheoryInst

theorem hol_SUM_POS_EQ_0_NUMSEG : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    (∀ (p : ℕ), m ≤ p ∧ p ≤ n → ↑(0 : ℕ) ≤ f p) ∧ Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i) ↑(0 : ℕ) →
      ∀ (p : ℕ), m ≤ p ∧ p ≤ n → f p = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_POS_EQ_0_NUMSEG holTheoryInst

theorem hol_SUM_SING_NUMSEG : 
  ∀ (f : ℕ → ℝ) (n : ℕ), ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc n n), f i = f n := @HolLightLean.hol_opam.thm_SUM_SING_NUMSEG holTheoryInst

theorem hol_SUM_CLAUSES_NUMSEG : 
  ∀ (f : ℕ → ℝ),
    (∀ (m : ℕ), ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (0 : ℕ)), f i = if m = (0 : ℕ) then f (0 : ℕ) else ↑(0 : ℕ)) ∧
      ∀ (m n : ℕ),
        ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n + (1 : ℕ))), f i =
          if m ≤ n + (1 : ℕ) then ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i + f (n + (1 : ℕ))
          else ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i := @HolLightLean.hol_opam.thm_SUM_CLAUSES_NUMSEG holTheoryInst

theorem hol_SUM_CLAUSES_NUMSEG_LT : 
  ∀ (f : ℕ → ℝ),
    Eq (α := ℝ)
        (∑ᶠ (i : ℕ) (_ :
          Membership.mem (γ := Set ℕ)
            (id fun (GEN_PVAR_336 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < (0 : ℕ) ∧ GEN_PVAR_336 = x'} i) i),
          f i)
        ↑(0 : ℕ) ∧
      ∀ (k : ℕ),
        ∑ᶠ (i : ℕ) (_ :
            Membership.mem (γ := Set ℕ)
              (id fun (GEN_PVAR_337 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k + (1 : ℕ) ∧ GEN_PVAR_337 = x'} i) i),
            f i =
          ∑ᶠ (i : ℕ) (_ :
              Membership.mem (γ := Set ℕ)
                (id fun (GEN_PVAR_338 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i < k ∧ GEN_PVAR_338 = x'} i) i),
              f i +
            f k := @HolLightLean.hol_opam.thm_SUM_CLAUSES_NUMSEG_LT holTheoryInst

theorem hol_SUM_CLAUSES_NUMSEG_LE : 
  ∀ (f : ℕ → ℝ),
    ∑ᶠ (i : ℕ) (_ :
          Membership.mem (γ := Set ℕ)
            (id fun (GEN_PVAR_339 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ (0 : ℕ) ∧ GEN_PVAR_339 = x'} i) i),
          f i =
        f (0 : ℕ) ∧
      ∀ (k : ℕ),
        ∑ᶠ (i : ℕ) (_ :
            Membership.mem (γ := Set ℕ)
              (id fun (GEN_PVAR_340 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k + (1 : ℕ) ∧ GEN_PVAR_340 = x'} i) i),
            f i =
          ∑ᶠ (i : ℕ) (_ :
              Membership.mem (γ := Set ℕ)
                (id fun (GEN_PVAR_341 : ℕ) ↦ ∃ (i : ℕ), {x' : ℕ | i ≤ k ∧ GEN_PVAR_341 = x'} i) i),
              f i +
            f (k + (1 : ℕ)) := @HolLightLean.hol_opam.thm_SUM_CLAUSES_NUMSEG_LE holTheoryInst

theorem hol_SUM_SWAP_NUMSEG : 
  ∀ (a b c d : ℕ) (f : ℕ → ℕ → ℝ),
    Eq (α := ℝ)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc a b), (fun (i : ℕ) ↦ (∑ᶠ (i_1 : ℕ) (_ : i_1 ∈ Set.Icc c d), f i i_1 : ℝ)) i)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc c d),
        (fun (j : ℕ) ↦ (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc a b), (fun (i : ℕ) ↦ f i j) i : ℝ)) i) := @HolLightLean.hol_opam.thm_SUM_SWAP_NUMSEG holTheoryInst

theorem hol_SUM_ADD_SPLIT : 
  ∀ (f : ℕ → ℝ) (m n p : ℕ),
    m ≤ n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n + p)), f i =
        HAdd.hAdd (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i)
          (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) (n + p)), f i) := @HolLightLean.hol_opam.thm_SUM_ADD_SPLIT holTheoryInst

theorem hol_SUM_OFFSET : 
  ∀ (p : ℕ) (f : ℕ → ℝ) (m n : ℕ),
    Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (m + p) (n + p)), f i)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ f (i + p)) i) := @HolLightLean.hol_opam.thm_SUM_OFFSET holTheoryInst

theorem hol_SUM_OFFSET_0 : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    m ≤ n →
      Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i)
        (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - m)), (fun (i : ℕ) ↦ f (i + m)) i) := @HolLightLean.hol_opam.thm_SUM_OFFSET_0 holTheoryInst

theorem hol_SUM_CLAUSES_LEFT : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    m ≤ n →
      ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i =
        f m + ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (m + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n), f i := @HolLightLean.hol_opam.thm_SUM_CLAUSES_LEFT holTheoryInst

theorem hol_SUM_CLAUSES_RIGHT : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    (0 : ℕ) < n ∧ m ≤ n →
      ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i =
        ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))), f i + f n := @HolLightLean.hol_opam.thm_SUM_CLAUSES_RIGHT holTheoryInst

theorem hol_SUM_PAIR : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    Eq (α := ℝ)
      (∑ᶠ (i : ℕ) (_ :
        i ∈
          Set.Icc (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * m)
            (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))),
        f i)
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n),
        (fun (i : ℕ) ↦
            f (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * i) +
              f (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * i + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))))
          i) := @HolLightLean.hol_opam.thm_SUM_PAIR holTheoryInst

theorem hol_SUM_REFLECT : 
  ∀ (x : ℕ → ℝ) (m n : ℕ),
    Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), x i)
      (if n < m then ↑(0 : ℕ) else ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - m)), (fun (i : ℕ) ↦ x (n - i)) i) := @HolLightLean.hol_opam.thm_SUM_REFLECT holTheoryInst

theorem hol_REAL_OF_NUM_SUM_NUMSEG : 
  ∀ (f : ℕ → ℕ) (m n : ℕ),
    Eq (α := ℝ) (↑(∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i))
      (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (i : ℕ) ↦ (↑(f i) : ℝ)) i) := @HolLightLean.hol_opam.thm_REAL_OF_NUM_SUM_NUMSEG holTheoryInst

theorem hol_SUM_PARTIAL_SUC : 
  ∀ (f g : ℕ → ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (k : ℕ) ↦ f k * (g (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) - g k)) i =
      if m ≤ n then
        f (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * g (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) - f m * g m -
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n),
            (fun (k : ℕ) ↦ g (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * (f (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) - f k)) i
      else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_PARTIAL_SUC holTheoryInst

theorem hol_SUM_PARTIAL_PRE : 
  ∀ (f g : ℕ → ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (k : ℕ) ↦ f k * (g k - g (k - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))))) i =
      if m ≤ n then
        f (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * g n - f m * g (m - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) -
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (k : ℕ) ↦ g k * (f (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) - f k)) i
      else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_PARTIAL_PRE holTheoryInst

theorem hol_SUM_DIFFS : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (k : ℕ) ↦ f k - f (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) i =
      if m ≤ n then f m - f (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_DIFFS holTheoryInst

theorem hol_SUM_DIFFS_ALT : 
  ∀ (f : ℕ → ℝ) (m n : ℕ),
    ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), (fun (k : ℕ) ↦ f (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) - f k) i =
      if m ≤ n then f (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) - f m else ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_SUM_DIFFS_ALT holTheoryInst

theorem hol_SUM_COMBINE_R : 
  ∀ (f : ℕ → ℝ) (m n p : ℕ),
    m ≤ n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ∧ n ≤ p →
      HAdd.hAdd (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m n), f i)
          (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (n + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) p), f i) =
        ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m p), f i := @HolLightLean.hol_opam.thm_SUM_COMBINE_R holTheoryInst

theorem hol_SUM_COMBINE_L : 
  ∀ (f : ℕ → ℝ) (m n p : ℕ),
    (0 : ℕ) < n ∧ m ≤ n ∧ n ≤ p + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) →
      HAdd.hAdd (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))), f i)
          (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc n p), f i) =
        ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc m p), f i := @HolLightLean.hol_opam.thm_SUM_COMBINE_L holTheoryInst

theorem hol_REAL_SUB_POW : 
  ∀ (x y : ℝ) (n : ℕ),
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n →
      x ^ n - y ^ n =
        (x - y) *
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))),
            (fun (i : ℕ) ↦ x ^ i * y ^ (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - i)) i := @HolLightLean.hol_opam.thm_REAL_SUB_POW holTheoryInst

theorem hol_REAL_SUB_POW_R1 : 
  ∀ (x : ℝ) (n : ℕ),
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n →
      x ^ n - ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) =
        (x - ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) *
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))), (fun (i : ℕ) ↦ x ^ i) i := @HolLightLean.hol_opam.thm_REAL_SUB_POW_R1 holTheoryInst

theorem hol_REAL_SUB_POW_L1 : 
  ∀ (x : ℝ) (n : ℕ),
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n →
      ↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - x ^ n =
        (↑((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) - x) *
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))), (fun (i : ℕ) ↦ x ^ i) i := @HolLightLean.hol_opam.thm_REAL_SUB_POW_L1 holTheoryInst

theorem hol_REAL_SUB_POLYFUN : 
  ∀ (a : ℕ → ℝ) (x y : ℝ) (n : ℕ),
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n →
      HSub.hSub (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ a i * x ^ i) i)
          (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ a i * y ^ i) i) =
        (x - y) *
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))),
            (fun (j : ℕ) ↦
                (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (j + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) n),
                    (fun (i : ℕ) ↦ a i * y ^ (i - j - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) i) *
                  x ^ j)
              i := @HolLightLean.hol_opam.thm_REAL_SUB_POLYFUN holTheoryInst

theorem hol_REAL_SUB_POLYFUN_ALT : 
  ∀ (a : ℕ → ℝ) (x y : ℝ) (n : ℕ),
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n →
      HSub.hSub (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ a i * x ^ i) i)
          (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ a i * y ^ i) i) =
        (x - y) *
          ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))),
            (fun (j : ℕ) ↦
                (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) (n - j - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))),
                    (fun (k : ℕ) ↦ a (j + (k + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)))) * y ^ k) i) *
                  x ^ j)
              i := @HolLightLean.hol_opam.thm_REAL_SUB_POLYFUN_ALT holTheoryInst

theorem hol_REAL_POLYFUN_ROOTBOUND : 
  ∀ (n : ℕ) (c : ℕ → ℝ),
    (¬∀ i ∈ Set.Icc (0 : ℕ) n, c i = ↑(0 : ℕ)) →
      Set.Finite (α := ℝ)
          (id fun (GEN_PVAR_347 : ℝ) ↦
            ∃ (x : ℝ),
              {x' : ℝ |
                  Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ c i * x ^ i) i) ↑(0 : ℕ) ∧
                    GEN_PVAR_347 = x'}
                x) ∧
        CARD (A := ℝ)
            (id fun (GEN_PVAR_348 : ℝ) ↦
              ∃ (x : ℝ),
                {x' : ℝ |
                    Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ c i * x ^ i) i) ↑(0 : ℕ) ∧
                      GEN_PVAR_348 = x'}
                  x) ≤
          n := @HolLightLean.hol_opam.thm_REAL_POLYFUN_ROOTBOUND holTheoryInst

theorem hol_REAL_POLYFUN_FINITE_ROOTS : 
  ∀ (n : ℕ) (c : ℕ → ℝ),
    Set.Finite (α := ℝ)
        (id fun (GEN_PVAR_350 : ℝ) ↦
          ∃ (x : ℝ),
            {x' : ℝ |
                Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ c i * x ^ i) i) ↑(0 : ℕ) ∧
                  GEN_PVAR_350 = x'}
              x) =
      ∃ i ∈ Set.Icc (0 : ℕ) n, ¬c i = ↑(0 : ℕ) := @HolLightLean.hol_opam.thm_REAL_POLYFUN_FINITE_ROOTS holTheoryInst

theorem hol_REAL_POLYFUN_EQ_0 : 
  ∀ (n : ℕ) (c : ℕ → ℝ),
    Eq (α := Prop)
      (∀ (x : ℝ), Eq (α := ℝ) (∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ c i * x ^ i) i) ↑(0 : ℕ))
      (∀ i ∈ Set.Icc (0 : ℕ) n, c i = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POLYFUN_EQ_0 holTheoryInst

theorem hol_REAL_POLYFUN_EQ_CONST : 
  ∀ (n : ℕ) (c : ℕ → ℝ) (k : ℝ),
    (∀ (x : ℝ), ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) n), (fun (i : ℕ) ↦ c i * x ^ i) i = k) =
      (c (0 : ℕ) = k ∧ ∀ i ∈ Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) n, c i = ↑(0 : ℕ)) := @HolLightLean.hol_opam.thm_REAL_POLYFUN_EQ_CONST holTheoryInst

theorem hol_polynomial_function : 
  ∀ (p : ℝ → ℝ),
    (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) =
      ∃ (m : ℕ) (c : ℕ → ℝ), ∀ (x : ℝ), p x = ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (0 : ℕ) m), (fun (i : ℕ) ↦ c i * x ^ i) i := @HolLightLean.hol_opam.thm_polynomial_function holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_CONST : 
  ∀ (c : ℝ), ∃ (p : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ c) x = Polynomial.eval x p := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_CONST holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_ID : 
  ∃ (p : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ x) x = Polynomial.eval x p := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_ID holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_I : 
  ∃ (p : Polynomial ℝ), ∀ (x : ℝ), id x = Polynomial.eval x p := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_I holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_ADD : 
  ∀ (p q : ℝ → ℝ),
    ((∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) ∧
        ∃ (p : Polynomial ℝ), ∀ (x : ℝ), q x = Polynomial.eval x p) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ p x + q x) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_ADD holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_LMUL : 
  ∀ (p : ℝ → ℝ) (c : ℝ),
    (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ c * p x) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_LMUL holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_RMUL : 
  ∀ (p : ℝ → ℝ) (c : ℝ),
    (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ p x * c) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_RMUL holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_NEG : 
  ∀ (p : ℝ → ℝ),
    (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ -p x) x = Polynomial.eval x p_1) =
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_NEG holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_SUB : 
  ∀ (p q : ℝ → ℝ),
    ((∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) ∧
        ∃ (p : Polynomial ℝ), ∀ (x : ℝ), q x = Polynomial.eval x p) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ p x - q x) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_SUB holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_MUL : 
  ∀ (p q : ℝ → ℝ),
    ((∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) ∧
        ∃ (p : Polynomial ℝ), ∀ (x : ℝ), q x = Polynomial.eval x p) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ p x * q x) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_MUL holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_SUM : 
  ∀ {A : Type} [Nonempty A] (s : Set A) (p : ℝ → A → ℝ),
    (s.Finite ∧ ∀ i ∈ s, ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ p x i) x = Polynomial.eval x p_1) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ (∑ᶠ (i : A) (_ : i ∈ s), p x i : ℝ)) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_SUM holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_POW : 
  ∀ (p : ℝ → ℝ) (n : ℕ),
    (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (fun (x : ℝ) ↦ p x ^ n) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_POW holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_INDUCT : 
  ∀ (P : Set (ℝ → ℝ)),
    ((P fun (x : ℝ) ↦ x) ∧
        (∀ (c : ℝ), P fun (x : ℝ) ↦ c) ∧
          (∀ (p q : ℝ → ℝ), P p ∧ P q → P fun (x : ℝ) ↦ p x + q x) ∧
            ∀ (p q : ℝ → ℝ), P p ∧ P q → P fun (x : ℝ) ↦ p x * q x) →
      ∀ (p : ℝ → ℝ), (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) → P p := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_INDUCT holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_o : 
  ∀ (p q : ℝ → ℝ),
    ((∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) ∧
        ∃ (p : Polynomial ℝ), ∀ (x : ℝ), q x = Polynomial.eval x p) →
      ∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), (p ∘ q) x = Polynomial.eval x p_1 := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_o holTheoryInst

theorem hol_POLYNOMIAL_FUNCTION_FINITE_ROOTS : 
  ∀ (p : ℝ → ℝ) (a : ℝ),
    (∃ (p_1 : Polynomial ℝ), ∀ (x : ℝ), p x = Polynomial.eval x p_1) →
      Set.Finite (α := ℝ) (id fun (GEN_PVAR_353 : ℝ) ↦ ∃ (x : ℝ), {x' : ℝ | p x = a ∧ GEN_PVAR_353 = x'} x) =
        ¬∀ (x : ℝ), p x = a := @HolLightLean.hol_opam.thm_POLYNOMIAL_FUNCTION_FINITE_ROOTS holTheoryInst

theorem hol_dimindex : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    (if Finite A then Nat.card A else (1 : ℕ)) =
      if Set.Finite (α := A) Set.univ then CARD (A := A) Set.univ else (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_dimindex holTheoryInst

theorem hol_DIMINDEX_NONZERO : 
  ∀ {A : Type} [Nonempty A] (s : Set A), ¬(if Finite A then Nat.card A else (1 : ℕ)) = (0 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_NONZERO holTheoryInst

theorem hol_DIMINDEX_GE_1 : 
  ∀ {A : Type} [Nonempty A] (s : Set A), (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_GE_1 holTheoryInst

theorem hol_DIMINDEX_UNIV : 
  ∀ {A : Type} [Nonempty A] (s : Set A),
    (if Finite A then Nat.card A else (1 : ℕ)) = if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_UNIV holTheoryInst

theorem hol_DIMINDEX_UNIQUE : 
  ∀ {A : Type} [Nonempty A] (n : ℕ),
    Set.Finite (α := A) Set.univ ∧ Set.ncard (α := A) Set.univ = n → (if Finite A then Nat.card A else (1 : ℕ)) = n := @HolLightLean.hol_opam.thm_DIMINDEX_UNIQUE holTheoryInst

theorem hol_UNIV_HAS_SIZE_DIMINDEX : 
  ∀ {N' : Type} [Nonempty N'],
    (Set.Finite (α := N') Set.univ ∧ Set.ncard (α := N') Set.univ = if Finite N' then Nat.card N' else (1 : ℕ)) =
      Set.Finite (α := N') Set.univ := @HolLightLean.hol_opam.thm_UNIV_HAS_SIZE_DIMINDEX holTheoryInst

theorem hol_HAS_SIZE_1 : 
  Set.Finite (α := Unit) Set.univ ∧ Set.ncard (α := Unit) Set.univ = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_HAS_SIZE_1 holTheoryInst

theorem hol_NUMSEG_LT_DIMINDEX : 
  ∀ {N' : Type} [Nonempty N'],
    (id fun (GEN_PVAR_354 : ℕ) ↦
        ∃ (i : ℕ), {x' : ℕ | (i < if Finite N' then Nat.card N' else (1 : ℕ)) ∧ GEN_PVAR_354 = x'} i) =
      Set.Icc (0 : ℕ) ((if Finite N' then Nat.card N' else (1 : ℕ)) - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_NUMSEG_LT_DIMINDEX holTheoryInst

theorem hol_FINITE_IMAGE_IMAGE : 
  ∀ {A : Type} [inst : Nonempty A],
    Eq (α := Set (finite_image A)) Set.univ
      (finite_index '' Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) (if Finite A then Nat.card A else (1 : ℕ))) := @HolLightLean.hol_opam.thm_FINITE_IMAGE_IMAGE holTheoryInst

theorem hol_HAS_SIZE_FINITE_IMAGE : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    Set.Finite (α := finite_image A) Set.univ ∧
      Set.ncard (α := finite_image A) Set.univ = if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_HAS_SIZE_FINITE_IMAGE holTheoryInst

theorem hol_CARD_FINITE_IMAGE : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set A),
    CARD (A := finite_image A) Set.univ = if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_CARD_FINITE_IMAGE holTheoryInst

theorem hol_FINITE_FINITE_IMAGE : 
  ∀ {A : Type} [inst : Nonempty A], Set.Finite (α := finite_image A) Set.univ := @HolLightLean.hol_opam.thm_FINITE_FINITE_IMAGE holTheoryInst

theorem hol_DIMINDEX_FINITE_IMAGE : 
  ∀ {A : Type} [inst : Nonempty A] (s : Set (finite_image A)) (t : Set A),
    (if Finite (finite_image A) then Nat.card (finite_image A) else (1 : ℕ)) = if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_FINITE_IMAGE holTheoryInst

theorem hol_FINITE_INDEX_WORKS : 
  ∀ {A : Type} [inst : Nonempty A] (i : finite_image A),
    ∃! n : ℕ, (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ n ∧ (n ≤ if Finite A then Nat.card A else (1 : ℕ)) ∧ finite_index n = i := @HolLightLean.hol_opam.thm_FINITE_INDEX_WORKS holTheoryInst

theorem hol_FINITE_INDEX_INJ : 
  ∀ {A : Type} [inst : Nonempty A] (i j : ℕ),
    ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧
        (i ≤ if Finite A then Nat.card A else (1 : ℕ)) ∧
          (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ j ∧ j ≤ if Finite A then Nat.card A else (1 : ℕ)) →
      Eq (α := finite_image A) (finite_index i) (finite_index j) = (i = j) := @HolLightLean.hol_opam.thm_FINITE_INDEX_INJ holTheoryInst

theorem hol_FORALL_FINITE_INDEX : 
  ∀ {N' : Type} [inst : Nonempty N'] (P : Set (finite_image N')),
    Eq (α := Prop) (∀ (k : finite_image N'), P k)
      (∀ (i : ℕ),
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite N' then Nat.card N' else (1 : ℕ)) → P (finite_index i)) := @HolLightLean.hol_opam.thm_FORALL_FINITE_INDEX holTheoryInst

theorem hol_finite_index : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'] (x : cart A N') (i : ℕ), dollar x i = id x (finite_index i) := @HolLightLean.hol_opam.thm_finite_index holTheoryInst

theorem hol_CART_EQ : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (x y : cart A B),
    (x = y) =
      ∀ (i : ℕ),
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite B then Nat.card B else (1 : ℕ)) → dollar x i = dollar y i := @HolLightLean.hol_opam.thm_CART_EQ holTheoryInst

theorem hol_lambda : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (g : ℕ → A),
    Eq (α := cart A B) (lambda g)
      (Classical.epsilon fun (f : cart A B) ↦
        ∀ (i : ℕ), ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite B then Nat.card B else (1 : ℕ)) → dollar f i = g i) := @HolLightLean.hol_opam.thm_lambda holTheoryInst

theorem hol_LAMBDA_BETA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (g : ℕ → A) (i : ℕ),
    ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite B then Nat.card B else (1 : ℕ)) →
      dollar (N' := B) (lambda g) i = g i := @HolLightLean.hol_opam.thm_LAMBDA_BETA holTheoryInst

theorem hol_LAMBDA_UNIQUE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (f : cart A B) (g : ℕ → A),
    (∀ (i : ℕ), ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite B then Nat.card B else (1 : ℕ)) → dollar f i = g i) =
      (lambda g = f) := @HolLightLean.hol_opam.thm_LAMBDA_UNIQUE holTheoryInst

theorem hol_LAMBDA_ETA : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B] (g : cart A B), (lambda fun (i : ℕ) ↦ dollar g i) = g := @HolLightLean.hol_opam.thm_LAMBDA_ETA holTheoryInst

theorem hol_FINITE_INDEX_INRANGE : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'] (i : ℕ),
    ∃ (k : ℕ),
      (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ k ∧
        (k ≤ if Finite N' then Nat.card N' else (1 : ℕ)) ∧ ∀ (x : cart A N'), dollar x i = dollar x k := @HolLightLean.hol_opam.thm_FINITE_INDEX_INRANGE holTheoryInst

theorem hol_FINITE_INDEX_INRANGE_2 : 
  ∀ {A B N' : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty N'] (i : ℕ),
    ∃ (k : ℕ),
      (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ k ∧
        (k ≤ if Finite N' then Nat.card N' else (1 : ℕ)) ∧
          (∀ (x : cart A N'), dollar x i = dollar x k) ∧ ∀ (y : cart B N'), dollar y i = dollar y k := @HolLightLean.hol_opam.thm_FINITE_INDEX_INRANGE_2 holTheoryInst

theorem hol_CART_EQ_FULL : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'] (x y : cart A N'),
    (x = y) = ∀ (i : ℕ), dollar x i = dollar y i := @HolLightLean.hol_opam.thm_CART_EQ_FULL holTheoryInst

theorem hol_pastecart : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (f : cart A M) (g : cart A N'),
    pastecart f g =
      lambda fun (i : ℕ) ↦
        if i ≤ if Finite M then Nat.card M else (1 : ℕ) then dollar f i
        else dollar g (i - if Finite M then Nat.card M else (1 : ℕ)) := @HolLightLean.hol_opam.thm_pastecart holTheoryInst

theorem hol_fstcart : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (f : cart A (finite_sum M N')),
    fstcart f = lambda fun (i : ℕ) ↦ dollar f i := @HolLightLean.hol_opam.thm_fstcart holTheoryInst

theorem hol_sndcart : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (f : cart A (finite_sum M N')),
    sndcart f = lambda fun (i : ℕ) ↦ dollar f (i + if Finite M then Nat.card M else (1 : ℕ)) := @HolLightLean.hol_opam.thm_sndcart holTheoryInst

theorem hol_FINITE_SUM_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Eq (α := Set (finite_sum A B)) Set.univ
      (mk_finite_sum ''
        Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))
          ((if Finite A then Nat.card A else (1 : ℕ)) + if Finite B then Nat.card B else (1 : ℕ))) := @HolLightLean.hol_opam.thm_FINITE_SUM_IMAGE holTheoryInst

theorem hol_DIMINDEX_HAS_SIZE_FINITE_SUM : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'],
    Set.Finite (α := finite_sum M N') Set.univ ∧
      Set.ncard (α := finite_sum M N') Set.univ =
        (if Finite M then Nat.card M else (1 : ℕ)) + if Finite N' then Nat.card N' else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_HAS_SIZE_FINITE_SUM holTheoryInst

theorem hol_DIMINDEX_FINITE_SUM : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'],
    (if Finite (finite_sum M N') then Nat.card (finite_sum M N') else (1 : ℕ)) =
      (if Finite M then Nat.card M else (1 : ℕ)) + if Finite N' then Nat.card N' else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_FINITE_SUM holTheoryInst

theorem hol_FSTCART_PASTECART : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x : cart A M) (y : cart A N'),
    fstcart (pastecart x y) = x := @HolLightLean.hol_opam.thm_FSTCART_PASTECART holTheoryInst

theorem hol_SNDCART_PASTECART : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x : cart A M) (y : cart A N'),
    sndcart (pastecart x y) = y := @HolLightLean.hol_opam.thm_SNDCART_PASTECART holTheoryInst

theorem hol_PASTECART_FST_SND : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (z : cart A (finite_sum M N')),
    pastecart (fstcart z) (sndcart z) = z := @HolLightLean.hol_opam.thm_PASTECART_FST_SND holTheoryInst

theorem hol_PASTECART_EQ : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x y : cart A (finite_sum M N')),
    (x = y) = (fstcart x = fstcart y ∧ sndcart x = sndcart y) := @HolLightLean.hol_opam.thm_PASTECART_EQ holTheoryInst

theorem hol_FORALL_PASTECART : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N']
    (P : Set (cart A (finite_sum M N'))),
    Eq (α := Prop) (∀ (p : cart A (finite_sum M N')), P p) (∀ (x : cart A M) (y : cart A N'), P (pastecart x y)) := @HolLightLean.hol_opam.thm_FORALL_PASTECART holTheoryInst

theorem hol_EXISTS_PASTECART : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N']
    (P : Set (cart A (finite_sum M N'))),
    (∃ (p : cart A (finite_sum M N')), P p) = ∃ (x : cart A M) (y : cart A N'), P (pastecart x y) := @HolLightLean.hol_opam.thm_EXISTS_PASTECART holTheoryInst

theorem hol_PASTECART_INJ : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x : cart A M) (y : cart A N')
    (w : cart A M) (z : cart A N'), (pastecart x y = pastecart w z) = (x = w ∧ y = z) := @HolLightLean.hol_opam.thm_PASTECART_INJ holTheoryInst

theorem hol_FSTCART_COMPONENT : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x : cart A (finite_sum M N'))
    (i : ℕ),
    ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite M then Nat.card M else (1 : ℕ)) → dollar (fstcart x) i = dollar x i := @HolLightLean.hol_opam.thm_FSTCART_COMPONENT holTheoryInst

theorem hol_SNDCART_COMPONENT : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x : cart A (finite_sum M N'))
    (i : ℕ),
    ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite N' then Nat.card N' else (1 : ℕ)) →
      dollar (sndcart x) i = dollar x (i + if Finite M then Nat.card M else (1 : ℕ)) := @HolLightLean.hol_opam.thm_SNDCART_COMPONENT holTheoryInst

theorem hol_PASTECART_COMPONENT : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    (∀ (u : cart A M) (v : cart A N') (i : ℕ),
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite M then Nat.card M else (1 : ℕ)) →
          dollar (pastecart u v) i = dollar u i) ∧
      ∀ (u : cart A M) (v : cart A N') (i : ℕ),
        ((if Finite M then Nat.card M else (1 : ℕ)) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) ≤ i ∧
            i ≤ (if Finite M then Nat.card M else (1 : ℕ)) + if Finite N' then Nat.card N' else (1 : ℕ)) →
          dollar (pastecart u v) i = dollar v (i - if Finite M then Nat.card M else (1 : ℕ)) := @HolLightLean.hol_opam.thm_PASTECART_COMPONENT holTheoryInst

theorem hol_FINITE_DIFF_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Eq (α := Set (finite_diff A B)) Set.univ
      (mk_finite_diff ''
        Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))
          (if (if Finite B then Nat.card B else (1 : ℕ)) < if Finite A then Nat.card A else (1 : ℕ) then
            (if Finite A then Nat.card A else (1 : ℕ)) - if Finite B then Nat.card B else (1 : ℕ)
          else (0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_FINITE_DIFF_IMAGE holTheoryInst

theorem hol_DIMINDEX_HAS_SIZE_FINITE_DIFF : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'],
    Set.Finite (α := finite_diff M N') Set.univ ∧
      Set.ncard (α := finite_diff M N') Set.univ =
        if (if Finite N' then Nat.card N' else (1 : ℕ)) < if Finite M then Nat.card M else (1 : ℕ) then
          (if Finite M then Nat.card M else (1 : ℕ)) - if Finite N' then Nat.card N' else (1 : ℕ)
        else (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_HAS_SIZE_FINITE_DIFF holTheoryInst

theorem hol_DIMINDEX_FINITE_DIFF : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'],
    (if Finite (finite_diff M N') then Nat.card (finite_diff M N') else (1 : ℕ)) =
      if (if Finite N' then Nat.card N' else (1 : ℕ)) < if Finite M then Nat.card M else (1 : ℕ) then
        (if Finite M then Nat.card M else (1 : ℕ)) - if Finite N' then Nat.card N' else (1 : ℕ)
      else (0 : ℕ) + (0 : ℕ) + (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_FINITE_DIFF holTheoryInst

theorem hol_FINITE_PROD_IMAGE : 
  ∀ {A B : Type} [inst : Nonempty A] [inst_1 : Nonempty B],
    Eq (α := Set (finite_prod A B)) Set.univ
      (mk_finite_prod ''
        Set.Icc ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))
          ((if Finite A then Nat.card A else (1 : ℕ)) * if Finite B then Nat.card B else (1 : ℕ))) := @HolLightLean.hol_opam.thm_FINITE_PROD_IMAGE holTheoryInst

theorem hol_DIMINDEX_HAS_SIZE_FINITE_PROD : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'],
    Set.Finite (α := finite_prod M N') Set.univ ∧
      Set.ncard (α := finite_prod M N') Set.univ =
        (if Finite M then Nat.card M else (1 : ℕ)) * if Finite N' then Nat.card N' else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_HAS_SIZE_FINITE_PROD holTheoryInst

theorem hol_DIMINDEX_FINITE_PROD : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'],
    (if Finite (finite_prod M N') then Nat.card (finite_prod M N') else (1 : ℕ)) =
      (if Finite M then Nat.card M else (1 : ℕ)) * if Finite N' then Nat.card N' else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_FINITE_PROD holTheoryInst

theorem hol_tybit0_INDUCT : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set (tybit0 A)),
    (∀ (a : finite_sum A A), P (mktybit0 a)) → ∀ (x : tybit0 A), P x := @HolLightLean.hol_opam.thm_tybit0_INDUCT holTheoryInst

theorem hol_tybit0_RECURSION : 
  ∀ {A Z' : Type} [inst : Nonempty A] [Nonempty Z'] (f : finite_sum A A → Z'),
    ∃ (fn : tybit0 A → Z'), ∀ (a : finite_sum A A), fn (mktybit0 a) = f a := @HolLightLean.hol_opam.thm_tybit0_RECURSION holTheoryInst

theorem hol_tybit1_INDUCT : 
  ∀ {A : Type} [inst : Nonempty A] (P : Set (tybit1 A)),
    (∀ (a : finite_sum (finite_sum A A) Unit), P (mktybit1 a)) → ∀ (x : tybit1 A), P x := @HolLightLean.hol_opam.thm_tybit1_INDUCT holTheoryInst

theorem hol_tybit1_RECURSION : 
  ∀ {A Z' : Type} [inst : Nonempty A] [Nonempty Z'] (f : finite_sum (finite_sum A A) Unit → Z'),
    ∃ (fn : tybit1 A → Z'), ∀ (a : finite_sum (finite_sum A A) Unit), fn (mktybit1 a) = f a := @HolLightLean.hol_opam.thm_tybit1_RECURSION holTheoryInst

theorem hol_HAS_SIZE_TYBIT0 : 
  ∀ {A : Type} [inst : Nonempty A],
    Set.Finite (α := tybit0 A) Set.univ ∧
      Set.ncard (α := tybit0 A) Set.univ =
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_HAS_SIZE_TYBIT0 holTheoryInst

theorem hol_HAS_SIZE_TYBIT1 : 
  ∀ {A : Type} [inst : Nonempty A],
    Set.Finite (α := tybit1 A) Set.univ ∧
      Set.ncard (α := tybit1 A) Set.univ =
        (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * if Finite A then Nat.card A else (1 : ℕ)) +
          ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_HAS_SIZE_TYBIT1 holTheoryInst

theorem hol_DIMINDEX_TYBIT0 : 
  ∀ {A : Type} [inst : Nonempty A],
    (if Finite (tybit0 A) then Nat.card (tybit0 A) else (1 : ℕ)) =
      ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * if Finite A then Nat.card A else (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_TYBIT0 holTheoryInst

theorem hol_DIMINDEX_TYBIT1 : 
  ∀ {A : Type} [inst : Nonempty A],
    (if Finite (tybit1 A) then Nat.card (tybit1 A) else (1 : ℕ)) =
      (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * if Finite A then Nat.card A else (1 : ℕ)) +
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_DIMINDEX_TYBIT1 holTheoryInst

theorem hol_DIMINDEX_CLAUSES : 
  ∀ {A : Type} [inst : Nonempty A],
    (if Finite Unit then Nat.card Unit else (1 : ℕ)) = (0 : ℕ) + (0 : ℕ) + (1 : ℕ) ∧
      ((if Finite (tybit0 A) then Nat.card (tybit0 A) else (1 : ℕ)) =
          ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * if Finite A then Nat.card A else (1 : ℕ)) ∧
        (if Finite (tybit1 A) then Nat.card (tybit1 A) else (1 : ℕ)) =
          (((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) * if Finite A then Nat.card A else (1 : ℕ)) +
            ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_DIMINDEX_CLAUSES holTheoryInst

theorem hol_FINITE_1 : 
  Set.Finite (α := Unit) Set.univ := @HolLightLean.hol_opam.thm_FINITE_1 holTheoryInst

theorem hol_FINITE_TYBIT0 : 
  ∀ {A : Type} [inst : Nonempty A], Set.Finite (α := tybit0 A) Set.univ := @HolLightLean.hol_opam.thm_FINITE_TYBIT0 holTheoryInst

theorem hol_FINITE_TYBIT1 : 
  ∀ {A : Type} [inst : Nonempty A], Set.Finite (α := tybit1 A) Set.univ := @HolLightLean.hol_opam.thm_FINITE_TYBIT1 holTheoryInst

theorem hol_FINITE_CLAUSES : 
  ∀ {A : Type} [inst : Nonempty A],
    Set.Finite (α := Unit) Set.univ ∧ Set.Finite (α := tybit0 A) Set.univ ∧ Set.Finite (α := tybit1 A) Set.univ := @HolLightLean.hol_opam.thm_FINITE_CLAUSES holTheoryInst

theorem hol_DIMINDEX_2 : 
  (if Finite (tybit0 Unit) then Nat.card (tybit0 Unit) else (1 : ℕ)) =
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) := @HolLightLean.hol_opam.thm_DIMINDEX_2 holTheoryInst

theorem hol_DIMINDEX_3 : 
  (if Finite (tybit1 Unit) then Nat.card (tybit1 Unit) else (1 : ℕ)) =
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) + (1 : ℕ) := @HolLightLean.hol_opam.thm_DIMINDEX_3 holTheoryInst

theorem hol_DIMINDEX_4 : 
  (if Finite (tybit0 (tybit0 Unit)) then Nat.card (tybit0 (tybit0 Unit)) else (1 : ℕ)) =
    (0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ)) +
      ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) + ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) := @HolLightLean.hol_opam.thm_DIMINDEX_4 holTheoryInst

theorem hol_FINITE_CART : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'] (P : ℕ → A → Prop),
    (∀ (i : ℕ),
        ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite N' then Nat.card N' else (1 : ℕ)) →
          Set.Finite (α := A) (id fun (GEN_PVAR_360 : A) ↦ ∃ (x : A), {x' : A | P i x ∧ GEN_PVAR_360 = x'} x)) →
      Set.Finite (α := cart A N')
        (id fun (GEN_PVAR_361 : cart A N') ↦
          ∃ (v : cart A N'),
            {x' : cart A N' |
                (∀ (i : ℕ),
                    ((0 : ℕ) + (0 : ℕ) + (1 : ℕ) ≤ i ∧ i ≤ if Finite N' then Nat.card N' else (1 : ℕ)) →
                      P i (dollar v i)) ∧
                  GEN_PVAR_361 = x'}
              v) := @HolLightLean.hol_opam.thm_FINITE_CART holTheoryInst

theorem hol_HAS_SIZE_CART_UNIV : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'] (m : ℕ),
    Set.Finite (α := A) Set.univ ∧ Set.ncard (α := A) Set.univ = m →
      Set.Finite (α := cart A N') Set.univ ∧
        Set.ncard (α := cart A N') Set.univ = m ^ if Finite N' then Nat.card N' else (1 : ℕ) := @HolLightLean.hol_opam.thm_HAS_SIZE_CART_UNIV holTheoryInst

theorem hol_CARD_CART_UNIV : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'],
    Set.Finite (α := A) Set.univ →
      CARD (A := cart A N') Set.univ = CARD (A := A) Set.univ ^ if Finite N' then Nat.card N' else (1 : ℕ) := @HolLightLean.hol_opam.thm_CARD_CART_UNIV holTheoryInst

theorem hol_FINITE_CART_UNIV : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'],
    Set.Finite (α := A) Set.univ → Set.Finite (α := cart A N') Set.univ := @HolLightLean.hol_opam.thm_FINITE_CART_UNIV holTheoryInst

theorem hol_vector : 
  ∀ {A N' : Type} [inst : Nonempty A] [inst_1 : Nonempty N'] (l : List A),
    Eq (α := cart A N') (vector l) (lambda fun (i : ℕ) ↦ EL (i - ((0 : ℕ) + (0 : ℕ) + (1 : ℕ))) l) := @HolLightLean.hol_opam.thm_vector holTheoryInst

theorem hol_IN_ELIM_PASTECART_THM : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (P : cart A M → cart A N' → Prop)
    (a : cart A M) (b : cart A N'),
    Membership.mem (γ := Set (cart A (finite_sum M N')))
        (id fun (GEN_PVAR_362 : cart A (finite_sum M N')) ↦
          ∃ (x : cart A M) (y : cart A N'), {x' : cart A (finite_sum M N') | P x y ∧ GEN_PVAR_362 = x'} (pastecart x y))
        (pastecart a b) =
      P a b := @HolLightLean.hol_opam.thm_IN_ELIM_PASTECART_THM holTheoryInst

theorem hol_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (cart A M))
    (t : Set (cart A N')),
    PCROSS s t =
      id fun (GEN_PVAR_363 : cart A (finite_sum M N')) ↦
        ∃ (x : cart A M) (y : cart A N'),
          {x' : cart A (finite_sum M N') | (x ∈ s ∧ y ∈ t) ∧ GEN_PVAR_363 = x'} (pastecart x y) := @HolLightLean.hol_opam.thm_PCROSS holTheoryInst

theorem hol_FORALL_IN_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (@cart A M inst inst_1))
    (t : Set (@cart A N' inst inst_2))
    (P : Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))),
    @Eq Prop
      (∀ (z : @cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)),
        @Membership.mem
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instMembership
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@PCROSS A M N' inst inst_1 inst_2 s t) z →
          P z)
      (∀ (x : @cart A M inst inst_1) (y : @cart A N' inst inst_2),
        And
            (@Membership.mem (@cart A M inst inst_1) (Set (@cart A M inst inst_1))
              (@Set.instMembership (@cart A M inst inst_1)) s x)
            (@Membership.mem (@cart A N' inst inst_2) (Set (@cart A N' inst inst_2))
              (@Set.instMembership (@cart A N' inst inst_2)) t y) →
          P (@pastecart A M N' inst inst_1 inst_2 x y)) := @HolLightLean.hol_opam.thm_FORALL_IN_PCROSS holTheoryInst

theorem hol_EXISTS_IN_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (@cart A M inst inst_1))
    (t : Set (@cart A N' inst inst_2))
    (P : Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))),
    @Eq Prop
      (∃ (z : @cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)),
        And
          (@Membership.mem
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instMembership
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@PCROSS A M N' inst inst_1 inst_2 s t) z)
          (P z))
      (∃ (x : @cart A M inst inst_1) (y : @cart A N' inst inst_2),
        And
          (@Membership.mem (@cart A M inst inst_1) (Set (@cart A M inst inst_1))
            (@Set.instMembership (@cart A M inst inst_1)) s x)
          (And
            (@Membership.mem (@cart A N' inst inst_2) (Set (@cart A N' inst inst_2))
              (@Set.instMembership (@cart A N' inst inst_2)) t y)
            (P (@pastecart A M N' inst inst_1 inst_2 x y)))) := @HolLightLean.hol_opam.thm_EXISTS_IN_PCROSS holTheoryInst

theorem hol_PASTECART_IN_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (@cart A M inst inst_1))
    (t : Set (@cart A N' inst inst_2)) (x : @cart A M inst inst_1) (y : @cart A N' inst inst_2),
    @Eq Prop
      (@Membership.mem
        (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))
        (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@Set.instMembership
          (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@PCROSS A M N' inst inst_1 inst_2 s t) (@pastecart A M N' inst inst_1 inst_2 x y))
      (And
        (@Membership.mem (@cart A M inst inst_1) (Set (@cart A M inst inst_1))
          (@Set.instMembership (@cart A M inst inst_1)) s x)
        (@Membership.mem (@cart A N' inst inst_2) (Set (@cart A N' inst inst_2))
          (@Set.instMembership (@cart A N' inst inst_2)) t y)) := @HolLightLean.hol_opam.thm_PASTECART_IN_PCROSS holTheoryInst

theorem hol_PCROSS_EQ_EMPTY : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (@cart A M inst inst_1))
    (t : Set (@cart A N' inst inst_2)),
    @Eq Prop
      (@Eq
        (Set
          (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
        (@PCROSS A M N' inst inst_1 inst_2 s t)
        (@EmptyCollection.emptyCollection
          (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
          (@Set.instEmptyCollection
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))))
      (Or
        (@Eq (Set (@cart A M inst inst_1)) s
          (@EmptyCollection.emptyCollection (Set (@cart A M inst inst_1))
            (@Set.instEmptyCollection (@cart A M inst inst_1))))
        (@Eq (Set (@cart A N' inst inst_2)) t
          (@EmptyCollection.emptyCollection (Set (@cart A N' inst inst_2))
            (@Set.instEmptyCollection (@cart A N' inst inst_2))))) := @HolLightLean.hol_opam.thm_PCROSS_EQ_EMPTY holTheoryInst

theorem hol_PCROSS_EMPTY : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    And
      (∀ (s : Set (@cart A M inst inst_1)),
        @Eq
          (Set
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
          (@PCROSS A M N' inst inst_1 inst_2 s
            (@EmptyCollection.emptyCollection (Set (@cart A N' inst inst_2))
              (@Set.instEmptyCollection (@cart A N' inst inst_2))))
          (@EmptyCollection.emptyCollection
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instEmptyCollection
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))))
      (∀ (t : Set (@cart A N' inst inst_2)),
        @Eq
          (Set
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
          (@PCROSS A M N' inst inst_1 inst_2
            (@EmptyCollection.emptyCollection (Set (@cart A M inst inst_1))
              (@Set.instEmptyCollection (@cart A M inst inst_1)))
            t)
          (@EmptyCollection.emptyCollection
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instEmptyCollection
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))))) := @HolLightLean.hol_opam.thm_PCROSS_EMPTY holTheoryInst

theorem hol_PCROSS_SING : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (x : @cart A M inst inst_1)
    (y : @cart A N' inst inst_2),
    @Eq
      (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
      (@PCROSS A M N' inst inst_1 inst_2
        (@insert (@cart A M inst inst_1) (Set (@cart A M inst inst_1)) (@Set.instInsert (@cart A M inst inst_1)) x
          (@EmptyCollection.emptyCollection (Set (@cart A M inst inst_1))
            (@Set.instEmptyCollection (@cart A M inst inst_1))))
        (@insert (@cart A N' inst inst_2) (Set (@cart A N' inst inst_2)) (@Set.instInsert (@cart A N' inst inst_2)) y
          (@EmptyCollection.emptyCollection (Set (@cart A N' inst inst_2))
            (@Set.instEmptyCollection (@cart A N' inst inst_2)))))
      (@insert (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))
        (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@Set.instInsert
          (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@pastecart A M N' inst inst_1 inst_2 x y)
        (@EmptyCollection.emptyCollection
          (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
          (@Set.instEmptyCollection
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2))))) := @HolLightLean.hol_opam.thm_PCROSS_SING holTheoryInst

theorem hol_SUBSET_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (@cart A M inst inst_1))
    (t : Set (@cart A N' inst inst_2)) (s' : Set (@cart A M inst inst_1)) (t' : Set (@cart A N' inst inst_2)),
    @Eq Prop
      (@Subset (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@Set.instHasSubset
          (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@PCROSS A M N' inst inst_1 inst_2 s t) (@PCROSS A M N' inst inst_1 inst_2 s' t'))
      (Or
        (@Eq (Set (@cart A M inst inst_1)) s
          (@EmptyCollection.emptyCollection (Set (@cart A M inst inst_1))
            (@Set.instEmptyCollection (@cart A M inst inst_1))))
        (Or
          (@Eq (Set (@cart A N' inst inst_2)) t
            (@EmptyCollection.emptyCollection (Set (@cart A N' inst inst_2))
              (@Set.instEmptyCollection (@cart A N' inst inst_2))))
          (And (@Subset (Set (@cart A M inst inst_1)) (@Set.instHasSubset (@cart A M inst inst_1)) s s')
            (@Subset (Set (@cart A N' inst inst_2)) (@Set.instHasSubset (@cart A N' inst inst_2)) t t')))) := @HolLightLean.hol_opam.thm_SUBSET_PCROSS holTheoryInst

theorem hol_PCROSS_MONO : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (@cart A M inst inst_1))
    (t : Set (@cart A N' inst inst_2)) (s' : Set (@cart A M inst inst_1)) (t' : Set (@cart A N' inst inst_2)),
    And (@Subset (Set (@cart A M inst inst_1)) (@Set.instHasSubset (@cart A M inst inst_1)) s s')
        (@Subset (Set (@cart A N' inst inst_2)) (@Set.instHasSubset (@cart A N' inst inst_2)) t t') →
      @Subset (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@Set.instHasSubset
          (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@PCROSS A M N' inst inst_1 inst_2 s t) (@PCROSS A M N' inst inst_1 inst_2 s' t') := @HolLightLean.hol_opam.thm_PCROSS_MONO holTheoryInst

theorem hol_PCROSS_EQ : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'] (s s' : Set (cart ℝ M)) (t t' : Set (cart ℝ N')),
    (PCROSS s t = PCROSS s' t') = ((s = ∅ ∨ t = ∅) ∧ (s' = ∅ ∨ t' = ∅) ∨ s = s' ∧ t = t') := @HolLightLean.hol_opam.thm_PCROSS_EQ holTheoryInst

theorem hol_UNIV_PCROSS_UNIV : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    Eq (α := Set (cart A (finite_sum M N'))) (PCROSS Set.univ Set.univ) Set.univ := @HolLightLean.hol_opam.thm_UNIV_PCROSS_UNIV holTheoryInst

theorem hol_HAS_SIZE_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (cart A M))
    (t : Set (cart A N')) (m n : ℕ),
    (s.Finite ∧ s.ncard = m) ∧ t.Finite ∧ t.ncard = n → Set.Finite (PCROSS s t) ∧ Set.ncard (PCROSS s t) = m * n := @HolLightLean.hol_opam.thm_HAS_SIZE_PCROSS holTheoryInst

theorem hol_FINITE_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (cart A M))
    (t : Set (cart A N')), s.Finite ∧ t.Finite → Set.Finite (PCROSS s t) := @HolLightLean.hol_opam.thm_FINITE_PCROSS holTheoryInst

theorem hol_FINITE_PCROSS_EQ : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (cart A M))
    (t : Set (cart A N')), Set.Finite (PCROSS s t) = (s = ∅ ∨ t = ∅ ∨ s.Finite ∧ t.Finite) := @HolLightLean.hol_opam.thm_FINITE_PCROSS_EQ holTheoryInst

theorem hol_IMAGE_FSTCART_PCROSS : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'] (s : Set (cart ℝ M)) (t : Set (cart ℝ N')),
    fstcart '' PCROSS s t = if t = ∅ then ∅ else s := @HolLightLean.hol_opam.thm_IMAGE_FSTCART_PCROSS holTheoryInst

theorem hol_IMAGE_SNDCART_PCROSS : 
  ∀ {M N' : Type} [inst : Nonempty M] [inst_1 : Nonempty N'] (s : Set (cart ℝ M)) (t : Set (cart ℝ N')),
    sndcart '' PCROSS s t = if s = ∅ then ∅ else t := @HolLightLean.hol_opam.thm_IMAGE_SNDCART_PCROSS holTheoryInst

theorem hol_PCROSS_INTER : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    And
      (∀ (s : Set (@cart A M inst inst_1)) (t u : Set (@cart A N' inst inst_2)),
        @Eq
          (Set
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
          (@PCROSS A M N' inst inst_1 inst_2 s
            (@Inter.inter (Set (@cart A N' inst inst_2)) (@Set.instInter (@cart A N' inst inst_2)) t u))
          (@Inter.inter
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instInter
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@PCROSS A M N' inst inst_1 inst_2 s t) (@PCROSS A M N' inst inst_1 inst_2 s u)))
      (∀ (s t : Set (@cart A M inst inst_1)) (u : Set (@cart A N' inst inst_2)),
        @Eq
          (Set
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
          (@PCROSS A M N' inst inst_1 inst_2
            (@Inter.inter (Set (@cart A M inst inst_1)) (@Set.instInter (@cart A M inst inst_1)) s t) u)
          (@Inter.inter
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instInter
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@PCROSS A M N' inst inst_1 inst_2 s u) (@PCROSS A M N' inst inst_1 inst_2 t u))) := @HolLightLean.hol_opam.thm_PCROSS_INTER holTheoryInst

theorem hol_PCROSS_UNION : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    And
      (∀ (s : Set (@cart A M inst inst_1)) (t u : Set (@cart A N' inst inst_2)),
        @Eq
          (Set
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
          (@PCROSS A M N' inst inst_1 inst_2 s
            (@Union.union (Set (@cart A N' inst inst_2)) (@Set.instUnion (@cart A N' inst inst_2)) t u))
          (@Union.union
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instUnion
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@PCROSS A M N' inst inst_1 inst_2 s t) (@PCROSS A M N' inst inst_1 inst_2 s u)))
      (∀ (s t : Set (@cart A M inst inst_1)) (u : Set (@cart A N' inst inst_2)),
        @Eq
          (Set
            (@cart A (@finite_sum M N' inst_1 inst_2) inst (@HOLTheory.ne_finite_sum holTheoryInst M N' inst_1 inst_2)))
          (@PCROSS A M N' inst inst_1 inst_2
            (@Union.union (Set (@cart A M inst inst_1)) (@Set.instUnion (@cart A M inst inst_1)) s t) u)
          (@Union.union
            (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@Set.instUnion
              (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
            (@PCROSS A M N' inst inst_1 inst_2 s u) (@PCROSS A M N' inst inst_1 inst_2 t u))) := @HolLightLean.hol_opam.thm_PCROSS_UNION holTheoryInst

theorem hol_PCROSS_DIFF : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    (∀ (s : Set (cart A M)) (t u : Set (cart A N')), PCROSS s (t \ u) = PCROSS s t \ PCROSS s u) ∧
      ∀ (s t : Set (cart A M)) (u : Set (cart A N')), PCROSS (s \ t) u = PCROSS s u \ PCROSS t u := @HolLightLean.hol_opam.thm_PCROSS_DIFF holTheoryInst

theorem hol_INTER_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N']
    (s s' : Set (@cart A M inst inst_1)) (t t' : Set (@cart A N' inst inst_2)),
    @Eq (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
      (@Inter.inter
        (Set (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@Set.instInter
          (@cart A (@finite_sum M N' inst_1 inst_2) inst (@instNeFiniteSum holTheoryInst M N' inst_1 inst_2)))
        (@PCROSS A M N' inst inst_1 inst_2 s t) (@PCROSS A M N' inst inst_1 inst_2 s' t'))
      (@PCROSS A M N' inst inst_1 inst_2
        (@Inter.inter (Set (@cart A M inst inst_1)) (@Set.instInter (@cart A M inst inst_1)) s s')
        (@Inter.inter (Set (@cart A N' inst inst_2)) (@Set.instInter (@cart A N' inst inst_2)) t t')) := @HolLightLean.hol_opam.thm_INTER_PCROSS holTheoryInst

theorem hol_PCROSS_UNIONS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    (∀ (s : Set (cart A M)) (f : Set (Set (cart A N'))),
        PCROSS s (⋃₀ f) =
          ⋃₀
            id fun (GEN_PVAR_365 : Set (cart A (finite_sum M N'))) ↦
              ∃ (t : Set (cart A N')), {x' : Set (cart A (finite_sum M N')) | t ∈ f ∧ GEN_PVAR_365 = x'} (PCROSS s t)) ∧
      ∀ (f : Set (Set (cart A M))) (t : Set (cart A N')),
        PCROSS (⋃₀ f) t =
          ⋃₀
            id fun (GEN_PVAR_366 : Set (cart A (finite_sum M N'))) ↦
              ∃ (s : Set (cart A M)), {x' : Set (cart A (finite_sum M N')) | s ∈ f ∧ GEN_PVAR_366 = x'} (PCROSS s t) := @HolLightLean.hol_opam.thm_PCROSS_UNIONS holTheoryInst

theorem hol_PCROSS_UNIONS_UNIONS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (f : Set (Set (cart A M)))
    (g : Set (Set (cart A N'))),
    PCROSS (⋃₀ f) (⋃₀ g) =
      ⋃₀
        id fun (GEN_PVAR_364 : Set (cart A (finite_sum M N'))) ↦
          ∃ (s : Set (cart A M)) (t : Set (cart A N')),
            {x' : Set (cart A (finite_sum M N')) | (s ∈ f ∧ t ∈ g) ∧ GEN_PVAR_364 = x'} (PCROSS s t) := @HolLightLean.hol_opam.thm_PCROSS_UNIONS_UNIONS holTheoryInst

theorem hol_PCROSS_INTERS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'],
    (∀ (s : Set (cart A M)) (f : Set (Set (cart A N'))),
        PCROSS s (⋂₀ f) =
          if f = ∅ then PCROSS s Set.univ
          else
            ⋂₀
              id fun (GEN_PVAR_370 : Set (cart A (finite_sum M N'))) ↦
                ∃ (t : Set (cart A N')),
                  {x' : Set (cart A (finite_sum M N')) | t ∈ f ∧ GEN_PVAR_370 = x'} (PCROSS s t)) ∧
      ∀ (f : Set (Set (cart A M))) (t : Set (cart A N')),
        PCROSS (⋂₀ f) t =
          if f = ∅ then PCROSS Set.univ t
          else
            ⋂₀
              id fun (GEN_PVAR_371 : Set (cart A (finite_sum M N'))) ↦
                ∃ (s : Set (cart A M)), {x' : Set (cart A (finite_sum M N')) | s ∈ f ∧ GEN_PVAR_371 = x'} (PCROSS s t) := @HolLightLean.hol_opam.thm_PCROSS_INTERS holTheoryInst

theorem hol_PCROSS_INTERS_INTERS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (f : Set (Set (cart A M)))
    (g : Set (Set (cart A N'))),
    PCROSS (⋂₀ f) (⋂₀ g) =
      if f = ∅ then
        ⋂₀
          id fun (GEN_PVAR_367 : Set (cart A (finite_sum M N'))) ↦
            ∃ (t : Set (cart A N')),
              {x' : Set (cart A (finite_sum M N')) | t ∈ g ∧ GEN_PVAR_367 = x'} (PCROSS Set.univ t)
      else
        if g = ∅ then
          ⋂₀
            id fun (GEN_PVAR_368 : Set (cart A (finite_sum M N'))) ↦
              ∃ (s : Set (cart A M)),
                {x' : Set (cart A (finite_sum M N')) | s ∈ f ∧ GEN_PVAR_368 = x'} (PCROSS s Set.univ)
        else
          ⋂₀
            id fun (GEN_PVAR_369 : Set (cart A (finite_sum M N'))) ↦
              ∃ (s : Set (cart A M)) (t : Set (cart A N')),
                {x' : Set (cart A (finite_sum M N')) | (s ∈ f ∧ t ∈ g) ∧ GEN_PVAR_369 = x'} (PCROSS s t) := @HolLightLean.hol_opam.thm_PCROSS_INTERS_INTERS holTheoryInst

theorem hol_DISJOINT_PCROSS : 
  ∀ {A M N' : Type} [inst : Nonempty A] [inst_1 : Nonempty M] [inst_2 : Nonempty N'] (s : Set (cart A M))
    (t : Set (cart A N')) (s' : Set (cart A M)) (t' : Set (cart A N')),
    Disjoint (PCROSS s t) (PCROSS s' t') = (Disjoint s s' ∨ Disjoint t t') := @HolLightLean.hol_opam.thm_DISJOINT_PCROSS holTheoryInst

theorem hol_CASEWISE_DEF : 
  ∀ {_138002 _138038 _138042 _138043 : Type} [inst : Nonempty _138002] [inst_1 : Nonempty _138038]
    [inst_2 : Nonempty _138042] [inst_3 : Nonempty _138043] (h : (_138038 → _138042) × (_138043 → _138038 → _138002))
    (t : List ((_138038 → _138042) × (_138043 → _138038 → _138002))) (f : _138043) (x : _138042),
    Eq (α := _138002) (CASEWISE (_138038 := _138038) [] f x) (Classical.epsilon fun (y : _138002) ↦ True) ∧
      CASEWISE (h :: t) f x =
        if ∃ (y : _138038), h.1 y = x then h.2 f (Classical.epsilon fun (y : _138038) ↦ h.1 y = x) else CASEWISE t f x := @HolLightLean.hol_opam.thm_CASEWISE_DEF holTheoryInst

theorem hol_CASEWISE : 
  ∀ {_138054 _138062 _138063 _138102 _138103 _138105 : Type} [inst : Nonempty _138054] [inst_1 : Nonempty _138062]
    [inst_2 : Nonempty _138063] [inst_3 : Nonempty _138102] [inst_4 : Nonempty _138103] [inst_5 : Nonempty _138105]
    (t : _138103 → _138105 → _138063) (s : _138105 → _138102)
    (clauses : List ((_138105 → _138102) × (_138103 → _138105 → _138063))) (f : _138103) (x : _138102),
    Eq (α := _138062) (CASEWISE (_138038 := _138054) [] f x) (Classical.epsilon fun (y : _138062) ↦ True) ∧
      CASEWISE ((s, t) :: clauses) f x =
        if ∃ (y : _138105), s y = x then t f (Classical.epsilon fun (y : _138105) ↦ s y = x) else CASEWISE clauses f x := @HolLightLean.hol_opam.thm_CASEWISE holTheoryInst

theorem hol_CASEWISE_CASES : 
  ∀ {_138194 _138195 _138197 _138204 : Type} [inst : Nonempty _138194] [inst_1 : Nonempty _138195]
    [inst_2 : Nonempty _138197] [inst_3 : Nonempty _138204]
    (clauses : List ((_138197 → _138194) × (_138195 → _138197 → _138204))) (c : _138195) (x : _138194),
    (∃ (s : _138197 → _138194) (t : _138195 → _138197 → _138204) (a : _138197),
        (s, t) ∈ clauses ∧ s a = x ∧ CASEWISE clauses c x = t c a) ∨
      (¬∃ (s : _138197 → _138194) (t : _138195 → _138197 → _138204) (a : _138197), (s, t) ∈ clauses ∧ s a = x) ∧
        CASEWISE clauses c x = Classical.epsilon fun (y : _138204) ↦ True := @HolLightLean.hol_opam.thm_CASEWISE_CASES holTheoryInst

theorem hol_CASEWISE_WORKS : 
  ∀ {A B C P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty P]
    (clauses : List ((P → A) × (C → P → B))) (c : C),
    (∀ (s : P → A) (t : C → P → B) (s' : P → A) (t' : C → P → B) (x y : P),
        (s, t) ∈ clauses ∧ (s', t') ∈ clauses ∧ s x = s' y → t c x = t' c y) →
      ALL
        (Classical.epsilon fun (f : Set ((P → A) × (C → P → B))) ↦
          ∀ (s : P → A) (t : C → P → B), f (s, t) = ∀ (x : P), CASEWISE clauses c (s x) = t c x)
        clauses := @HolLightLean.hol_opam.thm_CASEWISE_WORKS holTheoryInst

theorem hol_admissible : 
  ∀ {_138333 _138336 _138340 _138341 _138346 : Type} [inst : Nonempty _138333] [inst_1 : Nonempty _138336]
    [inst_2 : Nonempty _138340] [inst_3 : Nonempty _138341] [inst_4 : Nonempty _138346]
    (p : (_138340 → _138336) → _138346 → Prop) (lt2 : _138340 → _138333 → Prop) (s : _138346 → _138333)
    (t : (_138340 → _138336) → _138346 → _138341),
    admissible lt2 p s t =
      ∀ (f g : _138340 → _138336) (a : _138346),
        (p f a ∧ p g a ∧ ∀ (z : _138340), lt2 z (s a) → f z = g z) → t f a = t g a := @HolLightLean.hol_opam.thm_admissible holTheoryInst

theorem hol_tailadmissible : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop) (s : P → A)
    (p : (A → B) → P → Prop) (t : (A → B) → P → B),
    tailadmissible lt2 p s t =
      ∃ (P' : (A → B) → P → Prop) (G : (A → B) → P → A) (H : (A → B) → P → B),
        (∀ (f : A → B) (a : P) (y : A), P' f a ∧ lt2 y (G f a) → lt2 y (s a)) ∧
          (∀ (f g : A → B) (a : P),
              (∀ (z : A), lt2 z (s a) → f z = g z) → P' f a = P' g a ∧ G f a = G g a ∧ H f a = H g a) ∧
            ∀ (f : A → B) (a : P), p f a → t f a = if P' f a then f (G f a) else H f a := @HolLightLean.hol_opam.thm_tailadmissible holTheoryInst

theorem hol_superadmissible : 
  ∀ {_138490 _138492 _138498 : Type} [inst : Nonempty _138490] [inst_1 : Nonempty _138492] [inst_2 : Nonempty _138498]
    (lt2 : _138490 → _138490 → Prop) (p : (_138490 → _138492) → _138498 → Prop) (s : _138498 → _138490)
    (t : (_138490 → _138492) → _138498 → _138492),
    superadmissible lt2 p s t =
      (admissible lt2 (fun (f : _138490 → _138492) (a : _138498) ↦ True) s p → tailadmissible lt2 p s t) := @HolLightLean.hol_opam.thm_superadmissible holTheoryInst

theorem hol_MATCH_SEQPATTERN : 
  ∀ {_138526 _138533 : Type} [inst : Nonempty _138526] [inst_1 : Nonempty _138533] (r : _138533 → _138526 → Prop)
    (x : _138533) (s : _138533 → _138526 → Prop),
    _MATCH x (_SEQPATTERN r s) = if ∃ (y : _138526), r x y then _MATCH x r else _MATCH x s := @HolLightLean.hol_opam.thm_MATCH_SEQPATTERN holTheoryInst

theorem hol_ADMISSIBLE_CONST : 
  ∀ {_138553 _138554 _138555 _138556 _138557 : Type} [inst : Nonempty _138553] [inst_1 : Nonempty _138554]
    [inst_2 : Nonempty _138555] [inst_3 : Nonempty _138556] [inst_4 : Nonempty _138557] (lt2 : _138554 → _138553 → Prop)
    (p : (_138554 → _138555) → _138556 → Prop) (s : _138556 → _138553) (c : _138556 → _138557),
    admissible (_138341 := _138557) lt2 p s fun (f : _138554 → _138555) ↦ c := @HolLightLean.hol_opam.thm_ADMISSIBLE_CONST holTheoryInst

theorem hol_ADMISSIBLE_BASE : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop)
    (p : (A → B) → P → Prop) (s t : P → A),
    (∀ (f : A → B) (a : P), p f a → lt2 (t a) (s a)) →
      admissible (_138341 := B) lt2 p s fun (f : A → B) (x : P) ↦ f (t x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_BASE holTheoryInst

theorem hol_ADMISSIBLE_COMB : 
  ∀ {A B C D P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty D]
    [inst_4 : Nonempty P] (lt2 : A → A → Prop) (p : (A → B) → P → Prop) (s : P → A) (g : (A → B) → P → C → D)
    (y : (A → B) → P → C),
    admissible lt2 p s g ∧ admissible lt2 p s y →
      admissible (_138341 := D) lt2 p s fun (f : A → B) (x : P) ↦ g f x (y f x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_COMB holTheoryInst

theorem hol_ADMISSIBLE_RAND : 
  ∀ {A B C D P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty D]
    [inst_4 : Nonempty P] (lt2 : A → A → Prop) (p : (A → B) → P → Prop) (s : P → A) (g : P → C → D)
    (y : (A → B) → P → C),
    admissible lt2 p s y → admissible (_138341 := D) lt2 p s fun (f : A → B) (x : P) ↦ g x (y f x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_RAND holTheoryInst

theorem hol_ADMISSIBLE_LAMBDA : 
  ∀ {A B C P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty P]
    (lt2 : A → A → Prop) (p : (A → B) → P → Prop) (s : P → A) (t : (A → B) → C → P → Prop),
    (admissible (_138336 := B) (_138341 := Prop) (_138346 := C × P) lt2
        (fun (f : A → B) ↦ Classical.epsilon fun (f' : Set (C × P)) ↦ ∀ (u : C) (x : P), f' (u, x) = p f x)
        (Classical.epsilon fun (f : C × P → A) ↦ ∀ (u : C) (x : P), f (u, x) = s x) fun (f : A → B) ↦
        Classical.epsilon fun (f' : Set (C × P)) ↦ ∀ (u : C) (x : P), f' (u, x) = t f u x) →
      admissible (_138341 := Set C) lt2 p s fun (f : A → B) (x : P) (u : C) ↦ t f u x := @HolLightLean.hol_opam.thm_ADMISSIBLE_LAMBDA holTheoryInst

theorem hol_ADMISSIBLE_NEST : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop)
    (p : (A → B) → P → Prop) (s : P → A) (t : (A → B) → P → A),
    (admissible lt2 p s t ∧ ∀ (f : A → B) (a : P), p f a → lt2 (t f a) (s a)) →
      admissible (_138341 := B) lt2 p s fun (f : A → B) (x : P) ↦ f (t f x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_NEST holTheoryInst

theorem hol_ADMISSIBLE_COND : 
  ∀ {_138890 _138891 _138922 _138947 P : Type} [inst : Nonempty _138890] [inst_1 : Nonempty _138891]
    [inst_2 : Nonempty _138922] [inst_3 : Nonempty _138947] [inst_4 : Nonempty P] (lt2 : _138891 → _138890 → Prop)
    (p P' : (_138891 → _138922) → P → Prop) (s : P → _138890) (h k : (_138891 → _138922) → P → _138947),
    admissible lt2 p s P' ∧
        admissible lt2 (fun (f : _138891 → _138922) (x : P) ↦ p f x ∧ P' f x) s h ∧
          admissible lt2 (fun (f : _138891 → _138922) (x : P) ↦ p f x ∧ ¬P' f x) s k →
      admissible (_138341 := _138947) lt2 p s fun (f : _138891 → _138922) (x : P) ↦ if P' f x then h f x else k f x := @HolLightLean.hol_opam.thm_ADMISSIBLE_COND holTheoryInst

theorem hol_ADMISSIBLE_MATCH : 
  ∀ {_138988 _138989 _138990 _139022 _139025 P : Type} [inst : Nonempty _138988] [inst_1 : Nonempty _138989]
    [inst_2 : Nonempty _138990] [inst_3 : Nonempty _139022] [inst_4 : Nonempty _139025] [inst_5 : Nonempty P]
    (lt2 : _138989 → _138988 → Prop) (p : (_138989 → _138990) → P → Prop) (s : P → _138988)
    (e : (_138989 → _138990) → P → _139025) (c : (_138989 → _138990) → P → _139025 → _139022 → Prop),
    (admissible lt2 p s e ∧
        admissible (_138341 := Set _139022) lt2 p s fun (f : _138989 → _138990) (x : P) ↦ c f x (e f x)) →
      admissible (_138341 := _139022) lt2 p s fun (f : _138989 → _138990) (x : P) ↦ _MATCH (e f x) (c f x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_MATCH holTheoryInst

theorem hol_ADMISSIBLE_SEQPATTERN : 
  ∀ {_139065 _139066 _139128 _139144 _139154 P : Type} [inst : Nonempty _139065] [inst_1 : Nonempty _139066]
    [inst_2 : Nonempty _139128] [inst_3 : Nonempty _139144] [inst_4 : Nonempty _139154] [inst_5 : Nonempty P]
    (lt2 : _139066 → _139065 → Prop) (p : (_139066 → _139128) → P → Prop) (s : P → _139065)
    (c1 c2 : (_139066 → _139128) → P → _139154 → _139144 → Prop) (e : (_139066 → _139128) → P → _139154),
    ((admissible (_138341 := Prop) lt2 p s fun (f : _139066 → _139128) (x : P) ↦ ∃ (y : _139144), c1 f x (e f x) y) ∧
        (admissible (_138336 := _139128) (_138341 := Set _139144) lt2
            (fun (f : _139066 → _139128) (x : P) ↦ p f x ∧ ∃ (y : _139144), c1 f x (e f x) y) s
            fun (f : _139066 → _139128) (x : P) ↦ c1 f x (e f x)) ∧
          admissible (_138336 := _139128) (_138341 := Set _139144) lt2
            (fun (f : _139066 → _139128) (x : P) ↦ p f x ∧ ¬∃ (y : _139144), c1 f x (e f x) y) s
            fun (f : _139066 → _139128) (x : P) ↦ c2 f x (e f x)) →
      admissible (_138341 := Set _139144) lt2 p s fun (f : _139066 → _139128) (x : P) ↦
        _SEQPATTERN (c1 f x) (c2 f x) (e f x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_SEQPATTERN holTheoryInst

theorem hol_ADMISSIBLE_UNGUARDED_PATTERN : 
  ∀ {_139239 _139240 _139287 _139320 _139327 P : Type} [inst : Nonempty _139239] [inst_1 : Nonempty _139240]
    [inst_2 : Nonempty _139287] [inst_3 : Nonempty _139320] [inst_4 : Nonempty _139327] [inst_5 : Nonempty P]
    (lt2 : _139240 → _139239 → Prop) (p : (_139240 → _139287) → P → Prop) (s : P → _139239)
    (pat e : (_139240 → _139287) → P → _139320) (t y : (_139240 → _139287) → P → _139327),
    admissible lt2 p s pat ∧
        admissible lt2 p s e ∧
          admissible lt2 (fun (f : _139240 → _139287) (x : P) ↦ p f x ∧ pat f x = e f x) s t ∧
            admissible lt2 (fun (f : _139240 → _139287) (x : P) ↦ p f x ∧ pat f x = e f x) s y →
      admissible (_138341 := Prop) lt2 p s fun (f : _139240 → _139287) (x : P) ↦ pat f x = e f x ∧ t f x = y f x := @HolLightLean.hol_opam.thm_ADMISSIBLE_UNGUARDED_PATTERN holTheoryInst

theorem hol_ADMISSIBLE_GUARDED_PATTERN : 
  ∀ {_139413 _139414 _139491 _139529 _139538 P : Type} [inst : Nonempty _139413] [inst_1 : Nonempty _139414]
    [inst_2 : Nonempty _139491] [inst_3 : Nonempty _139529] [inst_4 : Nonempty _139538] [inst_5 : Nonempty P]
    (lt2 : _139414 → _139413 → Prop) (p : (_139414 → _139491) → P → Prop) (s : P → _139413)
    (pat : (_139414 → _139491) → P → _139529) (q : (_139414 → _139491) → P → Prop)
    (e : (_139414 → _139491) → P → _139529) (t y : (_139414 → _139491) → P → _139538),
    admissible lt2 p s pat ∧
        admissible lt2 p s e ∧
          admissible lt2 (fun (f : _139414 → _139491) (x : P) ↦ p f x ∧ pat f x = e f x ∧ q f x) s t ∧
            admissible lt2 (fun (f : _139414 → _139491) (x : P) ↦ p f x ∧ pat f x = e f x) s q ∧
              admissible lt2 (fun (f : _139414 → _139491) (x : P) ↦ p f x ∧ pat f x = e f x ∧ q f x) s y →
      admissible (_138341 := Prop) lt2 p s fun (f : _139414 → _139491) (x : P) ↦ pat f x = e f x ∧ q f x ∧ t f x = y f x := @HolLightLean.hol_opam.thm_ADMISSIBLE_GUARDED_PATTERN holTheoryInst

theorem hol_ADMISSIBLE_NSUM : 
  ∀ {A B C P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty P]
    (lt2 : B → A → Prop) (p : (B → C) → P → Prop) (s : P → A) (h : (B → C) → P → ℕ → ℕ) (a b : P → ℕ),
    (admissible (_138336 := C) (_138341 := ℕ) (_138346 := ℕ × P) lt2
        (fun (f : B → C) ↦
          Classical.epsilon fun (f' : Set (ℕ × P)) ↦ ∀ (k : ℕ) (x : P), f' (k, x) = (a x ≤ k ∧ k ≤ b x ∧ p f x))
        (Classical.epsilon fun (f : ℕ × P → A) ↦ ∀ (k : ℕ) (x : P), f (k, x) = s x) fun (f : B → C) ↦
        Classical.epsilon fun (f' : ℕ × P → ℕ) ↦ ∀ (k : ℕ) (x : P), f' (k, x) = h f x k) →
      admissible (_138341 := ℕ) lt2 p s fun (f : B → C) (x : P) ↦ ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (a x) (b x)), h f x i := @HolLightLean.hol_opam.thm_ADMISSIBLE_NSUM holTheoryInst

theorem hol_ADMISSIBLE_SUM : 
  ∀ {A B C P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty C] [inst_3 : Nonempty P]
    (lt2 : B → A → Prop) (p : (B → C) → P → Prop) (s : P → A) (h : (B → C) → P → ℕ → ℝ) (a b : P → ℕ),
    (admissible (_138336 := C) (_138341 := ℝ) (_138346 := ℕ × P) lt2
        (fun (f : B → C) ↦
          Classical.epsilon fun (f' : Set (ℕ × P)) ↦ ∀ (k : ℕ) (x : P), f' (k, x) = (a x ≤ k ∧ k ≤ b x ∧ p f x))
        (Classical.epsilon fun (f : ℕ × P → A) ↦ ∀ (k : ℕ) (x : P), f (k, x) = s x) fun (f : B → C) ↦
        Classical.epsilon fun (f' : ℕ × P → ℝ) ↦ ∀ (k : ℕ) (x : P), f' (k, x) = h f x k) →
      admissible (_138341 := ℝ) lt2 p s fun (f : B → C) (x : P) ↦ ∑ᶠ (i : ℕ) (_ : i ∈ Set.Icc (a x) (b x)), h f x i := @HolLightLean.hol_opam.thm_ADMISSIBLE_SUM holTheoryInst

theorem hol_ADMISSIBLE_MAP : 
  ∀ {_139831 _139840 _139846 A B P : Type} [inst : Nonempty _139831] [inst_1 : Nonempty _139840]
    [inst_2 : Nonempty _139846] [inst_3 : Nonempty A] [inst_4 : Nonempty B] [inst_5 : Nonempty P]
    (lt2 : A → _139831 → Prop) (p : (A → B) → P → Prop) (s : P → _139831) (h : (A → B) → P → _139846 → _139840)
    (l : (A → B) → P → List _139846),
    (admissible lt2 p s l ∧
        admissible (_138336 := B) (_138341 := _139840) (_138346 := _139846 × P) lt2
          (fun (f : A → B) ↦
            Classical.epsilon fun (f' : Set (_139846 × P)) ↦ ∀ (y : _139846) (x : P), f' (y, x) = (p f x ∧ y ∈ l f x))
          (Classical.epsilon fun (f : _139846 × P → _139831) ↦ ∀ (y : _139846) (x : P), f (y, x) = s x)
          fun (f : A → B) ↦
          Classical.epsilon fun (f' : _139846 × P → _139840) ↦ ∀ (y : _139846) (x : P), f' (y, x) = h f x y) →
      admissible (_138341 := List _139840) lt2 p s fun (f : A → B) (x : P) ↦ List.map (h f x) (l f x) := @HolLightLean.hol_opam.thm_ADMISSIBLE_MAP holTheoryInst

theorem hol_ADMISSIBLE_MATCH_SEQPATTERN : 
  ∀ {_139903 _139904 _139969 _139993 _140024 P : Type} [inst : Nonempty _139903] [inst_1 : Nonempty _139904]
    [inst_2 : Nonempty _139969] [inst_3 : Nonempty _139993] [inst_4 : Nonempty _140024] [inst_5 : Nonempty P]
    (lt2 : _139904 → _139903 → Prop) (p : (_139904 → _139969) → P → Prop) (s : P → _139903)
    (c1 c2 : (_139904 → _139969) → P → _140024 → _139993 → Prop) (e : (_139904 → _139969) → P → _140024),
    ((admissible (_138341 := Prop) lt2 p s fun (f : _139904 → _139969) (x : P) ↦ ∃ (y : _139993), c1 f x (e f x) y) ∧
        (admissible (_138336 := _139969) (_138341 := _139993) lt2
            (fun (f : _139904 → _139969) (x : P) ↦ p f x ∧ ∃ (y : _139993), c1 f x (e f x) y) s
            fun (f : _139904 → _139969) (x : P) ↦ _MATCH (e f x) (c1 f x)) ∧
          admissible (_138336 := _139969) (_138341 := _139993) lt2
            (fun (f : _139904 → _139969) (x : P) ↦ p f x ∧ ¬∃ (y : _139993), c1 f x (e f x) y) s
            fun (f : _139904 → _139969) (x : P) ↦ _MATCH (e f x) (c2 f x)) →
      admissible (_138341 := _139993) lt2 p s fun (f : _139904 → _139969) (x : P) ↦
        _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)) := @HolLightLean.hol_opam.thm_ADMISSIBLE_MATCH_SEQPATTERN holTheoryInst

theorem hol_ADMISSIBLE_IMP_SUPERADMISSIBLE : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop)
    (p : (A → B) → P → Prop) (s : P → A) (t : (A → B) → P → B), admissible lt2 p s t → superadmissible lt2 p s t := @HolLightLean.hol_opam.thm_ADMISSIBLE_IMP_SUPERADMISSIBLE holTheoryInst

theorem hol_SUPERADMISSIBLE_CONST : 
  ∀ {_140103 _140104 _140105 : Type} [inst : Nonempty _140103] [inst_1 : Nonempty _140104] [inst_2 : Nonempty _140105]
    (lt2 : _140103 → _140103 → Prop) (p : (_140103 → _140105) → _140104 → Prop) (s : _140104 → _140103)
    (c : _140104 → _140105), superadmissible lt2 p s fun (f : _140103 → _140105) ↦ c := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_CONST holTheoryInst

theorem hol_SUPERADMISSIBLE_TAIL : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop)
    (p : (A → B) → P → Prop) (s : P → A) (t : (A → B) → P → A),
    (admissible lt2 p s t ∧ ∀ (f : A → B) (a : P), p f a → ∀ (y : A), lt2 y (t f a) → lt2 y (s a)) →
      superadmissible lt2 p s fun (f : A → B) (x : P) ↦ f (t f x) := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_TAIL holTheoryInst

theorem hol_SUPERADMISSIBLE_COND : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop)
    (p P' : (A → B) → P → Prop) (s : P → A) (h k : (A → B) → P → B),
    admissible lt2 p s P' ∧
        superadmissible lt2 (fun (f : A → B) (x : P) ↦ p f x ∧ P' f x) s h ∧
          superadmissible lt2 (fun (f : A → B) (x : P) ↦ p f x ∧ ¬P' f x) s k →
      superadmissible lt2 p s fun (f : A → B) (x : P) ↦ if P' f x then h f x else k f x := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_COND holTheoryInst

theorem hol_SUPERADMISSIBLE_MATCH_SEQPATTERN : 
  ∀ {_140424 _140539 _140540 P : Type} [inst : Nonempty _140424] [inst_1 : Nonempty _140539] [inst_2 : Nonempty _140540]
    [inst_3 : Nonempty P] (lt2 : _140424 → _140424 → Prop) (p : (_140424 → _140540) → P → Prop) (s : P → _140424)
    (c1 c2 : (_140424 → _140540) → P → _140539 → _140540 → Prop) (e : (_140424 → _140540) → P → _140539),
    ((admissible (_138341 := Prop) lt2 p s fun (f : _140424 → _140540) (x : P) ↦ ∃ (y : _140540), c1 f x (e f x) y) ∧
        (superadmissible (_138492 := _140540) lt2
            (fun (f : _140424 → _140540) (x : P) ↦ p f x ∧ ∃ (y : _140540), c1 f x (e f x) y) s
            fun (f : _140424 → _140540) (x : P) ↦ _MATCH (e f x) (c1 f x)) ∧
          superadmissible (_138492 := _140540) lt2
            (fun (f : _140424 → _140540) (x : P) ↦ p f x ∧ ¬∃ (y : _140540), c1 f x (e f x) y) s
            fun (f : _140424 → _140540) (x : P) ↦ _MATCH (e f x) (c2 f x)) →
      superadmissible lt2 p s fun (f : _140424 → _140540) (x : P) ↦ _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)) := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_MATCH_SEQPATTERN holTheoryInst

theorem hol_SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN : 
  ∀ {A B D P Q : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty D] [inst_3 : Nonempty P]
    [Nonempty Q] (lt2 : A → A → Prop) (p : (A → B) → P → Prop) (s : P → A) (e : P → D) (pat : Q → D) (arg : P → Q → A),
    ((∀ (f : A → B) (a : P) (t u : Q), p f a ∧ pat t = e a ∧ pat u = e a → arg a t = arg a u) ∧
        ∀ (f : A → B) (a : P) (t : Q), p f a ∧ pat t = e a → ∀ (y : A), lt2 y (arg a t) → lt2 y (s a)) →
      superadmissible lt2 p s fun (f : A → B) (x : P) ↦
        _MATCH (e x) fun (u : D) (v : B) ↦ ∃ (t : Q), pat t = u ∧ f (arg x t) = v := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN holTheoryInst

theorem hol_SUPERADMISSIBLE_MATCH_GUARDED_PATTERN : 
  ∀ {A B D P Q : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty D] [inst_3 : Nonempty P]
    [Nonempty Q] (lt2 : A → A → Prop) (p : (A → B) → P → Prop) (s : P → A) (e : P → D) (pat : Q → D) (q : P → Q → Prop)
    (arg : P → Q → A),
    ((∀ (f : A → B) (a : P) (t u : Q), p f a ∧ pat t = e a ∧ q a t ∧ pat u = e a ∧ q a u → arg a t = arg a u) ∧
        ∀ (f : A → B) (a : P) (t : Q), p f a ∧ q a t ∧ pat t = e a → ∀ (y : A), lt2 y (arg a t) → lt2 y (s a)) →
      superadmissible lt2 p s fun (f : A → B) (x : P) ↦
        _MATCH (e x) fun (u : D) (v : B) ↦ ∃ (t : Q), pat t = u ∧ q x t ∧ f (arg x t) = v := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_MATCH_GUARDED_PATTERN holTheoryInst

theorem hol_WF_REC_CASES : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P] (lt2 : A → A → Prop)
    (clauses : List ((P → A) × ((A → B) → P → B))),
    WellFounded lt2 ∧
        ALL
          (Classical.epsilon fun (f : Set ((P → A) × ((A → B) → P → B))) ↦
            ∀ (s : P → A) (t : (A → B) → P → B),
              f (s, t) =
                ∃ (P' : (A → B) → P → Prop) (G : (A → B) → P → A) (H : (A → B) → P → B),
                  (∀ (f' : A → B) (a : P) (y : A), P' f' a ∧ lt2 y (G f' a) → lt2 y (s a)) ∧
                    (∀ (f' g : A → B) (a : P),
                        (∀ (z : A), lt2 z (s a) → f' z = g z) → P' f' a = P' g a ∧ G f' a = G g a ∧ H f' a = H g a) ∧
                      ∀ (f' : A → B) (a : P), t f' a = if P' f' a then f' (G f' a) else H f' a)
          clauses →
      ∃ (f : A → B), ∀ (x : A), f x = CASEWISE clauses f x := @HolLightLean.hol_opam.thm_WF_REC_CASES holTheoryInst

theorem hol_RECURSION_CASEWISE : 
  ∀ {A B P : Type} [inst : Nonempty A] [inst_1 : Nonempty B] [inst_2 : Nonempty P]
    (clauses : List ((P → A) × ((A → B) → P → B))),
    ((∃ (lt2 : A → A → Prop),
          WellFounded lt2 ∧
            ALL
              (Classical.epsilon fun (f : Set ((P → A) × ((A → B) → P → B))) ↦
                ∀ (s : P → A) (t : (A → B) → P → B),
                  f (s, t) = tailadmissible lt2 (fun (f' : A → B) (a : P) ↦ True) s t)
              clauses) ∧
        ∀ (s : P → A) (t : (A → B) → P → B) (s' : P → A) (t' : (A → B) → P → B) (f : A → B) (x y : P),
          (s, t) ∈ clauses ∧ (s', t') ∈ clauses → s x = s' y → t f x = t' f y) →
      ∃ (f : A → B),
        ALL
          (Classical.epsilon fun (f' : Set ((P → A) × ((A → B) → P → B))) ↦
            ∀ (s : P → A) (t : (A → B) → P → B), f' (s, t) = ∀ (x : P), f (s x) = t f x)
          clauses := @HolLightLean.hol_opam.thm_RECURSION_CASEWISE holTheoryInst

theorem hol_RECURSION_CASEWISE_PAIRWISE : 
  ∀ {_141763 _141779 _141783 : Type} [inst : Nonempty _141763] [inst_1 : Nonempty _141779] [inst_2 : Nonempty _141783]
    (clauses : List ((_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779))),
    (∃ (lt2 : _141763 → _141763 → Prop),
          WellFounded lt2 ∧
            ALL
              (Classical.epsilon fun (f : Set ((_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779))) ↦
                ∀ (s : _141783 → _141763) (t : (_141763 → _141779) → _141783 → _141779),
                  f (s, t) = tailadmissible lt2 (fun (f' : _141763 → _141779) (a : _141783) ↦ True) s t)
              clauses) ∧
        ALL
            (Classical.epsilon fun (f : Set ((_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779))) ↦
              ∀ (s : _141783 → _141763) (t : (_141763 → _141779) → _141783 → _141779),
                f (s, t) = ∀ (f' : _141763 → _141779) (x y : _141783), s x = s y → t f' x = t f' y)
            clauses ∧
          List.Pairwise
            (Classical.epsilon
              fun
                (f :
                  (_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779) →
                    (_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779) → Prop) ↦
              ∀ (s : _141783 → _141763) (t : (_141763 → _141779) → _141783 → _141779),
                f (s, t) =
                  Classical.epsilon fun (f' : Set ((_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779))) ↦
                    ∀ (s' : _141783 → _141763) (t' : (_141763 → _141779) → _141783 → _141779),
                      f' (s', t') = ∀ (f'' : _141763 → _141779) (x y : _141783), s x = s' y → t f'' x = t' f'' y)
            clauses →
      ∃ (f : _141763 → _141779),
        ALL
          (Classical.epsilon fun (f' : Set ((_141783 → _141763) × ((_141763 → _141779) → _141783 → _141779))) ↦
            ∀ (s : _141783 → _141763) (t : (_141763 → _141779) → _141783 → _141779),
              f' (s, t) = ∀ (x : _141783), f (s x) = t f x)
          clauses := @HolLightLean.hol_opam.thm_RECURSION_CASEWISE_PAIRWISE holTheoryInst

theorem hol_SUPERADMISSIBLE_T : 
  ∀ {_141893 _141895 _141899 : Type} [inst : Nonempty _141893] [inst_1 : Nonempty _141895] [inst_2 : Nonempty _141899]
    (lt2 : _141893 → _141893 → Prop) (s : _141899 → _141893) (t : (_141893 → _141895) → _141899 → _141895),
    superadmissible lt2 (fun (f : _141893 → _141895) (x : _141899) ↦ True) s t =
      tailadmissible lt2 (fun (f : _141893 → _141895) (x : _141899) ↦ True) s t := @HolLightLean.hol_opam.thm_SUPERADMISSIBLE_T holTheoryInst