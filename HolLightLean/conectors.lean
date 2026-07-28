-- Writing guidelines: https://leanprover-community.github.io/contribute/style.html

import Mathlib

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable def el {α : Type*} [h : Nonempty α] : α := Nonempty.some h

instance {A B : Type*} [h : Nonempty B] : Nonempty (A -> B) :=
 Nonempty.intro (fun _ => Nonempty.some h)

/-
Currified versions of some connectives
-/

def imp (p q : Prop) : Prop := p -> q

/-
Proof of some HOL Light rules
-/

theorem MK_COMB {α β : Type*} {s t : α -> β } {u v : α } (h1 : s = t) (h2 : u = v) : s u = t v := by
    rw [h1, h2]

theorem EQ_MP {p q : Prop} (e : p = q) (h : p) : q := by
 subst e ; exact h

/-
Proof of some natural deduction rules
-/

theorem or_intro1 {p : Prop} (h : p) (q : Prop) : p ∨ q := Or.inl h

theorem or_intro2 {q : Prop} (h : q) (p : Prop) : p ∨ q := Or.inr h

theorem or_elim {p q : Prop} (h : p ∨ q) {r : Prop} (h1 : p -> r) (h2: q -> r) : r := Or.elim h h1 h2


theorem ex_elim {a : Type*} {p : a -> Prop} (h1 : exists x, p x)
    {r : Prop} (h2 : forall x : a, (p x) -> r) : r := Exists.elim h1 h2

/-
From Rocq original mappings. To erase probably
-/

theorem is_True P : (P = True) = P := by
    apply Eq.propIntro
    · intro h
      rewrite [h]
      exact trivial
    · exact fun h => Eq.propIntro (fun a => trivial) (fun a_1 => h)

/--
From hypothesis h : P, rewrite P to True
-/
macro "is_True" h:ident : tactic =>
-- TODO: I am not sure this is the best way to declare a macro
  `(tactic |
    let h' := $h <;> -- is it always fresh?
    rw [← is_True (type_of% h')] at h' <;>
    rw [h'] at * <;>
    try clear $h
  )

theorem is_False P : (P = False) = ¬ P := by
    apply Eq.propIntro
    ·   intro h
        rewrite [h]
        exact (fun a => a)
    ·   exact fun h => Eq.propIntro h (fun a_1 => False.elim a_1)


macro "is_False" h:ident : tactic =>
  `(tactic |
    have h' := $h <;>
    rw [← is_True (type_of% h')] at h' <;>
    rw [h'] at * <;>
    try clear $h
  )

/-!
# Alignment of connectives
-/

theorem True_def : Eq True (Eq (fun p : Prop => p) (fun p : Prop => p)) :=
by simp

theorem and_def : Eq And (fun p : Prop => fun q : Prop => Eq (fun f : Prop -> Prop -> Prop => f p q)
(fun f : Prop -> Prop -> Prop => f True True)) := by
    funext P Q;
    apply Eq.propIntro
    ·   intro h
        funext a
        have h1 : P = True := by exact Eq.propIntro (fun a ↦ trivial) (fun True ↦ h.left)
        have h2 : Q = True := by exact Eq.propIntro (fun a ↦ trivial) (fun True ↦ h.right)
        rewrite [h1,h2]
        rfl
    ·   intro h
        have h_t := congrArg (fun f => f And) h
        simp only [and_self, eq_iff_iff, iff_true] at h_t
        exact h_t

theorem imp_def : Eq imp (fun p : Prop => fun q : Prop => Eq (And p q) p) := by
    unfold imp
    funext P Q
    apply Eq.propIntro
    ·   intro h
        simp only [eq_iff_iff, and_iff_left_iff_imp]
        exact h
    ·   intro h
        rw [← h]
        exact fun a ↦ a.right

def FORALL {α : Type*} [Nonempty α] (P : α -> Prop) := ∀ x : α, P x

theorem FORALL_def : ∀ {α : Type*} [Nonempty α], (@FORALL α _) =
(fun P : α -> Prop => Eq P (fun _ : α => True)) := by
    intros α _
    funext P
    apply Eq.propIntro
    ·   intro h
        unfold FORALL at h
        funext x
        specialize h x
        is_True h
    ·   intro h
        unfold FORALL
        intro x
        have hx := congrArg (fun f => f x) h ; simp only [eq_iff_iff, iff_true] at hx
        exact hx

def EXISTS {α : Type*} [Nonempty α] (P : α -> Prop) := ∃ x : α, P x
theorem EXISTS_exists : ∀ {α : Type*} [Nonempty α], (@EXISTS α _) = (@Exists α) := rfl

theorem exists_def : ∀ {α : Type*} [Nonempty α], (@Exists α) =
(fun P : α -> Prop => ∀ q : Prop, (∀ x : α, (P x) -> q) -> q) := by
    intros α N
    funext P
    apply Eq.propIntro
    ·   intros h Q h1
        obtain ⟨x, px⟩ := h
        have h1x := h1 x
        exact h1x px
    ·   intros h
        apply h
        intros x px
        exact ⟨x, px⟩

def exists_intro {α : Type*} (P : α -> Prop) (w : α) (h : P w):= @Exists.intro _ P w h

def or_inl {a : Prop} (h : a) (b : Prop) : a ∨ b := Or.inl h
def or_inr {b : Prop} (a : Prop) (h : b) : a ∨ b := Or.inr h

theorem or_def : Eq Or (fun p : Prop => fun q : Prop => ∀ r : Prop, (p -> r) -> (q -> r) -> r) := by
    funext P
    funext Q
    apply Eq.propIntro
    ·   intros h h1 h2 h3
        exact Or.elim h h2 h3
    ·   intros h
        apply h
        · exact Or.inl
        · exact Or.inr

theorem false_def : Eq False (∀ p : Prop, p) := by
    apply Eq.propIntro
    ·   intro h
        contradiction
    ·   intro h
        apply h

theorem not_def : Eq Not (fun p : Prop => p -> False) := by
    funext P ; apply Eq.propIntro <;> (intro h ; exact h)

def EXISTSUNIQUE {α : Type*} [Nonempty α] (P : α -> Prop) := ExistsUnique P

theorem EXISTSUNIQUE_def : ∀ {α : Type*} [Nonempty α], Eq (@EXISTSUNIQUE α _) (fun P : α -> Prop => And (Exists P) (∀ x : α, ∀ y : α, (And (P x) (P y)) -> Eq x y)) := by
    intros α _
    funext P
    apply Eq.propIntro
    ·   intro h
        unfold EXISTSUNIQUE at h
        obtain ⟨x,hx⟩ := h
        apply And.intro
        ·   exact ⟨x, hx.left⟩
        ·   rintro a b ⟨ha, hb⟩
            have ⟨h1,h2⟩ := hx
            exact Eq.trans (h2 a ha) (h2 b hb).symm
    ·   rintro ⟨hl, hr⟩
        unfold EXISTSUNIQUE
        obtain ⟨x,hx⟩ := hl
        apply Exists.intro x
        apply And.intro
        ·   exact hx
        ·   intro y hy
            exact (hr x y ⟨hx,hy⟩).symm

/-!
# epsilon operator alignment
-/

theorem align_epsilon (α : Type*) [Nonempty α] (P : α -> Prop) (a : α) :
P a -> (forall x, P a -> P x -> a = x) -> a = Classical.epsilon P := by
    intros h1 h2
    apply h2
    ·   exact h1
    ·   apply Classical.epsilon_spec_aux
        exact Exists.intro a h1

theorem partial_align_1 {U A B : Type*} [Nonempty B] {uv0 : U} {x : A} (Q : A -> Prop) (f : U -> A -> B) (P : (U -> A -> B) -> Prop) :
P f -> (∀ x', Q x' -> f uv0 x' = Classical.epsilon P uv0 x') ->
(forall f' uv x', P f ->  P f' -> (forall x'', Q x'' -> f uv x'' = f' uv x'') ->
f uv x' = f' uv x') -> f uv0 x = Classical.epsilon P uv0 x := by
    intros Hf HQ Hunique
    apply Hunique <;> try assumption
    apply Classical.epsilon_spec ; exact ⟨f, Hf⟩

theorem partial_align_2 {U A B C : Type*} [Nonempty C] {uv0 : U} {x : B} {y : A}
(Q : A -> Prop) (f : U -> B -> A -> C) (P : (U -> B -> A -> C) -> Prop) :
P f -> (forall x' y', Q y' -> f uv0 x' y' = Classical.epsilon P uv0 x' y') ->
(forall f' uv x' y', P f ->  P f' ->
(forall x'' y'', Q y'' -> f uv x'' y'' = f' uv x'' y'') ->
f uv x' y' = f' uv x' y') -> f uv0 x y = Classical.epsilon P uv0 x y := by
    intros Hf HQ Hunique
    apply Hunique <;> try assumption
    apply Classical.epsilon_spec ; exact ⟨f, Hf⟩

theorem partial_align_3 {U A B C D : Type*} [Nonempty C] [Nonempty D] {uv0 : U} {x : B} {y : C} {z : A}
(Q : A -> Prop) (f : U -> B -> C -> A -> D) (P : (U -> B -> C -> A -> D) -> Prop) :
P f -> (forall x' y' z', Q z' -> f uv0 x' y' z' = Classical.epsilon P uv0 x' y' z') ->
(forall f' uv x' y' z', P f ->  P f' ->
(forall x'' y'' z'', Q z'' -> f uv x'' y'' z'' = f' uv x'' y'' z'') ->
f uv x' y' z' = f' uv x' y' z') -> f uv0 x y z = Classical.epsilon P uv0 x y z := by
    intros Hf HQ Hunique
    apply Hunique <;> try assumption
    apply Classical.epsilon_spec ; exact ⟨f, Hf⟩

/-!
# COND aligning
-/

open Classical in noncomputable def COND {α : Type*} [Nonempty α] (P : Prop) (x y : α) := if P then x else y

open Classical in theorem COND_def {α : Type*} [Nonempty α] : (@COND α _) =
(fun P : Prop => fun x : α => fun y : α => epsilon (fun z : α => And ((P = True) -> z = x) ((P = False) -> z = y) )) := by
    funext P x y
    unfold COND
    apply align_epsilon
    ·   simp_all only [↓reduceIte, implies_true, and_self]
    ·   intro x_2 a a_1
        simp_all only [↓reduceIte, implies_true, and_self]
        obtain ⟨left, right⟩ := a_1
        split <;>
        next h => simp_all only [forall_const]

theorem COND_True {α : Type*} [Nonempty α] (x y : α) : COND True x y = x := by
  unfold COND ; simp

theorem COND_False {α : Type*} [Nonempty α] (x y : α) : COND False x y = y := by
  unfold COND ; simp

/-!
# Subtype alignment
-/

section Subtype

variable {α : Type*} {P : α → Prop} {a : α} (h : P a)

/--
In HOL Light one can define a type `β` from a type `α`, a proposition `P : α → β` and
a proof `h : P a` for some `a : α` (i.e, it is not empty).
This construction generates in HOL Light the functions `mk : α → β` and `dest : β → α` stating that

· `mk(dest b) = b` for all `b : β`.
  Hence `mk` is surjective and `dest` injective

· `P a = (dest (mk a) = a)` for all `a : α`.
  The image of `dest` is the subset generated by `P` on `α`.

In Lean we have the Subtype construction `{x:α // P x}` but it does not need a proof
of non-emptiness, so we extend it to need one, defining `SUBTYPE` which at every
declaration will have its own instance of non-emptiness.
-/
def SUBTYPE (_ : P a) := Subtype P

instance : Nonempty (SUBTYPE h) := ⟨⟨a,h⟩⟩

def dest : SUBTYPE h -> α := fun x => x.val

open Classical in noncomputable def mk : α -> SUBTYPE h :=
fun x => dite (P x) (fun y => Subtype.mk x y) (fun _ => Subtype.mk a h)

theorem dest_mk x : P x = (dest h (mk _ x) = x) := by
  apply Eq.propIntro
  · intro H
    unfold mk dite
    cases (Classical.propDecidable (P x))
    · contradiction
    · rfl
  · unfold dest
    obtain  ⟨val, prp⟩ := mk h x
    simp only
    intro h_eq
    rw [← h_eq]
    exact prp

theorem dest_mk_aux x : P x → (dest h (mk _ x) = x) := (Iff.of_eq (dest_mk h x)).1

theorem mk_dest x : mk h (dest _ x) = x := by
    unfold mk dite
    obtain ⟨val,prp⟩ := x
    cases (Classical.propDecidable (P _))
    ·   simp only
        rename _ => h_f
        exact False.elim (h_f prp)
    ·   rfl

theorem dest_inj x y : dest h x = dest _ y → x = y := by
    intro h_dest ; obtain ⟨x,hx⟩ := x; obtain ⟨y,hy⟩ := y ;
    subst h_dest ; rfl

theorem mk_inj x y : P x → P y → mk h x = mk _ y → x = y := by
  intros hPx hPy ; unfold mk
  cases (em (P x)) <;> cases (em (P y)) <;> intro h_em  <;> lia

end Subtype

/-!
# Quotient Alignment
-/

section Quotient

variable {α : Type*} (R : α → α → Prop)

def is_eq_class (A : α → Prop) := ∃ a : α, A = R a
def class_of (a : α) := R a

theorem is_eq_class_of (a : α) : is_eq_class R (class_of R a) := ⟨a, by rfl⟩

variable [h : Nonempty α]

theorem non_empty : is_eq_class R (class_of R h.some) := ⟨h.some, by rfl⟩

/--
the QUOTIENT type is represented as the subtype of sets of elements in α that
are equivalence classes under the equivalence relation R.

`{q : α → Prop | ∃ a : α, q = R a}`
-/
def QUOTIENT := SUBTYPE (non_empty R)
instance : Nonempty (QUOTIENT R) := instNonemptySUBTYPE (non_empty R)

noncomputable def mk_quotient : (α → Prop) → QUOTIENT R := mk (non_empty R)
def dest_quotient : QUOTIENT R -> (α → Prop) := dest (non_empty R)

theorem mk_dest_quotient : ∀ q : QUOTIENT R, mk_quotient R (dest_quotient R q) = q :=
mk_dest (non_empty R)

theorem dest_mk_quotient : ∀ A : α → Prop,
  is_eq_class R A = (dest_quotient R (mk_quotient R A) = A) :=
  dest_mk (non_empty R)

noncomputable def elt_of : QUOTIENT R → α := fun q => Classical.epsilon (dest_quotient R q)

variable {Rrefl : ∀ a, R a a}
         {Rsymm : ∀ a b, R a b = R b a}
         {Rtrans : ∀ a b c, R a b → R b c → R a c}

include Rrefl

theorem eq_elt_of a : R a (Classical.epsilon (R a)) := by
  apply Classical.epsilon_spec
  exact ⟨a, Rrefl a⟩

theorem dest_quotient_elt_of q : dest_quotient R q (elt_of R q) := by
  unfold elt_of dest_quotient dest ; obtain ⟨a, ⟨b, A⟩⟩ := q ; simp only
  subst A ; apply Classical.epsilon_spec ; exact ⟨b, Rrefl b⟩

include Rsymm Rtrans

theorem dest_quotient_elim q a : dest_quotient R q a → R (elt_of R q) a := by
  unfold elt_of dest_quotient dest ; obtain ⟨b, ⟨c, A⟩⟩ := q ; simp only
  subst A ; intro h1 ; apply Rtrans _ c
  · rw[Rsymm]
    apply eq_elt_of
    exact Rrefl
  · exact h1

theorem eq_class_intro_elt (q1 q2 : QUOTIENT R) : R (elt_of R q1) (elt_of R q2) → q1 = q2 := by
  intros h
  obtain ⟨q1, ⟨a, hq1⟩⟩ := q1 ; obtain ⟨q2, ⟨b, hq2⟩⟩ := q2
  congr
  subst q1 q2
  funext c
  apply Eq.propIntro <;> intro h_p <;> unfold elt_of dest_quotient dest at h <;> simp only at h
  · apply Rtrans b (Classical.epsilon (R b)) _
    · apply eq_elt_of ; apply Rrefl
    apply Rtrans _ a c ;
    · apply Rtrans _ (Classical.epsilon (R a)) a ;
      · rw[Rsymm]; exact h
      · rw[Rsymm] ; apply eq_elt_of ; exact Rrefl ;
    exact h_p
  · apply Rtrans a (Classical.epsilon (R a)) _
    · apply eq_elt_of ; apply Rrefl
    apply Rtrans _ b c ;
    · apply Rtrans _ (Classical.epsilon (R b)) b ;
      · exact h
      · rw[Rsymm] ; apply eq_elt_of ; exact Rrefl ;
    exact h_p

omit h Rtrans in
theorem eq_class_intro (a b : α) : R a = R b -> R a b := by
  intro h
  have ha := congrArg (fun f => f a) h
  rw[Rsymm, ← ha]
  exact Rrefl a

theorem mk_quotient_elt_of q : mk_quotient R (R (elt_of R q)) = q := by
    apply eq_class_intro_elt _ <;> try assumption
    generalize (elt_of R q) = a ; unfold elt_of
    obtain ⟨q, h_eq⟩ := q
    have h_aux := (Iff.of_eq (@dest_mk_quotient α R h (R a))).1
    rw[h_aux, Rsymm]
    · apply eq_elt_of R ; assumption
    · unfold is_eq_class ; exact ⟨a, by rfl⟩

def setoid_quot : Setoid α := ⟨R, ⟨Rrefl, (Iff.of_eq (Rsymm _ _)).1, Rtrans _ _ _⟩⟩

noncomputable def QUOT_to_quot : QUOTIENT R → Quotient (@setoid_quot α R Rrefl Rsymm Rtrans)
  := fun (q : QUOTIENT R) => Quotient.mk (@setoid_quot α R Rrefl Rsymm Rtrans) (elt_of R q)

noncomputable def quot_to_QUOT : Quotient (@setoid_quot α R Rrefl Rsymm Rtrans) → QUOTIENT R
  := fun q => mk_quotient R (class_of R (q.out))

theorem Qq_qQ : ∀ q : Quotient (@setoid_quot α R Rrefl Rsymm Rtrans),
  QUOT_to_quot R (quot_to_QUOT R q) = q := by
    intro q
    unfold QUOT_to_quot quot_to_QUOT mk_quotient mk ;
    have h_y : is_eq_class R (class_of R q.out) :=
      by unfold is_eq_class class_of ; exact ⟨q.out, by rfl⟩
    simp only [h_y] ; unfold elt_of dest_quotient dest class_of ; simp
    have h_1 : R q.out (Classical.epsilon (R q.out)) :=
      Classical.epsilon_spec ⟨q.out, Rrefl q.out⟩
    rw[Rsymm] at h_1
    have h_2 : ⟦Classical.epsilon (R q.out)⟧ = ⟦q.out⟧
      := @Quotient.sound _ (@setoid_quot α R Rrefl Rsymm Rtrans) _ _ h_1
    simpa [Quot.out_eq] using h_2

omit h in
theorem rel_out : ∀ a : α,
  R a (⟦a⟧ : Quotient ((@setoid_quot α R Rrefl Rsymm Rtrans))).out := by
    intro x
    have h1 : ⟦(⟦x⟧ : Quotient (@setoid_quot α R Rrefl Rsymm Rtrans)).out⟧ = ⟦x⟧ :=
      Quotient.out_eq ⟦x⟧
    exact Quotient.exact (h1.symm)

theorem qQ_Qq : ∀ q : QUOTIENT R,
   @quot_to_QUOT α R h Rrefl Rsymm Rtrans (QUOT_to_quot R q) = q := by
    intro q
    unfold quot_to_QUOT QUOT_to_quot mk_quotient mk
    have h_y : is_eq_class R
        (class_of R (@Quotient.out α (@setoid_quot α R Rrefl Rsymm Rtrans) ⟦elt_of R q⟧))
        := by unfold is_eq_class class_of ; exact ⟨⟦elt_of R q⟧.out, by rfl⟩
    simp only [h_y, ↓reduceDIte]
    obtain ⟨q, ⟨a, A⟩⟩ := q
    congr ; funext x
    apply Eq.propIntro <;> intro h
    · unfold class_of elt_of dest_quotient dest at h
      simp only at h
      subst A
      have h_1 : R a (Classical.epsilon (R a)) := by apply eq_elt_of R ; assumption
      have h_2 : R (Classical.epsilon (R a))
                  (@Quotient.out α (@setoid_quot α R Rrefl Rsymm Rtrans) ⟦Classical.epsilon (R a)⟧)
                  := by apply rel_out
      have h_t := Rtrans _ _ _ h_1 h_2
      apply Rtrans _ _ _ h_t h
    · unfold class_of elt_of dest_quotient dest ; simp only
      subst A
      have h_1 : R (Classical.epsilon (R a))
        (@Quotient.out α (@setoid_quot α R Rrefl Rsymm Rtrans) ⟦Classical.epsilon (R a)⟧)
          := by apply rel_out
      rw[Rsymm] at h
      have h_2 := @eq_elt_of α R _ Rrefl a
      have h_t := Rtrans _ _ _ h h_2
      rw[Rsymm]
      apply Rtrans _ _ _ h_t h_1

end Quotient


/-!
# Alignment of Unit
-/

def one_ABS : Prop -> Unit := fun _ => ()

def one_REP : Unit -> Prop := fun _ => True

theorem axiom_0 : ∀ {α β : Type*} [Nonempty α] [Nonempty β], ∀ (t : α -> β),
Eq (fun x : α => t x) t := by
    intros α β _ _ t
    rfl

theorem axiom_1 : ∀ {α : Type*} [Nonempty α], ∀ P : α -> Prop, ∀ x : α,
(P x) -> P (@Classical.epsilon  α _ P) := by
    intros _ _ _ x h
    apply Classical.epsilon_spec_aux
    exact ⟨x, h⟩

theorem axiom_2 : ∀ (a : Unit), Eq (one_ABS (one_REP a)) a := fun _ => rfl

theorem axiom_3 : ∀ (r : Prop), Eq ((fun b : Prop => b) r) (Eq (one_REP (one_ABS r)) r) := by
    intros r
    unfold one_REP
    simp

theorem one_def : Eq () (@Classical.epsilon Unit _ one_REP ) := Eq.refl ()

/-!
# Alignment of Product Type*
-/

def prod (A B : Type*) [Nonempty A] [Nonempty B] := Prod A B
def prod_mk {A B : Type*} [Nonempty A] [Nonempty B] := @Prod.mk A B
def prod_fst {A B : Type*} [Nonempty A] [Nonempty B] (P : A × B) := Prod.fst P
def prod_snd {A B : Type*} [Nonempty A] [Nonempty B] (P : A × B) := Prod.snd P

instance (A B : Type*) [Nonempty A] [Nonempty B] : Nonempty (prod A B) :=
      Nonempty.intro (prod_mk (@Classical.ofNonempty A _) (@Classical.ofNonempty B _))

@[simp]
theorem prod_def (A B : Type*) [Nonempty A] [Nonempty B] : prod A B = Prod A B := rfl

def mk_pair {α β : Type*} [Nonempty α] [Nonempty β] := fun x : α => fun y : β =>
fun a : α => fun b : β => (a = x) ∧ (b = y)

noncomputable def ABS_prod : ∀ {α β : Type*} [Nonempty α] [Nonempty β], (α -> β -> Prop) -> Prod α β
:= fun f => Classical.epsilon (fun p => f = mk_pair (Prod.fst p) (Prod.snd p))

def REP_prod : ∀ {α β : Type*} [Nonempty α] [Nonempty β], Prod α β -> α -> β -> Prop
:= fun P a b => mk_pair (Prod.fst P) (Prod.snd P) a b

theorem mk_pair_inj {α β : Type*} [Nonempty α] [Nonempty β] {x x1 : α} {y y1 : β} :
mk_pair x y = mk_pair x1 y1 -> x = x1 ∧ y = y1 := by
    intro h
    unfold mk_pair at h
    have hxy := congrArg (fun f => f x y) h
    simp only [and_self, eq_iff_iff, true_iff] at hxy
    exact hxy

theorem ABS_prod_mk_pair {α β : Type*} [Nonempty α] [Nonempty β] {x : α} {y : β} :
(x,y) = ABS_prod (mk_pair x y) := by
    unfold ABS_prod
    apply align_epsilon
    ·   rfl
    ·   intros _ _ _; expose_names
        apply (Prod.ext_iff).2
        symm at h
        have h_aux := Eq.trans h h_1
        exact mk_pair_inj h_aux

theorem axiom_4 : ∀ {α β : Type*} [Nonempty α] [Nonempty β] (a : Prod α β),
Eq (@ABS_prod α β _ _ (@REP_prod α β _ _ a)) a := fun _ => ABS_prod_mk_pair.symm

theorem axiom_5 : ∀ {α β : Type*} [Nonempty α] [Nonempty β] (r : α -> β -> Prop), Eq ((fun x : α -> β -> Prop => ∃ a : α, ∃ b : β, Eq x (@mk_pair α β _ _ a b)) r) (Eq (@REP_prod α β _ _ (@ABS_prod α β _ _ r)) r) := by
    intro α β _ _ r
    apply Eq.propIntro
    ·   intro h
        simp only at h
        obtain ⟨a, b, hr⟩ := h
        rewrite [hr, <- ABS_prod_mk_pair]
        rfl
    ·   intro h
        simp only
        generalize ABS_prod r = p at h
        unfold REP_prod at h
        refine ⟨p.fst,p.snd,?_⟩
        symm
        exact h

theorem mk_pair_def {α β : Type*} [Nonempty α] [Nonempty β] : Eq (@mk_pair α β _ _) (fun x : α => fun y : β => fun a : α => fun b : β => And (Eq a x) (Eq b y)) := Eq.refl (@mk_pair α β _ _)

theorem pair_def {α β : Type*} [Nonempty α] [Nonempty β] : Eq (@prod_mk α β _ _) (fun x : α => fun y : β => @ABS_prod α β _ _ (@mk_pair α β _ _ x y)) := by
    funext x y ; exact ABS_prod_mk_pair

theorem FST_def {α β : Type*} [Nonempty α] [Nonempty β] : Eq (@prod_fst α β _ _) (fun p : Prod α β => @Classical.epsilon α _ (fun x : α => ∃ y : β, Eq p (@prod_mk α β _ _ x y))) := by
    funext p
    apply align_epsilon
    ·   exact ⟨p.snd, rfl⟩
    ·   intro x _ h
        obtain ⟨y', h⟩ := h
        unfold prod_mk at h; unfold prod_fst
        rw [h]

theorem SND_def {α β : Type*} [Nonempty α] [Nonempty β] : Eq (@prod_snd α β _ _) (fun p : Prod α β => @Classical.epsilon β _ (fun y : β => ∃ x : α, Eq p (@prod_mk α β _ _ x y))) := by
    funext p
    apply align_epsilon
    ·   exact ⟨p.fst, rfl⟩
    ·   intro x _ h
        obtain ⟨y, h⟩ := h
        unfold prod_mk at h; unfold prod_snd
        rw [h]
