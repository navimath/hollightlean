/- Record fully parametrizing the translation from Lambdapi (lp) to Lean.
   Every HOL-Light type, constant, definition and theorem of the standard
   library is a field; proof terms and definitional bodies are erased. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option genInjectivity false
set_option linter.unusedVariables false

instance {A B : Type} [h : Nonempty B] : Nonempty (A -> B) := Nonempty.intro (fun _ => Classical.choice h)

class HOLTheory where
  hol_eq : ∀ {A : Type} [Nonempty A], A -> A -> Prop
  epsilon : ∀ {A : Type} [Nonempty A], (A -> Prop) -> A
  fun_ext : ∀ {a b : Type} [Nonempty a] [Nonempty b] {f g : a -> b}, (∀ x, hol_eq (f x) (g x)) -> hol_eq f g
  prop_ext : ∀ {p q : Prop}, (p -> q) -> (q -> p) -> hol_eq p q
  REFL : ∀ {a : Type} [Nonempty a] (t : a), hol_eq t t
  MK_COMB : ∀ {a b : Type} [Nonempty a] [Nonempty b] {s t : a -> b} {u v : a}, (hol_eq s t) -> (hol_eq u v) -> hol_eq (s u) (t v)
  EQ_MP : ∀ {p q : Prop}, (hol_eq p q) -> p -> q
  TRANS {a : Type} [Nonempty a] {x y z : a} (xy : hol_eq x y) (yz : hol_eq y z) : hol_eq x z
  SYM {a : Type} [Nonempty a] {x y : a} (xy : hol_eq x y) : hol_eq y x
  hexists_one : ∀ {A : Type} [Nonempty A], (A -> Prop) -> Prop
  not : Prop -> Prop
  hfalse : Prop
  hor : Prop -> Prop -> Prop
  hexists : ∀ {A : Type} [Nonempty A], (A -> Prop) -> Prop
  hforall : ∀ {A : Type} [Nonempty A], (A -> Prop) -> Prop
  himpl : Prop -> Prop -> Prop
  hand : Prop -> Prop -> Prop
  htrue : Prop
  htrue_intro : htrue
  hand_intro : ∀ {p : Prop}, p -> ∀ {q : Prop}, q -> hand p q
  hand_elim_left : ∀ {p q : Prop}, (hand p q) -> p
  hand_elim_right : ∀ {p q : Prop}, (hand p q) -> q
  hexists_intro : ∀ {a : Type} [Nonempty a] (p : a -> Prop) t, (p t) -> hexists p
  hexists_elim : ∀ {a : Type} [Nonempty a] {p : a -> Prop}, (∃ x, p x) -> ∀ {r : Prop}, (∀ x : a, (p x) -> r) -> r
  hor_intro_left : ∀ {p : Prop}, p -> ∀ q : Prop, hor p q
  hor_intro_right : ∀ (p : Prop) {q : Prop}, q -> hor p q
  hor_elim : ∀ {p q : Prop}, (hor p q) -> ∀ {r}, (p -> r) -> (q -> r) -> r
  unit : Type
  [ne_unit : Nonempty unit]
  prod : Type -> Type -> Type
  [ne_prod : ∀ (a0 a1 : Type), Nonempty (prod a0 a1)]
  ind : Type
  [ne_ind : Nonempty ind]
  num : Type
  [ne_num : Nonempty num]
  recspace : Type -> Type
  [ne_recspace : ∀ (a0 : Type), Nonempty (recspace a0)]
  SUM : Type -> Type -> Type
  [ne_SUM : ∀ (a0 a1 : Type), Nonempty (SUM a0 a1)]
  option : Type -> Type
  [ne_option : ∀ (a0 : Type), Nonempty (option a0)]
  list : Type -> Type
  [ne_list : ∀ (a0 : Type), Nonempty (list a0)]
  char : Type
  [ne_char : Nonempty char]
  nadd : Type
  [ne_nadd : Nonempty nadd]
  hreal : Type
  [ne_hreal : Nonempty hreal]
  Real : Type
  [ne_Real : Nonempty Real]
  int : Type
  [ne_int : Nonempty int]
  finite_image : Type -> Type
  [ne_finite_image : ∀ (a0 : Type), Nonempty (finite_image a0)]
  cart : Type -> Type -> Type
  [ne_cart : ∀ (a0 a1 : Type), Nonempty (cart a0 a1)]
  finite_sum : Type -> Type -> Type
  [ne_finite_sum : ∀ (a0 a1 : Type), Nonempty (finite_sum a0 a1)]
  finite_diff : Type -> Type -> Type
  [ne_finite_diff : ∀ (a0 a1 : Type), Nonempty (finite_diff a0 a1)]
  finite_prod : Type -> Type -> Type
  [ne_finite_prod : ∀ (a0 a1 : Type), Nonempty (finite_prod a0 a1)]
  tybit0 : Type -> Type
  [ne_tybit0 : ∀ (a0 : Type), Nonempty (tybit0 a0)]
  tybit1 : Type -> Type
  [ne_tybit1 : ∀ (a0 : Type), Nonempty (tybit1 a0)]
  htrue_def : hol_eq htrue (hol_eq (fun p : Prop => p) (fun p : Prop => p))
  hand_def : hol_eq hand (fun p : Prop => fun q : Prop => hol_eq (fun f : Prop -> Prop -> Prop => f p q) (fun f : Prop -> Prop -> Prop => f htrue htrue))
  himpl_def : hol_eq himpl (fun p : Prop => fun q : Prop => hol_eq (hand p q) p)
  hforall_def : ∀ {A : Type} [Nonempty A], hol_eq (@hforall A _) (fun P : A -> Prop => hol_eq P (fun x : A => htrue))
  hexists_def : ∀ {A : Type} [Nonempty A], hol_eq (@hexists A _) (fun P : A -> Prop => ∀ q : Prop, (∀ x : A, (P x) -> q) -> q)
  hor_def : hol_eq hor (fun p : Prop => fun q : Prop => ∀ r : Prop, (p -> r) -> (q -> r) -> r)
  hfalse_def : hol_eq hfalse (∀ p : Prop, p)
  not_def : hol_eq not (fun p : Prop => p -> hfalse)
  hexists_one_def : ∀ {A : Type} [Nonempty A], hol_eq (@hexists_one A _) (fun P : A -> Prop => hand (hexists P) (∀ x : A, ∀ y : A, (hand (P x) (P y)) -> hol_eq x y))
  _FALSITY_ : Prop
  _FALSITY__def : hol_eq _FALSITY_ hfalse
  COND {A : Type} [Nonempty A] : Prop -> A -> A -> A
  COND_def {A : Type} [Nonempty A] : hol_eq (@COND A _) (fun t : Prop => fun t1 : A => fun t2 : A => @epsilon A _ (fun x : A => hand ((hol_eq t htrue) -> hol_eq x t1) ((hol_eq t hfalse) -> hol_eq x t2)))
  o {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : (B -> C) -> (A -> B) -> A -> C
  o_def {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : hol_eq (@o A B C _ _ _) (fun f : B -> C => fun g : A -> B => fun x : A => f (g x))
  I {A : Type} [Nonempty A] : A -> A
  I_def {A : Type} [Nonempty A] : hol_eq (@I A _) (fun x : A => x)
  one_ABS : Prop -> unit
  one_REP : unit -> Prop
  one : unit
  one_def : hol_eq one (@epsilon unit _ (fun x : unit => htrue))
  hashek : Prop
  hashek_def : hol_eq hashek htrue
  LET {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> A -> B
  LET_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@LET A B _ _) (fun f : A -> B => fun x : A => f x)
  LET_END {A : Type} [Nonempty A] : A -> A
  LET_END_def {A : Type} [Nonempty A] : hol_eq (@LET_END A _) (fun t : A => t)
  GABS {A : Type} [Nonempty A] : (A -> Prop) -> A
  GABS_def {A : Type} [Nonempty A] : hol_eq (@GABS A _) (fun P : A -> Prop => @epsilon A _ P)
  GEQ {A : Type} [Nonempty A] : A -> A -> Prop
  GEQ_def {A : Type} [Nonempty A] : hol_eq (@GEQ A _) (fun a : A => fun b : A => hol_eq a b)
  _SEQPATTERN {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (A -> B -> Prop) -> A -> B -> Prop
  _SEQPATTERN_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@_SEQPATTERN A B _ _) (fun r : A -> B -> Prop => fun s : A -> B -> Prop => fun x : A => @COND (B -> Prop) _ (∃ y : B, r x y) (r x) (s x))
  _UNGUARDED_PATTERN : Prop -> Prop -> Prop
  _UNGUARDED_PATTERN_def : hol_eq _UNGUARDED_PATTERN (fun p : Prop => fun r : Prop => hand p r)
  _GUARDED_PATTERN : Prop -> Prop -> Prop -> Prop
  _GUARDED_PATTERN_def : hol_eq _GUARDED_PATTERN (fun p : Prop => fun g : Prop => fun r : Prop => hand p (hand g r))
  _MATCH {A B : Type} [Nonempty A] [Nonempty B] : A -> (A -> B -> Prop) -> B
  _MATCH_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@_MATCH A B _ _) (fun e : A => fun r : A -> B -> Prop => @COND B _ (@hexists_one B _ (r e)) (@epsilon B _ (r e)) (@epsilon B _ (fun z : B => hfalse)))
  _FUNCTION {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> A -> B
  _FUNCTION_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@_FUNCTION A B _ _) (fun r : A -> B -> Prop => fun x : A => @COND B _ (@hexists_one B _ (r x)) (@epsilon B _ (r x)) (@epsilon B _ (fun z : B => hfalse)))
  mk_pair {A B : Type} [Nonempty A] [Nonempty B] : A -> B -> A -> B -> Prop
  mk_pair_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@mk_pair A B _ _) (fun x : A => fun y : B => fun a : A => fun b : B => hand (hol_eq a x) (hol_eq b y))
  ABS_prod : ∀ {A B : Type} [Nonempty A] [Nonempty B], (A -> B -> Prop) -> prod A B
  REP_prod : ∀ {A B : Type} [Nonempty A] [Nonempty B], (prod A B) -> A -> B -> Prop
  Prod_mk {A B : Type} [Nonempty A] [Nonempty B] : A -> B -> prod A B
  pair_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@Prod_mk A B _ _) (fun x : A => fun y : B => @ABS_prod A B _ _ (@mk_pair A B _ _ x y))
  FST {A B : Type} [Nonempty A] [Nonempty B] : (prod A B) -> A
  FST_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@FST A B _ _) (fun p : prod A B => @epsilon A _ (fun x : A => ∃ y : B, hol_eq p (@Prod_mk A B _ _ x y)))
  SND {A B : Type} [Nonempty A] [Nonempty B] : (prod A B) -> B
  SND_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@SND A B _ _) (fun p : prod A B => @epsilon B _ (fun y : B => ∃ x : A, hol_eq p (@Prod_mk A B _ _ x y)))
  CURRY {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : ((prod A B) -> C) -> A -> B -> C
  CURRY_def {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : hol_eq (@CURRY A B C _ _ _) (fun _1283 : (prod A B) -> C => fun _1284 : A => fun _1285 : B => _1283 (@Prod_mk A B _ _ _1284 _1285))
  UNCURRY {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C) -> (prod A B) -> C
  UNCURRY_def {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : hol_eq (@UNCURRY A B C _ _ _) (fun _1304 : A -> B -> C => fun _1305 : prod A B => _1304 (@FST A B _ _ _1305) (@SND A B _ _ _1305))
  PASSOC {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] : ((prod (prod A B) C) -> D) -> (prod A (prod B C)) -> D
  PASSOC_def {A B C D : Type} [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] : hol_eq (@PASSOC A B C D _ _ _ _) (fun _1321 : (prod (prod A B) C) -> D => fun _1322 : prod A (prod B C) => _1321 (@Prod_mk (prod A B) C _ _ (@Prod_mk A B _ _ (@FST A (prod B C) _ _ _1322) (@FST B C _ _ (@SND A (prod B C) _ _ _1322))) (@SND B C _ _ (@SND A (prod B C) _ _ _1322))))
  ONE_ONE {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> Prop
  ONE_ONE_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ONE_ONE A B _ _) (fun _2064 : A -> B => ∀ x1 : A, ∀ x2 : A, (hol_eq (_2064 x1) (_2064 x2)) -> hol_eq x1 x2)
  ONTO {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> Prop
  ONTO_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ONTO A B _ _) (fun _2069 : A -> B => ∀ y : B, ∃ x : A, hol_eq y (_2069 x))
  IND_SUC : ind -> ind
  IND_SUC_def : hol_eq IND_SUC (@epsilon (ind -> ind) _ (fun f : ind -> ind => ∃ z : ind, hand (∀ x1 : ind, ∀ x2 : ind, hol_eq (hol_eq (f x1) (f x2)) (hol_eq x1 x2)) (∀ x : ind, not (hol_eq (f x) z))))
  IND_0 : ind
  IND_0_def : hol_eq IND_0 (@epsilon ind _ (fun z : ind => hand (∀ x1 : ind, ∀ x2 : ind, hol_eq (hol_eq (IND_SUC x1) (IND_SUC x2)) (hol_eq x1 x2)) (∀ x : ind, not (hol_eq (IND_SUC x) z))))
  NUM_REP : ind -> Prop
  NUM_REP_def : hol_eq NUM_REP (fun a : ind => ∀ NUM_REP' : ind -> Prop, (∀ a' : ind, (hor (hol_eq a' IND_0) (∃ i : ind, hand (hol_eq a' (IND_SUC i)) (NUM_REP' i))) -> NUM_REP' a') -> NUM_REP' a)
  mk_num : ind -> num
  dest_num : num -> ind
  _0 : num
  _0_def : hol_eq _0 (mk_num IND_0)
  SUC : num -> num
  SUC_def : hol_eq SUC (fun _2104 : num => mk_num (IND_SUC (dest_num _2104)))
  NUMERAL : num -> num
  NUMERAL_def : hol_eq NUMERAL (fun _2128 : num => _2128)
  BIT0 : num -> num
  BIT0_def : hol_eq BIT0 (@epsilon (num -> num) _ (fun fn : num -> num => hand (hol_eq (fn (NUMERAL _0)) (NUMERAL _0)) (∀ n : num, hol_eq (fn (SUC n)) (SUC (SUC (fn n))))))
  BIT1 : num -> num
  BIT1_def : hol_eq BIT1 (fun _2143 : num => SUC (BIT0 _2143))
  PRE : num -> num
  PRE_def : hol_eq PRE (@epsilon ((prod num (prod num num)) -> num -> num) _ (fun PRE' : (prod num (prod num num)) -> num -> num => ∀ _2151 : prod num (prod num num), hand (hol_eq (PRE' _2151 (NUMERAL _0)) (NUMERAL _0)) (∀ n : num, hol_eq (PRE' _2151 (SUC n)) n)) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))
  Nat_add : num -> num -> num
  add_def : hol_eq Nat_add (@epsilon (num -> num -> num -> num) _ (fun add' : num -> num -> num -> num => ∀ _2155 : num, hand (∀ n : num, hol_eq (add' _2155 (NUMERAL _0) n) n) (∀ m : num, ∀ n : num, hol_eq (add' _2155 (SUC m) n) (SUC (add' _2155 m n)))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))
  Nat_mul : num -> num -> num
  mul_def : hol_eq Nat_mul (@epsilon (num -> num -> num -> num) _ (fun mul' : num -> num -> num -> num => ∀ _2186 : num, hand (∀ n : num, hol_eq (mul' _2186 (NUMERAL _0) n) (NUMERAL _0)) (∀ m : num, ∀ n : num, hol_eq (mul' _2186 (SUC m) n) (Nat_add (mul' _2186 m n) n))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))
  EXP : num -> num -> num
  EXP_def : hol_eq EXP (@epsilon ((prod num (prod num num)) -> num -> num -> num) _ (fun EXP' : (prod num (prod num num)) -> num -> num -> num => ∀ _2224 : prod num (prod num num), hand (∀ m : num, hol_eq (EXP' _2224 m (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ m : num, ∀ n : num, hol_eq (EXP' _2224 m (SUC n)) (Nat_mul m (EXP' _2224 m n)))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))
  Nat_le : num -> num -> Prop
  le_def : hol_eq Nat_le (@epsilon ((prod num num) -> num -> num -> Prop) _ (fun le' : (prod num num) -> num -> num -> Prop => ∀ _2241 : prod num num, hand (∀ m : num, hol_eq (le' _2241 m (NUMERAL _0)) (hol_eq m (NUMERAL _0))) (∀ m : num, ∀ n : num, hol_eq (le' _2241 m (SUC n)) (hor (hol_eq m (SUC n)) (le' _2241 m n)))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0)))))))))
  Nat_lt : num -> num -> Prop
  lt_def : hol_eq Nat_lt (@epsilon (num -> num -> num -> Prop) _ (fun lt : num -> num -> num -> Prop => ∀ _2248 : num, hand (∀ m : num, hol_eq (lt _2248 m (NUMERAL _0)) hfalse) (∀ m : num, ∀ n : num, hol_eq (lt _2248 m (SUC n)) (hor (hol_eq m n) (lt _2248 m n)))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 (BIT1 _0))))))))
  Nat_ge : num -> num -> Prop
  ge_def : hol_eq Nat_ge (fun _2249 : num => fun _2250 : num => Nat_le _2250 _2249)
  Nat_gt : num -> num -> Prop
  gt_def : hol_eq Nat_gt (fun _2261 : num => fun _2262 : num => Nat_lt _2262 _2261)
  MAX : num -> num -> num
  MAX_def : hol_eq MAX (fun _2273 : num => fun _2274 : num => @COND num _ (Nat_le _2273 _2274) _2274 _2273)
  MIN : num -> num -> num
  MIN_def : hol_eq MIN (fun _2285 : num => fun _2286 : num => @COND num _ (Nat_le _2285 _2286) _2285 _2286)
  EVEN : num -> Prop
  EVEN_def : hol_eq EVEN (@epsilon ((prod num (prod num (prod num num))) -> num -> Prop) _ (fun EVEN' : (prod num (prod num (prod num num))) -> num -> Prop => ∀ _2603 : prod num (prod num (prod num num)), hand (hol_eq (EVEN' _2603 (NUMERAL _0)) htrue) (∀ n : num, hol_eq (EVEN' _2603 (SUC n)) (not (EVEN' _2603 n)))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))))
  ODD : num -> Prop
  ODD_def : hol_eq ODD (@epsilon ((prod num (prod num num)) -> num -> Prop) _ (fun ODD' : (prod num (prod num num)) -> num -> Prop => ∀ _2607 : prod num (prod num num), hand (hol_eq (ODD' _2607 (NUMERAL _0)) hfalse) (∀ n : num, hol_eq (ODD' _2607 (SUC n)) (not (ODD' _2607 n)))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))
  Nat_minus : num -> num -> num
  minus_def : hol_eq Nat_minus (@epsilon (num -> num -> num -> num) _ (fun minus' : num -> num -> num -> num => ∀ _2766 : num, hand (∀ m : num, hol_eq (minus' _2766 m (NUMERAL _0)) m) (∀ m : num, ∀ n : num, hol_eq (minus' _2766 m (SUC n)) (PRE (minus' _2766 m n)))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0))))))))
  FACT : num -> num
  FACT_def : hol_eq FACT (@epsilon ((prod num (prod num (prod num num))) -> num -> num) _ (fun FACT' : (prod num (prod num (prod num num))) -> num -> num => ∀ _2944 : prod num (prod num (prod num num)), hand (hol_eq (FACT' _2944 (NUMERAL _0)) (NUMERAL (BIT1 _0))) (∀ n : num, hol_eq (FACT' _2944 (SUC n)) (Nat_mul (SUC n) (FACT' _2944 n)))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))
  DIV : num -> num -> num
  DIV_def : hol_eq DIV (@epsilon ((prod num (prod num num)) -> num -> num -> num) _ (fun q : (prod num (prod num num)) -> num -> num -> num => ∀ _3086 : prod num (prod num num), ∃ r : num -> num -> num, ∀ m : num, ∀ n : num, @COND Prop _ (hol_eq n (NUMERAL _0)) (hand (hol_eq (q _3086 m n) (NUMERAL _0)) (hol_eq (r m n) m)) (hand (hol_eq m (Nat_add (Nat_mul (q _3086 m n) n) (r m n))) (Nat_lt (r m n) n))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))
  MOD : num -> num -> num
  MOD_def : hol_eq MOD (@epsilon ((prod num (prod num num)) -> num -> num -> num) _ (fun r : (prod num (prod num num)) -> num -> num -> num => ∀ _3087 : prod num (prod num num), ∀ m : num, ∀ n : num, @COND Prop _ (hol_eq n (NUMERAL _0)) (hand (hol_eq (DIV m n) (NUMERAL _0)) (hol_eq (r _3087 m n) m)) (hand (hol_eq m (Nat_add (Nat_mul (DIV m n) n) (r _3087 m n))) (Nat_lt (r _3087 m n) n))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))
  minimal : (num -> Prop) -> num
  minimal_def : hol_eq minimal (fun _6536 : num -> Prop => @epsilon num _ (fun n : num => hand (_6536 n) (∀ m : num, (Nat_lt m n) -> not (_6536 m))))
  WF {A : Type} [Nonempty A] : (A -> A -> Prop) -> Prop
  WF_def {A : Type} [Nonempty A] : hol_eq (@WF A _) (fun _6923 : A -> A -> Prop => ∀ P : A -> Prop, (∃ x : A, P x) -> ∃ x : A, hand (P x) (∀ y : A, (_6923 y x) -> not (P y)))
  MEASURE {A : Type} [Nonempty A] : (A -> num) -> A -> A -> Prop
  MEASURE_def {A : Type} [Nonempty A] : hol_eq (@MEASURE A _) (fun _8094 : A -> num => fun x : A => fun y : A => Nat_lt (_8094 x) (_8094 y))
  NUMPAIR : num -> num -> num
  NUMPAIR_def : hol_eq NUMPAIR (fun _17487 : num => fun _17488 : num => Nat_mul (EXP (NUMERAL (BIT0 (BIT1 _0))) _17487) (Nat_add (Nat_mul (NUMERAL (BIT0 (BIT1 _0))) _17488) (NUMERAL (BIT1 _0))))
  NUMFST : num -> num
  NUMFST_def : hol_eq NUMFST (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> num -> num) _ (fun X : (prod num (prod num (prod num (prod num (prod num num))))) -> num -> num => ∀ _17503 : prod num (prod num (prod num (prod num (prod num num)))), ∃ Y : num -> num, ∀ x : num, ∀ y : num, hand (hol_eq (X _17503 (NUMPAIR x y)) x) (hol_eq (Y (NUMPAIR x y)) y)) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))
  NUMSND : num -> num
  NUMSND_def : hol_eq NUMSND (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> num -> num) _ (fun Y : (prod num (prod num (prod num (prod num (prod num num))))) -> num -> num => ∀ _17504 : prod num (prod num (prod num (prod num (prod num num)))), ∀ x : num, ∀ y : num, hand (hol_eq (NUMFST (NUMPAIR x y)) x) (hol_eq (Y _17504 (NUMPAIR x y)) y)) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))
  NUMSUM : Prop -> num -> num
  NUMSUM_def : hol_eq NUMSUM (fun _17505 : Prop => fun _17506 : num => @COND num _ _17505 (SUC (Nat_mul (NUMERAL (BIT0 (BIT1 _0))) _17506)) (Nat_mul (NUMERAL (BIT0 (BIT1 _0))) _17506))
  NUMLEFT : num -> Prop
  NUMLEFT_def : hol_eq NUMLEFT (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> num -> Prop) _ (fun X : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> num -> Prop => ∀ _17535 : prod num (prod num (prod num (prod num (prod num (prod num num))))), ∃ Y : num -> num, ∀ x : Prop, ∀ y : num, hand (hol_eq (X _17535 (NUMSUM x y)) x) (hol_eq (Y (NUMSUM x y)) y)) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))))
  NUMRIGHT : num -> num
  NUMRIGHT_def : hol_eq NUMRIGHT (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> num -> num) _ (fun Y : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> num -> num => ∀ _17536 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), ∀ x : Prop, ∀ y : num, hand (hol_eq (NUMLEFT (NUMSUM x y)) x) (hol_eq (Y _17536 (NUMSUM x y)) y)) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))))
  INJN {A : Type} [Nonempty A] : num -> num -> A -> Prop
  INJN_def {A : Type} [Nonempty A] : hol_eq (@INJN A _) (fun _17537 : num => fun n : num => fun a : A => hol_eq n _17537)
  INJA {A : Type} [Nonempty A] : A -> num -> A -> Prop
  INJA_def {A : Type} [Nonempty A] : hol_eq (@INJA A _) (fun _17542 : A => fun n : num => fun b : A => hol_eq b _17542)
  INJF {A : Type} [Nonempty A] : (num -> num -> A -> Prop) -> num -> A -> Prop
  INJF_def {A : Type} [Nonempty A] : hol_eq (@INJF A _) (fun _17549 : num -> num -> A -> Prop => fun n : num => _17549 (NUMFST n) (NUMSND n))
  INJP {A : Type} [Nonempty A] : (num -> A -> Prop) -> (num -> A -> Prop) -> num -> A -> Prop
  INJP_def {A : Type} [Nonempty A] : hol_eq (@INJP A _) (fun _17554 : num -> A -> Prop => fun _17555 : num -> A -> Prop => fun n : num => fun a : A => @COND Prop _ (NUMLEFT n) (_17554 (NUMRIGHT n) a) (_17555 (NUMRIGHT n) a))
  ZCONSTR {A : Type} [Nonempty A] : num -> A -> (num -> num -> A -> Prop) -> num -> A -> Prop
  ZCONSTR_def {A : Type} [Nonempty A] : hol_eq (@ZCONSTR A _) (fun _17566 : num => fun _17567 : A => fun _17568 : num -> num -> A -> Prop => @INJP A _ (@INJN A _ (SUC _17566)) (@INJP A _ (@INJA A _ _17567) (@INJF A _ _17568)))
  ZBOT {A : Type} [Nonempty A] : num -> A -> Prop
  ZBOT_def {A : Type} [Nonempty A] : hol_eq (@ZBOT A _) (@INJP A _ (@INJN A _ (NUMERAL _0)) (@epsilon (num -> A -> Prop) _ (fun z : num -> A -> Prop => htrue)))
  ZRECSPACE {A : Type} [Nonempty A] : (num -> A -> Prop) -> Prop
  ZRECSPACE_def {A : Type} [Nonempty A] : hol_eq (@ZRECSPACE A _) (fun a : num -> A -> Prop => ∀ ZRECSPACE' : (num -> A -> Prop) -> Prop, (∀ a' : num -> A -> Prop, (hor (hol_eq a' (@ZBOT A _)) (∃ c : num, ∃ i : A, ∃ r : num -> num -> A -> Prop, hand (hol_eq a' (@ZCONSTR A _ c i r)) (∀ n : num, ZRECSPACE' (r n)))) -> ZRECSPACE' a') -> ZRECSPACE' a)
  _mk_rec : ∀ {A : Type} [Nonempty A], (num -> A -> Prop) -> recspace A
  _dest_rec : ∀ {A : Type} [Nonempty A], (recspace A) -> num -> A -> Prop
  BOTTOM {A : Type} [Nonempty A] : recspace A
  BOTTOM_def {A : Type} [Nonempty A] : hol_eq (@BOTTOM A _) (@_mk_rec A _ (@ZBOT A _))
  CONSTR {A : Type} [Nonempty A] : num -> A -> (num -> recspace A) -> recspace A
  CONSTR_def {A : Type} [Nonempty A] : hol_eq (@CONSTR A _) (fun _17591 : num => fun _17592 : A => fun _17593 : num -> recspace A => @_mk_rec A _ (@ZCONSTR A _ _17591 _17592 (fun n : num => @_dest_rec A _ (_17593 n))))
  FCONS {A : Type} [Nonempty A] : A -> (num -> A) -> num -> A
  FCONS_def {A : Type} [Nonempty A] : hol_eq (@FCONS A _) (@epsilon ((prod num (prod num (prod num (prod num num)))) -> A -> (num -> A) -> num -> A) _ (fun FCONS' : (prod num (prod num (prod num (prod num num)))) -> A -> (num -> A) -> num -> A => ∀ _17623 : prod num (prod num (prod num (prod num num))), hand (∀ a : A, ∀ f : num -> A, hol_eq (FCONS' _17623 a f (NUMERAL _0)) a) (∀ a : A, ∀ f : num -> A, ∀ n : num, hol_eq (FCONS' _17623 a f (SUC n)) (f n))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))
  FNIL {A : Type} [Nonempty A] : num -> A
  FNIL_def {A : Type} [Nonempty A] : hol_eq (@FNIL A _) (fun _17624 : num => @epsilon A _ (fun x : A => htrue))
  _mk_sum : ∀ {A B : Type} [Nonempty A] [Nonempty B], (recspace (prod A B)) -> SUM A B
  _dest_sum : ∀ {A B : Type} [Nonempty A] [Nonempty B], (SUM A B) -> recspace (prod A B)
  INL {A B : Type} [Nonempty A] [Nonempty B] : A -> SUM A B
  INL_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@INL A B _ _) (fun a : A => @_mk_sum A B _ _ ((fun a' : A => @CONSTR (prod A B) _ (NUMERAL _0) (@Prod_mk A B _ _ a' (@epsilon B _ (fun v : B => htrue))) (fun n : num => @BOTTOM (prod A B) _)) a))
  INR {A B : Type} [Nonempty A] [Nonempty B] : B -> SUM A B
  INR_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@INR A B _ _) (fun a : B => @_mk_sum A B _ _ ((fun a' : B => @CONSTR (prod A B) _ (SUC (NUMERAL _0)) (@Prod_mk A B _ _ (@epsilon A _ (fun v : A => htrue)) a') (fun n : num => @BOTTOM (prod A B) _)) a))
  OUTL {A B : Type} [Nonempty A] [Nonempty B] : (SUM A B) -> A
  OUTL_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@OUTL A B _ _) (@epsilon ((prod num (prod num (prod num num))) -> (SUM A B) -> A) _ (fun OUTL' : (prod num (prod num (prod num num))) -> (SUM A B) -> A => ∀ _17649 : prod num (prod num (prod num num)), ∀ x : A, hol_eq (OUTL' _17649 (@INL A B _ _ x)) x) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))))
  OUTR {A B : Type} [Nonempty A] [Nonempty B] : (SUM A B) -> B
  OUTR_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@OUTR A B _ _) (@epsilon ((prod num (prod num (prod num num))) -> (SUM A B) -> B) _ (fun OUTR' : (prod num (prod num (prod num num))) -> (SUM A B) -> B => ∀ _17651 : prod num (prod num (prod num num)), ∀ y : B, hol_eq (OUTR' _17651 (@INR A B _ _ y)) y) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))
  _mk_option : ∀ {A : Type} [Nonempty A], (recspace A) -> option A
  _dest_option : ∀ {A : Type} [Nonempty A], (option A) -> recspace A
  NONE {A : Type} [Nonempty A] : option A
  NONE_def {A : Type} [Nonempty A] : hol_eq (@NONE A _) (@_mk_option A _ (@CONSTR A _ (NUMERAL _0) (@epsilon A _ (fun v : A => htrue)) (fun n : num => @BOTTOM A _)))
  SOME {A : Type} [Nonempty A] : A -> option A
  SOME_def {A : Type} [Nonempty A] : hol_eq (@SOME A _) (fun a : A => @_mk_option A _ ((fun a' : A => @CONSTR A _ (SUC (NUMERAL _0)) a' (fun n : num => @BOTTOM A _)) a))
  _mk_list : ∀ {A : Type} [Nonempty A], (recspace A) -> list A
  _dest_list : ∀ {A : Type} [Nonempty A], (list A) -> recspace A
  NIL {A : Type} [Nonempty A] : list A
  NIL_def {A : Type} [Nonempty A] : hol_eq (@NIL A _) (@_mk_list A _ (@CONSTR A _ (NUMERAL _0) (@epsilon A _ (fun v : A => htrue)) (fun n : num => @BOTTOM A _)))
  CONS {A : Type} [Nonempty A] : A -> (list A) -> list A
  CONS_def {A : Type} [Nonempty A] : hol_eq (@CONS A _) (fun a0 : A => fun a1 : list A => @_mk_list A _ ((fun a0' : A => fun a1' : recspace A => @CONSTR A _ (SUC (NUMERAL _0)) a0' (@FCONS (recspace A) _ a1' (fun n : num => @BOTTOM A _))) a0 (@_dest_list A _ a1)))
  ISO {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> (B -> A) -> Prop
  ISO_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ISO A B _ _) (fun _17732 : A -> B => fun _17733 : B -> A => hand (∀ x : B, hol_eq (_17732 (_17733 x)) x) (∀ y : A, hol_eq (_17733 (_17732 y)) y))
  HD {A : Type} [Nonempty A] : (list A) -> A
  HD_def {A : Type} [Nonempty A] : hol_eq (@HD A _) (@epsilon ((prod num num) -> (list A) -> A) _ (fun HD' : (prod num num) -> (list A) -> A => ∀ _18090 : prod num num, ∀ t : list A, ∀ h : A, hol_eq (HD' _18090 (@CONS A _ h t)) h) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))
  TL {A : Type} [Nonempty A] : (list A) -> list A
  TL_def {A : Type} [Nonempty A] : hol_eq (@TL A _) (@epsilon ((prod num num) -> (list A) -> list A) _ (fun TL' : (prod num num) -> (list A) -> list A => ∀ _18094 : prod num num, ∀ h : A, ∀ t : list A, hol_eq (TL' _18094 (@CONS A _ h t)) t) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))
  APPEND {A : Type} [Nonempty A] : (list A) -> (list A) -> list A
  APPEND_def {A : Type} [Nonempty A] : hol_eq (@APPEND A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> (list A) -> list A) _ (fun APPEND' : (prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> (list A) -> list A => ∀ _18098 : prod num (prod num (prod num (prod num (prod num num)))), hand (∀ l : list A, hol_eq (APPEND' _18098 (@NIL A _) l) l) (∀ h : A, ∀ t : list A, ∀ l : list A, hol_eq (APPEND' _18098 (@CONS A _ h t) l) (@CONS A _ h (APPEND' _18098 t l)))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))
  REVERSE {A : Type} [Nonempty A] : (list A) -> list A
  REVERSE_def {A : Type} [Nonempty A] : hol_eq (@REVERSE A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A) _ (fun REVERSE' : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A => ∀ _18102 : prod num (prod num (prod num (prod num (prod num (prod num num))))), hand (hol_eq (REVERSE' _18102 (@NIL A _)) (@NIL A _)) (∀ l : list A, ∀ x : A, hol_eq (REVERSE' _18102 (@CONS A _ x l)) (@APPEND A _ (REVERSE' _18102 l) (@CONS A _ x (@NIL A _))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))))))
  LENGTH {A : Type} [Nonempty A] : (list A) -> num
  LENGTH_def {A : Type} [Nonempty A] : hol_eq (@LENGTH A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> num) _ (fun LENGTH' : (prod num (prod num (prod num (prod num (prod num num))))) -> (list A) -> num => ∀ _18106 : prod num (prod num (prod num (prod num (prod num num)))), hand (hol_eq (LENGTH' _18106 (@NIL A _)) (NUMERAL _0)) (∀ h : A, ∀ t : list A, hol_eq (LENGTH' _18106 (@CONS A _ h t)) (SUC (LENGTH' _18106 t)))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))))))
  MAP {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> (list A) -> list B
  MAP_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@MAP A B _ _) (@epsilon ((prod num (prod num num)) -> (A -> B) -> (list A) -> list B) _ (fun MAP' : (prod num (prod num num)) -> (A -> B) -> (list A) -> list B => ∀ _18113 : prod num (prod num num), hand (∀ f : A -> B, hol_eq (MAP' _18113 f (@NIL A _)) (@NIL B _)) (∀ f : A -> B, ∀ h : A, ∀ t : list A, hol_eq (MAP' _18113 f (@CONS A _ h t)) (@CONS B _ (f h) (MAP' _18113 f t)))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))
  LAST {A : Type} [Nonempty A] : (list A) -> A
  LAST_def {A : Type} [Nonempty A] : hol_eq (@LAST A _) (@epsilon ((prod num (prod num (prod num num))) -> (list A) -> A) _ (fun LAST' : (prod num (prod num (prod num num))) -> (list A) -> A => ∀ _18117 : prod num (prod num (prod num num)), ∀ h : A, ∀ t : list A, hol_eq (LAST' _18117 (@CONS A _ h t)) (@COND A _ (hol_eq t (@NIL A _)) h (LAST' _18117 t))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))
  BUTLAST {A : Type} [Nonempty A] : (list A) -> list A
  BUTLAST_def {A : Type} [Nonempty A] : hol_eq (@BUTLAST A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A) _ (fun BUTLAST' : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (list A) -> list A => ∀ _18121 : prod num (prod num (prod num (prod num (prod num (prod num num))))), hand (hol_eq (BUTLAST' _18121 (@NIL A _)) (@NIL A _)) (∀ h : A, ∀ t : list A, hol_eq (BUTLAST' _18121 (@CONS A _ h t)) (@COND (list A) _ (hol_eq t (@NIL A _)) (@NIL A _) (@CONS A _ h (BUTLAST' _18121 t))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))))))
  REPLICATE {A : Type} [Nonempty A] : num -> A -> list A
  REPLICATE_def {A : Type} [Nonempty A] : hol_eq (@REPLICATE A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) -> num -> A -> list A) _ (fun REPLICATE' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) -> num -> A -> list A => ∀ _18125 : prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))), hand (∀ x : A, hol_eq (REPLICATE' _18125 (NUMERAL _0) x) (@NIL A _)) (∀ n : num, ∀ x : A, hol_eq (REPLICATE' _18125 (SUC n) x) (@CONS A _ x (REPLICATE' _18125 n x)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))))))))
  NULL {A : Type} [Nonempty A] : (list A) -> Prop
  NULL_def {A : Type} [Nonempty A] : hol_eq (@NULL A _) (@epsilon ((prod num (prod num (prod num num))) -> (list A) -> Prop) _ (fun NULL' : (prod num (prod num (prod num num))) -> (list A) -> Prop => ∀ _18129 : prod num (prod num (prod num num)), hand (hol_eq (NULL' _18129 (@NIL A _)) htrue) (∀ h : A, ∀ t : list A, hol_eq (NULL' _18129 (@CONS A _ h t)) hfalse)) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))))
  ALL {A : Type} [Nonempty A] : (A -> Prop) -> (list A) -> Prop
  ALL_def {A : Type} [Nonempty A] : hol_eq (@ALL A _) (@epsilon ((prod num (prod num num)) -> (A -> Prop) -> (list A) -> Prop) _ (fun ALL' : (prod num (prod num num)) -> (A -> Prop) -> (list A) -> Prop => ∀ _18136 : prod num (prod num num), hand (∀ P : A -> Prop, hol_eq (ALL' _18136 P (@NIL A _)) htrue) (∀ h : A, ∀ P : A -> Prop, ∀ t : list A, hol_eq (ALL' _18136 P (@CONS A _ h t)) (hand (P h) (ALL' _18136 P t)))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))
  EX {A : Type} [Nonempty A] : (A -> Prop) -> (list A) -> Prop
  EX_def {A : Type} [Nonempty A] : hol_eq (@EX A _) (@epsilon ((prod num num) -> (A -> Prop) -> (list A) -> Prop) _ (fun EX' : (prod num num) -> (A -> Prop) -> (list A) -> Prop => ∀ _18143 : prod num num, hand (∀ P : A -> Prop, hol_eq (EX' _18143 P (@NIL A _)) hfalse) (∀ h : A, ∀ P : A -> Prop, ∀ t : list A, hol_eq (EX' _18143 P (@CONS A _ h t)) (hor (P h) (EX' _18143 P t)))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0))))))))))
  ITLIST {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> B) -> (list A) -> B -> B
  ITLIST_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ITLIST A B _ _) (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> (A -> B -> B) -> (list A) -> B -> B) _ (fun ITLIST' : (prod num (prod num (prod num (prod num (prod num num))))) -> (A -> B -> B) -> (list A) -> B -> B => ∀ _18151 : prod num (prod num (prod num (prod num (prod num num)))), hand (∀ f : A -> B -> B, ∀ b : B, hol_eq (ITLIST' _18151 f (@NIL A _) b) b) (∀ h : A, ∀ f : A -> B -> B, ∀ t : list A, ∀ b : B, hol_eq (ITLIST' _18151 f (@CONS A _ h t) b) (f h (ITLIST' _18151 f t b)))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))
  MEM {A : Type} [Nonempty A] : A -> (list A) -> Prop
  MEM_def {A : Type} [Nonempty A] : hol_eq (@MEM A _) (@epsilon ((prod num (prod num num)) -> A -> (list A) -> Prop) _ (fun MEM' : (prod num (prod num num)) -> A -> (list A) -> Prop => ∀ _18158 : prod num (prod num num), hand (∀ x : A, hol_eq (MEM' _18158 x (@NIL A _)) hfalse) (∀ h : A, ∀ x : A, ∀ t : list A, hol_eq (MEM' _18158 x (@CONS A _ h t)) (hor (hol_eq x h) (MEM' _18158 x t)))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))))))
  ALL2 {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (list A) -> (list B) -> Prop
  ALL2_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ALL2 A B _ _) (@epsilon ((prod num (prod num (prod num num))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop) _ (fun ALL2' : (prod num (prod num (prod num num))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop => ∀ _18166 : prod num (prod num (prod num num)), hand (∀ P : A -> B -> Prop, ∀ l2 : list B, hol_eq (ALL2' _18166 P (@NIL A _) l2) (hol_eq l2 (@NIL B _))) (∀ h1' : A, ∀ P : A -> B -> Prop, ∀ t1 : list A, ∀ l2 : list B, hol_eq (ALL2' _18166 P (@CONS A _ h1' t1) l2) (@COND Prop _ (hol_eq l2 (@NIL B _)) hfalse (hand (P h1' (@HD B _ l2)) (ALL2' _18166 P t1 (@TL B _ l2)))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))))))
  MAP2 {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C) -> (list A) -> (list B) -> list C
  MAP2_def {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : hol_eq (@MAP2 A B C _ _ _) (@epsilon ((prod num (prod num (prod num num))) -> (A -> B -> C) -> (list A) -> (list B) -> list C) _ (fun MAP2' : (prod num (prod num (prod num num))) -> (A -> B -> C) -> (list A) -> (list B) -> list C => ∀ _18174 : prod num (prod num (prod num num)), hand (∀ f : A -> B -> C, ∀ l : list B, hol_eq (MAP2' _18174 f (@NIL A _) l) (@NIL C _)) (∀ h1' : A, ∀ f : A -> B -> C, ∀ t1 : list A, ∀ l : list B, hol_eq (MAP2' _18174 f (@CONS A _ h1' t1) l) (@CONS C _ (f h1' (@HD B _ l)) (MAP2' _18174 f t1 (@TL B _ l))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))))))
  EL {A : Type} [Nonempty A] : num -> (list A) -> A
  EL_def {A : Type} [Nonempty A] : hol_eq (@EL A _) (@epsilon ((prod num num) -> num -> (list A) -> A) _ (fun EL' : (prod num num) -> num -> (list A) -> A => ∀ _18178 : prod num num, hand (∀ l : list A, hol_eq (EL' _18178 (NUMERAL _0) l) (@HD A _ l)) (∀ n : num, ∀ l : list A, hol_eq (EL' _18178 (SUC n) l) (EL' _18178 n (@TL A _ l)))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0))))))))))
  FILTER {A : Type} [Nonempty A] : (A -> Prop) -> (list A) -> list A
  FILTER_def {A : Type} [Nonempty A] : hol_eq (@FILTER A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> (A -> Prop) -> (list A) -> list A) _ (fun FILTER' : (prod num (prod num (prod num (prod num (prod num num))))) -> (A -> Prop) -> (list A) -> list A => ∀ _18185 : prod num (prod num (prod num (prod num (prod num num)))), hand (∀ P : A -> Prop, hol_eq (FILTER' _18185 P (@NIL A _)) (@NIL A _)) (∀ h : A, ∀ P : A -> Prop, ∀ t : list A, hol_eq (FILTER' _18185 P (@CONS A _ h t)) (@COND (list A) _ (P h) (@CONS A _ h (FILTER' _18185 P t)) (FILTER' _18185 P t)))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))
  ASSOC {A B : Type} [Nonempty A] [Nonempty B] : A -> (list (prod A B)) -> B
  ASSOC_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ASSOC A B _ _) (@epsilon ((prod num (prod num (prod num (prod num num)))) -> A -> (list (prod A B)) -> B) _ (fun ASSOC' : (prod num (prod num (prod num (prod num num)))) -> A -> (list (prod A B)) -> B => ∀ _18192 : prod num (prod num (prod num (prod num num))), ∀ h : prod A B, ∀ a : A, ∀ t : list (prod A B), hol_eq (ASSOC' _18192 a (@CONS (prod A B) _ h t)) (@COND B _ (hol_eq (@FST A B _ _ h) a) (@SND A B _ _ h) (ASSOC' _18192 a t))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))))))))
  ITLIST2 {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C
  ITLIST2_def {A B C : Type} [Nonempty A] [Nonempty B] [Nonempty C] : hol_eq (@ITLIST2 A B C _ _ _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C) _ (fun ITLIST2' : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (A -> B -> C -> C) -> (list A) -> (list B) -> C -> C => ∀ _18201 : prod num (prod num (prod num (prod num (prod num (prod num num))))), hand (∀ f : A -> B -> C -> C, ∀ l2 : list B, ∀ b : C, hol_eq (ITLIST2' _18201 f (@NIL A _) l2 b) b) (∀ h1' : A, ∀ f : A -> B -> C -> C, ∀ t1 : list A, ∀ l2 : list B, ∀ b : C, hol_eq (ITLIST2' _18201 f (@CONS A _ h1' t1) l2 b) (f h1' (@HD B _ l2) (ITLIST2' _18201 f t1 (@TL B _ l2) b)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0))))))))))))))
  ZIP {A B : Type} [Nonempty A] [Nonempty B] : (list A) -> (list B) -> list (prod A B)
  ZIP_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ZIP A B _ _) (@epsilon ((prod num (prod num num)) -> (list A) -> (list B) -> list (prod A B)) _ (fun ZIP' : (prod num (prod num num)) -> (list A) -> (list B) -> list (prod A B) => ∀ _18205 : prod num (prod num num), hand (∀ l2 : list B, hol_eq (ZIP' _18205 (@NIL A _) l2) (@NIL (prod A B) _)) (∀ h1' : A, ∀ t1 : list A, ∀ l2 : list B, hol_eq (ZIP' _18205 (@CONS A _ h1' t1) l2) (@CONS (prod A B) _ (@Prod_mk A B _ _ h1' (@HD B _ l2)) (ZIP' _18205 t1 (@TL B _ l2))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))))))
  ALLPAIRS {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> Prop) -> (list A) -> (list B) -> Prop
  ALLPAIRS_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ALLPAIRS A B _ _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop) _ (fun ALLPAIRS' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> B -> Prop) -> (list A) -> (list B) -> Prop => ∀ _18213 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), hand (∀ f : A -> B -> Prop, ∀ l : list B, hol_eq (ALLPAIRS' _18213 f (@NIL A _) l) htrue) (∀ h : A, ∀ f : A -> B -> Prop, ∀ t : list A, ∀ l : list B, hol_eq (ALLPAIRS' _18213 f (@CONS A _ h t) l) (hand (@ALL B _ (f h) l) (ALLPAIRS' _18213 f t l)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0))))))))))))))))
  PAIRWISE {A : Type} [Nonempty A] : (A -> A -> Prop) -> (list A) -> Prop
  PAIRWISE_def {A : Type} [Nonempty A] : hol_eq (@PAIRWISE A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> A -> Prop) -> (list A) -> Prop) _ (fun PAIRWISE' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (A -> A -> Prop) -> (list A) -> Prop => ∀ _18220 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), hand (∀ r : A -> A -> Prop, hol_eq (PAIRWISE' _18220 r (@NIL A _)) htrue) (∀ h : A, ∀ r : A -> A -> Prop, ∀ t : list A, hol_eq (PAIRWISE' _18220 r (@CONS A _ h t)) (hand (@ALL A _ (r h) t) (PAIRWISE' _18220 r t)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))))
  list_of_seq {A : Type} [Nonempty A] : (num -> A) -> num -> list A
  list_of_seq_def {A : Type} [Nonempty A] : hol_eq (@list_of_seq A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))))) -> (num -> A) -> num -> list A) _ (fun list_of_seq' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))))) -> (num -> A) -> num -> list A => ∀ _18227 : prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))))), hand (∀ s : num -> A, hol_eq (list_of_seq' _18227 s (NUMERAL _0)) (@NIL A _)) (∀ s : num -> A, ∀ n : num, hol_eq (list_of_seq' _18227 s (SUC n)) (@APPEND A _ (list_of_seq' _18227 s n) (@CONS A _ (s n) (@NIL A _))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))))))))))))))
  _mk_char : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> char
  _dest_char : char -> recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))
  _22943 : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> char
  _22943_def : hol_eq _22943 (fun a0 : Prop => fun a1 : Prop => fun a2 : Prop => fun a3 : Prop => fun a4 : Prop => fun a5 : Prop => fun a6 : Prop => fun a7 : Prop => _mk_char ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _ (NUMERAL _0) (@Prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) _ _ a0' (@Prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) _ _ a1' (@Prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) _ _ a2' (@Prod_mk Prop (prod Prop (prod Prop (prod Prop Prop))) _ _ a3' (@Prod_mk Prop (prod Prop (prod Prop Prop)) _ _ a4' (@Prod_mk Prop (prod Prop Prop) _ _ a5' (@Prod_mk Prop Prop _ _ a6' a7'))))))) (fun n : num => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _)) a0 a1 a2 a3 a4 a5 a6 a7))
  ASCII : Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> Prop -> char
  ASCII_def : hol_eq ASCII _22943
  dist : (prod num num) -> num
  dist_def : hol_eq dist (fun _23033 : prod num num => Nat_add (Nat_minus (@FST num num _ _ _23033) (@SND num num _ _ _23033)) (Nat_minus (@SND num num _ _ _23033) (@FST num num _ _ _23033)))
  is_nadd : (num -> num) -> Prop
  is_nadd_def : hol_eq is_nadd (fun _23343 : num -> num => ∃ B : num, ∀ m : num, ∀ n : num, Nat_le (dist (@Prod_mk num num _ _ (Nat_mul m (_23343 n)) (Nat_mul n (_23343 m)))) (Nat_mul B (Nat_add m n)))
  mk_nadd : (num -> num) -> nadd
  dest_nadd : nadd -> num -> num
  nadd_eq : nadd -> nadd -> Prop
  nadd_eq_def : hol_eq nadd_eq (fun _23362 : nadd => fun _23363 : nadd => ∃ B : num, ∀ n : num, Nat_le (dist (@Prod_mk num num _ _ (dest_nadd _23362 n) (dest_nadd _23363 n))) B)
  nadd_of_num : num -> nadd
  nadd_of_num_def : hol_eq nadd_of_num (fun _23374 : num => mk_nadd (fun n : num => Nat_mul _23374 n))
  nadd_le : nadd -> nadd -> Prop
  nadd_le_def : hol_eq nadd_le (fun _23381 : nadd => fun _23382 : nadd => ∃ B : num, ∀ n : num, Nat_le (dest_nadd _23381 n) (Nat_add (dest_nadd _23382 n) B))
  nadd_add : nadd -> nadd -> nadd
  nadd_add_def : hol_eq nadd_add (fun _23397 : nadd => fun _23398 : nadd => mk_nadd (fun n : num => Nat_add (dest_nadd _23397 n) (dest_nadd _23398 n)))
  nadd_mul : nadd -> nadd -> nadd
  nadd_mul_def : hol_eq nadd_mul (fun _23411 : nadd => fun _23412 : nadd => mk_nadd (fun n : num => dest_nadd _23411 (dest_nadd _23412 n)))
  nadd_rinv : nadd -> num -> num
  nadd_rinv_def : hol_eq nadd_rinv (fun _23548 : nadd => fun n : num => DIV (Nat_mul n n) (dest_nadd _23548 n))
  nadd_inv : nadd -> nadd
  nadd_inv_def : hol_eq nadd_inv (fun _23562 : nadd => @COND nadd _ (nadd_eq _23562 (nadd_of_num (NUMERAL _0))) (nadd_of_num (NUMERAL _0)) (mk_nadd (nadd_rinv _23562)))
  mk_hreal : (nadd -> Prop) -> hreal
  dest_hreal : hreal -> nadd -> Prop
  hreal_of_num : num -> hreal
  hreal_of_num_def : hol_eq hreal_of_num (fun m : num => mk_hreal (fun u : nadd => nadd_eq (nadd_of_num m) u))
  hreal_add : hreal -> hreal -> hreal
  hreal_add_def : hol_eq hreal_add (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, ∃ y' : nadd, hand (nadd_eq (nadd_add x' y') u) (hand (dest_hreal x x') (dest_hreal y y'))))
  hreal_mul : hreal -> hreal -> hreal
  hreal_mul_def : hol_eq hreal_mul (fun x : hreal => fun y : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, ∃ y' : nadd, hand (nadd_eq (nadd_mul x' y') u) (hand (dest_hreal x x') (dest_hreal y y'))))
  hreal_le : hreal -> hreal -> Prop
  hreal_le_def : hol_eq hreal_le (fun x : hreal => fun y : hreal => @epsilon Prop _ (fun u : Prop => ∃ x' : nadd, ∃ y' : nadd, hand (hol_eq (nadd_le x' y') u) (hand (dest_hreal x x') (dest_hreal y y'))))
  hreal_inv : hreal -> hreal
  hreal_inv_def : hol_eq hreal_inv (fun x : hreal => mk_hreal (fun u : nadd => ∃ x' : nadd, hand (nadd_eq (nadd_inv x') u) (dest_hreal x x')))
  treal_of_num : num -> prod hreal hreal
  treal_of_num_def : hol_eq treal_of_num (fun _23807 : num => @Prod_mk hreal hreal _ _ (hreal_of_num _23807) (hreal_of_num (NUMERAL _0)))
  treal_neg : (prod hreal hreal) -> prod hreal hreal
  treal_neg_def : hol_eq treal_neg (fun _23812 : prod hreal hreal => @Prod_mk hreal hreal _ _ (@SND hreal hreal _ _ _23812) (@FST hreal hreal _ _ _23812))
  treal_add : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal
  treal_add_def : hol_eq treal_add (fun _23821 : prod hreal hreal => fun _23822 : prod hreal hreal => @Prod_mk hreal hreal _ _ (hreal_add (@FST hreal hreal _ _ _23821) (@FST hreal hreal _ _ _23822)) (hreal_add (@SND hreal hreal _ _ _23821) (@SND hreal hreal _ _ _23822)))
  treal_mul : (prod hreal hreal) -> (prod hreal hreal) -> prod hreal hreal
  treal_mul_def : hol_eq treal_mul (fun _23843 : prod hreal hreal => fun _23844 : prod hreal hreal => @Prod_mk hreal hreal _ _ (hreal_add (hreal_mul (@FST hreal hreal _ _ _23843) (@FST hreal hreal _ _ _23844)) (hreal_mul (@SND hreal hreal _ _ _23843) (@SND hreal hreal _ _ _23844))) (hreal_add (hreal_mul (@FST hreal hreal _ _ _23843) (@SND hreal hreal _ _ _23844)) (hreal_mul (@SND hreal hreal _ _ _23843) (@FST hreal hreal _ _ _23844))))
  treal_le : (prod hreal hreal) -> (prod hreal hreal) -> Prop
  treal_le_def : hol_eq treal_le (fun _23865 : prod hreal hreal => fun _23866 : prod hreal hreal => hreal_le (hreal_add (@FST hreal hreal _ _ _23865) (@SND hreal hreal _ _ _23866)) (hreal_add (@FST hreal hreal _ _ _23866) (@SND hreal hreal _ _ _23865)))
  treal_inv : (prod hreal hreal) -> prod hreal hreal
  treal_inv_def : hol_eq treal_inv (fun _23887 : prod hreal hreal => @COND (prod hreal hreal) _ (hol_eq (@FST hreal hreal _ _ _23887) (@SND hreal hreal _ _ _23887)) (@Prod_mk hreal hreal _ _ (hreal_of_num (NUMERAL _0)) (hreal_of_num (NUMERAL _0))) (@COND (prod hreal hreal) _ (hreal_le (@SND hreal hreal _ _ _23887) (@FST hreal hreal _ _ _23887)) (@Prod_mk hreal hreal _ _ (hreal_inv (@epsilon hreal _ (fun d : hreal => hol_eq (@FST hreal hreal _ _ _23887) (hreal_add (@SND hreal hreal _ _ _23887) d)))) (hreal_of_num (NUMERAL _0))) (@Prod_mk hreal hreal _ _ (hreal_of_num (NUMERAL _0)) (hreal_inv (@epsilon hreal _ (fun d : hreal => hol_eq (@SND hreal hreal _ _ _23887) (hreal_add (@FST hreal hreal _ _ _23887) d)))))))
  treal_eq : (prod hreal hreal) -> (prod hreal hreal) -> Prop
  treal_eq_def : hol_eq treal_eq (fun _23896 : prod hreal hreal => fun _23897 : prod hreal hreal => hol_eq (hreal_add (@FST hreal hreal _ _ _23896) (@SND hreal hreal _ _ _23897)) (hreal_add (@FST hreal hreal _ _ _23897) (@SND hreal hreal _ _ _23896)))
  mk_real : ((prod hreal hreal) -> Prop) -> Real
  dest_real : Real -> (prod hreal hreal) -> Prop
  real_of_num : num -> Real
  real_of_num_def : hol_eq real_of_num (fun m : num => mk_real (fun u : prod hreal hreal => treal_eq (treal_of_num m) u))
  real_neg : Real -> Real
  real_neg_def : hol_eq real_neg (fun x1 : Real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, hand (treal_eq (treal_neg x1') u) (dest_real x1 x1')))
  real_add : Real -> Real -> Real
  real_add_def : hol_eq real_add (fun x1 : Real => fun y1 : Real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, hand (treal_eq (treal_add x1' y1') u) (hand (dest_real x1 x1') (dest_real y1 y1'))))
  real_mul : Real -> Real -> Real
  real_mul_def : hol_eq real_mul (fun x1 : Real => fun y1 : Real => mk_real (fun u : prod hreal hreal => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, hand (treal_eq (treal_mul x1' y1') u) (hand (dest_real x1 x1') (dest_real y1 y1'))))
  real_le : Real -> Real -> Prop
  real_le_def : hol_eq real_le (fun x1 : Real => fun y1 : Real => @epsilon Prop _ (fun u : Prop => ∃ x1' : prod hreal hreal, ∃ y1' : prod hreal hreal, hand (hol_eq (treal_le x1' y1') u) (hand (dest_real x1 x1') (dest_real y1 y1'))))
  real_inv : Real -> Real
  real_inv_def : hol_eq real_inv (fun x : Real => mk_real (fun u : prod hreal hreal => ∃ x' : prod hreal hreal, hand (treal_eq (treal_inv x') u) (dest_real x x')))
  real_sub : Real -> Real -> Real
  real_sub_def : hol_eq real_sub (fun _24112 : Real => fun _24113 : Real => real_add _24112 (real_neg _24113))
  real_lt : Real -> Real -> Prop
  real_lt_def : hol_eq real_lt (fun _24124 : Real => fun _24125 : Real => not (real_le _24125 _24124))
  real_ge : Real -> Real -> Prop
  real_ge_def : hol_eq real_ge (fun _24136 : Real => fun _24137 : Real => real_le _24137 _24136)
  real_gt : Real -> Real -> Prop
  real_gt_def : hol_eq real_gt (fun _24148 : Real => fun _24149 : Real => real_lt _24149 _24148)
  real_abs : Real -> Real
  real_abs_def : hol_eq real_abs (fun _24160 : Real => @COND Real _ (real_le (real_of_num (NUMERAL _0)) _24160) _24160 (real_neg _24160))
  real_pow : Real -> num -> Real
  real_pow_def : hol_eq real_pow (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> Real -> num -> Real) _ (fun real_pow' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> Real -> num -> Real => ∀ _24171 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), hand (∀ x : Real, hol_eq (real_pow' _24171 x (NUMERAL _0)) (real_of_num (NUMERAL (BIT1 _0)))) (∀ x : Real, ∀ n : num, hol_eq (real_pow' _24171 x (SUC n)) (real_mul x (real_pow' _24171 x n)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0))))))))))))))))
  real_div : Real -> Real -> Real
  real_div_def : hol_eq real_div (fun _24172 : Real => fun _24173 : Real => real_mul _24172 (real_inv _24173))
  real_max : Real -> Real -> Real
  real_max_def : hol_eq real_max (fun _24184 : Real => fun _24185 : Real => @COND Real _ (real_le _24184 _24185) _24185 _24184)
  real_min : Real -> Real -> Real
  real_min_def : hol_eq real_min (fun _24196 : Real => fun _24197 : Real => @COND Real _ (real_le _24196 _24197) _24196 _24197)
  real_sgn : Real -> Real
  real_sgn_def : hol_eq real_sgn (fun _26684 : Real => @COND Real _ (real_lt (real_of_num (NUMERAL _0)) _26684) (real_of_num (NUMERAL (BIT1 _0))) (@COND Real _ (real_lt _26684 (real_of_num (NUMERAL _0))) (real_neg (real_of_num (NUMERAL (BIT1 _0)))) (real_of_num (NUMERAL _0))))
  SQRT : Real -> Real
  SQRT_def : hol_eq SQRT (fun _27235 : Real => @epsilon Real _ (fun y : Real => hand (hol_eq (real_sgn y) (real_sgn _27235)) (hol_eq (real_pow y (NUMERAL (BIT0 (BIT1 _0)))) (real_abs _27235))))
  DECIMAL : num -> num -> Real
  DECIMAL_def : hol_eq DECIMAL (fun _27914 : num => fun _27915 : num => real_div (real_of_num _27914) (real_of_num _27915))
  integer : Real -> Prop
  integer_def : hol_eq integer (fun _28801 : Real => ∃ n : num, hol_eq (real_abs _28801) (real_of_num n))
  int_of_real : Real -> int
  real_of_int : int -> Real
  int_le : int -> int -> Prop
  int_le_def : hol_eq int_le (fun _28827 : int => fun _28828 : int => real_le (real_of_int _28827) (real_of_int _28828))
  int_lt : int -> int -> Prop
  int_lt_def : hol_eq int_lt (fun _28839 : int => fun _28840 : int => real_lt (real_of_int _28839) (real_of_int _28840))
  int_ge : int -> int -> Prop
  int_ge_def : hol_eq int_ge (fun _28851 : int => fun _28852 : int => real_ge (real_of_int _28851) (real_of_int _28852))
  int_gt : int -> int -> Prop
  int_gt_def : hol_eq int_gt (fun _28863 : int => fun _28864 : int => real_gt (real_of_int _28863) (real_of_int _28864))
  int_of_num : num -> int
  int_of_num_def : hol_eq int_of_num (fun _28875 : num => int_of_real (real_of_num _28875))
  int_neg : int -> int
  int_neg_def : hol_eq int_neg (fun _28880 : int => int_of_real (real_neg (real_of_int _28880)))
  int_add : int -> int -> int
  int_add_def : hol_eq int_add (fun _28889 : int => fun _28890 : int => int_of_real (real_add (real_of_int _28889) (real_of_int _28890)))
  int_sub : int -> int -> int
  int_sub_def : hol_eq int_sub (fun _28921 : int => fun _28922 : int => int_of_real (real_sub (real_of_int _28921) (real_of_int _28922)))
  int_mul : int -> int -> int
  int_mul_def : hol_eq int_mul (fun _28933 : int => fun _28934 : int => int_of_real (real_mul (real_of_int _28933) (real_of_int _28934)))
  int_abs : int -> int
  int_abs_def : hol_eq int_abs (fun _28953 : int => int_of_real (real_abs (real_of_int _28953)))
  int_sgn : int -> int
  int_sgn_def : hol_eq int_sgn (fun _28964 : int => int_of_real (real_sgn (real_of_int _28964)))
  int_max : int -> int -> int
  int_max_def : hol_eq int_max (fun _29024 : int => fun _29025 : int => int_of_real (real_max (real_of_int _29024) (real_of_int _29025)))
  int_min : int -> int -> int
  int_min_def : hol_eq int_min (fun _29042 : int => fun _29043 : int => int_of_real (real_min (real_of_int _29042) (real_of_int _29043)))
  int_pow : int -> num -> int
  int_pow_def : hol_eq int_pow (fun _29060 : int => fun _29061 : num => int_of_real (real_pow (real_of_int _29060) _29061))
  div : int -> int -> int
  div_def : hol_eq div (@epsilon ((prod num (prod num num)) -> int -> int -> int) _ (fun q : (prod num (prod num num)) -> int -> int -> int => ∀ _29412 : prod num (prod num num), ∃ r : int -> int -> int, ∀ m : int, ∀ n : int, @COND Prop _ (hol_eq n (int_of_num (NUMERAL _0))) (hand (hol_eq (q _29412 m n) (int_of_num (NUMERAL _0))) (hol_eq (r m n) m)) (hand (int_le (int_of_num (NUMERAL _0)) (r m n)) (hand (int_lt (r m n) (int_abs n)) (hol_eq m (int_add (int_mul (q _29412 m n) n) (r m n)))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))))))
  rem : int -> int -> int
  rem_def : hol_eq rem (@epsilon ((prod num (prod num num)) -> int -> int -> int) _ (fun r : (prod num (prod num num)) -> int -> int -> int => ∀ _29413 : prod num (prod num num), ∀ m : int, ∀ n : int, @COND Prop _ (hol_eq n (int_of_num (NUMERAL _0))) (hand (hol_eq (div m n) (int_of_num (NUMERAL _0))) (hol_eq (r _29413 m n) m)) (hand (int_le (int_of_num (NUMERAL _0)) (r _29413 m n)) (hand (int_lt (r _29413 m n) (int_abs n)) (hol_eq m (int_add (int_mul (div m n) n) (r _29413 m n)))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))))))
  eq2 {A : Type} [Nonempty A] : A -> A -> (A -> A -> Prop) -> Prop
  eq2_def {A : Type} [Nonempty A] : hol_eq (@eq2 A _) (fun _29688 : A => fun _29689 : A => fun _29690 : A -> A -> Prop => _29690 _29688 _29689)
  real_mod : Real -> Real -> Real -> Prop
  real_mod_def : hol_eq real_mod (fun _29709 : Real => fun _29710 : Real => fun _29711 : Real => ∃ q : Real, hand (integer q) (hol_eq (real_sub _29710 _29711) (real_mul q _29709)))
  int_divides : int -> int -> Prop
  int_divides_def : hol_eq int_divides (fun _29730 : int => fun _29731 : int => ∃ x : int, hol_eq _29731 (int_mul _29730 x))
  int_mod : int -> int -> int -> Prop
  int_mod_def : hol_eq int_mod (fun _29750 : int => fun _29751 : int => fun _29752 : int => int_divides _29750 (int_sub _29751 _29752))
  int_coprime : (prod int int) -> Prop
  int_coprime_def : hol_eq int_coprime (fun _29777 : prod int int => ∃ x : int, ∃ y : int, hol_eq (int_add (int_mul (@FST int int _ _ _29777) x) (int_mul (@SND int int _ _ _29777) y)) (int_of_num (NUMERAL (BIT1 _0))))
  int_gcd : (prod int int) -> int
  int_gcd_def : hol_eq int_gcd (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (prod int int) -> int) _ (fun d : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (prod int int) -> int => ∀ _31046 : prod num (prod num (prod num (prod num (prod num (prod num num))))), ∀ a : int, ∀ b : int, hand (int_le (int_of_num (NUMERAL _0)) (d _31046 (@Prod_mk int int _ _ a b))) (hand (int_divides (d _31046 (@Prod_mk int int _ _ a b)) a) (hand (int_divides (d _31046 (@Prod_mk int int _ _ a b)) b) (∃ x : int, ∃ y : int, hol_eq (d _31046 (@Prod_mk int int _ _ a b)) (int_add (int_mul a x) (int_mul b y)))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))))))))))
  int_lcm : (prod int int) -> int
  int_lcm_def : hol_eq int_lcm (fun _31047 : prod int int => @COND int _ (hol_eq (int_mul (@FST int int _ _ _31047) (@SND int int _ _ _31047)) (int_of_num (NUMERAL _0))) (int_of_num (NUMERAL _0)) (div (int_abs (int_mul (@FST int int _ _ _31047) (@SND int int _ _ _31047))) (int_gcd (@Prod_mk int int _ _ (@FST int int _ _ _31047) (@SND int int _ _ _31047)))))
  num_of_int : int -> num
  num_of_int_def : hol_eq num_of_int (fun _31320 : int => @epsilon num _ (fun n : num => hol_eq (int_of_num n) _31320))
  num_divides : num -> num -> Prop
  num_divides_def : hol_eq num_divides (fun _31352 : num => fun _31353 : num => int_divides (int_of_num _31352) (int_of_num _31353))
  num_mod : num -> num -> num -> Prop
  num_mod_def : hol_eq num_mod (fun _31364 : num => fun _31365 : num => fun _31366 : num => int_mod (int_of_num _31364) (int_of_num _31365) (int_of_num _31366))
  num_coprime : (prod num num) -> Prop
  num_coprime_def : hol_eq num_coprime (fun _31385 : prod num num => int_coprime (@Prod_mk int int _ _ (int_of_num (@FST num num _ _ _31385)) (int_of_num (@SND num num _ _ _31385))))
  num_gcd : (prod num num) -> num
  num_gcd_def : hol_eq num_gcd (fun _31394 : prod num num => num_of_int (int_gcd (@Prod_mk int int _ _ (int_of_num (@FST num num _ _ _31394)) (int_of_num (@SND num num _ _ _31394)))))
  num_lcm : (prod num num) -> num
  num_lcm_def : hol_eq num_lcm (fun _31403 : prod num num => num_of_int (int_lcm (@Prod_mk int int _ _ (int_of_num (@FST num num _ _ _31403)) (int_of_num (@SND num num _ _ _31403)))))
  prime : num -> Prop
  prime_def : hol_eq prime (fun _32188 : num => hand (not (hol_eq _32188 (NUMERAL (BIT1 _0)))) (∀ x : num, (num_divides x _32188) -> hor (hol_eq x (NUMERAL (BIT1 _0))) (hol_eq x _32188)))
  real_zpow : Real -> int -> Real
  real_zpow_def : hol_eq real_zpow (fun _32346 : Real => fun _32347 : int => @COND Real _ (int_le (int_of_num (NUMERAL _0)) _32347) (real_pow _32346 (num_of_int _32347)) (real_inv (real_pow _32346 (num_of_int (int_neg _32347)))))
  IN {A : Type} [Nonempty A] : A -> (A -> Prop) -> Prop
  IN_def {A : Type} [Nonempty A] : hol_eq (@IN A _) (fun _32403 : A => fun _32404 : A -> Prop => _32404 _32403)
  GSPEC {A : Type} [Nonempty A] : (A -> Prop) -> A -> Prop
  GSPEC_def {A : Type} [Nonempty A] : hol_eq (@GSPEC A _) (fun _32415 : A -> Prop => _32415)
  SETSPEC {A : Type} [Nonempty A] : A -> Prop -> A -> Prop
  SETSPEC_def {A : Type} [Nonempty A] : hol_eq (@SETSPEC A _) (fun _32420 : A => fun _32421 : Prop => fun _32422 : A => hand _32421 (hol_eq _32420 _32422))
  EMPTY {A : Type} [Nonempty A] : A -> Prop
  EMPTY_def {A : Type} [Nonempty A] : hol_eq (@EMPTY A _) (fun x : A => hfalse)
  INSERT {A : Type} [Nonempty A] : A -> (A -> Prop) -> A -> Prop
  INSERT_def {A : Type} [Nonempty A] : hol_eq (@INSERT A _) (fun _32459 : A => fun _32460 : A -> Prop => fun y : A => hor (@IN A _ y _32460) (hol_eq y _32459))
  UNIV {A : Type} [Nonempty A] : A -> Prop
  UNIV_def {A : Type} [Nonempty A] : hol_eq (@UNIV A _) (fun x : A => htrue)
  UNION {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop
  UNION_def {A : Type} [Nonempty A] : hol_eq (@UNION A _) (fun _32471 : A -> Prop => fun _32472 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_0 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_0 (hor (@IN A _ x _32471) (@IN A _ x _32472)) x))
  UNIONS {A : Type} [Nonempty A] : ((A -> Prop) -> Prop) -> A -> Prop
  UNIONS_def {A : Type} [Nonempty A] : hol_eq (@UNIONS A _) (fun _32483 : (A -> Prop) -> Prop => @GSPEC A _ (fun GEN_PVAR_1 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_1 (∃ u : A -> Prop, hand (@IN (A -> Prop) _ u _32483) (@IN A _ x u)) x))
  INTER {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop
  INTER_def {A : Type} [Nonempty A] : hol_eq (@INTER A _) (fun _32488 : A -> Prop => fun _32489 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_2 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_2 (hand (@IN A _ x _32488) (@IN A _ x _32489)) x))
  INTERS {A : Type} [Nonempty A] : ((A -> Prop) -> Prop) -> A -> Prop
  INTERS_def {A : Type} [Nonempty A] : hol_eq (@INTERS A _) (fun _32500 : (A -> Prop) -> Prop => @GSPEC A _ (fun GEN_PVAR_3 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_3 (∀ u : A -> Prop, (@IN (A -> Prop) _ u _32500) -> @IN A _ x u) x))
  DIFF {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> A -> Prop
  DIFF_def {A : Type} [Nonempty A] : hol_eq (@DIFF A _) (fun _32505 : A -> Prop => fun _32506 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_4 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_4 (hand (@IN A _ x _32505) (not (@IN A _ x _32506))) x))
  DELETE {A : Type} [Nonempty A] : (A -> Prop) -> A -> A -> Prop
  DELETE_def {A : Type} [Nonempty A] : hol_eq (@DELETE A _) (fun _32517 : A -> Prop => fun _32518 : A => @GSPEC A _ (fun GEN_PVAR_6 : A => ∃ y : A, @SETSPEC A _ GEN_PVAR_6 (hand (@IN A _ y _32517) (not (hol_eq y _32518))) y))
  SUBSET {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop
  SUBSET_def {A : Type} [Nonempty A] : hol_eq (@SUBSET A _) (fun _32529 : A -> Prop => fun _32530 : A -> Prop => ∀ x : A, (@IN A _ x _32529) -> @IN A _ x _32530)
  PSUBSET {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop
  PSUBSET_def {A : Type} [Nonempty A] : hol_eq (@PSUBSET A _) (fun _32541 : A -> Prop => fun _32542 : A -> Prop => hand (@SUBSET A _ _32541 _32542) (not (hol_eq _32541 _32542)))
  DISJOINT {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Prop) -> Prop
  DISJOINT_def {A : Type} [Nonempty A] : hol_eq (@DISJOINT A _) (fun _32553 : A -> Prop => fun _32554 : A -> Prop => hol_eq (@INTER A _ _32553 _32554) (@EMPTY A _))
  SING {A : Type} [Nonempty A] : (A -> Prop) -> Prop
  SING_def {A : Type} [Nonempty A] : hol_eq (@SING A _) (fun _32565 : A -> Prop => ∃ x : A, hol_eq _32565 (@INSERT A _ x (@EMPTY A _)))
  FINITE {A : Type} [Nonempty A] : (A -> Prop) -> Prop
  FINITE_def {A : Type} [Nonempty A] : hol_eq (@FINITE A _) (fun a : A -> Prop => ∀ FINITE' : (A -> Prop) -> Prop, (∀ a' : A -> Prop, (hor (hol_eq a' (@EMPTY A _)) (∃ x : A, ∃ s : A -> Prop, hand (hol_eq a' (@INSERT A _ x s)) (FINITE' s))) -> FINITE' a') -> FINITE' a)
  INFINITE {A : Type} [Nonempty A] : (A -> Prop) -> Prop
  INFINITE_def {A : Type} [Nonempty A] : hol_eq (@INFINITE A _) (fun _32574 : A -> Prop => not (@FINITE A _ _32574))
  IMAGE {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> B -> Prop
  IMAGE_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@IMAGE A B _ _) (fun _32579 : A -> B => fun _32580 : A -> Prop => @GSPEC B _ (fun GEN_PVAR_7 : B => ∃ y : B, @SETSPEC B _ GEN_PVAR_7 (∃ x : A, hand (@IN A _ x _32580) (hol_eq y (_32579 x))) y))
  INJ {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop
  INJ_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@INJ A B _ _) (fun _32591 : A -> B => fun _32592 : A -> Prop => fun _32593 : B -> Prop => hand (∀ x : A, (@IN A _ x _32592) -> @IN B _ (_32591 x) _32593) (∀ x : A, ∀ y : A, (hand (@IN A _ x _32592) (hand (@IN A _ y _32592) (hol_eq (_32591 x) (_32591 y)))) -> hol_eq x y))
  SURJ {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop
  SURJ_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@SURJ A B _ _) (fun _32612 : A -> B => fun _32613 : A -> Prop => fun _32614 : B -> Prop => hand (∀ x : A, (@IN A _ x _32613) -> @IN B _ (_32612 x) _32614) (∀ x : B, (@IN B _ x _32614) -> ∃ y : A, hand (@IN A _ y _32613) (hol_eq (_32612 y) x)))
  BIJ {A B : Type} [Nonempty A] [Nonempty B] : (A -> B) -> (A -> Prop) -> (B -> Prop) -> Prop
  BIJ_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@BIJ A B _ _) (fun _32633 : A -> B => fun _32634 : A -> Prop => fun _32635 : B -> Prop => hand (@INJ A B _ _ _32633 _32634 _32635) (@SURJ A B _ _ _32633 _32634 _32635))
  CHOICE {A : Type} [Nonempty A] : (A -> Prop) -> A
  CHOICE_def {A : Type} [Nonempty A] : hol_eq (@CHOICE A _) (fun _32654 : A -> Prop => @epsilon A _ (fun x : A => @IN A _ x _32654))
  REST {A : Type} [Nonempty A] : (A -> Prop) -> A -> Prop
  REST_def {A : Type} [Nonempty A] : hol_eq (@REST A _) (fun _32659 : A -> Prop => @DELETE A _ _32659 (@CHOICE A _ _32659))
  FINREC {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> B) -> B -> (A -> Prop) -> B -> num -> Prop
  FINREC_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@FINREC A B _ _) (@epsilon ((prod num (prod num (prod num (prod num (prod num num))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> num -> Prop) _ (fun FINREC' : (prod num (prod num (prod num (prod num (prod num num))))) -> (A -> B -> B) -> B -> (A -> Prop) -> B -> num -> Prop => ∀ _42261 : prod num (prod num (prod num (prod num (prod num num)))), hand (∀ f : A -> B -> B, ∀ s : A -> Prop, ∀ a : B, ∀ b : B, hol_eq (FINREC' _42261 f b s a (NUMERAL _0)) (hand (hol_eq s (@EMPTY A _)) (hol_eq a b))) (∀ b : B, ∀ s : A -> Prop, ∀ n : num, ∀ a : B, ∀ f : A -> B -> B, hol_eq (FINREC' _42261 f b s a (SUC n)) (∃ x : A, ∃ c : B, hand (@IN A _ x s) (hand (FINREC' _42261 f b (@DELETE A _ s x) c n) (hol_eq a (f x c)))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))
  ITSET {A B : Type} [Nonempty A] [Nonempty B] : (A -> B -> B) -> (A -> Prop) -> B -> B
  ITSET_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ITSET A B _ _) (fun _43111 : A -> B -> B => fun _43112 : A -> Prop => fun _43113 : B => @epsilon ((A -> Prop) -> B) _ (fun g : (A -> Prop) -> B => hand (hol_eq (g (@EMPTY A _)) _43113) (∀ x : A, ∀ s : A -> Prop, (@FINITE A _ s) -> hol_eq (g (@INSERT A _ x s)) (@COND B _ (@IN A _ x s) (g s) (_43111 x (g s))))) _43112)
  CARD {A : Type} [Nonempty A] : (A -> Prop) -> num
  CARD_def {A : Type} [Nonempty A] : hol_eq (@CARD A _) (fun _43314 : A -> Prop => @ITSET A num _ _ (fun x : A => fun n : num => SUC n) _43314 (NUMERAL _0))
  HAS_SIZE {A : Type} [Nonempty A] : (A -> Prop) -> num -> Prop
  HAS_SIZE_def {A : Type} [Nonempty A] : hol_eq (@HAS_SIZE A _) (fun _43489 : A -> Prop => fun _43490 : num => hand (@FINITE A _ _43489) (hol_eq (@CARD A _ _43489) _43490))
  CROSS {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> (prod A B) -> Prop
  CROSS_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@CROSS A B _ _) (fun _47408 : A -> Prop => fun _47409 : B -> Prop => @GSPEC (prod A B) _ (fun GEN_PVAR_132 : prod A B => ∃ x : A, ∃ y : B, @SETSPEC (prod A B) _ GEN_PVAR_132 (hand (@IN A _ x _47408) (@IN B _ y _47409)) (@Prod_mk A B _ _ x y)))
  ARB {A : Type} [Nonempty A] : A
  ARB_def {A : Type} [Nonempty A] : hol_eq (@ARB A _) (@epsilon A _ (fun x : A => hfalse))
  EXTENSIONAL {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (A -> B) -> Prop
  EXTENSIONAL_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@EXTENSIONAL A B _ _) (fun _48182 : A -> Prop => @GSPEC (A -> B) _ (fun GEN_PVAR_141 : A -> B => ∃ f : A -> B, @SETSPEC (A -> B) _ GEN_PVAR_141 (∀ x : A, (not (@IN A _ x _48182)) -> hol_eq (f x) (@ARB B _)) f))
  RESTRICTION {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (A -> B) -> A -> B
  RESTRICTION_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@RESTRICTION A B _ _) (fun _48234 : A -> Prop => fun _48235 : A -> B => fun _48236 : A => @COND B _ (@IN A _ _48236 _48234) (_48235 _48236) (@ARB B _))
  cartesian_product {A K : Type} [Nonempty A] [Nonempty K] : (K -> Prop) -> (K -> A -> Prop) -> (K -> A) -> Prop
  cartesian_product_def {A K : Type} [Nonempty A] [Nonempty K] : hol_eq (@cartesian_product A K _ _) (fun _48429 : K -> Prop => fun _48430 : K -> A -> Prop => @GSPEC (K -> A) _ (fun GEN_PVAR_142 : K -> A => ∃ f : K -> A, @SETSPEC (K -> A) _ GEN_PVAR_142 (hand (@EXTENSIONAL K A _ _ _48429 f) (∀ i : K, (@IN K _ i _48429) -> @IN A _ (f i) (_48430 i))) f))
  product_map {A B K : Type} [Nonempty A] [Nonempty B] [Nonempty K] : (K -> Prop) -> (K -> A -> B) -> (K -> A) -> K -> B
  product_map_def {A B K : Type} [Nonempty A] [Nonempty B] [Nonempty K] : hol_eq (@product_map A B K _ _ _) (fun _49478 : K -> Prop => fun _49479 : K -> A -> B => fun x : K -> A => @RESTRICTION K B _ _ _49478 (fun i : K => _49479 i (x i)))
  disjoint_union {A K : Type} [Nonempty A] [Nonempty K] : (K -> Prop) -> (K -> A -> Prop) -> (prod K A) -> Prop
  disjoint_union_def {A K : Type} [Nonempty A] [Nonempty K] : hol_eq (@disjoint_union A K _ _) (fun _49614 : K -> Prop => fun _49615 : K -> A -> Prop => @GSPEC (prod K A) _ (fun GEN_PVAR_145 : prod K A => ∃ i : K, ∃ x : A, @SETSPEC (prod K A) _ GEN_PVAR_145 (hand (@IN K _ i _49614) (@IN A _ x (_49615 i))) (@Prod_mk K A _ _ i x)))
  set_of_list {A : Type} [Nonempty A] : (list A) -> A -> Prop
  set_of_list_def {A : Type} [Nonempty A] : hol_eq (@set_of_list A _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))))) -> (list A) -> A -> Prop) _ (fun set_of_list' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))))) -> (list A) -> A -> Prop => ∀ _56511 : prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))))), hand (hol_eq (set_of_list' _56511 (@NIL A _)) (@EMPTY A _)) (∀ h : A, ∀ t : list A, hol_eq (set_of_list' _56511 (@CONS A _ h t)) (@INSERT A _ h (set_of_list' _56511 t)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))))))))))))))
  list_of_set {A : Type} [Nonempty A] : (A -> Prop) -> list A
  list_of_set_def {A : Type} [Nonempty A] : hol_eq (@list_of_set A _) (fun _56512 : A -> Prop => @epsilon (list A) _ (fun l : list A => hand (hol_eq (@set_of_list A _ l) _56512) (hol_eq (@LENGTH A _ l) (@CARD A _ _56512))))
  pairwise {A : Type} [Nonempty A] : (A -> A -> Prop) -> (A -> Prop) -> Prop
  pairwise_def {A : Type} [Nonempty A] : hol_eq (@pairwise A _) (fun _56702 : A -> A -> Prop => fun _56703 : A -> Prop => ∀ x : A, ∀ y : A, (hand (@IN A _ x _56703) (hand (@IN A _ y _56703) (not (hol_eq x y)))) -> _56702 x y)
  UNION_OF {A : Type} [Nonempty A] : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop
  UNION_OF_def {A : Type} [Nonempty A] : hol_eq (@UNION_OF A _) (fun _57415 : ((A -> Prop) -> Prop) -> Prop => fun _57416 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, hand (_57415 u) (hand (∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57416 c) (hol_eq (@UNIONS A _ u) s)))
  INTERSECTION_OF {A : Type} [Nonempty A] : (((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop
  INTERSECTION_OF_def {A : Type} [Nonempty A] : hol_eq (@INTERSECTION_OF A _) (fun _57427 : ((A -> Prop) -> Prop) -> Prop => fun _57428 : (A -> Prop) -> Prop => fun s : A -> Prop => ∃ u : (A -> Prop) -> Prop, hand (_57427 u) (hand (∀ c : A -> Prop, (@IN (A -> Prop) _ c u) -> _57428 c) (hol_eq (@INTERS A _ u) s)))
  ARBITRARY {A : Type} [Nonempty A] : ((A -> Prop) -> Prop) -> Prop
  ARBITRARY_def {A : Type} [Nonempty A] : hol_eq (@ARBITRARY A _) (fun _57563 : (A -> Prop) -> Prop => htrue)
  le_c {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop
  le_c_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@le_c A B _ _) (fun _64157 : A -> Prop => fun _64158 : B -> Prop => ∃ f : A -> B, hand (∀ x : A, (@IN A _ x _64157) -> @IN B _ (f x) _64158) (∀ x : A, ∀ y : A, (hand (@IN A _ x _64157) (hand (@IN A _ y _64157) (hol_eq (f x) (f y)))) -> hol_eq x y))
  lt_c {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop
  lt_c_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@lt_c A B _ _) (fun _64169 : A -> Prop => fun _64170 : B -> Prop => hand (@le_c A B _ _ _64169 _64170) (not (@le_c B A _ _ _64170 _64169)))
  eq_c {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop
  eq_c_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@eq_c A B _ _) (fun _64181 : A -> Prop => fun _64182 : B -> Prop => ∃ f : A -> B, hand (∀ x : A, (@IN A _ x _64181) -> @IN B _ (f x) _64182) (∀ y : B, (@IN B _ y _64182) -> @hexists_one A _ (fun x : A => hand (@IN A _ x _64181) (hol_eq (f x) y))))
  ge_c {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop
  ge_c_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@ge_c A B _ _) (fun _64193 : A -> Prop => fun _64194 : B -> Prop => @le_c B A _ _ _64194 _64193)
  gt_c {A B : Type} [Nonempty A] [Nonempty B] : (A -> Prop) -> (B -> Prop) -> Prop
  gt_c_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@gt_c A B _ _) (fun _64205 : A -> Prop => fun _64206 : B -> Prop => @lt_c B A _ _ _64206 _64205)
  COUNTABLE {A : Type} [Nonempty A] : (A -> Prop) -> Prop
  COUNTABLE_def {A : Type} [Nonempty A] : hol_eq (@COUNTABLE A _) (fun _64356 : A -> Prop => @ge_c num A _ _ (@UNIV num _) _64356)
  sup : (Real -> Prop) -> Real
  sup_def : hol_eq sup (fun _64361 : Real -> Prop => @epsilon Real _ (fun a : Real => hand (∀ x : Real, (@IN Real _ x _64361) -> real_le x a) (∀ b : Real, (∀ x : Real, (@IN Real _ x _64361) -> real_le x b) -> real_le a b)))
  inf : (Real -> Prop) -> Real
  inf_def : hol_eq inf (fun _65220 : Real -> Prop => @epsilon Real _ (fun a : Real => hand (∀ x : Real, (@IN Real _ x _65220) -> real_le a x) (∀ b : Real, (∀ x : Real, (@IN Real _ x _65220) -> real_le b x) -> real_le b a)))
  has_inf : (Real -> Prop) -> Real -> Prop
  has_inf_def : hol_eq has_inf (fun _66570 : Real -> Prop => fun _66571 : Real => ∀ c : Real, hol_eq (∀ x : Real, (@IN Real _ x _66570) -> real_le c x) (real_le c _66571))
  has_sup : (Real -> Prop) -> Real -> Prop
  has_sup_def : hol_eq has_sup (fun _66582 : Real -> Prop => fun _66583 : Real => ∀ c : Real, hol_eq (∀ x : Real, (@IN Real _ x _66582) -> real_le x c) (real_le _66583 c))
  dotdot : num -> num -> num -> Prop
  dotdot_def : hol_eq dotdot (fun _67008 : num => fun _67009 : num => @GSPEC num _ (fun GEN_PVAR_231 : num => ∃ x : num, @SETSPEC num _ GEN_PVAR_231 (hand (Nat_le _67008 x) (Nat_le x _67009)) x))
  neutral {A : Type} [Nonempty A] : (A -> A -> A) -> A
  neutral_def {A : Type} [Nonempty A] : hol_eq (@neutral A _) (fun _68920 : A -> A -> A => @epsilon A _ (fun x : A => ∀ y : A, hand (hol_eq (_68920 x y) y) (hol_eq (_68920 y x) y)))
  monoidal {A : Type} [Nonempty A] : (A -> A -> A) -> Prop
  monoidal_def {A : Type} [Nonempty A] : hol_eq (@monoidal A _) (fun _68925 : A -> A -> A => hand (∀ x : A, ∀ y : A, hol_eq (_68925 x y) (_68925 y x)) (hand (∀ x : A, ∀ y : A, ∀ z : A, hol_eq (_68925 x (_68925 y z)) (_68925 (_68925 x y) z)) (∀ x : A, hol_eq (_68925 (@neutral A _ _68925) x) x)))
  support {A B : Type} [Nonempty A] [Nonempty B] : (B -> B -> B) -> (A -> B) -> (A -> Prop) -> A -> Prop
  support_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@support A B _ _) (fun _69010 : B -> B -> B => fun _69011 : A -> B => fun _69012 : A -> Prop => @GSPEC A _ (fun GEN_PVAR_239 : A => ∃ x : A, @SETSPEC A _ GEN_PVAR_239 (hand (@IN A _ x _69012) (not (hol_eq (_69011 x) (@neutral B _ _69010)))) x))
  iterate {A B : Type} [Nonempty A] [Nonempty B] : (B -> B -> B) -> (A -> Prop) -> (A -> B) -> B
  iterate_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@iterate A B _ _) (fun _69031 : B -> B -> B => fun _69032 : A -> Prop => fun _69033 : A -> B => @COND B _ (@FINITE A _ (@support A B _ _ _69031 _69033 _69032)) (@ITSET A B _ _ (fun x : A => fun a : B => _69031 (_69033 x) a) (@support A B _ _ _69031 _69033 _69032) (@neutral B _ _69031)) (@neutral B _ _69031))
  iterato {A K : Type} [Nonempty A] [Nonempty K] : (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A
  iterato_def {A K : Type} [Nonempty A] [Nonempty K] : hol_eq (@iterato A K _ _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A) _ (fun itty : (prod num (prod num (prod num (prod num (prod num (prod num num)))))) -> (A -> Prop) -> A -> (A -> A -> A) -> (K -> K -> Prop) -> (K -> Prop) -> (K -> A) -> A => ∀ _76787 : prod num (prod num (prod num (prod num (prod num (prod num num))))), ∀ dom : A -> Prop, ∀ neut : A, ∀ op : A -> A -> A, ∀ ltle : K -> K -> Prop, ∀ k : K -> Prop, ∀ f : K -> A, hol_eq (itty _76787 dom neut op ltle k f) (@COND A _ (hand (@FINITE K _ (@GSPEC K _ (fun GEN_PVAR_265 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_265 (hand (@IN K _ i k) (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i))) (not (hol_eq (@GSPEC K _ (fun GEN_PVAR_266 : K => ∃ i : K, @SETSPEC K _ GEN_PVAR_266 (hand (@IN K _ i k) (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) i)) (@EMPTY K _)))) (@LET K A _ _ (fun i : K => @LET_END A _ (op (f i) (itty _76787 dom neut op ltle (@GSPEC K _ (fun GEN_PVAR_267 : K => ∃ j : K, @SETSPEC K _ GEN_PVAR_267 (hand (@IN K _ j (@DELETE K _ k i)) (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _))))) j)) f))) (@COND K _ (∃ i : K, hand (@IN K _ i k) (hand (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) (∀ j : K, (hand (ltle j i) (hand (@IN K _ j k) (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> hol_eq j i))) (@epsilon K _ (fun i : K => hand (@IN K _ i k) (hand (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))) (∀ j : K, (hand (ltle j i) (hand (@IN K _ j k) (@IN A _ (f j) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))) -> hol_eq j i)))) (@epsilon K _ (fun i : K => hand (@IN K _ i k) (@IN A _ (f i) (@DIFF A _ dom (@INSERT A _ neut (@EMPTY A _)))))))) neut)) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 (BIT1 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT1 _0)))))))))))))))
  nproduct {A : Type} [Nonempty A] : (A -> Prop) -> (A -> num) -> num
  nproduct_def {A : Type} [Nonempty A] : hol_eq (@nproduct A _) (@iterate A num _ _ Nat_mul)
  iproduct {A : Type} [Nonempty A] : (A -> Prop) -> (A -> int) -> int
  iproduct_def {A : Type} [Nonempty A] : hol_eq (@iproduct A _) (@iterate A int _ _ int_mul)
  product {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Real) -> Real
  product_def {A : Type} [Nonempty A] : hol_eq (@product A _) (@iterate A Real _ _ real_mul)
  isum {A : Type} [Nonempty A] : (A -> Prop) -> (A -> int) -> int
  isum_def {A : Type} [Nonempty A] : hol_eq (@isum A _) (@iterate A int _ _ int_add)
  nsum {A : Type} [Nonempty A] : (A -> Prop) -> (A -> num) -> num
  nsum_def {A : Type} [Nonempty A] : hol_eq (@nsum A _) (@iterate A num _ _ Nat_add)
  sum {A : Type} [Nonempty A] : (A -> Prop) -> (A -> Real) -> Real
  sum_def {A : Type} [Nonempty A] : hol_eq (@sum A _) (@iterate A Real _ _ real_add)
  polynomial_function : (Real -> Real) -> Prop
  polynomial_function_def : hol_eq polynomial_function (fun _94200 : Real -> Real => ∃ m : num, ∃ c : num -> Real, ∀ x : Real, hol_eq (_94200 x) (@sum num _ (dotdot (NUMERAL _0) m) (fun i : num => real_mul (c i) (real_pow x i))))
  dimindex {A : Type} [Nonempty A] : (A -> Prop) -> num
  dimindex_def {A : Type} [Nonempty A] : hol_eq (@dimindex A _) (fun _94242 : A -> Prop => @COND num _ (@FINITE A _ (@UNIV A _)) (@CARD A _ (@UNIV A _)) (NUMERAL (BIT1 _0)))
  finite_index : ∀ {A : Type} [Nonempty A], num -> finite_image A
  dest_finite_image : ∀ {A : Type} [Nonempty A], (finite_image A) -> num
  mk_cart : ∀ {A B : Type} [Nonempty A] [Nonempty B], ((finite_image B) -> A) -> cart A B
  dest_cart : ∀ {A B : Type} [Nonempty A] [Nonempty B], (cart A B) -> (finite_image B) -> A
  dollar {A N' : Type} [Nonempty A] [Nonempty N'] : (cart A N') -> num -> A
  dollar_def {A N' : Type} [Nonempty A] [Nonempty N'] : hol_eq (@dollar A N' _ _) (fun _94652 : cart A N' => fun _94653 : num => @dest_cart A N' _ _ _94652 (@finite_index N' _ _94653))
  lambda {A B : Type} [Nonempty A] [Nonempty B] : (num -> A) -> cart A B
  lambda_def {A B : Type} [Nonempty A] [Nonempty B] : hol_eq (@lambda A B _ _) (fun _94688 : num -> A => @epsilon (cart A B) _ (fun f : cart A B => ∀ i : num, (hand (Nat_le (NUMERAL (BIT1 _0)) i) (Nat_le i (@dimindex B _ (@UNIV B _)))) -> hol_eq (@dollar A B _ _ f i) (_94688 i)))
  mk_finite_sum : ∀ {A B : Type} [Nonempty A] [Nonempty B], num -> finite_sum A B
  dest_finite_sum : ∀ {A B : Type} [Nonempty A] [Nonempty B], (finite_sum A B) -> num
  pastecart {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A M) -> (cart A N') -> cart A (finite_sum M N')
  pastecart_def {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : hol_eq (@pastecart A M N' _ _ _) (fun _94979 : cart A M => fun _94980 : cart A N' => @lambda A (finite_sum M N') _ _ (fun i : num => @COND A _ (Nat_le i (@dimindex M _ (@UNIV M _))) (@dollar A M _ _ _94979 i) (@dollar A N' _ _ _94980 (Nat_minus i (@dimindex M _ (@UNIV M _))))))
  fstcart {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A (finite_sum M N')) -> cart A M
  fstcart_def {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : hol_eq (@fstcart A M N' _ _ _) (fun _94991 : cart A (finite_sum M N') => @lambda A M _ _ (fun i : num => @dollar A (finite_sum M N') _ _ _94991 i))
  sndcart {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : (cart A (finite_sum M N')) -> cart A N'
  sndcart_def {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : hol_eq (@sndcart A M N' _ _ _) (fun _94996 : cart A (finite_sum M N') => @lambda A N' _ _ (fun i : num => @dollar A (finite_sum M N') _ _ _94996 (Nat_add i (@dimindex M _ (@UNIV M _)))))
  mk_finite_diff : ∀ {A B : Type} [Nonempty A] [Nonempty B], num -> finite_diff A B
  dest_finite_diff : ∀ {A B : Type} [Nonempty A] [Nonempty B], (finite_diff A B) -> num
  mk_finite_prod : ∀ {A B : Type} [Nonempty A] [Nonempty B], num -> finite_prod A B
  dest_finite_prod : ∀ {A B : Type} [Nonempty A] [Nonempty B], (finite_prod A B) -> num
  _mk_tybit0 : ∀ {A : Type} [Nonempty A], (recspace (finite_sum A A)) -> tybit0 A
  _dest_tybit0 : ∀ {A : Type} [Nonempty A], (tybit0 A) -> recspace (finite_sum A A)
  _100406 {A : Type} [Nonempty A] : (finite_sum A A) -> tybit0 A
  _100406_def {A : Type} [Nonempty A] : hol_eq (@_100406 A _) (fun a : finite_sum A A => @_mk_tybit0 A _ ((fun a' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL _0) a' (fun n : num => @BOTTOM (finite_sum A A) _)) a))
  mktybit0 {A : Type} [Nonempty A] : (finite_sum A A) -> tybit0 A
  mktybit0_def {A : Type} [Nonempty A] : hol_eq (@mktybit0 A _) (@_100406 A _)
  _mk_tybit1 : ∀ {A : Type} [Nonempty A], (recspace (finite_sum (finite_sum A A) unit)) -> tybit1 A
  _dest_tybit1 : ∀ {A : Type} [Nonempty A], (tybit1 A) -> recspace (finite_sum (finite_sum A A) unit)
  _100425 {A : Type} [Nonempty A] : (finite_sum (finite_sum A A) unit) -> tybit1 A
  _100425_def {A : Type} [Nonempty A] : hol_eq (@_100425 A _) (fun a : finite_sum (finite_sum A A) unit => @_mk_tybit1 A _ ((fun a' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) _ (NUMERAL _0) a' (fun n : num => @BOTTOM (finite_sum (finite_sum A A) unit) _)) a))
  mktybit1 {A : Type} [Nonempty A] : (finite_sum (finite_sum A A) unit) -> tybit1 A
  mktybit1_def {A : Type} [Nonempty A] : hol_eq (@mktybit1 A _) (@_100425 A _)
  vector {A N' : Type} [Nonempty A] [Nonempty N'] : (list A) -> cart A N'
  vector_def {A N' : Type} [Nonempty A] [Nonempty N'] : hol_eq (@vector A N' _ _) (fun _102119 : list A => @lambda A N' _ _ (fun i : num => @EL A _ (Nat_minus i (NUMERAL (BIT1 _0))) _102119))
  PCROSS {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : ((cart A M) -> Prop) -> ((cart A N') -> Prop) -> (cart A (finite_sum M N')) -> Prop
  PCROSS_def {A M N' : Type} [Nonempty A] [Nonempty M] [Nonempty N'] : hol_eq (@PCROSS A M N' _ _ _) (fun _102146 : (cart A M) -> Prop => fun _102147 : (cart A N') -> Prop => @GSPEC (cart A (finite_sum M N')) _ (fun GEN_PVAR_363 : cart A (finite_sum M N') => ∃ x : cart A M, ∃ y : cart A N', @SETSPEC (cart A (finite_sum M N')) _ GEN_PVAR_363 (hand (@IN (cart A M) _ x _102146) (@IN (cart A N') _ y _102147)) (@pastecart A M N' _ _ _ x y)))
  CASEWISE {_138002 _138038 _138042 _138043 : Type} [Nonempty _138002] [Nonempty _138038] [Nonempty _138042] [Nonempty _138043] : (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002
  CASEWISE_def {_138002 _138038 _138042 _138043 : Type} [Nonempty _138002] [Nonempty _138038] [Nonempty _138042] [Nonempty _138043] : hol_eq (@CASEWISE _138002 _138038 _138042 _138043 _ _ _ _) (@epsilon ((prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002) _ (fun CASEWISE' : (prod num (prod num (prod num (prod num (prod num (prod num (prod num num))))))) -> (list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002))) -> _138043 -> _138042 -> _138002 => ∀ _102751 : prod num (prod num (prod num (prod num (prod num (prod num (prod num num)))))), hand (∀ f : _138043, ∀ x : _138042, hol_eq (CASEWISE' _102751 (@NIL (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _) f x) (@epsilon _138002 _ (fun y : _138002 => htrue))) (∀ h : prod (_138038 -> _138042) (_138043 -> _138038 -> _138002), ∀ t : list (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)), ∀ f : _138043, ∀ x : _138042, hol_eq (CASEWISE' _102751 (@CONS (prod (_138038 -> _138042) (_138043 -> _138038 -> _138002)) _ h t) f x) (@COND _138002 _ (∃ y : _138038, hol_eq (@FST (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) x) (@SND (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h f (@epsilon _138038 _ (fun y : _138038 => hol_eq (@FST (_138038 -> _138042) (_138043 -> _138038 -> _138002) _ _ h y) x))) (CASEWISE' _102751 t f x)))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num (prod num num)))))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num (prod num num))))) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num (prod num num)))) _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num (prod num num))) _ _ (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num (prod num num)) _ _ (NUMERAL (BIT1 (BIT1 (BIT1 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (@Prod_mk num (prod num num) _ _ (NUMERAL (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT0 (BIT1 _0)))))))) (@Prod_mk num num _ _ (NUMERAL (BIT1 (BIT1 (BIT0 (BIT0 (BIT1 (BIT0 (BIT1 _0)))))))) (NUMERAL (BIT1 (BIT0 (BIT1 (BIT0 (BIT0 (BIT0 (BIT1 _0))))))))))))))))
  admissible {_138333 _138336 _138340 _138341 _138346 : Type} [Nonempty _138333] [Nonempty _138336] [Nonempty _138340] [Nonempty _138341] [Nonempty _138346] : (_138340 -> _138333 -> Prop) -> ((_138340 -> _138336) -> _138346 -> Prop) -> (_138346 -> _138333) -> ((_138340 -> _138336) -> _138346 -> _138341) -> Prop
  admissible_def {_138333 _138336 _138340 _138341 _138346 : Type} [Nonempty _138333] [Nonempty _138336] [Nonempty _138340] [Nonempty _138341] [Nonempty _138346] : hol_eq (@admissible _138333 _138336 _138340 _138341 _138346 _ _ _ _ _) (fun _103818 : _138340 -> _138333 -> Prop => fun _103819 : (_138340 -> _138336) -> _138346 -> Prop => fun _103820 : _138346 -> _138333 => fun _103821 : (_138340 -> _138336) -> _138346 -> _138341 => ∀ f : _138340 -> _138336, ∀ g : _138340 -> _138336, ∀ a : _138346, (hand (_103819 f a) (hand (_103819 g a) (∀ z : _138340, (_103818 z (_103820 a)) -> hol_eq (f z) (g z)))) -> hol_eq (_103821 f a) (_103821 g a))
  tailadmissible {A B P : Type} [Nonempty A] [Nonempty B] [Nonempty P] : (A -> A -> Prop) -> ((A -> B) -> P -> Prop) -> (P -> A) -> ((A -> B) -> P -> B) -> Prop
  tailadmissible_def {A B P : Type} [Nonempty A] [Nonempty B] [Nonempty P] : hol_eq (@tailadmissible A B P _ _ _) (fun _103850 : A -> A -> Prop => fun _103851 : (A -> B) -> P -> Prop => fun _103852 : P -> A => fun _103853 : (A -> B) -> P -> B => ∃ P' : (A -> B) -> P -> Prop, ∃ G : (A -> B) -> P -> A, ∃ H : (A -> B) -> P -> B, hand (∀ f : A -> B, ∀ a : P, ∀ y : A, (hand (P' f a) (_103850 y (G f a))) -> _103850 y (_103852 a)) (hand (∀ f : A -> B, ∀ g : A -> B, ∀ a : P, (∀ z : A, (_103850 z (_103852 a)) -> hol_eq (f z) (g z)) -> hand (hol_eq (P' f a) (P' g a)) (hand (hol_eq (G f a) (G g a)) (hol_eq (H f a) (H g a)))) (∀ f : A -> B, ∀ a : P, (_103851 f a) -> hol_eq (_103853 f a) (@COND B _ (P' f a) (f (G f a)) (H f a)))))
  superadmissible {_138490 _138492 _138498 : Type} [Nonempty _138490] [Nonempty _138492] [Nonempty _138498] : (_138490 -> _138490 -> Prop) -> ((_138490 -> _138492) -> _138498 -> Prop) -> (_138498 -> _138490) -> ((_138490 -> _138492) -> _138498 -> _138492) -> Prop
  superadmissible_def {_138490 _138492 _138498 : Type} [Nonempty _138490] [Nonempty _138492] [Nonempty _138498] : hol_eq (@superadmissible _138490 _138492 _138498 _ _ _) (fun _103882 : _138490 -> _138490 -> Prop => fun _103883 : (_138490 -> _138492) -> _138498 -> Prop => fun _103884 : _138498 -> _138490 => fun _103885 : (_138490 -> _138492) -> _138498 -> _138492 => (@admissible _138490 _138492 _138490 Prop _138498 _ _ _ _ _ _103882 (fun f : _138490 -> _138492 => fun a : _138498 => htrue) _103884 _103883) -> @tailadmissible _138490 _138492 _138498 _ _ _ _103882 _103883 _103884 _103885)
  axiom_0 : ∀ {A B : Type} [Nonempty A] [Nonempty B], ∀ t : A -> B, hol_eq (fun x : A => t x) t
  axiom_1 : ∀ {A : Type} [Nonempty A], ∀ P : A -> Prop, ∀ x : A, (P x) -> P (@epsilon A _ P)
  axiom_2 : ∀ (a : unit), hol_eq (one_ABS (one_REP a)) a
  axiom_3 : ∀ (r : Prop), hol_eq ((fun b : Prop => b) r) (hol_eq (one_REP (one_ABS r)) r)
  axiom_4 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : prod A B), hol_eq (@ABS_prod A B _ _ (@REP_prod A B _ _ a)) a
  axiom_5 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (r : A -> B -> Prop), hol_eq ((fun x : A -> B -> Prop => ∃ a : A, ∃ b : B, hol_eq x (@mk_pair A B _ _ a b)) r) (hol_eq (@REP_prod A B _ _ (@ABS_prod A B _ _ r)) r)
  axiom_6 : ∃ f : ind -> ind, hand (@ONE_ONE ind ind _ _ f) (not (@ONTO ind ind _ _ f))
  axiom_7 : ∀ (a : num), hol_eq (mk_num (dest_num a)) a
  axiom_8 : ∀ (r : ind), hol_eq (NUM_REP r) (hol_eq (dest_num (mk_num r)) r)
  axiom_9 : ∀ {A : Type} [Nonempty A] (a : recspace A), hol_eq (@_mk_rec A _ (@_dest_rec A _ a)) a
  axiom_10 : ∀ {A : Type} [Nonempty A] (r : num -> A -> Prop), hol_eq (@ZRECSPACE A _ r) (hol_eq (@_dest_rec A _ (@_mk_rec A _ r)) r)
  axiom_11 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : SUM A B), hol_eq (@_mk_sum A B _ _ (@_dest_sum A B _ _ a)) a
  axiom_12 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (r : recspace (prod A B)), hol_eq ((fun a : recspace (prod A B) => ∀ sum' : (recspace (prod A B)) -> Prop, (∀ a' : recspace (prod A B), (hor (∃ a'' : A, hol_eq a' ((fun a''' : A => @CONSTR (prod A B) _ (NUMERAL _0) (@Prod_mk A B _ _ a''' (@epsilon B _ (fun v : B => htrue))) (fun n : num => @BOTTOM (prod A B) _)) a'')) (∃ a'' : B, hol_eq a' ((fun a''' : B => @CONSTR (prod A B) _ (SUC (NUMERAL _0)) (@Prod_mk A B _ _ (@epsilon A _ (fun v : A => htrue)) a''') (fun n : num => @BOTTOM (prod A B) _)) a''))) -> sum' a') -> sum' a) r) (hol_eq (@_dest_sum A B _ _ (@_mk_sum A B _ _ r)) r)
  axiom_13 : ∀ {A : Type} [Nonempty A] (a : option A), hol_eq (@_mk_option A _ (@_dest_option A _ a)) a
  axiom_14 : ∀ {A : Type} [Nonempty A] (r : recspace A), hol_eq ((fun a : recspace A => ∀ option' : (recspace A) -> Prop, (∀ a' : recspace A, (hor (hol_eq a' (@CONSTR A _ (NUMERAL _0) (@epsilon A _ (fun v : A => htrue)) (fun n : num => @BOTTOM A _))) (∃ a'' : A, hol_eq a' ((fun a''' : A => @CONSTR A _ (SUC (NUMERAL _0)) a''' (fun n : num => @BOTTOM A _)) a''))) -> option' a') -> option' a) r) (hol_eq (@_dest_option A _ (@_mk_option A _ r)) r)
  axiom_15 : ∀ {A : Type} [Nonempty A] (a : list A), hol_eq (@_mk_list A _ (@_dest_list A _ a)) a
  axiom_16 : ∀ {A : Type} [Nonempty A] (r : recspace A), hol_eq ((fun a : recspace A => ∀ list' : (recspace A) -> Prop, (∀ a' : recspace A, (hor (hol_eq a' (@CONSTR A _ (NUMERAL _0) (@epsilon A _ (fun v : A => htrue)) (fun n : num => @BOTTOM A _))) (∃ a0 : A, ∃ a1 : recspace A, hand (hol_eq a' ((fun a0' : A => fun a1' : recspace A => @CONSTR A _ (SUC (NUMERAL _0)) a0' (@FCONS (recspace A) _ a1' (fun n : num => @BOTTOM A _))) a0 a1)) (list' a1))) -> list' a') -> list' a) r) (hol_eq (@_dest_list A _ (@_mk_list A _ r)) r)
  axiom_17 : ∀ (a : char), hol_eq (_mk_char (_dest_char a)) a
  axiom_18 : ∀ (r : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))), hol_eq ((fun a : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) => ∀ char' : (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop, (∀ a' : recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))), (∃ a0 : Prop, ∃ a1 : Prop, ∃ a2 : Prop, ∃ a3 : Prop, ∃ a4 : Prop, ∃ a5 : Prop, ∃ a6 : Prop, ∃ a7 : Prop, hol_eq a' ((fun a0' : Prop => fun a1' : Prop => fun a2' : Prop => fun a3' : Prop => fun a4' : Prop => fun a5' : Prop => fun a6' : Prop => fun a7' : Prop => @CONSTR (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _ (NUMERAL _0) (@Prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))) _ _ a0' (@Prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))) _ _ a1' (@Prod_mk Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))) _ _ a2' (@Prod_mk Prop (prod Prop (prod Prop (prod Prop Prop))) _ _ a3' (@Prod_mk Prop (prod Prop (prod Prop Prop)) _ _ a4' (@Prod_mk Prop (prod Prop Prop) _ _ a5' (@Prod_mk Prop Prop _ _ a6' a7'))))))) (fun n : num => @BOTTOM (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))) _)) a0 a1 a2 a3 a4 a5 a6 a7)) -> char' a') -> char' a) r) (hol_eq (_dest_char (_mk_char r)) r)
  axiom_19 : ∀ (a : nadd), hol_eq (mk_nadd (dest_nadd a)) a
  axiom_20 : ∀ (r : num -> num), hol_eq (is_nadd r) (hol_eq (dest_nadd (mk_nadd r)) r)
  axiom_21 : ∀ (a : hreal), hol_eq (mk_hreal (dest_hreal a)) a
  axiom_22 : ∀ (r : nadd -> Prop), hol_eq ((fun s : nadd -> Prop => ∃ x : nadd, hol_eq s (nadd_eq x)) r) (hol_eq (dest_hreal (mk_hreal r)) r)
  axiom_23 : ∀ (a : Real), hol_eq (mk_real (dest_real a)) a
  axiom_24 : ∀ (r : (prod hreal hreal) -> Prop), hol_eq ((fun s : (prod hreal hreal) -> Prop => ∃ x : prod hreal hreal, hol_eq s (treal_eq x)) r) (hol_eq (dest_real (mk_real r)) r)
  axiom_25 : ∀ (a : int), hol_eq (int_of_real (real_of_int a)) a
  axiom_26 : ∀ (r : Real), hol_eq ((fun x : Real => integer x) r) (hol_eq (real_of_int (int_of_real r)) r)
  axiom_27 : ∀ {A : Type} [Nonempty A] (a : finite_image A), hol_eq (@finite_index A _ (@dest_finite_image A _ a)) a
  axiom_28 : ∀ {A : Type} [Nonempty A] (r : num), hol_eq ((fun x : num => @IN num _ x (dotdot (NUMERAL (BIT1 _0)) (@dimindex A _ (@UNIV A _)))) r) (hol_eq (@dest_finite_image A _ (@finite_index A _ r)) r)
  axiom_29 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : cart A B), hol_eq (@mk_cart A B _ _ (@dest_cart A B _ _ a)) a
  axiom_30 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (r : (finite_image B) -> A), hol_eq ((fun f : (finite_image B) -> A => htrue) r) (hol_eq (@dest_cart A B _ _ (@mk_cart A B _ _ r)) r)
  axiom_31 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : finite_sum A B), hol_eq (@mk_finite_sum A B _ _ (@dest_finite_sum A B _ _ a)) a
  axiom_32 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (r : num), hol_eq ((fun x : num => @IN num _ x (dotdot (NUMERAL (BIT1 _0)) (Nat_add (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))))) r) (hol_eq (@dest_finite_sum A B _ _ (@mk_finite_sum A B _ _ r)) r)
  axiom_33 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : finite_diff A B), hol_eq (@mk_finite_diff A B _ _ (@dest_finite_diff A B _ _ a)) a
  axiom_34 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (r : num), hol_eq ((fun x : num => @IN num _ x (dotdot (NUMERAL (BIT1 _0)) (@COND num _ (Nat_lt (@dimindex B _ (@UNIV B _)) (@dimindex A _ (@UNIV A _))) (Nat_minus (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))) (NUMERAL (BIT1 _0))))) r) (hol_eq (@dest_finite_diff A B _ _ (@mk_finite_diff A B _ _ r)) r)
  axiom_35 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (a : finite_prod A B), hol_eq (@mk_finite_prod A B _ _ (@dest_finite_prod A B _ _ a)) a
  axiom_36 : ∀ {A B : Type} [Nonempty A] [Nonempty B] (r : num), hol_eq ((fun x : num => @IN num _ x (dotdot (NUMERAL (BIT1 _0)) (Nat_mul (@dimindex A _ (@UNIV A _)) (@dimindex B _ (@UNIV B _))))) r) (hol_eq (@dest_finite_prod A B _ _ (@mk_finite_prod A B _ _ r)) r)
  axiom_37 : ∀ {A : Type} [Nonempty A] (a : tybit0 A), hol_eq (@_mk_tybit0 A _ (@_dest_tybit0 A _ a)) a
  axiom_38 : ∀ {A : Type} [Nonempty A] (r : recspace (finite_sum A A)), hol_eq ((fun a : recspace (finite_sum A A) => ∀ tybit0' : (recspace (finite_sum A A)) -> Prop, (∀ a' : recspace (finite_sum A A), (∃ a'' : finite_sum A A, hol_eq a' ((fun a''' : finite_sum A A => @CONSTR (finite_sum A A) _ (NUMERAL _0) a''' (fun n : num => @BOTTOM (finite_sum A A) _)) a'')) -> tybit0' a') -> tybit0' a) r) (hol_eq (@_dest_tybit0 A _ (@_mk_tybit0 A _ r)) r)
  axiom_39 : ∀ {A : Type} [Nonempty A] (a : tybit1 A), hol_eq (@_mk_tybit1 A _ (@_dest_tybit1 A _ a)) a
  axiom_40 : ∀ {A : Type} [Nonempty A] (r : recspace (finite_sum (finite_sum A A) unit)), hol_eq ((fun a : recspace (finite_sum (finite_sum A A) unit) => ∀ tybit1' : (recspace (finite_sum (finite_sum A A) unit)) -> Prop, (∀ a' : recspace (finite_sum (finite_sum A A) unit), (∃ a'' : finite_sum (finite_sum A A) unit, hol_eq a' ((fun a''' : finite_sum (finite_sum A A) unit => @CONSTR (finite_sum (finite_sum A A) unit) _ (NUMERAL _0) a''' (fun n : num => @BOTTOM (finite_sum (finite_sum A A) unit) _)) a'')) -> tybit1' a') -> tybit1' a) r) (hol_eq (@_dest_tybit1 A _ (@_mk_tybit1 A _ r)) r)

-- make the Nonempty witnesses usable by instance search outside the class
instance instNeUnit [T : HOLTheory] : Nonempty (HOLTheory.unit) := HOLTheory.ne_unit
instance instNeProd [T : HOLTheory] (a0 a1 : Type) : Nonempty (HOLTheory.prod a0 a1) := HOLTheory.ne_prod a0 a1
instance instNeInd [T : HOLTheory] : Nonempty (HOLTheory.ind) := HOLTheory.ne_ind
instance instNeNum [T : HOLTheory] : Nonempty (HOLTheory.num) := HOLTheory.ne_num
instance instNeRecspace [T : HOLTheory] (a0 : Type) : Nonempty (HOLTheory.recspace a0) := HOLTheory.ne_recspace a0
instance instNeSUM [T : HOLTheory] (a0 a1 : Type) : Nonempty (HOLTheory.SUM a0 a1) := HOLTheory.ne_SUM a0 a1
instance instNeOption [T : HOLTheory] (a0 : Type) : Nonempty (HOLTheory.option a0) := HOLTheory.ne_option a0
instance instNeList [T : HOLTheory] (a0 : Type) : Nonempty (HOLTheory.list a0) := HOLTheory.ne_list a0
instance instNeChar [T : HOLTheory] : Nonempty (HOLTheory.char) := HOLTheory.ne_char
instance instNeNadd [T : HOLTheory] : Nonempty (HOLTheory.nadd) := HOLTheory.ne_nadd
instance instNeHreal [T : HOLTheory] : Nonempty (HOLTheory.hreal) := HOLTheory.ne_hreal
instance instNeReal [T : HOLTheory] : Nonempty (HOLTheory.Real) := HOLTheory.ne_Real
instance instNeInt [T : HOLTheory] : Nonempty (HOLTheory.int) := HOLTheory.ne_int
instance instNeFiniteImage [T : HOLTheory] (a0 : Type) : Nonempty (HOLTheory.finite_image a0) := HOLTheory.ne_finite_image a0
instance instNeCart [T : HOLTheory] (a0 a1 : Type) : Nonempty (HOLTheory.cart a0 a1) := HOLTheory.ne_cart a0 a1
instance instNeFiniteSum [T : HOLTheory] (a0 a1 : Type) : Nonempty (HOLTheory.finite_sum a0 a1) := HOLTheory.ne_finite_sum a0 a1
instance instNeFiniteDiff [T : HOLTheory] (a0 a1 : Type) : Nonempty (HOLTheory.finite_diff a0 a1) := HOLTheory.ne_finite_diff a0 a1
instance instNeFiniteProd [T : HOLTheory] (a0 a1 : Type) : Nonempty (HOLTheory.finite_prod a0 a1) := HOLTheory.ne_finite_prod a0 a1
instance instNeTybit0 [T : HOLTheory] (a0 : Type) : Nonempty (HOLTheory.tybit0 a0) := HOLTheory.ne_tybit0 a0
instance instNeTybit1 [T : HOLTheory] (a0 : Type) : Nonempty (HOLTheory.tybit1 a0) := HOLTheory.ne_tybit1 a0
