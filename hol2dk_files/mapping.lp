/* Map from dk/lp symbols on the right to Lean expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Lean expressions. */

// primitive types
builtin "Type _" ≔ Set;
builtin "el" ≔ el;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;

// connectives
builtin "Eq" ≔ =;

builtin "imp" ≔ ⇒;
builtin "imp_def" ≔ ⇒_def;

builtin "FORALL" ≔ ∀;
builtin "FORALL_def" ≔ ∀_def;

builtin "Or" ≔ ∨;
builtin "or_def" ≔ ∨_def;

builtin "And" ≔ ∧;
builtin "and_def" ≔ ∧_def;

builtin "EXISTS" ≔ ∃;
builtin "exists_def" ≔ ∃_def;

builtin "Not" ≔ ¬;
builtin "not_def" ≔ ¬_def;

builtin "True" ≔ ⊤;
builtin "True_def" ≔ ⊤_def;

builtin "False" ≔ ⊥;
builtin "false_def" ≔ ⊥_def;

builtin "EXISTSUNIQUE" ≔ ∃₁;
builtin "EXISTSUNIQUE_def" ≔ ∃₁_def;

// natural deduction rules
builtin "True.intro" ≔ ⊤ᵢ;
builtin "And.intro" ≔ ∧ᵢ;
builtin "And.left" ≔ ∧ₑ₁;
builtin "And.right" ≔ ∧ₑ₂;
builtin "or_inl" ≔ ∨ᵢ₁;
builtin "or_inr" ≔ ∨ᵢ₂;
builtin "Or.elim" ≔ ∨ₑ;
builtin "exists_intro" ≔ ∃ᵢ;
builtin "Exists.elim" ≔ ∃ₑ;

// HOL-Light rules
builtin "Eq.refl" ≔ REFL;
builtin "EQ_MP" ≔ EQ_MP;
builtin "MK_COMB" ≔ MK_COMB;
builtin "Eq.trans" ≔ TRANS;
builtin "Eq.symm" ≔ SYM;

// HOL-Light axioms
builtin "Classical.epsilon" ≔ ε;
builtin "axiom_0" ≔ axiom_0;
builtin "axiom_1" ≔ axiom_1;
builtin "funext" ≔ fun_ext;
builtin "Eq.propIntro" ≔ prop_ext;

// miscellaneous
builtin "COND" ≔ COND;
builtin "COND_def" ≔ COND_def;
builtin "GEQ" ≔ GEQ;
builtin "GEQ_def" ≔ GEQ_def;
builtin "ISO" ≔ ISO;
builtin "ISO_def" ≔ ISO_def;
builtin "GABS" ≔ GABS;
builtin "GABS_def" ≔ GABS_def;
builtin "_UNGUARDED_PATTERN" ≔ _UNGUARDED_PATTERN;
builtin "_UNGUARDED_PATTERN_def" ≔ _UNGUARDED_PATTERN_def;
builtin "_SEQPATTERN" ≔ _SEQPATTERN;
builtin "_SEQPATTERN_def" ≔ _SEQPATTERN_def;
builtin "_GUARDED_PATTERN" ≔ _GUARDED_PATTERN;
builtin "_GUARDED_PATTERN_def" ≔ _GUARDED_PATTERN_def;
builtin "_MATCH" ≔ _MATCH;
builtin "_MATCH_def" ≔ _MATCH_def;
builtin "_FUNCTION" ≔ _FUNCTION;
builtin "_FUNCTION_def" ≔ _FUNCTION_def;
builtin "_FALSITY_" ≔ _FALSITY_;
builtin "_FALSITY__def" ≔ _FALSITY__def;
builtin "hashek" ≔ hashek;
builtin "hashek_def" ≔ hashek_def;
builtin "LET" ≔ LET;
builtin "LET_def" ≔ LET_def;
builtin "LET_END" ≔ LET_END;
builtin "LET_END_def" ≔ LET_END_def;
builtin "HolLightLean.hol_up_real_terms.MEASURE" ≔ MEASURE;
builtin "HolLightLean.hol_up_real_terms.MEASURE_def" ≔ MEASURE_def;
builtin "o" ≔ o;
builtin "o_def" ≔ o_def;
builtin "I" ≔ I;
builtin "I_def" ≔ I_def;

// unit type
builtin "Unit" ≔ unit;
builtin "one_ABS" ≔ one_ABS;
builtin "one_REP" ≔ one_REP;
builtin "axiom_2" ≔ axiom_2;
builtin "axiom_3" ≔ axiom_3;
builtin "()" ≔ one;
builtin "one_def" ≔ one_def;

// product type
builtin "mk_pair" ≔ mk_pair;
builtin "mk_pair_def" ≔ mk_pair_def;
builtin "prod" ≔ prod;
builtin "ABS_prod" ≔ ABS_prod;
builtin "REP_prod" ≔ REP_prod;
builtin "axiom_4" ≔ axiom_4;
builtin "axiom_5" ≔ axiom_5;
builtin "prod_mk" ≔ ̦‚;
builtin "pair_def" ≔ ̦‚_def;
builtin "prod_fst" ≔ FST;
builtin "FST_def" ≔ FST_def;
builtin "prod_snd" ≔ SND;
builtin "SND_def" ≔ SND_def;

// infinite type ind
builtin "ind" ≔ ind;
builtin "ONE_ONE" ≔ ONE_ONE;
builtin "ONE_ONE_def" ≔ ONE_ONE_def;
builtin "ONTO" ≔ ONTO;
builtin "ONTO_def" ≔ ONTO_def;
builtin "axiom_6" ≔ axiom_6;
builtin "IND_SUC" ≔ IND_SUC;
builtin "IND_SUC_def" ≔ IND_SUC_def;
builtin "IND_0" ≔ IND_0;
builtin "IND_0_def" ≔ IND_0_def;

// type of natural numbers
builtin "Nat" ≔ num;
builtin "mk_num" ≔ mk_num;
builtin "dest_num" ≔ dest_num;
builtin "NUM_REP" ≔ NUM_REP;
builtin "NUM_REP_def" ≔ NUM_REP_def;
builtin "axiom_7" ≔ axiom_7;
builtin "axiom_8" ≔ axiom_8;
builtin "Nat.zero" ≔ _0;
builtin "_0_def" ≔ _0_def;
builtin "Nat.succ" ≔ SUC;
builtin "SUC_def" ≔ SUC_def;

// usual mathematical functions on natural numbers
builtin "NUMERAL" ≔ NUMERAL;
builtin "NUMERAL_def" ≔ NUMERAL_def;
builtin "BIT0" ≔ BIT0;
builtin "BIT0_def" ≔ BIT0_def;
builtin "BIT1" ≔ BIT1;
builtin "BIT1_def" ≔ BIT1_def;
builtin "Nat.pred" ≔ PRE;
builtin "PRE_def" ≔ PRE_def;
builtin "Nat.add" ≔ +;
builtin "add_def" ≔ +_def;
builtin "Nat.mul" ≔ *;
builtin "mul_def" ≔ *_def;
builtin "Nat.pow" ≔ EXP;
builtin "EXP_def" ≔ EXP_def;
builtin "Nat.le" ≔ <=;
builtin "le_def" ≔ <=_def;
builtin "Nat.lt" ≔ <;
builtin "lt_def" ≔ <_def;
builtin "GE.ge" ≔ >=;
builtin "ge_def" ≔ >=_def;
builtin "GT.gt" ≔ >;
builtin "gt_def" ≔ >_def;
builtin "Nat.max" ≔ MAX;
builtin "MAX_def" ≔ MAX_def;
builtin "Nat.min" ≔ MIN;
builtin "MIN_def" ≔ MIN_def;
builtin "Nat.sub" ≔ -;
builtin "minus_def" ≔ -_def;
builtin "Nat.factorial" ≔ FACT;
builtin "FACT_def" ≔ FACT_def;
builtin "Nat.div" ≔ DIV;
builtin "DIV_def" ≔ DIV_def;
builtin "Nat.mod" ≔ MOD;
builtin "MOD_def" ≔ MOD_def;
builtin "EVEN" ≔ EVEN;
builtin "EVEN_def" ≔ EVEN_def;
builtin "ODD" ≔ ODD;
builtin "ODD_def" ≔ ODD_def;

// wf
builtin "WF" ≔ WF;
builtin "WF_def" ≔ WF_def;

// indtypes
builtin "NUMLEFT" ≔ NUMLEFT;
builtin "NUMLEFT_def" ≔ NUMLEFT_def;
builtin "NUMRIGHT" ≔ NUMRIGHT;
builtin "NUMRIGHT_def" ≔ NUMRIGHT_def;
builtin "ZRECSPACE" ≔ ZRECSPACE;
builtin "ZRECSPACE_def" ≔ ZRECSPACE_def;
builtin "FCONS" ≔ FCONS;
builtin "FCONS_def" ≔ FCONS_def;
builtin "recspace" ≔ recspace;
builtin "_mk_rec" ≔ _mk_rec;
builtin "_dest_rec" ≔ _dest_rec;
builtin "axiom_9" ≔ axiom_9;
builtin "axiom_10" ≔ axiom_10;
builtin "BOTTOM" ≔ BOTTOM;
builtin "BOTTOM_def" ≔ BOTTOM_def;
builtin "CONSTR" ≔ CONSTR;
builtin "CONSTR_def" ≔ CONSTR_def;

// option
builtin "Option" ≔ option;
builtin "_mk_option" ≔ _mk_option;
builtin "_dest_option" ≔ _dest_option;
builtin "axiom_13" ≔ axiom_13;
builtin "axiom_14" ≔ axiom_14;
builtin "NONE" ≔ NONE;
builtin "NONE_def" ≔ NONE_def;
builtin "SOME" ≔ SOME;
builtin "SOME_def" ≔ SOME_def;

// sum
builtin "SUM" ≔ Sum;
builtin "_mk_sum" ≔ _mk_sum;
builtin "_dest_sum" ≔ _dest_sum;
builtin "axiom_11" ≔ axiom_11;
builtin "axiom_12" ≔ axiom_12;
builtin "INL" ≔ INL;
builtin "INL_def" ≔ INL_def;
builtin "INR" ≔ INR;
builtin "INR_def" ≔ INR_def;

// lists
builtin "List" ≔ list;
builtin "_dest_list" ≔ _dest_list;
builtin "_mk_list" ≔ _mk_list;
builtin "axiom_15" ≔ axiom_15;
builtin "axiom_16" ≔ axiom_16;
builtin "NIL" ≔ NIL;
builtin "NIL_def" ≔ NIL_def;
builtin "CONS" ≔ CONS;
builtin "CONS_def" ≔ CONS_def;
builtin "APPEND" ≔ APPEND;
builtin "APPEND_def" ≔ APPEND_def;
builtin "REVERSE" ≔ REVERSE;
builtin "REVERSE_def" ≔ REVERSE_def;
builtin "LENGTH" ≔ LENGTH;
builtin "LENGTH_def" ≔ LENGTH_def;
builtin "MAP" ≔ MAP;
builtin "MAP_def" ≔ MAP_def;
builtin "BUTLAST" ≔ BUTLAST;
builtin "BUTLAST_def" ≔ BUTLAST_def;
builtin "ALL" ≔ ALL;
builtin "ALL_def" ≔ ALL_def;
builtin "PAIRWISE" ≔ PAIRWISE;
builtin "PAIRWISE_def" ≔ PAIRWISE_def;
builtin "FILTER" ≔ FILTER;
builtin "FILTER_def" ≔ FILTER_def;
builtin "MEM" ≔ MEM;
builtin "MEM_def" ≔ MEM_def;
builtin "REPLICATE" ≔ REPLICATE;
builtin "REPLICATE_def" ≔ REPLICATE_def;
builtin "ITLIST" ≔ ITLIST;
builtin "ITLIST_def" ≔ ITLIST_def;
builtin "HD" ≔ HD;
builtin "HD_def" ≔ HD_def;
builtin "TL" ≔ TL;
builtin "TL_def" ≔ TL_def;
builtin "NULL" ≔ NULL;
builtin "NULL_def" ≔ NULL_def;
builtin "EX" ≔ EX;
builtin "EX_def" ≔ EX_def;
builtin "ALL2" ≔ ALL2;
builtin "ALL2_def" ≔ ALL2_def;
builtin "LAST" ≔ LAST;
builtin "LAST_def" ≔ LAST_def;
builtin "MAP2" ≔ MAP2;
builtin "MAP2_def" ≔ MAP2_def;
builtin "EL" ≔ EL;
builtin "EL_def" ≔ EL_def;
builtin "ASSOC" ≔ ASSOC;
builtin "ASSOC_def" ≔ ASSOC_def;
builtin "ZIP" ≔ ZIP;
builtin "ZIP_def" ≔ ZIP_def;
builtin "ALLPAIRS" ≔ ALLPAIRS;
builtin "ALLPAIRS_def" ≔ ALLPAIRS_def;
builtin "list_of_seq" ≔ list_of_seq;
builtin "list_of_seq_def" ≔ list_of_seq_def;
builtin "ITLIST2" ≔ ITLIST2;
builtin "ITLIST2_def" ≔ ITLIST2_def;

// char
builtin "CHAR" ≔ char;
builtin "_dest_char" ≔ _dest_char;
builtin "_mk_char" ≔ _mk_char;
builtin "axiom_17" ≔ axiom_17;
builtin "axiom_18" ≔ axiom_18;

// realax
builtin "DIST" ≔ dist;
builtin "DIST_def" ≔ dist_def;
builtin "is_nadd" ≔ is_nadd;
builtin "is_nadd_def" ≔ is_nadd_def;
builtin "nadd" ≔ nadd;
builtin "dest_nadd" ≔ dest_nadd;
builtin "mk_nadd" ≔ mk_nadd;
builtin "axiom_19" ≔ axiom_19;
builtin "axiom_20" ≔ axiom_20;

builtin "nadd_of_num" ≔ nadd_of_num;
builtin "nadd_of_num_def" ≔ nadd_of_num_def;
builtin "nadd_le" ≔ nadd_le;
builtin "nadd_le_def" ≔ nadd_le_def;
builtin "nadd_add" ≔ nadd_add;
builtin "nadd_add_def" ≔ nadd_add_def;
builtin "nadd_mul" ≔ nadd_mul;
builtin "nadd_mul_def" ≔ nadd_mul_def;
builtin "nadd_rinv" ≔ nadd_rinv;
builtin "nadd_rinv_def" ≔ nadd_rinv_def;
builtin "nadd_inv" ≔ nadd_inv;
builtin "nadd_inv_def" ≔ nadd_inv_def;
builtin "nadd_eq" ≔ nadd_eq;
builtin "nadd_eq_def" ≔ nadd_eq_def;

builtin "hreal" ≔ hreal;
builtin "mk_hreal" ≔ mk_hreal;
builtin "dest_hreal" ≔ dest_hreal;
builtin "axiom_21" ≔ axiom_21;
builtin "axiom_22" ≔ axiom_22;

builtin "hreal_of_num" ≔ hreal_of_num;
builtin "hreal_of_num_def" ≔ hreal_of_num_def;
builtin "hreal_add" ≔ hreal_add;
builtin "hreal_add_def" ≔ hreal_add_def;
builtin "hreal_mul" ≔ hreal_mul;
builtin "hreal_mul_def" ≔ hreal_mul_def;
builtin "hreal_le" ≔ hreal_le;
builtin "hreal_le_def" ≔ hreal_le_def;
builtin "hreal_inv" ≔ hreal_inv;
builtin "hreal_inv_def" ≔ hreal_inv_def;

builtin "treal_of_num" ≔ treal_of_num;
builtin "treal_of_num_def" ≔ treal_of_num_def;
builtin "treal_le" ≔ treal_le;
builtin "treal_le_def" ≔ treal_le_def;
builtin "treal_eq" ≔ treal_eq;
builtin "treal_eq_def" ≔ treal_eq_def;
builtin "treal_add" ≔ treal_add;
builtin "treal_add_def" ≔ treal_add_def;
builtin "treal_mul" ≔ treal_mul;
builtin "treal_mul_def" ≔ treal_mul_def;
builtin "treal_inv" ≔ treal_inv;
builtin "treal_inv_def" ≔ treal_inv_def;
builtin "treal_neg" ≔ treal_neg;
builtin "treal_neg_def" ≔ treal_neg_def;

builtin "Real" ≔ Real;
builtin "mk_real" ≔ mk_real;
builtin "dest_real" ≔ dest_real;
builtin "axiom_23" ≔ axiom_23;
builtin "axiom_24" ≔ axiom_24;

builtin "real_le" ≔ real_le;
builtin "real_le_def" ≔ real_le_def;
builtin "real_add" ≔ real_add;
builtin "real_add_def" ≔ real_add_def;
builtin "real_mul" ≔ real_mul;
builtin "real_mul_def" ≔ real_mul_def;
builtin "real_inv" ≔ real_inv;
builtin "real_inv_def" ≔ real_inv_def;
builtin "real_neg" ≔ real_neg;
builtin "real_neg_def" ≔ real_neg_def;
builtin "real_of_num" ≔ real_of_num;
builtin "real_of_num_def" ≔ real_of_num_def;
builtin "real_pow" ≔ real_pow;
builtin "real_pow_def" ≔ real_pow_def;
builtin "real_abs" ≔ real_abs;
builtin "real_abs_def" ≔ real_abs_def;
builtin "real_div" ≔ real_div;
builtin "real_div_def" ≔ real_div_def;
builtin "real_sub" ≔ real_sub;
builtin "real_sub_def" ≔ real_sub_def;
builtin "real_ge" ≔ real_ge;
builtin "real_ge_def" ≔ real_ge_def;
builtin "real_gt" ≔ real_gt;
builtin "real_gt_def" ≔ real_gt_def;
builtin "real_lt" ≔ real_lt;
builtin "real_lt_def" ≔ real_lt_def;
builtin "real_max" ≔ real_max;
builtin "real_max_def" ≔ real_max_def;
builtin "real_min" ≔ real_min;
builtin "real_min_def" ≔ real_min_def;
builtin "real_sgn" ≔ real_sgn;
builtin "real_sgn_def" ≔ real_sgn_def;
builtin "SQRT_HOL" ≔ sqrt;
builtin "SQRT_def" ≔ sqrt_def;
builtin "real_mod" ≔ real_mod;
builtin "real_mod_def" ≔ real_mod_def;

// integers
builtin "Int" ≔ int;
builtin "real_of_int" ≔ real_of_int;
builtin "int_of_real" ≔ int_of_real;
builtin "integer" ≔ integer;
builtin "integer_def" ≔ integer_def;
builtin "axiom_25" ≔ axiom_25;
builtin "axiom_26" ≔ axiom_26;
builtin "int_of_num" ≔ int_of_num;
builtin "int_of_num_def" ≔ int_of_num_def;
builtin "int_le" ≔ int_le;
builtin "int_le_def" ≔ int_le_def;
builtin "int_lt" ≔ int_lt;
builtin "int_lt_def" ≔ int_lt_def;
builtin "int_ge" ≔ int_ge;
builtin "int_ge_def" ≔ int_ge_def;
builtin "int_gt" ≔ int_gt;
builtin "int_gt_def" ≔ int_gt_def;
builtin "int_neg" ≔ int_neg;
builtin "int_neg_def" ≔ int_neg_def;
builtin "int_add" ≔ int_add;
builtin "int_add_def" ≔ int_add_def;
builtin "int_sub" ≔ int_sub;
builtin "int_sub_def" ≔ int_sub_def;
builtin "int_mul" ≔ int_mul;
builtin "int_mul_def" ≔ int_mul_def;
builtin "int_abs" ≔ int_abs;
builtin "int_abs_def" ≔ int_abs_def;
builtin "int_sgn" ≔ int_sgn;
builtin "int_sgn_def" ≔ int_sgn_def;
builtin "int_max" ≔ int_max;
builtin "int_max_def" ≔ int_max_def;
builtin "int_min" ≔ int_min;
builtin "int_min_def" ≔ int_min_def;
builtin "int_pow" ≔ int_pow;
builtin "int_pow_def" ≔ int_pow_def;
builtin "div" ≔ div;
builtin "div_def" ≔ div_def;
builtin "rem" ≔ rem;
builtin "rem_def" ≔ rem_def;
builtin "int_divides" ≔ int_divides;
builtin "int_divides_def" ≔ int_divides_def;
builtin "int_coprime" ≔ int_coprime;
builtin "int_coprime_def" ≔ int_coprime_def;
builtin "int_gcd" ≔ int_gcd;
builtin "int_gcd_def" ≔ int_gcd_def;
builtin "int_lcm" ≔ int_lcm;
builtin "int_lcm_def" ≔ int_lcm_def;

// sets
builtin "IN" ≔ IN;
builtin "IN_def" ≔ IN_def;
builtin "EMPTY" ≔ EMPTY;
builtin "EMPTY_def" ≔ EMPTY_def;
builtin "INSERT" ≔ INSERT;
builtin "INSERT_def" ≔ INSERT_def;
builtin "UNIV_def" ≔ UNIV_def;
builtin "UNIV" ≔ UNIV;
builtin "GSPEC" ≔ GSPEC;
builtin "GSPEC_def" ≔ GSPEC_def;
builtin "SETSPEC" ≔ SETSPEC;
builtin "SETSPEC_def" ≔ SETSPEC_def;
builtin "SUBSET" ≔ SUBSET;
builtin "SUBSET_def" ≔ SUBSET_def;
builtin "UNION" ≔ UNION;
builtin "UNION_def" ≔ UNION_def;
builtin "INTER" ≔ INTER;
builtin "INTER_def" ≔ INTER_def;
builtin "UNIONS" ≔ UNIONS;
builtin "UNIONS_def" ≔ UNIONS_def;
builtin "INTERS" ≔ INTERS;
builtin "INTERS_def" ≔ INTERS_def;
builtin "IMAGE" ≔ IMAGE;
builtin "IMAGE_def" ≔ IMAGE_def;
builtin "DIFF" ≔ DIFF;
builtin "DIFF_def" ≔ DIFF_def;
builtin "DELETE" ≔ DELETE;
builtin "DELETE_def" ≔ DELETE_def;
builtin "PSUBSET" ≔ PSUBSET;
builtin "PSUBSET_def" ≔ PSUBSET_def;
builtin "DISJOINT" ≔ DISJOINT;
builtin "DISJOINT_def" ≔ DISJOINT_def;
builtin "SING" ≔ SING;
builtin "SING_def" ≔ SING_def;

// finite sets
builtin "FINITE" ≔ FINITE;
builtin "FINITE_def" ≔ FINITE_def;
builtin "ITSET" ≔ ITSET;
builtin "ITSET_def" ≔ ITSET_def;
builtin "CARD" ≔ CARD;
builtin "CARD_def" ≔ CARD_def;
builtin "dimindex" ≔ dimindex;
builtin "dimindex_def" ≔ dimindex_def;
builtin "set_of_list" ≔ set_of_list;
builtin "set_of_list_def" ≔ set_of_list_def;
builtin "list_of_set" ≔ list_of_set;
builtin "list_of_set_def" ≔ list_of_set_def;

// finite_image
builtin "dotdot" ≔ …;
builtin "dotdot_def" ≔ …_def;
builtin "finite_image" ≔ finite_image;
builtin "finite_index" ≔ finite_index;
builtin "dest_finite_image" ≔ dest_finite_image;
builtin "axiom_27" ≔ axiom_27;
builtin "axiom_28" ≔ axiom_28;

// cart + iterate
builtin "cart" ≔ cart;
builtin "mk_cart" ≔ mk_cart;
builtin "dest_cart" ≔ dest_cart;
builtin "axiom_29" ≔ axiom_29;
builtin "axiom_30" ≔ axiom_30;
builtin "neutral" ≔ neutral;
builtin "neutral_def" ≔ neutral_def;
builtin "support" ≔ support;
builtin "support_def" ≔ support_def;
builtin "iterate" ≔ iterate;
builtin "iterate_def" ≔ iterate_def;
builtin "sum" ≔ sum;
builtin "sum_def" ≔ sum_def;
builtin "dollar" ≔ ﹩;
builtin "dollar_def" ≔ ﹩_def;

// finite_sum
builtin "finite_sum" ≔ finite_sum;
builtin "mk_finite_sum" ≔ mk_finite_sum;
builtin "dest_finite_sum" ≔ dest_finite_sum;
builtin "axiom_31" ≔ axiom_31;
builtin "axiom_32" ≔ axiom_32;

// finite_diff
builtin "finite_diff" ≔ finite_diff;
builtin "mk_finite_diff" ≔ mk_finite_diff;
builtin "dest_finite_diff" ≔ dest_finite_diff;
builtin "axiom_33" ≔ axiom_33;
builtin "axiom_34" ≔ axiom_34;

// finite_prod
builtin "finite_prod" ≔ finite_prod;
builtin "mk_finite_prod" ≔ mk_finite_prod;
builtin "dest_finite_prod" ≔ dest_finite_prod;
builtin "axiom_35" ≔ axiom_35;
builtin "axiom_36" ≔ axiom_36;

// tybit0
builtin "tybit0" ≔ tybit0;
builtin "_mk_tybit0" ≔ _mk_tybit0;
builtin "_dest_tybit0" ≔ _dest_tybit0;
builtin "axiom_37" ≔ axiom_37;
builtin "axiom_38" ≔ axiom_38;

// tybit1
builtin "tybit1" ≔ tybit1;
builtin "_mk_tybit1" ≔ _mk_tybit1;
builtin "_dest_tybit1" ≔ _dest_tybit1;
builtin "axiom_39" ≔ axiom_39;
builtin "axiom_40" ≔ axiom_40;
