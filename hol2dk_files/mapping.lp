/* Map from dk/lp symbols on the right to Lean expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Lean expressions. */

// builtin "<lean_exp>" = <lp_symbol> 

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

builtin "Not" ≔ ¬; //propositional negation
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
 builtin "Nat.zero" ≔ _0;
builtin "Nat.succ" ≔ SUC;


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

// NUMPAIR, NUMSUM, NUMFST and NUMSND
builtin "NUMPAIR" ≔ NUMPAIR;
builtin "NUMPAIR_def" ≔ NUMPAIR_def;
builtin "NUMSUM" ≔ NUMSUM;
builtin "NUMSUM_def" ≔ NUMSUM_def;
builtin "NUMFST" ≔ NUMFST;
builtin "NUMFST_def" ≔ NUMFST_def;
builtin "NUMSND" ≔ NUMSND;
builtin "NUMSND_def" ≔ NUMSND_def;

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
builtin "ZBOT" ≔  ZBOT;
builtin "ZBOT_def" ≔  ZBOT_def;
builtin "ZCONSTR" ≔  ZCONSTR;
builtin "ZCONSTR_def" ≔  ZCONSTR_def;
builtin "INJN" ≔  INJN;
builtin "INJN_def" ≔  INJN_def;
builtin "INJA" ≔  INJA;
builtin "INJA_def" ≔  INJA_def;
builtin "INJF" ≔  INJF;
builtin "INJF_def" ≔  INJF_def;
builtin "INJP" ≔  INJP;
builtin "INJP_def" ≔  INJP_def;
builtin "FNIL" ≔  FNIL;
builtin "FNIL_def" ≔  FNIL_def;

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
builtin "OUTL" ≔ OUTL;
builtin "OUTL_def" ≔ OUTL_def;
builtin "OUTR" ≔ OUTR;
builtin "OUTR_def" ≔ OUTR_def;


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
/* builtin "ALL2" ≔ ALL2;
builtin "ALL2_def" ≔ ALL2_def; */
builtin "LAST" ≔ LAST;
builtin "LAST_def" ≔ LAST_def;
/* builtin "MAP2" ≔ MAP2;
builtin "MAP2_def" ≔ MAP2_def; */
/* builtin "EL" ≔ EL;
builtin "EL_def" ≔ EL_def; */
builtin "ASSOC" ≔ ASSOC;
builtin "ASSOC_def" ≔ ASSOC_def;
/* builtin "ZIP" ≔ ZIP;
builtin "ZIP_def" ≔ ZIP_def;
builtin "ALLPAIRS" ≔ ALLPAIRS;
builtin "ALLPAIRS_def" ≔ ALLPAIRS_def;
builtin "list_of_seq" ≔ list_of_seq;
builtin "list_of_seq_def" ≔ list_of_seq_def;
builtin "ITLIST2" ≔ ITLIST2;
builtin "ITLIST2_def" ≔ ITLIST2_def; */

// char
builtin "CHAR" ≔ char;
/* 
builtin "_dest_char" ≔ _dest_char;
builtin "_mk_char" ≔ _mk_char;
builtin "axiom_17" ≔ axiom_17;
builtin "axiom_18" ≔ axiom_18; 
*/

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

builtin "real" ≔ Real;
builtin "mk_real" ≔ mk_real;
builtin "dest_real" ≔ dest_real;
builtin "axiom_23" ≔ axiom_23;
builtin "axiom_24" ≔ axiom_24;