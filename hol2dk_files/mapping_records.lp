/* Map from dk/lp symbols on the right to Lean expressions on the left:
The declarations of dk/lp symbols are removed and their occurrences are
replaced by the given Lean expressions. */

// builtin "<lean_exp>" = <lp_symbol> 

// primitive types
builtin "Type" ≔ Set;
builtin "el" ≔ el;
builtin "Prop" ≔ bool;
builtin "arr" ≔ fun;
// connectives with native Lean syntax: mapped to transparent defs that are
// definitionally equal to the syntax the exporter emits when they are
// saturated (see Hol/HOLTheory.lean). They are NOT fields of HOLTheory.
builtin "imp" ≔ ⇒;
builtin "FORALL" ≔ ∀;
//builtin "EXISTS" ≔ ∃;
