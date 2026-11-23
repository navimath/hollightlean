import HolLightLean.hol_opam
open Lean Elab Command Meta

set_option linter.style.longLine false

/--
From the opam environment, the function collects al `hol_` prefixed theorems
and returns an ordered array respect to their `thm_` counterparts.
-/
def get_oarray : CommandElabM (Array (ℕ × Name)) := do
  let env ← getEnv
  let ns := `HolLightLean.hol_opam
  let names := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match n with
    | .str p s => if p == ns && s.startsWith "hol_" then acc.push n else acc
    | _ => acc
  let line (n : Name) : CommandElabM Nat := do
    let thm := ns.str ("thm_" ++ (n.getString!.drop 4).toString)
    return (← findDeclarationRanges? thm).map (·.range.pos.line) |>.getD 0
  let opair ← names.mapM fun n => return (← line n, n)
  return opair.qsort (·.1 < ·.1)

/--
Recursively turns function types from `A → Prop` to `Set A`.
-/
partial def toSet (e : Expr) : MetaM Expr := Meta.transform e (post := fun e => do
    match e with
    | .forallE _ d (.sort .zero) _ => -- A → Prop ⇒ Set A
      if let some e' ← observing? (mkAppM ``Set #[d]) then return .done e'
      return .continue
    | .forallE n d b bi => -- A → (... → Prop)
       if b.hasLooseBVars || !b.getForallBody.isProp then return .continue
       return .done (.forallE n d (← toSet b) bi)
    | _ => return .continue)

/--
Pretty prints an expression `e` using the list of options below.
-/
def pprint_with (style : Options → Options) (e : Expr) : TermElabM String := do
  return toString ((Format.line ++  (← withOptions style (ppExpr e))).nest 2)

/--
This function will substitude operators that need explicit type ascriptions:
First, in `toTyAsc` it detects whether certain applications constants appear,
for instance `∅`, and returns instead `tyAsc (Set α) ∅` that delaborates
into `(∅ : Set α)` using `delabTyAsc`.
-/
def tyAsc (α : Sort u) (a : α) : α := a

/-- Wraps `e` into `tyAsc (type of e) e`. -/
def mkTyAsc (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  return mkApp2 (.const ``tyAsc [← getLevel ty]) ty e

/--
Wraps every fully applied coercion `↑x` (any `@[coe]` function) into `tyAsc`,
so that it prints as `(↑x : ℝ)` and fixes the target type of the coercion.
A coercion already wrapped by `toTyAsc` (e.g. `SetLike.coe`) is not wrapped twice.
-/
def coeTyAsc (e : Expr) : MetaM Expr := transform e (post := fun e => do
  if e.isAppOfArity ``tyAsc 2 && (e.getArg! 1).isAppOfArity ``tyAsc 2 then
    return .done (e.getArg! 1)
  if let .const fn _ := e.getAppFn then
    if let some info ← getCoeFnInfo? fn then
      if e.getAppNumArgs == info.numArgs then
        return .done (← mkTyAsc e)
  return .continue)

/--
A printing style: pretty printer options plus a transformation of the
statement applied before printing.
-/
structure Style where
  name : String
  opts : Options → Options
  prep : Expr → MetaM Expr := pure

def readableOpts (analyze : Bool) (o : Options) : Options :=
  (o.setBool `pp.funBinderTypes true).setBool `pp.analyze analyze
    |>.setBool `pp.numericTypes true |>.setBool `pp.proofs true

/--
Styles tried in order; the first one that elaborates back is used.
`pp.analyze` is last: it may print implicit arguments as `(α := _)`,
which prevents notations such as `=` or `∈` from being used.
-/
def styles : List Style := [
    { name := "plain", opts := readableOpts false },
    { name := "coercion ascriptions", opts := readableOpts false, prep := coeTyAsc },
    { name := "pp.analyze", opts := readableOpts true }]
/-  fun o => (o.setBool `pp.explicit true).setBool `pp.funBinderTypes true
      |>.setBool `pp.numericTypes true |>.setBool `pp.proofs true, -- prints all explicits
    fun o => o.setBool `pp.all true -- prints everything -/

/--
Checks whether the output of `pprint_with` is still definitionally equal to the original expression.
-/
def are_defEq (ty : Expr) (s : String) : TermElabM Bool := withoutModifyingState do
    let .ok stx := Parser.runParserCategory (← getEnv) `term s | return false
    Core.resetMessageLog
    try
      Term.withoutErrToSorry do
        let e ← Term.elabType stx
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasMVar || (← MonadLog.hasErrors) then return false
        isDefEq e ty
      catch _ => return false

/--
Takes the original type expression, the new version and checks whether
they are defEq after `new` has been pretty printed to a convenient style.
In case it fails, it returns `none` as one does not have a printable statement.
-/
def get_stmt? (new original : Expr) : TermElabM (Option (String × ℕ)) := do
    for (style, i) in styles.zipIdx do
      let s ← pprint_with style.opts (← style.prep new)
      if ← are_defEq original s then
        return some (s, i)
    return none

open PrettyPrinter Delaborator SubExpr in
@[delab app.abs]
def absParen : Delab := do
  guard ((← getExpr).getAppNumArgs == 4)     -- @abs α inst₁ inst₂ x
  let a ← withAppArg delab
  `(|($a)|)

/--
Check if a term is of the form of the if statements
and in that case changes the term by `tyAsc ty e` that delaborates into (e : ty)
-/
def toTyAsc (e : Expr) : MetaM Expr := transform e (post := fun e => do
  if e.isAppOfArity ``EmptyCollection.emptyCollection 2
    || e.isAppOfArity ``Set.univ 1
    || e.isAppOfArity ``SetLike.coe 4
    || e.isAppOfArity ``List.nil 1 then
      return .done (← mkTyAsc e)
  return .continue
)

open PrettyPrinter Delaborator SubExpr in
/--
tyAsc delaborator when appearing in applications
-/
@[delab app.tyAsc]
def delabTyAsc : Delab := do
  --guard ((← getExpr).getAppNumArgs == 2) should not be needed
  let ty ← withNaryArg 0 delab
  let a ← withNaryArg 1 delab
  `(($a : $ty))

def create_file : CommandElabM Unit := do
  let counts ←  IO.mkRef (Array.replicate styles.length 0)
  let unchecked ←  IO.mkRef (#[] : Array Name)
  let sorted ← get_oarray
  let lines ← liftTermElabM <| withoutModifyingEnv do
    addInstance ``Classical.propDecidable .local 10000
    sorted.toList.mapM fun (_, n) => do
      let info ← getConstInfo n
      let some pf := info.value? (allowOpaque := true) | throwError "{n} has no proof"
      let inst ← ppExpr pf.appArg!
      let .const thm _ := pf.getAppFn | throwError "{n} is not an application"
      let setTy ← toTyAsc (← toSet info.type)
      let stmt ← match (← get_stmt? setTy info.type) with
        | some (s, i) => do counts.modify (·.modify i (· + 1))
                         pure s
        | none => do unchecked.modify (·.push n); pprint_with (readableOpts false) setTy
      return s!"theorem {n.getString!} : {stmt} := @{thm} {inst}"
  let perStyle := (styles.zip (← counts.get).toList).map fun (st, k) => s!"{st.name}: {k}"
  logInfo m!"{lines.length} theorems printed with style ({", ".intercalate perStyle})"
  unless (← unchecked.get).isEmpty do
    logWarning m!"statements that do not elaborate back: {← unchecked.get}"
  let header := "import HolLightLean.hol_opam\n\nset_option linter.unusedVariables false\nset_option linter.style.longLine false\nset_option linter.style.nameCheck false
                \n\nattribute [local instance 10000] Classical.propDecidable"
  IO.FS.writeFile "thms_export.lean" (String.intercalate "\n\n" (header :: lines))

#exit
set_option maxHeartbeats 0 in
set_option format.width 100 in
run_cmd do create_file
