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
Changes `A → Prop` to `Set A`
-/
def toSet (e : Expr) : MetaM Expr := Meta.transform e (post := fun e => do
    if let .forallE _ d (.sort .zero) _ := e then
      if let some e' ← observing? (mkAppM ``Set #[d]) then return .done e'
    return .continue)

/--
Pretty prints an expression `e` using the list of options below.
-/
def pprint_with (style : Options → Options) (e : Expr) : TermElabM String := do
  return toString ((Format.line ++  (← withOptions style (ppExpr e))).nest 2)

def styles : List (Options → Options) := [
    fun o => (o.setBool `pp.funBinderTypes true).setBool `pp.analyze true
      |>.setBool `pp.numericTypes true |>.setBool `pp.proofs true, --prints readable style
    fun o => (o.setBool `pp.explicit true).setBool `pp.funBinderTypes true
      |>.setBool `pp.numericTypes true |>.setBool `pp.proofs true, -- prints all explicits
    fun o => o.setBool `pp.all true] -- prints everything

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
      let s ← pprint_with style new
      if ← are_defEq original s then
        return some (s, i)
    return none

def create_file : CommandElabM Unit := do
  let fallbacks ←  IO.mkRef 0
  let unchecked ←  IO.mkRef (#[] : Array Name)
  let sorted ← get_oarray
  let lines ← liftTermElabM <| withoutModifyingEnv do
    addInstance ``Classical.propDecidable .local 10000
    sorted.toList.mapM fun (_, n) => do
      let info ← getConstInfo n
      let some pf := info.value? (allowOpaque := true) | throwError "{n} has no proof"
      let inst ← ppExpr pf.appArg!
      let .const thm _ := pf.getAppFn | throwError "{n} is not an application"
      let setTy ← toSet info.type
      let stmt ← match (← get_stmt? setTy info.type) with
        | some (s, i) => do if i > 0 then fallbacks.modify (· + 1)
                         pure s
        | none => do unchecked.modify (·.push n); pprint_with styles.head! setTy
      return s!"theorem {n.getString!} : {stmt} := @{thm} {inst}"
  logInfo m!"{lines.length} theorems, {← fallbacks.get} printed with explicit arguments"
  unless (← unchecked.get).isEmpty do
    logWarning m!"statements that do not elaborate back: {← unchecked.get}"
  let header := "import HolLightLean.hol_opam\n\nset_option linter.unusedVariables false\nset_option linter.style.longLine false\nset_option linter.style.nameCheck false
                \n\nattribute [local instance 10000] Classical.propDecidable"
  IO.FS.writeFile "thms_export.lean" (String.intercalate "\n\n" (header :: lines))

#exit
set_option maxHeartbeats 0 in
set_option format.width 100 in
run_cmd do create_file
