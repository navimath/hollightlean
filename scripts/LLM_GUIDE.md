# Guide for LLM agents: exporting a HOL Light library to readable Lean theorems

You are an LLM agent helping a user of this repository (`HolLightLean`). **The user may not be a
programmer but assume they are mathematicians.** They only need to have installed `hol2dk`, `lambdapi` (the version with `param_stt_lean`) and
cloned this repository (See step §3). They may only tell you **which HOL Light library they want in Lean**
(for example `Library/binomial.ml`, `Library/prime.ml` or `Multivariate/vectors.ml`). Everything
else is your job: dumping, translating, extending the record, aligning, and generating the final
file of readable Lean theorems unless stated otherwise.

Read this whole file before you start. It describes the pipeline, the files involved, the
conventions to follow and the pitfalls already found.

---

## 0. How to work with the user

- **Who the user is.** Unless stated, assume a mathematician who probably knows basic Lean (reading statements,
  `theorem … := by …`, Mathlib names), but not necessarily programming or tooling (shell, `sed`,
  Makefiles, opam, Lean metaprogramming, HOL Light, Lambdapi). Talk mathematics and Lean freely. Explain tooling only as
  far as needed to follow what you are doing.
- Run the commands yourself. Show the user what step you are on, how long it may take, and the
  result.
- Ask the user about the **mathematical** choices: which Mathlib object a HOL constant should be
  aligned to when several are possible, how to treat junk values outside a domain, whether an
  alignment that you could not finish may stay as `sorry` (§6.6). Also ask before a long or large
  step (hours of CPU, tens of GB of disk). Do not ask them to fix tooling problems.
- **`sorry` policy (§6.6).** An alignment that is *true but too hard* may be closed with `sorry`,
  **only** together with a comment that gives the reason and the strategy you followed, and an
  entry in your final report. An alignment that is *false* (the HOL definition and the chosen Lean
  object differ) must **never** be closed with `sorry`: change the counterpart or keep the HOL
  meaning (§6.6 (a)), and explain the mismatch. Never use `admit`, a new `axiom` or `native_decide`
  to make an alignment build.
- Do not modify `complete.lean` or the `hol2dk_files/mapping.lp` route. For a new library you
  **append** fields to `HolLightLean/hol_theory_record.lean` and the matching values to
  `HolLightLean/hol_theory_inst.lean` (§5, §6). Never change or reorder the existing fields or
  their values. Write the alignment proofs in a **new** file (§6.2).
- Report honestly at the end: how many theorems were exported, how many constants were aligned to
  Lean/Mathlib, which ones were left unaligned (and why), which alignments are `sorry` (and why),
  and which statements could not be printed in readable form.

---

## 1. The big picture

```
HOL Light library (.ml)
   │  hol2dk dump-simp            (records every proof step while HOL Light runs)
   ▼
<base>.prf/.sig/.thm/...          (in $HOLLIGHT_DIR)
   │  hol2dk config + make split / make lp
   ▼
Lambdapi files (.lp)              (one per theorem + <base>_types/_terms/_axioms/_opam.lp)
   │  lambdapi export -o param_stt_lean     (mapping_records.lp, renaming_records.lp)
   ▼
Lean statements over a record     axiom thm_X [T : HOLTheory] : <statement using fields of T>
   │  + record fields for every HOL type/constant/definition       (HOLTheory, new fields appended)
   │  + an instance filling the fields with Lean/Mathlib objects   (HolTheoryInst, new values appended)
   │  + @[hol_readable HolTheoryInst] on each axiom → hol_X := thm_X HolTheoryInst, projections unfolded
   ▼
scripts/export_thms_repo.lean     pretty-prints every hol_X and checks it parses back
   ▼
thms_export.lean (or <lib>_export.lean): `theorem hol_X : <readable statement> := @thm_X Inst`
```

Key ideas:

1. **Parametrized translation.** With `-o param_stt_lean`, Lambdapi does not translate a HOL
   constant to a fixed Lean object. It translates it to a *field* of the Lean class `HOLTheory`
   (the class name `HOLTheory` and the variable name `T` are hard-coded in Lambdapi:
   `src/export/stt.ml`, `theory_class` / `class_var`). Every generated declaration takes
   `[T : HOLTheory]`. A symbol becomes a class field unless it is a local variable or is listed in
   the `--mapping` file.
2. **The record** (`HOLTheory`, file `HolLightLean/hol_theory_record.lean`) has one field per HOL
   type, constant, definition (`c_def`), type-definition axiom (`axiom_N`) and inference rule.
3. **The instance** (`HolTheoryInst`, file `HolLightLean/hol_theory_inst.lean`) fills each field
   with its Lean/Mathlib counterpart. Each `_def`/`axiom_N` field must be *proved* for that
   counterpart. That proof is the **alignment**.
4. **Readable theorems.** `thm_X HolTheoryInst` is a proof of the HOL theorem about the Lean
   objects. The `hol_readable` attribute (`HolLightLean/meta.lean`) unfolds the instance's
   projections, so `hol_eq (real_add x y) …` becomes `x + y = …`. The export script prints these
   statements, checks that each printed string elaborates back to the same statement, and writes
   them to a file.

Because the `thm_X` are axioms over an *arbitrary* `T`, they are justified by the translated HOL
proofs, which are also parametrized by `T` (optional check in §4.5). The instance is where the
Lean/Mathlib meaning comes in, and there everything is proved.

### 1.1 Why every type carries `[Nonempty A]`

Every generated statement and every record field quantifies over types as
`∀ {A : Type} [Nonempty A], …`. The record has `[ne_X : …]` fields for its type constructors, and
it has `instance … [Nonempty B] : Nonempty (A -> B)` at the top. The reasons:

- **Hilbert's ε needs it.** HOL Light's `@` (`ε`) is a total choice operator: `ε P` exists for every
  predicate `P` on every type. In Lean, the corresponding `Classical.epsilon` has type
  `{α : Sort u} → [Nonempty α] → (α → Prop) → α`: it can only be applied to a type known to be
  inhabited. Every HOL definition that uses `ε` (directly, or through `define`,
  `new_recursive_definition`, `GABS`, `COND`, …) therefore needs this hypothesis on its types.
- **HOL Light types are non-empty by construction.** `bool` and `ind` are inhabited, `A → B` is
  inhabited when `B` is, and `new_type_definition` only accepts a predicate together with a proof
  that it has a witness. So every HOL type is non-empty. The translation records this as the
  hypothesis `[Nonempty A]` on every type variable, and as the `ne_X` fields and instances for
  every type constructor. No HOL theorem becomes weaker: the hypothesis holds for every type HOL
  can talk about.
- **Why not `Type'`, as in the Rocq translation.** The Rocq side (hol2dk's Rocq export,
  `coq-hol-light`) interprets HOL types in `Record Type' := { type :> Type; el : type }`: a type
  bundled with a chosen element, plus `Canonical` declarations (`bool'`, `Prop'`, `arr`, …) so that
  Rocq finds the bundle of `nat`, `A -> B`, … automatically. Lean has no direct, commonly used
  equivalent of canonical structures. With `Type'`, each Lean/Mathlib type would need an explicit
  wrapper (`nat' : Type'`, `arr a b` for function types, `lambda'` for functions), and coercions
  `↥A` would appear everywhere. The statements would be about the wrappers, not about `ℕ`, `ℝ`,
  `A → B`, so a Mathlib user could not apply them directly. This was tried; see the commented-out
  `Type'` experiment at the end of `HolLightLean/meta.lean`. `[Nonempty A]` avoids all of this:
  - it is a **class**, so instance resolution finds it automatically (Mathlib provides instances
    for `ℕ`, `ℝ`, `List A`, `Set A`, functions, products, …);
  - it is a **`Prop`**, so it carries no data. Unlike `el`, no particular element is chosen, any
    two instances are equal (proof irrelevance), and there are no instance diamonds;
  - it is **instance-implicit**, so the readable theorems are stated on plain Lean types, with at
    most a binder `[inst : Nonempty A]`.

What this means for your work:

- each **new HOL type** gets a field `[ne_X : …]` and an `instance` (§5.2), and its value in the
  instance needs a proof of `Nonempty` (`inferInstance`, or `⟨witness⟩`, §6.4);
- write alignment definitions with the same binders as the export, `{A : Type*} [Nonempty A]`,
  even when the Lean definition does not use the hypothesis;
- `[inst : Nonempty A]` binders in the readable statements are expected. They come from HOL's
  semantics, not from the alignment.

---

## 2. Files of this repository you will use

| File | Role |
|---|---|
| `hol2dk_files/Makefile` | Makefile with the Lean targets (`lean`, `olean`, `lean-thms`). `hol2dk config` links the one from `$HOL2DK_DIR`; replace it with this one if `make help` does not list Lean targets. |
| `hol2dk_files/encoding.lp` | Symbols of the simple-type-theory encoding (normally taken from `$HOL2DK_DIR/encoding.lp`). |
| `hol2dk_files/mapping_records.lp` | Mapping for the **parametrized** export: only primitive types and `imp`/`FORALL` are mapped to fixed Lean objects; everything else becomes a field. **Do not modify** (§4.4). |
| `hol2dk_files/renaming_records.lp` | Renaming for the parametrized export (e.g. `=` → `hol_eq`, `ε` → `epsilon`, `+` on nat → `Nat_add`). The produced names **must be the record's field names**. **May need new entries** for a new library (§4.4). |
| `hol2dk_files/mapping.lp`, `renaming.lp` | Mapping for the **non-parametrized** route (`scripts/reproduce`, `complete.lean`). Not used by the record route. |
| `hol2dk_files/lean_thms.lean.in` | Old template of the readable-theorem generator, used by `make lean-thms`. Prefer `scripts/export_thms_repo.lean`. |
| `HolLightLean/hol_theory_record.lean` | The class `HOLTheory` (standard library `hol.ml`), plus `Nonempty` instances for its types. |
| `HolLightLean/hol_theory_inst.lean` | `noncomputable instance HolTheoryInst : HOLTheory`, the alignments of `hol.ml`. |
| `HolLightLean/conectors.lean`, `meta.lean`, `up_to_real.lean`, `real_align.lean`, `after_real.lean` | The alignment definitions and proofs (Lean definitions, `X_def` theorems, tactics). |
| `HolLightLean/hol_opam.lean` | The `thm_X [T : HOLTheory]` axioms of `hol.ml`, each tagged `@[hol_readable HolTheoryInst]`. |
| `scripts/export_thms_repo.lean` | Generator of the readable file (`thms_export.lean`). |
| `scripts/reproduce` | Automated non-parametrized pipeline (mappings only, no record). Useful to see pinned versions and the dump commands. |

---

## 3. Before starting: check the tools

Run and check:

```bash
hol2dk | head -5                    # hol2dk installed
lambdapi export --help 2>&1 | grep param_stt_lean   # MUST print a line: records-capable lambdapi
lean --version; lake --version      # elan toolchain
echo $HOLLIGHT_DIR $HOL2DK_DIR      # both set, absolute paths
ls $HOL2DK_DIR/encoding.lp $HOL2DK_DIR/Makefile
cd <repo> && lake exe cache get && lake build && lake build HolLightLean.hol_opam
```

- If `HOLLIGHT_DIR` / `HOL2DK_DIR` are unset, see the README ("Environment variables").
- HOL Light must be **patched** by hol2dk (`cd $HOLLIGHT_DIR && hol2dk patch`; there is a
  `fusion-bak.ml` once patched) and rebuilt (`make`).
- Use `<repo>` below for the absolute path of this repository and `<lib>` for a short lowercase
  name of the chosen library (e.g. `binomial`).

---

## 4. Dump and translate the library

### 4.1 Choose the `.ml` file and estimate the cost

- A library that **depends on `hol.ml`** (anything in `Library/`, `Multivariate/`, …): dump it
  with `hol2dk dump-simp`. The dump contains `hol.ml` **and** the library. The new constants are
  the ones that are not already fields of `HOLTheory`.
- A **fragment of `hol.ml`** (like `hol_up_real.ml` in the README): use
  `hol2dk dump-simp-before-hol`. It must contain `hol.ml` at least up to `loads "fusion.ml";;`.
- If the library has no single entry file, create `$HOLLIGHT_DIR/<lib>.ml` containing
  `needs "Library/xxx.ml";;` lines (one per file to load).
- Warn the user about cost: `hol.ml` alone takes minutes and a few GB. `Multivariate/make_complex.ml`
  takes hours and >100 GB (see the hol2dk README, "Performances"). Start with the smallest file
  that contains what the user wants.

### 4.2 Dump

```bash
cd $HOLLIGHT_DIR                 # mandatory: theorem names are computed relative to this dir
hol2dk dump-simp Library/<file>.ml          # or: hol2dk dump-simp-before-hol <fragment>.ml
```

This produces `<file>.{prf,sig,thm,pos,use,nbp}` next to the `.ml` file. Below, `<base>` is the
file name without `.ml` (e.g. `binomial`).

### 4.3 Configure a work directory and generate Lambdapi files

Use a fresh directory **outside** `$HOLLIGHT_DIR` and outside this repository, e.g.
`~/hol2lean/<lib>`:

```bash
mkdir -p ~/hol2lean/<lib> && cd ~/hol2lean/<lib>
cp <repo>/hol2dk_files/mapping_records.lp <repo>/hol2dk_files/renaming_records.lp .
cp <repo>/HolLightLean/hol_theory_record.lean HOLTheory.lean
hol2dk config Library/<file>.ml <Root> HOLTheory.lean --mapping ./mapping_records.lp --renaming ./renaming_records.lp
make help        # if no "lean targets" line: rm Makefile && cp <repo>/hol2dk_files/Makefile .
make split
make -j$(nproc) lp               # one .lp file per theorem, plus <base>_types/_terms/_axioms
make <base>_opam.lp              # all theorem statements, as axioms, in one file
make tvs                         # <base>.tvs: number of type variables of each constant
make <base>_theory.lp            # every type, constant, definition and axiom of the dump
```

- `<Root>` is the Lean library name of the work directory (e.g. `HolBinomial`), CamelCase.
- The `./` before the mapping files is needed so that the Makefile does not try to translate them.
- `make lp` is the long step. Large proofs: see `BIG_FILES` and `MAX_PROOF` in the hol2dk README.

### 4.4 `mapping_records.lp` vs `renaming_records.lp`: which one may change

Both files have lines `builtin "<Lean text>" ≔ <Lambdapi symbol>;`, but they do very different
things:

- **`mapping_records.lp`: do not modify it.** A *mapped* symbol is replaced by a fixed Lean
  expression and is **not** a field of `HOLTheory`. This file maps only the structural part of the
  encoding of HOL: `Set` (HOL types) → `Type`, `el`, `bool` → `Prop`, `fun` → `→`, and `⇒`, `∀`,
  which become Lean's own `→` and `∀`. The whole parametrization relies on **every other symbol**
  being a field. Mapping a library constant here would hard-wire it to a Lean object: it would
  bypass the record and the instance, so its alignment would never be proved, and the generated
  files would no longer match the record. A new library never needs a new mapping.
- **`renaming_records.lp`: may need new entries.** A *renamed* symbol is still a field. Only the
  **name printed** in Lean changes. A new library needs an entry for every new symbol whose
  Lambdapi name is not a valid Lean identifier: HOL infix operators such as `++`, `<<=`, `%`,
  `$$`, `===`. The convention is a word-like name, with its `_def` companion, e.g.
  `builtin "addadd" ≔ ++;` and `builtin "addadd_def" ≔ ++_def;`. The file already contains entries
  for many operators of `Library/` and `Multivariate/`. The Lean name you choose **is** the record
  field name (§5.2).

To list the symbols of the dump that still need a renaming entry (run in the work directory after
`make lp`):

```bash
grep -oE '^(constant )?symbol [^ :]+' <base>_types.lp <base>_terms.lp <base>_axioms.lp \
  | awk '{print $NF}' | grep -vE "^[A-Za-z_][A-Za-z0-9_']*$" | sort -u > symbols.txt
cat mapping_records.lp renaming_records.lp | grep -oE '≔ [^;]+;' | sed -E 's/≔ (.*);/\1/' \
  | sort -u > covered.txt
comm -23 symbols.txt covered.txt            # each line needs a renaming entry
```

(On `hol.ml` this list is empty.) Add the entries to the work-directory copy of
`renaming_records.lp`, export (§4.5), and copy the new lines into
`<repo>/hol2dk_files/renaming_records.lp` so that the next library reuses them. Never change or
remove the existing entries: the `hol.ml` part of the record depends on them.

### 4.5 Export to Lean with `param_stt_lean`

Only two exports are needed for readable theorems: the theory file (to see the new fields) and the
`_opam` file (the statements).

```bash
OPTS="--encoding $HOL2DK_DIR/encoding.lp --mapping mapping_records.lp --renaming renaming_records.lp --arities <base>.tvs"
lambdapi export -o stt_lean       $OPTS <base>_theory.lp > <base>_theory.lean    # declarations, as plain axioms
lambdapi export -o param_stt_lean $OPTS <base>_opam.lp   > <base>_opam.lean      # thm_X [T : HOLTheory] : ...
```

(If a `.tvs` file named after the theory file was produced instead, use that one for the theory
export. Run `ls *.tvs` to check.)

**Optional, full check of the proofs** (all theorems proved for any `T`, which justifies the
`thm_X` axioms). This is large (one Lean file per theorem; ~16k files for `hol.ml`). Do it only if
the user agrees:

```bash
sed -i 's/-o stt_lean/-o param_stt_lean/' Makefile     # local copy only, never in the repo
make -j$(nproc) lean
# lakefile.toml: see README §3 (Mathlib not required for this check); then
ulimit -s unlimited; make olean
```

---

## 5. Add the new fields to the record

### 5.1 Find the new names

`<base>_theory.lean` contains one declaration per type, constant, definition and axiom of the dump.
The names already in `HOLTheory` are skipped:

```bash
grep -oE "^(axiom|nonrec theorem|theorem|noncomputable def|opaque) [^ :]+" <base>_theory.lean \
  | awk '{print $NF}' | sort -u > all_names.txt
grep -oE "^  \[?[A-Za-z0-9_']+" <repo>/HolLightLean/hol_theory_record.lean \
  | tr -d ' [' | sort -u > record_names.txt
comm -23 all_names.txt record_names.txt | grep -v '^thm_' > new_names.txt   # fields to add, check by hand
```

(The `grep -v '^thm_'` only drops theorem names. `<base>_theory.lean` lists the theorems too, as
`axiom thm_X : …`, but theorems are not record fields: they go to the `_opam` file (§7).)
On `hol.ml`, the names that remain are `hexists`, `hforall`, `himpl`. They are not new fields
either, because the record handles them with its definitions `EXISTS`, `FORALL` and `imp` (see the last
point below).

Then check by hand:

- `ne_X` names are the `Nonempty` witnesses of new types: they become `[ne_X : …]` fields (§5.2).
- **Same name, different statement.** Compare the statement of every *old* `axiom_N` and of any
  constant with a numeric name (`_22943`, …) with the record. These names depend on load order,
  so a dump that does not start with exactly the same `hol.ml` may renumber them. If a statement
  differs, stop and report it. Do not silently rename.
- **Names that differ from the record by design.** With the repository's `mapping_records.lp`
  and `renaming_records.lp`, the export of `hol.ml` matches the record except for two names,
  which were fixed by hand in `hol_opam.lean`. Apply the same fix to the new `_opam` file (§7,
  steps (a) and (b)):
  - `hnot` → `HOLTheory.not` (the field is `not`; a bare `not` is ambiguous with
    `_root_.not : Bool → Bool`);
  - `hexists` (with or without `T`, e.g. `@hexists T A _`) → `HOLTheory.EXISTS` (e.g.
    `@HOLTheory.EXISTS A _`). `EXISTS` is a definition of the record, not a field, so it takes
    no `T`.
  Any **other** name in `<base>_opam.lean` that is neither a field nor a definition of the record
  is a real mismatch. Fix it in `renaming_records.lp` (§4.4; work-directory copy first) and re-export, never in
  `mapping_records.lp`.

### 5.2 Add the new fields to `HOLTheory`

Append the new fields at the **end of the class** in `HolLightLean/hol_theory_record.lean`
(after the last field, currently `axiom_40`, and before the `-- make the Nonempty witnesses …`
comment). Mark the block with a comment naming the library:

```lean
  axiom_40 : …                         -- last field of hol.ml (existing, do not touch)
  -- ===== <file>.ml =====
  -- new type of arity 1: `axiom foo : Type -> Type` + `axiom ne_foo (a0 : Type) : Nonempty (foo a0)`
  foo : (a0 : Type) -> [Nonempty a0] -> Type
  [ne_foo : ∀ (a0 : Type) [Nonempty a0], Nonempty (foo a0)]
  -- new constant + its definition, copied from <base>_theory.lean (type variables as binders)
  bar {A : Type} [Nonempty A] : A -> foo A
  bar_def {A : Type} [Nonempty A] : hol_eq (@bar A _) (fun x : A => …)
  -- new type-definition axioms, same name and statement as in <base>_theory.lean
  axiom_41 : …
```

and, at the end of the file, one instance per new type, like the existing ones:

```lean
instance instNeFoo [T : HOLTheory] (a0 : Type) [Nonempty a0] : Nonempty (HOLTheory.foo a0) :=
  HOLTheory.ne_foo a0
```

Rules (this is how the existing fields were made):

- Keep the **declaration order** of `<base>_theory.lean`. A field may only mention earlier ones.
- A theory `axiom c : ∀ {A : Type _} [Nonempty A], τ` becomes the field `c {A : Type} [Nonempty A] : τ`.
  Replace `Type _` with `Type`.
- A theory `theorem`/`def` keeps only its **statement/type** as a field (the body or proof is
  dropped). Definitions appear as a constant field `c` plus its `c_def` equation field.
- Every new type gets a `[ne_X : …]` field **and** an `instance` at the end of the file.
- If a new name clashes with a root-level name in Lean (Lean says *ambiguous*), write it
  `HOLTheory.<name>` where it is used.
- Check: `lake build HolLightLean.hol_theory_record`. `hol_theory_inst.lean` will fail until
  the new fields have values (§6.4). That is expected.

### 5.3 Why the fields go into `HOLTheory` and not into an extending class

Putting the library's fields in a separate `class HOLTheory<Lib> extends HOLTheory` would keep
the base record untouched, but **for now it does not work with the generated files**. Both
problems below were tested on a small example:

1. **Lambdapi hard-codes the class.** `param_stt_lean` always prints `[T : HOLTheory]` (the
   class name `HOLTheory` and the variable `T` are fixed in Lambdapi's `src/export/stt.ml`), and it
   applies fields explicitly to `T`, as in `@hexists_one T A _`. With `T : HOLTheory<Lib>`, Lean
   rejects `@HOLTheory.hexists_one T` (type mismatch), because it does not create
   `HOLTheory<Lib>.hexists_one` for inherited fields. Every generated file would have to be
   rewritten with `sed` (`[T : HOLTheory]` → `[T : HOLTheory<Lib>]`, `@f T` → `@f _`). This is
   fragile and makes the files differ from what Lambdapi produces.
2. **`hol_readable` would only half work.** `unfoldInstProjections` in `HolLightLean/meta.lean`
   unfolds only the projections of the instance's own class. With an extended instance, the new
   fields unfold but the inherited ones (`hol_eq`, `hand`, …) stay folded, so the statements are
   not readable (`hol_eq (id x) x` instead of `id x = x`).

With a single `HOLTheory`, the generated files are used as Lambdapi prints them (apart from the
two names of §5.1), and `hol_readable` and the export script work unchanged. An extension can be
reconsidered once Lambdapi takes the class name as an option and `hol_readable` also unfolds
parent-class projections (e.g. with `getAllParentStructures`).

---

## 6. Alignments: give values to the new fields

### 6.1 What an alignment is

For each new field you choose a **Lean/Mathlib object** and prove that it satisfies the HOL
specification:

| Field kind | You provide | Proof obligation |
|---|---|---|
| type `foo` | a Lean type, e.g. `Finset A`, `ℂ`, a `Subtype` | `Nonempty` instance (`inferInstance` or `⟨witness⟩`) |
| constant `bar` | a Lean term, e.g. `Finset.card`, `fun x y => x + y` | none by itself |
| definition `bar_def` | a proof | `hol_eq bar <HOL body>`, i.e. `bar = <HOL body>` after instantiation |
| type axiom `axiom_N` (pairs `mk_foo`/`dest_foo`) | `mk_foo`, `dest_foo` | `mk (dest a) = a` and `P r = (dest (mk r) = r)` |

Under `HolTheoryInst`, `hol_eq` is `Eq`, `hand` is `And`, `htrue` is `True`, `epsilon` is
`Classical.epsilon`, `NUMERAL`/`BIT0`/`BIT1` are on `ℕ`, `Real` is `ℝ`, `int` is `ℤ`, `list` is `List`,
`cart` is the HOL `cart` (vectors), sets `A -> Prop` are handled as `Set A`, … (see
`hol_theory_inst.lean`). So a `_def` obligation is an ordinary Lean/Mathlib statement.

Choose the counterpart in this order:

1. **The Mathlib object a Lean user expects** (`Finset.sum`, `Nat.choose`, `Real.sqrt`,
   `Function.Injective`, `Set.image`, …). Search Mathlib by name, by `exact?`, or with
   `#loogle`/`#leansearch` if available. Make sure the definitions agree on **all** inputs, including
   degenerate ones (division by 0, `Nat` subtraction, empty sets, infinite sets, `epsilon` of an
   empty predicate). HOL definitions often fix junk values differently.
2. **A simple Lean term** (`fun f x => f x`, `if P then x else y`) when Mathlib has nothing.
3. **Partial alignment** when the HOL constant is only specified on part of its domain (defined
   with `epsilon` / `new_specification`). See `partial_align_*` in `conectors.lean` and
   `epsilon_align_partial` in `meta.lean`.
4. **Unaligned** (keep the HOL meaning) as a last resort (§6.6).

### 6.2 Where to write the proofs

Create `HolLightLean/<lib>_align.lean` (imports `HolLightLean.after_real`, which brings
everything; `hol_theory_inst.lean` will import this file). For each constant, follow the style of `after_real.lean`:

```lean
@[simp] noncomputable def bar {A : Type*} [Nonempty A] : A -> Finset A := fun x => {x}

theorem bar_def {A : Type*} [Nonempty A] : bar = (fun x : A => <HOL body, in Lean terms>) := by
  funext x; simp [bar]           -- or one of the tactics below
```

To get `<HOL body, in Lean terms>`, take the statement of the field `bar_def` and replace each
field by its value in the instance. Fastest way: state the field in the instance first (§6.4) and
read the goal Lean shows. For definitions made only of aligned constants, `rfl`, `simp`, `funext`
plus `simp`, `grind` or `aesop` usually close the goal.

The tactics for the usual HOL definition shapes are described in §6.3.

### 6.3 The alignment tactics of `meta.lean`

HOL Light builds most definitions in a few fixed shapes, and `HolLightLean/meta.lean` has one
tactic per shape. A `_def` goal always has the form

```
<your Lean object> = <HOL body>
```

**Before calling a tactic, `unfold` your Lean definition** (and any helper names such as `NIL`,
`GSPEC`), so that the right-hand side is literally the HOL body. Then pick the tactic from the
shape of the body. Each tactic is a sequence of smaller steps. When it fails, run the steps one by
one (as listed below), look at the remaining goal, and finish by hand.

#### `finisher_tacs`: close simple goals

`first | rfl | lia | grind | (aesop; done) | done`. The other tactics use it on their side goals.
You may try it to close simple goals but do not leave it, write the corresponding tactic.

#### `epsilon_align_total`: total recursive functions

- **HOL shape.** Functions defined by recursion with `define`/`new_recursive_definition`, e.g.
  `MEM`, `APPEND`, `LENGTH`, `MAP`. The body is `ε (fun f' => ∀ tag, <recursion equations of f' tag>) tag₀`:
  HOL takes the epsilon of the equations, over functions with an extra dummy argument `tag` (a tuple
  of numerals encoding the name, like `_18158` in `MEM_def`).
- **Lean side.** A definition by structural recursion (pattern matching), or a Mathlib function
  whose defining equations `simp` knows. The recursion must be on the first argument (functions of
  2 or 3 arguments) or on the second (3 arguments), over `ℕ` or lists.
- **Usage.** `unfold f; epsilon_align_total` (example: `MEM_def` in `up_to_real.lean`).
- **Steps.**
  1. `epsilon_elim`: unfolds `NUMERAL BIT0 BIT1`, removes the dummy argument (`congrArg`), and
     applies `align_epsilon` (`conectors.lean`): `P a → (∀ x, P a → P x → a = x) → a = ε P`.
     Two goals remain: the **existence** goal `P (fun _ => f)` (the Lean function satisfies the HOL
     equations) and the **uniqueness** goal (any function satisfying them equals `f`).
  2. `epsilon_align_1_total_rec_nat` proves the existence goal: `constructor` on the conjunction of
     equations, `simp_all +arith`, `finisher_tacs`.
  3. `epsilon_align_2_total_rec_nat` proves the uniqueness goal: `funext`, then induction on the
     recursive argument (`ind_on_2_of2`, `ind_on_2_of3` or `ind_on_3`), then `finisher_tacs`.
- **If it fails.** Run `epsilon_elim` alone. Prove the existence goal with `simp [f]` or
  `constructor <;> intros <;> simp [f]`, and the uniqueness goal with `funext` and `induction` on
  the argument the function recurses on, rewriting with the hypotheses. Common causes: recursion on
  another argument, or equations that `simp` does not normalize to the same form (`SUC n` vs
  `n + 1`: add `Nat.succ_eq_add_one` or similar lemmas).

#### `epsilon_align_partial Q`: functions specified only on part of their domain

- **HOL shape.** Same epsilon shape, but the equations do not determine the function everywhere,
  e.g. `OUTL (INL x) = x` says nothing about `OUTL (INR y)`, and `HD (CONS h t) = h` says nothing
  about `HD []`.
- **Lean side (strategy).** No Lean function can be proved equal to the HOL constant outside the
  specified part, because the HOL value there is an unknown epsilon. So define the Lean function as
  the intended value on the specified part, and as **the HOL value itself** on the rest. Keep a
  copy of the HOL body as `f_HOL` and define, e.g.
  ```lean
  noncomputable def OUTL : (SUM A B) -> A := fun S => match S with
    | Sum.inl a => a
    | Sum.inr b => OUTL_HOL (INR b)
  ```
  (`up_to_real.lean`, also `OUTR`, `HD`, `TL`, …). Readable theorems then show `OUTL`, which is
  honest: HOL proves nothing about the unspecified values.
- **Usage.** `unfold f_HOL; funext x; epsilon_align_partial (fun x : τ => <unspecified part>)`.
  The argument `Q` is the predicate of the **unspecified** part, where `f` is defined as the HOL
  value. Example: `OUTL_def` uses `(fun S : SUM A B => ∃ b : B, S = INR b)`. The function may have
  1, 2 or 3 explicit arguments (`part_tac_1/2/3`, built on `partial_align_1/2/3` of
  `conectors.lean`). `Q` is about the **last** argument.
- **Steps.** `epsilon_part_elim Q` leaves three goals, each attempted automatically:
  (1) `P f`, the equations hold (`epsilon_part_g1 τ`: case split / induction on `τ`, `simp_all`);
  (2) on `Q`, `f` agrees with the epsilon (`epsilon_part_g2`: destructs `∃`/`∧`, `subst`);
  (3) uniqueness outside `Q` (`epsilon_part_g3 τ`: induction on `τ`). The goals it cannot close
  are left to you (they are wrapped in `try`), so **check that no goal remains**.

**Worked example: `HD`** (`up_to_real.lean`). In HOL Light, `HD (CONS h t) = h` is the only
equation, so `HD []` is unspecified. The exported definition is an epsilon over functions with a
dummy tag argument. Copy it verbatim as `HD_HOL`:

```lean
noncomputable def HD_HOL {A : Type*} [Nonempty A] : (List A) -> A :=
  @Classical.epsilon ((prod Nat Nat) -> (List A) -> A) _
    (fun HD' => ∀ _18090 : prod Nat Nat, ∀ t : List A, ∀ h : A,
      Eq (HD' _18090 (@List.cons A h t)) h)
    (@prod_mk Nat Nat _ _ (NUMERAL …) (NUMERAL …))       -- the tag, copied from the export

-- intended value on non-empty lists, the HOL value on `[]`
noncomputable def HD {A : Type*} [Nonempty A] (l : List A) : A :=
  List.headD l (HD_HOL [])

theorem HD_def {A : Type*} [Nonempty A] : (@HD A _) = (@HD_HOL A _) := by
  unfold HD_HOL
  funext l
  epsilon_align_partial (fun l : List A => l = [])   -- Q = the unspecified part: `[]`
```

The instance then uses `HD := HD`. Readable theorems mention `HD l`, which is `List.headD`
on non-empty lists.

**All partial alignments in the repository** (all in `up_to_real.lean`):

| Constant | Lean definition | `Q` (unspecified part) | Proof |
|---|---|---|---|
| `OUTL` | `match S with \| Sum.inl a => a \| Sum.inr b => OUTL_HOL (INR b)` | `fun S => ∃ b, S = INR b` | `epsilon_align_partial` |
| `OUTR` | `match S with \| Sum.inl a => OUTR_HOL (INL a) \| Sum.inr b => b` | `fun S => ∃ a, S = INL a` | `epsilon_align_partial` |
| `HD` | `List.headD l (HD_HOL [])` | `fun l => l = []` | `epsilon_align_partial` |
| `TL` | `match l with \| [] => TL_HOL l \| hd :: t => List.tail (hd :: t)` | `fun l => l = []` | `epsilon_align_partial` |
| `LAST` | `List.getLastD l (LAST_HOL [])` | `fun l => l = []` | `epsilon_align_partial` |
| `ASSOC` | `match l with \| [] => ASSOC_HOL a [] \| (a', b) :: l' => if a = a' then b else ASSOC a l'` | `fun l => l = []` (2 arguments; `Q` is on the last one) | `epsilon_align_partial`, then the remaining specification/uniqueness goals **by hand** |
| `EL` | `if h : n < l.length then l.get ⟨n, h⟩ else EL_HOL n l` | out of range, `¬ n < l.length` | **by hand**: lemma `EL_HOL_get` (in range, `EL_HOL n l = l.get ⟨n, h⟩`, via `Classical.epsilon_spec` and induction on `n`), then `by_cases h : n < l.length` |

Use them as templates:

- **`HD`, `LAST`**: the Mathlib function with a default argument (`headD`, `getLastD`). The
  default is the HOL value on the unspecified input.
- **`OUTL`, `OUTR`, `TL`**: pattern matching, with the HOL value in the unspecified branch.
- **`ASSOC`**: the tactic only goes part of the way, and the remaining goals are proved by hand.
- **`EL`**: the unspecified part is not a single constructor (out-of-range indices), and the
  recursion is on the first argument while `Q` would be about both arguments. So the tactic does
  not apply: prove a lemma "the HOL value is the intended one on the specified part"
  (`EL_HOL_get`), then split cases.

#### `ind_align` / `ind_align using e`: inductively defined predicates

- **HOL shape.** `new_inductive_definition`, e.g. `FINITE`, `NUM_REP`. The body is the
  impredicative closure: `fun x => ∀ P', (∀ a, <rules for P'> → P' a) → P' x`.
- **Lean side.** An `inductive` predicate whose constructors are the HOL rules, or a Mathlib
  predicate with an induction principle (`Set.Finite` with `Set.Finite.induction_on`).
- **Usage.** `unfold p; ind_align` or `unfold p; ind_align using <induction principle>` (examples:
  `NUM_REP_eq_id` in `up_to_real.lean`, `FINITE_def` in `after_real.lean`).
- **Steps.** `funext x; apply Eq.propIntro`. For (→): induction on the Lean proof `h`
  (`induction h` or `induction x, h`, with `using e` if given), each case closed by
  `finisher_tacs`. For (←): apply the HOL hypothesis to the Lean predicate and prove that it
  satisfies the rules with `finisher_tacs`. It is written for predicates of **one** argument
  (sets). For relations, do these steps by hand.

#### `gspec_align`: set-builder definitions

- **HOL shape.** `{f x | P x}`, i.e. `GSPEC (fun v => ∃ x, SETSPEC v (P x) (f x))` with one or two
  bound variables (e.g. `UNIONS`, `INTERS`, `IMAGE`).
- **Lean side.** The Mathlib set (`⋃₀ F`, `⋂₀ F`, `f '' s`, …), with the field typed `Set A`.
- **Usage.** `unfold f; gspec_align` (examples: `UNIONS_def`, `INTERS_def` in `after_real.lean`).
- **Steps.** Unfolds `GSPEC SETSPEC id IN`, `funext`, `Eq.propIntro`, gives the witnesses
  (`refine ⟨_, ?_, rfl⟩` or `⟨_, _, ?_, rfl⟩`) in one direction and destructs them in the other.
  Membership goals are closed by `exact h` or `finisher_tacs`.

#### `set_align`: pointwise set operations

- **HOL shape.** Set operations whose body `simp` can reduce pointwise (`UNION`, `INTER`, `DIFF`,
  `DELETE`, `INSERT`, `SUBSET`, …).
- **Usage.** `unfold f; set_align` (examples: `UNION_def`, `DIFF_def` in `after_real.lean`).
- **Steps.** `simp_all`, then the first that works: done, `gspec_align`, or `funext` +
  `Eq.propIntro` with `finisher_tacs`/`solve_by_elim` on each direction. The last branch may
  **leave goals** (`skip`). Check that no goal remains.

#### Without a tactic: `align_epsilon`

For any other epsilon-defined constant (`new_specification`, `@` in HOL), use the lemma directly:
`apply align_epsilon` (`conectors.lean`), then prove that the Lean value satisfies the
specification and that the specification has a unique solution. This is what `epsilon_elim` does
after removing the dummy argument.

### 6.4 Give the values in `HolTheoryInst`

In `HolLightLean/hol_theory_inst.lean`:

1. add `import HolLightLean.<lib>_align` below the existing imports;
2. append the values of the new fields at the **end** of `noncomputable instance HolTheoryInst`,
   under a comment naming the library, in the same order as in the record:

```lean
  axiom_40 := axiom_40                 -- last value for hol.ml (existing, do not touch)
  -- ===== <file>.ml =====
  foo := fun A _ => Finset A
  ne_foo := fun _ _ => inferInstance
  bar := fun x => {x}
  bar_def := bar_def
  axiom_41 := axiom_41
```

Prefer giving a field the **body** of the Lean definition (as the file already does, e.g.
`COND := fun P x y => if P then x else y`, `o := fun f g => f ∘ g`) rather than an intermediate
name. The readable statements then show Mathlib notation.

Check, in this order:

- `lake build HolLightLean.hol_theory_inst`: the only `sorry` warnings are the documented ones
  of §6.6 (b);
- `lake build HolLightLean.hol_opam`: the existing `hol.ml` statements must still build. Adding
  fields does not change them, and this confirms it;
- in a scratch file, `#print axioms HolTheoryInst`: only `propext`, `Classical.choice`,
  `Quot.sound` and the generated HOL declarations (`thm_…`, `_mk_…`/`_dest_…` of
  `hol_up_real_terms`) may appear.

### 6.5 Type definitions (`axiom_N`)

A HOL type definition introduces a type `foo`, `mk_foo : rep -> foo`, `dest_foo : foo -> rep` and
two axioms:

- `axiom_N   : ∀ a, mk_foo (dest_foo a) = a`
- `axiom_N+1 : ∀ r, P r = (dest_foo (mk_foo r) = r)`

Align `foo` with a Lean type that is in bijection with `{r // P r}`. Define `dest_foo` as the
embedding and `mk_foo r` as `if h : P r then ⟨r, h⟩ else <default>`. Prove both. Examples:
`cart`, `mk_cart`, `axiom_29`, `axiom_30` in `after_real.lean`; `finite_sum`, `tybit0` there too.

### 6.6 When an alignment fails

First decide which of the two cases you are in. Tell the user and ask before choosing (§0).

**(a) Impossible: the HOL constant and the Lean object really differ.** Typically they disagree on
degenerate inputs: junk values such as division by zero, `Nat` subtraction, `epsilon` of an
unsatisfiable predicate, infinite sets in `CARD`, or the head of the empty list. Then:

1. find the input where they differ, and if possible prove it in Lean
   (`example : <HOL body> a ≠ <Lean object> a`);
2. try another counterpart: another Mathlib object, or a Lean function that matches HOL's junk
   values;
3. if they agree on the part of the domain that HOL specifies, use a **partial alignment** (§6.3,
   `epsilon_align_partial`);
4. otherwise keep the **HOL meaning**: the field's value is the HOL body (written with the already
   aligned objects) and the `_def` proof is `rfl`. The theorems stay correct, but they mention a
   HOL-specific construction.

**Never** use `sorry` in this case: it would assert something false. Add a comment above the
definition: `-- NOT ALIGNED to <Mathlib object>: differs at <input>, because <reason>.`

**(b) True but too hard.** You are convinced that the alignment holds (you can argue it on paper),
but the proof does not go through in reasonable time. Close it with `sorry`, keep the `sorry` as
**small as possible** (only the failing subgoal, not the whole proof), and document it right above
the theorem:

```lean
/- ALIGNMENT SORRY: bar_def
   Why it holds: <mathematical argument, short>.
   Strategy followed: unfold bar; epsilon_elim; existence goal by simp [bar] (done);
     uniqueness goal: induction on n, stuck at the SUC case, remaining goal:
     <paste the goal>.
   Suggested next step: <lemma that would close it, or another induction>. -/
theorem bar_def … := by
  unfold bar
  epsilon_elim
  · simp [bar]
  · sorry
```

Consequences to report: `HolTheoryInst` and every exported `hol_X` then depend on `sorryAx`.
`#print axioms HolTheoryInst` shows it, and so does `#print axioms hol_X` for each theorem that
uses the constant. The export (§8) still works. List every `sorry` in the final report, with the
reason and the strategy that was followed.

---

## 7. Prepare the statements file

Turn the raw export `<base>_opam.lean` (work directory) into `HolLightLean/<lib>_opam.lean`, the
way `hol_opam.lean` was made from the `hol.ml` export. The raw file has one `axiom thm_X …` per
line. Its header imports the empty `theory_hol`/`<base>_types`/`<base>_terms` modules of a
parametrized export and is replaced: everything is in the record.

```bash
CLASH='not|imp|FORALL|EXISTS|_FALSITY_|prod|Real|cart|finite_image|finite_sum|finite_diff|finite_prod|hreal|nadd|ind|recspace|SUM|tybit0|tybit1|NUM_REP|_GUARDED_PATTERN|_UNGUARDED_PATTERN'
{ echo 'import HolLightLean.hol_theory_inst'
  echo 'open HOLTheory'
  echo
  echo 'namespace HolLightLean.<lib>_opam'
  echo 'set_option linter.unusedVariables false'
  echo 'set_option linter.style.longLine false'
  echo 'set_option linter.style.nameCheck false'
  grep '^axiom thm_' <base>_opam.lean | perl -pe '
    s/\@hexists T /\@EXISTS /g;                                  # (a) hexists -> EXISTS
    s/(?<![\w.\x27])hexists(?![\w\x27])/EXISTS/g;
    s/(?<![\w.\x27])hnot(?![\w\x27])/not/g;                       # (b) hnot -> not
    s/(?<![\w.\x27])('"$CLASH"')(?![\w\x27])/HOLTheory.$1/g;      # (c) qualify clashing names
    s/^axiom thm_/\@[hol_readable HolTheoryInst]\naxiom thm_/'    # (d) attribute
  echo 'end HolLightLean.<lib>_opam'
} > <repo>/HolLightLean/<lib>_opam.lean
```

What each step does:

- **(a), (b)** are the two names of §5.1 that differ from the record. `EXISTS` is a definition
  of the record, not a field, so `@hexists T A _` loses its `T`.
- **(c)** The alignment files (imported by `hol_theory_inst`) define root-level names that are
  also record names (`prod`, `Real`, `cart`, `not`, …). A bare name would be *ambiguous*, so it is
  written `HOLTheory.<name>`, as in `hol_opam.lean`. The lookarounds (`(?<![\w.'])`,
  `(?![\w'])`) avoid touching `prod'`, `Prod.prod` or `HOLTheory.prod`. If your new fields add a
  clash (Lean: *ambiguous, possible interpretations*), add the name to `CLASH` and rerun.
- **(d)** `@[hol_readable HolTheoryInst]` creates, for each `thm_X`, the theorem `hol_X` with the
  instance's projections unfolded. The export script (§8) reads these `hol_X`.

Then build (it takes a while: every attribute creates a theorem):

```bash
ulimit -s unlimited; LEAN_STACK_SIZE_KB=0 lake build HolLightLean.<lib>_opam
```

Tested on the `hol.ml` export: the script above, applied to a fresh `param_stt_lean` export made
with the repository's `mapping_records.lp`/`renaming_records.lp`, compiles without errors and
produces 2902 `hol_X` theorems whose statements are **identical** to those of the repository's
`hol_opam.lean`.

---

## 8. Generate the readable theorems

`scripts/export_thms_repo.lean` is written for `hol_opam`. Make a copy for the new library,
`scripts/export_<lib>.lean`, and change:

- `import HolLightLean.hol_opam` → `import HolLightLean.<lib>_opam` (first line **and** the
  `header` string in `create_file`);
- `let ns := \`HolLightLean.hol_opam` → `` `HolLightLean.<lib>_opam `` (in `get_oarray`);
- the output file `"thms_export.lean"` → `"<lib>_export.lean"`;
- **delete the `#exit` line** before `run_cmd do create_file`, otherwise nothing runs.

Run from the repository root:

```bash
lake env lean -Dpp.unicode.fun=true scripts/export_<lib>.lean
lake env lean <lib>_export.lean        # the generated file must check
```

How to read the messages:

- `N theorems printed with style (plain: a, coercion ascriptions: b, pp.analyze: c)`: the
  statements that round-trip with the most readable style, then with type ascriptions on
  coercions, then with `pp.analyze` (more explicit, may show `(α := …)`).
- `statements that do not elaborate back: [...]`: those statements were printed anyway but **do not
  parse back**, and `<lib>_export.lean` will fail on them. Usual causes (all seen on `hol.ml`):
  - a predicate `A → Prop` printed where Lean needs `Set A` or the reverse. Make the field's type
    in the instance use `Set A` (and `setOf` for `GSPEC`), as in `after_real.lean`;
  - a constant like `∅`, `Set.univ`, `[]` whose type cannot be inferred. Add it to `toTyAsc`
    in the script;
  - `|x|` inside `|…|` (`||x| - |y||`). Handled by the `absParen` delaborator in the script.
  Fix the cause (instance first, script second) and rerun. Report what remains.

The final deliverable is `<lib>_export.lean`: one `theorem hol_X : <readable statement> := @thm_X HolTheoryInst`
per HOL theorem, in HOL Light order.

---

## 9. Final checklist and report

- [ ] `lake build`, `lake build HolLightLean.hol_opam` and `lake build HolLightLean.<lib>_opam` succeed.
- [ ] `<lib>_export.lean` checks with `lake env lean`.
- [ ] No new `axiom`, `admit` or `native_decide`; every `sorry` has its `ALIGNMENT SORRY` comment
      (§6.6 (b)) and is in the report: `grep -n "sorry\|^axiom\|admit\|native_decide" HolLightLean/<lib>_align.lean HolLightLean/hol_theory_inst.lean`.
- [ ] Every constant kept with its HOL meaning has its `NOT ALIGNED` comment (§6.6 (a)).
- [ ] Work-directory files (dump, `.lp`, raw exports) are **not** committed. Only the appended
      `hol_theory_record.lean`/`hol_theory_inst.lean`, the new `HolLightLean/<lib>_align.lean` and
      `HolLightLean/<lib>_opam.lean`, `scripts/export_<lib>.lean`, and the new entries of
      `hol2dk_files/renaming_records.lp` (§4.4). `mapping_records.lp` is unchanged.

Tell the user, in plain words: which library was exported, the number of theorems, the number of
new constants aligned to Mathlib / to simple Lean terms / partially / left unaligned (with names
and the reason), the alignments closed with `sorry` (with the reason and the strategy followed),
the statements that could not be printed readably, and where the result file is.

---

## 10. Troubleshooting

| Symptom | Cause and fix |
|---|---|
| `Unknown format: param_stt_lean` | Upstream Lambdapi. Install the records branch (§3). |
| `hol2dk dump…` gives wrong or missing theorem names | Not run from `$HOLLIGHT_DIR`, or HOL Light not patched (`hol2dk patch`, then `make`). |
| `make lean` / `make olean` targets missing | `Makefile` is the link from `$HOL2DK_DIR`. Copy `<repo>/hol2dk_files/Makefile`. |
| `make lp` tries to translate `mapping_records.lp` | The `./` prefix was omitted in `hol2dk config --mapping`. |
| `Stack overflow detected` when building generated files | `ulimit -s unlimited` before `make olean` / `lake build`. `LEAN_STACK_SIZE_KB=0` is set by the Makefile. |
| `Unknown identifier` (a field name) in the opam file | The renaming file and the record disagree, or the field was not added (§5.1, §5.2). |
| `hol_theory_inst.lean`: `fields missing: …` | New record fields without a value in `HolTheoryInst` (§6.4). |
| `ambiguous, possible interpretations` | Add the name to `CLASH` in §7 and regenerate. |
| readable statement still shows a HOL name (`hol_eq`, a constant, …) | The field is unaligned (§6.6) or its value is an intermediate definition instead of its body (§6.4). |
| `failed to synthesize Decidable …` in the export file | The export header must keep `attribute [local instance 10000] Classical.propDecidable`. |
| Export script prints nothing | The `#exit` line is still there (§8). |
