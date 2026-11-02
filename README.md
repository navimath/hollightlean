# HolLightLean

Translation and Alignment project between the HOL Light standard library with Lean 4 and Mathlib.
HOL Light proofs are exported with [hol2dk](https://github.com/Deducteam/hol2dk) to
[Lambdapi](https://github.com/Deducteam/lambdapi), then to Lean 4 using Lambdapi's export option. HOL Light (the appropriate) types and
constants are then mapped to their Lean/Mathlib counterpart, with a proof that they are extensionally the same for functions or that type definitions in the target system hold for the same predicates as in HOL Light. At last, one obtains a translated (and proved) version of HOL Light theorems for Lean/Mathlib objects.

## To replicate the translation

### Automatic replication

`scripts/reproduce` automatic replicate the translation for the HOL standard library or for a subset of it (up to `real.ml`). It installs pinned versions of HOL Light, hol2dk, Lambdapi and Lean in a local opam switch under `tmp/` (only opam, git, curl and make are needed beforehand). It then dumps and translates the proofs using this repository's mapping files and `complete.lean`, and checks the result with `lake build`. The Lean project is created in `tmp/output-<LIB>/`, and a rerun resumes after the last completed stage.
```bash
scripts/reproduce <library_option>     # HOL or Up_to_Real
scripts/reproduce <library> <stage>   # restart from stage <stage>
```

### Manually replicate

Requirements: [opam](https://opam.ocaml.org/), [HOL Light](https://github.com/jrh13/hol-light),
[hol2dk](https://github.com/Deducteam/hol2dk), [Lambdapi](https://github.com/Deducteam/lambdapi)
built from sources and Lean `v4.31.0`. The versions used by `scripts/reproduce` are HOL Light 3.1.0,
hol2dk `11e45c0`, Lambdapi `dfd44e0a` and OCaml 5.3.0.

The steps below export `hol_up_real.ml` (the library up to `real.ml`) as the Lean project
`HolUptoReal`. To export the whole library, skip the fragment in step 1 and use `hol.ml`, `Hol` and
`hol_opam` in place of `hol_up_real.ml`, `HolUptoReal` and `hol_up_real_opam`.

#### 0. Set up the tools

**opam and dune**
```bash
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
opam init -y                      # creates ~/.opam and a default switch with an OCaml compiler
eval $(opam env)                  # load it in the current shell (opam init offers to add this to your profile)
opam install -y dune
```

**HOL Light**
```bash
opam pin -y camlp5 8.03.06
opam install -y --deps-only hol_light.3.1.0
git clone https://github.com/jrh13/hol-light
make -C hol-light
```

**hol2dk** (from sources, so that `hol2dk config` and the generated `Makefile` have the Lean targets)
```bash
git clone https://github.com/Deducteam/hol2dk
cd hol2dk && dune build && dune install
```

**Lambdapi** (from sources, for `lambdapi export -o stt_lean`)
```bash
git clone https://github.com/Deducteam/lambdapi
opam pin add -y lambdapi ./lambdapi
lambdapi --version                # should print a dev version, not 3.0.0
```

**Lean** (through [elan](https://github.com/leanprover/elan))
```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
elan toolchain install leanprover/lean4:v4.31.0 #pin to version 4.31.0
```

**Environment variables**, e.g. in your shell profile:
```bash
export HOLLIGHT_DIR=/absolute/path/to/hol-light
export HOL2DK_DIR=$(opam var share)/hol2dk    # or the hol2dk sources
```
`HOL2DK_DIR` must contain the `Makefile`, `encoding.lp` and `theory_hol.lp` used by `hol2dk config`.


#### 1. Patch HOL Light and choose a *fragment of `hol.ml`*

`hol2dk patch` modifies `fusion.ml`, `bool.ml` and `equal.ml` so that HOL Light records proof
steps (use `hol2dk unpatch` to restore):
```bash
cd $HOLLIGHT_DIR
hol2dk patch
```

A *fragment of `hol.ml`* is a `.ml` file that loads only an initial part of the standard library.
In current HOL Light, `hol.ml` loads the library through `hol_lib.ml`, so a fragment is a pair of
copies of these two files. For example, `hol_up_real.ml` loads `hol_lib_up_real.ml`, which keeps
the lines of `hol_lib.ml` up to `loads "real.ml";;` (the following `loads` and the final
`check_axioms` block are dropped):
```bash
cd $HOLLIGHT_DIR
awk '{print} /^loads "real.ml"/{exit}' hol_lib.ml > hol_lib_up_real.ml
sed -e 's/loads "hol_lib.ml"/loads "hol_lib_up_real.ml"/' hol.ml > hol_up_real.ml
```
A fragment must keep at least everything up to `loads "fusion.ml";;`.

#### 2. Dump the HOL Light proofs

```bash
cd $HOLLIGHT_DIR                   # must be run here to compute theorem names correctly
hol2dk dump-simp-before-hol hol_up_real.ml
```
This produces `hol_up_real.{prf,sig,thm,nbp,pos,use}` in `$HOLLIGHT_DIR`.

#### 3. Translate to Lambdapi, then to Lean

Create a fresh folder outside `$HOLLIGHT_DIR` and copy inside `mapping.lp` and `renaming.lp` from
this repository's `hol2dk_files/` folder, together with `complete.lean`. Then, inside the folder:
```bash
hol2dk config hol_up_real.ml HolUptoReal complete.lean --mapping ./mapping.lp --renaming ./renaming.lp
make split && make -j$(nproc) lp
make hol_up_real_opam.lp           # create theorem statements
make -j$(nproc) lean
```
The `./` in front of `mapping.lp` and `renaming.lp` is needed for the `Makefile` to exclude them
from the files to translate. The translation uses `complete.lean` and the mappings only: the
generated `HolUptoReal/*.lean` files are used as they are.

`hol2dk config` creates a `lakefile.toml` without Mathlib. Replace it with:
```toml
name = "HolUptoReal"
defaultTargets = ["HolUptoReal"]
moreLeanArgs = ["--tstack=1000000"]   # thread stack size in KB

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.31.0"

[[lean_lib]]
name = "HolUptoReal"
```
and fetch Mathlib:
```bash
echo "leanprover/lean4:v4.31.0" > lean-toolchain
lake update
lake exe cache get
```

#### 4. Check the translation

```bash
ulimit -s unlimited                       # large generated files overflow the default stack
make olean                                # runs LEAN_STACK_SIZE_KB=0 lake build
lake build HolUptoReal.hol_up_real_opam   # theorem statements (not imported by HolUptoReal.lean)
```
Without `ulimit -s unlimited`, some files (e.g. `thm1536906.lean` for `hol_up_real`) fail with
`Stack overflow detected`, even with `--tstack`.

**Optional**: `complete.lean` is generated from the files in `HolLightLean/` by the script
`mk_complete.py`. To regenerate it, run from the root of this repository:
```bash
lake exe cache get && lake build
python3 scripts/mk_complete.py
```

## Status

- **Aligned:** The HOL Light standard library is aligned with no `sorry`: logic, naturals, lists, reals, integers, sets, finite
  sums/products (as `finsum`/`finprod`), vectors and index types, … (`up_to_real`,
  `real_align`, `after_real`). Most are mapped to Mathlib. The project also includes a `meta.lean` file that automates alignments on (most of) functions inductively defined, epsilon-defined functions (partial alignments included) and set theory operations using custom tactics.
- **Parametrized translation:** exporting every theorem over a record of all HOL types and
  constants (`[T : HOLTheory]`) relies on an experimental version of Lambdapi that can be found [here](https://github.com/navimath/lambdapi/tree/records). To use it, the repo includes:
  - `hol_theory_record.lean`: the `HOLTheory` record;
  - `hol_theory_inst.lean`: `holTheoryInst`, the record filled with the Lean alignments;
  - `hol_opam.lean`: the exported theorem statements over `HOLTheory`
    (`lake build HolLightLean.hol_opam`).
- **In progress:** To generate a file containing all exported theorems in the parametrized version using a new `hol_readable` attribute appearing at the `hol_opam.lean` file. A first version of the script that generates this file can be found at `scripts/exports_thms_repo.lean` and the result can be found at `thms_export.lean`.
