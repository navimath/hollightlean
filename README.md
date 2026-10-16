# HolLightLean

Translation and Alignment project between the HOL Light standard library with Lean 4 and Mathlib.
HOL Light proofs are exported with [hol2dk](https://github.com/Deducteam/hol2dk) to
[Lambdapi](https://github.com/Deducteam/lambdapi), then to Lean 4 using Lambdapi's export option. HOL Light (the appropriate) types and
constants are then mapped to their Lean/Mathlib counterpart, with a proof that they are extensionally the same for functions or that type definitions in the target system hold for the same predicates as in HOL Light. At last, one obtains a translated (and proved) version of HOL Light theorems for Lean/Mathlib objects.

## To replicate the translation

Requirements: [opam](https://opam.ocaml.org/), [HOL Light](https://github.com/jrh13/hol-light),
[hol2dk](https://github.com/Deducteam/hol2dk),[Lambdapi](https://github.com/Deducteam/lambdapi)
built from sources and Lean `v4.31.0`.

### 0. Set up the tools

**opam and dune** 
```bash
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
opam init -y                      # creates ~/.opam and a default switch with an OCaml compiler
eval $(opam env)                  # load it in the current shell (opam init offers to add this to your profile)
opam install -y dune
```

**HOL Light**
```bash
opam install -y --deps-only hol_light.3.0.0
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
opam pin add lambdapi ./lambdapi
lambdapi --version                # should print a dev version, not 3.0.0
```

**Environment variables**, e.g. in your shell profile:
```bash
export HOLLIGHT_DIR=/absolute/path/to/hol-light
export HOL2DK_DIR=/absolute/path/to/hol2dk    #(different if installed via opam)
```

### 1. Patch HOL Light and choose a *fragment of `hol.ml`*

`hol2dk patch` modifies `fusion.ml`, `bool.ml` and `equal.ml` so that HOL Light records proof
steps (backups are kept as `*-bak.ml`; `hol2dk unpatch` restores them):
```bash
cd $HOLLIGHT_DIR
hol2dk patch
```

A *fragment of `hol.ml`* is a `.ml` file that loads only an initial part of the standard library.
In current HOL Light, `hol.ml` loads the library through `hol_lib.ml`, so a fragment is a pair of
copies of these two files. For example, `hol_up_real.ml` (everything up to `real.ml`):
```bash
cd $HOLLIGHT_DIR
cp hol.ml hol_up_real.ml
cp hol_lib.ml hol_lib_up_real.ml
# in hol_up_real.ml, load the truncated library instead of the full one
sed -i 's/loads "hol_lib.ml"/loads "hol_lib_up_real.ml"/' hol_up_real.ml
```
Then edit `hol_lib_up_real.ml` and comment out (or delete) every `loads` line after
`loads "real.ml";;`, i.e. from `calc_rat.ml` to the end of the file (including the final
`check_axioms` block). The fragment must keep at least everything up to `loads "fusion.ml";;`.
Use `hol.ml` itself to export the whole library.

### 2. Dump the HOL Light proofs

```bash
cd $HOLLIGHT_DIR                   # must be run here to compute theorem names correctly
hol2dk dump-simp-before-hol hol_up_real.ml
```
This produces `hol_up_real.{prf,sig,thm,nbp,pos,use}` in `$HOLLIGHT_DIR`.

### 3. Translate to Lambdapi, then to Lean

Create a fresh folder outside `$HOLLIGHT_DIR` and copy inside the `encoding.lp`, `mapping.lp` and
`renaming.lp` files from this repository's `hol2dk_files/` folder, together with `complete.lean`.
```bash
# inside the folder
hol2dk config hol_up_real.ml HolUptoReal complete.lean --mapping mapping.lp --renaming renaming.lp
make split && make -j$(nproc) lp
make hol_up_real_opam.lp           # create theorem statements
make lean                          # creates HolUptoReal/ and translates the .lp files inside
```

### 4. Add the alignment files

Copy to the generated Lean folder `hol_up_real_{terms,opam}.lean` from `HolLightLean/`, replacing their imports with the corresponding header.

### 5. Check the translation

To verify the translation, use the command `make olean` (it runs `LEAN_STACK_SIZE_KB=0 lake build`). Large files can overflow the stack, and older Lean versions ignore `LEAN_STACK_SIZE_KB`. You can add this line to the top level of the generated project's `lakefile.toml`:

   ```toml
   moreLeanArgs = ["--tstack=1000000"]   # thread stack size in KB
   ```

**Optional**: To generate the `complete.file` you can use the script `mk_complete.py` within the `scripts` folder.

   ```bash
   lake exe cache get && lake build
   python3 scripts/mk_complete.py           # optional: regenerate the single-file complete.lean
   ```

The whole standard library is exported the same way, using `hol.ml` with root path `Hol`.

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
- **In progress:** To generate readable Lean theorems from the instance:
  The MWE at the end of `meta.lean` does this today with a command:
  `hol_readable thm_ADD_SYM using miniInst [nat_add_eq]` gives
  `hol_ADD_SYM (x y : ℕ) : x + y = y + x`.
