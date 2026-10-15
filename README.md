# HolLightLean

Translation and Alignment project between the HOL Light standard library with Lean 4 and Mathlib.
HOL Light proofs are exported with [hol2dk](https://github.com/Deducteam/hol2dk) to
[Lambdapi](https://github.com/Deducteam/lambdapi), then to Lean 4 using Lambdapi's export option. HOL Light (the appropriate) types and
constants are then mapped to their Lean/Mathlib counterpart, with a proof that they are extensionally the same for functions or that type definitions in the target system hold for the same predicates as in HOL Light. At last, one obtains a translated (and proved) version of HOL Light theorems for Lean/Mathlib objects.

## To replicate the translation

Requirements: [HOL Light](https://github.com/jrh13/hol-light), [hol2dk](https://github.com/Deducteam/hol2dk), main version [Lambdapi](https://github.com/Deducteam/lambdapi) and
Lean `v4.31.0` (via elan) installed.

1. Dump the HOL Light proofs
```bash
cd $HOLLIGHT_DIR
hol2dk patch
hol2dk dump-simp-before-hol <fragment_of_hol.ml>.ml
```

2. Translate to Lambdapi, then to Lean
   Create a folder in your system and copy inside the `encoding,mapping,renaming.lp` files from this repository folder `hol2k_files`.
```bash
#inside the folder, execute
hol2dk config <fragment_of_hol.ml>.ml <project name> complete.lean --mapping mapping.lp --renaming renaming.lp
make split && make -j$(nproc) lp
make hol_up_real_opam.lp            # create theorem statements
make lean                  # creates HolUptoReal/ and translate the .lp files inside
```

3. Copy to the generated Lean folder `hol_up_real_{terms,opam}.lean` from `HolLightLean/`, replacing their imports with the corresponding header.

4. To verify the translation, use the command `make olean` (it runs `LEAN_STACK_SIZE_KB=0 lake build`). Large files can overflow the stack, and older Lean versions ignore `LEAN_STACK_SIZE_KB`. You can add this line to the top level of the generated project's `lakefile.toml`:

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
  `real_align`, `after_real`). Most are mapped to Mathlib. The project also includes a `meta.lean` file that automates some alignments using custom tactics.
- **Parametrized translation:** exporting every theorem over a record of all HOL types and
  constants (`[T : HOLTheory]`) relies on a version of Lambdapi export that is **not publicly available
  yet**. To use it, the repo includes:
  - `hol_theory_record.lean`: the `HOLTheory` record;
  - `hol_theory_inst.lean`: `holTheoryInst`, the record filled with the Lean alignments;
  - `hol_opam.lean`: the exported theorem statements over `HOLTheory`
    (`lake build HolLightLean.hol_opam`).
- **In progress:** two attributes to generate readable Lean theorems from the instance:
  - `@[hol_readable holTheoryInst]` on an exported theorem `thm_X`: instantiates it and
    generates `hol_X`, stated with native Lean notation;
  - `@[hol_rw]` on alignment lemmas (e.g. `real_add_eq`): the rewrites the elaborator may use.

  The MWE at the end of `meta.lean` does this today with a command:
  `hol_readable thm_ADD_SYM using miniInst [nat_add_eq]` gives
  `hol_ADD_SYM (x y : ℕ) : x + y = y + x`.
