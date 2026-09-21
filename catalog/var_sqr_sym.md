# `var_sqr_sym`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `var_sqr_sym`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecodes `E0`, `E2` (shared row with `var_perm_sym`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/var_sqr_sym.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — the row cites Chu & Stuckey 2011, which `CHRISTMAS_LIST.md:142` describes as carrying no dedicated `lex` explanation |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/*.tex`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: the square-matrix specialisation, and the one place it is *easier* than `var_perm_sym`

`var_sqr_sym` is [`var_perm_sym`](var_perm_sym.md) specialised to a **square matrix's**
row, column and transpose symmetries: the same `lex_lesseq`-per-generator shape, with the
matrix's second dimension addressed through the `R` index family
(`decomps/var_sqr_sym.md:3-6`). Everything about the chain is
[`lex_lesseq`](lex_lesseq.md)'s — **S5**, the `tied` accumulated-state auxiliary, the `rule3`
conjunction, the `rule4` guard — and everything about the per-generator structure is
[`var_perm_sym`](var_perm_sym.md)'s. This file states what is specific and cites the rest.

**What is specific, and it cuts the other way from what one would expect.** `var_perm_sym`'s
second blocker is that a permutation group's generator set is *instance data*, so the number
of comparisons is not fixed by the arity — **G7**, via the withdrawn `D2` escape hatch
(`docs/DECOMP_FORMAT_NOTES.md:96-104`). **A square matrix's symmetry group is not given by
instance data**: its generators are the row swaps, the column swaps and the transpose, all
determined by the matrix's shape. So on the reading `decomps/var_sqr_sym.md` gives, the
generator count here is a function of the arity and **G7 need not bite**.

This is stated as a reading, not a measurement, and with its weakest joint named: it depends
on whether `var_sqr_sym`'s MiniZinc signature really fixes the group from the shape or takes a
generator set as data, and **no `.mzn` is vendored in this checkout** to check
(`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/var_sqr_sym.md:6` itself carries
`var_perm_sym`'s "same E0/E2 hedge", so the spec does not settle it either.

**The transpose generator is the interesting one, and it has no `ind_op`.** Row and column
swaps are index permutations within one family; the transpose maps `X_{r,i}` to `X_{i,r}`,
i.e. it **exchanges two index families**. `ind_op`'s constructors
(`explenation generator.ml:39-49`) are identity, replace-with-fresh (`OpOn`), drop
(`OpOut`), prepend-∀ (`OpForall`), prepend-free (`OpPoint`), prime-and-differ
(`OpSum`/`OpPrim`), shift by a constant (`OpShift`/`OpShiftC`) and sequence (`OpSeq`). **None
swaps `FI` with `FR`.** This session found no numbered gap for it — `G10` is a *decision
variable* in index position, `G16` is the enum's size — so it is recorded here rather than
invented into the list, which is `docs/DECOMP_FORMAT_NOTES.md`'s to keep.

## Constraint

`var_sqr_sym(array[int, int] of var int: x)`

Breaks the row, column and transpose symmetries of a square matrix of variables.

**Provenance of the signature:** not vendored in this repo, and **weak**.
`tools/data/minizinc-2.10.1-globals.txt:130` carries the *name* only; there is no `.mzn` in
this checkout. `decomps/var_sqr_sym.md` is a seven-line pointer to `decomps/var_perm_sym.md`
and gives no argument list, and `decomps/var_perm_sym.md:3-6` states its own provenance as
"read off `CHRISTMAS_LIST.md` §3 alone — not independently checked against a spec text". The
signature above is this entry's rendering of that prose; **treat it as recall, and as the
weakest line in this file.**

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:145`, literature cell, verbatim:

> Chu & Stuckey 2011 (above)

— the same *Symmetries and lazy clause generation* (IJCAI 2011) the lex row cites, described
at `CHRISTMAS_LIST.md:142` as establishing that static symmetry breaking is LCG-compatible
**provided the added constraints have explaining propagators**, and as not being a dedicated
`lex` explanation paper.

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session. The observation
that the cited result is a *conditional* whose hypothesis is exactly what this method would
supply is made once, in [`var_perm_sym`](var_perm_sym.md#published-explanation), and is not
repeated as if it were independent evidence.

## Solver support

| | |
|---|---|
| Chuffed | native (`sym-break.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | absent (no `[C]` on the row) |

Source: `CHRISTMAS_LIST.md:145`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers both names on the row.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `var_sqr_sym`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/var_sqr_sym.md` → `decomps/var_perm_sym.md` → `decomps/lex_less.md`; shape
**B** in `decomps/_shapes-seq.md:31-62`, renumbered **S5** in `decomps/_shapes.md:155-175`
(which names `var_sqr_sym` among S5's twelve instances), plus modifier **M-row**
(`decomps/_shapes.md:44-47`).

One `lex_lesseq` per generator, each expanded through
[`lex_lesseq`](lex_lesseq.md#decomposition-used-here)'s chain. For a row swap `(r, r+1)`:

```
tied_{r,1}  = true
tied_{r,i+1} ⇔ tied_{r,i} ∧ (X_{r,i} = X_{r+1,i})       rule3, fixed shift by 1 in i
tied_{r,i}  → X_{r,i} ≤ X_{r+1,i}                        rule4 guard
```

for a column swap the same with `I` and `R` exchanged (`decomps/orbitope.md:5-6` describes
that exchange for the orbitope shape and it is the same move here), and for the transpose the
index-family swap that has no `ind_op`.

**The row index itself is not a blocker** and this session re-checked it: `ind_name` includes
`R` (`explenation generator.ml:5`), `ind_fam` includes `FR` (`:38`), `printind_name` renders
it as `r` (`:485`), and the shipped `table` decomposition uses it (`:862-864`, emitted from the
three-index `x3ac` at `:875`). That is W2-A's checked negative
(`docs/DECOMP_FORMAT_NOTES.md:94-95`), and [`lex2`](lex2.md#read-this-first-a-matrix-is-a-modifier-not-a-shape)
carries this session's one sharpening of it: **no generated artifact has ever contained an `r`
index**, because `cata/table.tex` has held 0 rules since W1-T2 (measured 2026-09-21).

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/var_sqr_sym.tex` and
therefore no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{r,i}=t` (would be, from a three-index `xac`-style event) | — | **0** | not run: `X_{r,i} = X_{r+1,i}` has no representation (G3); and the transpose generator has no index operation |

## Generated rules

**None.** There is no `cata/var_sqr_sym.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

The binding gap is the family's: variable-vs-variable comparison. Behind it sit G17 (the
`tied` pivot) and W1-T10's raise, both inherited from S5.

**Two things this entry establishes that are specific to it, and they point opposite ways.**
The square case is *better* off than [`var_perm_sym`](var_perm_sym.md) on G7 — its generators
come from the matrix's shape, not from instance data — and *worse* off on the transpose, which
needs an index operation that exchanges two families and does not exist. Neither is measured;
both are readings, and the first depends on a signature this repo does not vendor.

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two independent failures, either sufficient: no published shape is in the repo
(`catalog/_literature/` has no file for Chu & Stuckey 2011, and `catalog/README.md` step 2
forbids writing one from memory), and there are **0** generated rules, so there is no premise
to place in an implication order.

**A prior, recorded as a prior**, and it is [`var_perm_sym`](var_perm_sym.md#calibration-w3-t5-d-0013)'s
unchanged: the citation is reached by a "(above)" cross-reference to the lex row, which says
no dedicated `lex` explanation paper was found, so if that row is right there is no
symmetry-breaking rule to calibrate against either. Not claimed — the paper is unread.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `X_{r,i} = X_{r+1,i}` is variable-vs-variable; no comparison can be written |
| `G17` | no pivot-elimination pass, so `tied_{r,i}` cannot be removed from a finished rule |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printer path that now **raises** (`explenation generator.ml:488`, `:517`) |
| — (no number) | **an index operation exchanging two families**, for the transpose generator. `ind_op` (`:39-49`) has no such constructor; `G10` and `G16` are different things. Recorded, not numbered |
| `G7` | **probably *not* this entry's**, unlike [`var_perm_sym`](var_perm_sym.md)'s: a square matrix's generators are fixed by its shape, so the comparison count is a function of the arity. Conditional on a signature this repo does not vendor |
| — | **not a gap: the row index.** `R`/`FR` exist and `table`'s decomposition uses them (`:5`, `:38`, `:485`, `:862-864`, `:875`) — though no artifact has ever printed one |

Extensions: **E0 / E2** (`CHRISTMAS_LIST.md:145`), with `decomps/var_sqr_sym.md:6`'s explicit
"same E0/E2 hedge as `var_perm_sym`" carried across rather than resolved.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `grep -o '\frac' cata/table.tex | wc -l` → **0**; a search for an `r` index across
  `cata/*.tex` → no match. The basis for the "`R` is unwitnessed in output" remark.
- `ls cata/` → 16 `.tex` files, none named `var_sqr_sym.tex`. `find . -name '*.mzn'` → empty.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E0", "E2"]`, `CHRISTMAS_LIST.md` line 145.
  Confirms the stub's tier row; D-0014 left it untouched.
- `explenation generator.ml` read, not run → `:5`, `:38`, `:485`, `:862-864`, `:875` (the `R`
  index family end to end), `:39-49` (`ind_op`'s constructors — the basis for "nothing
  exchanges two families"), `:488`/`:517` (the raising printers), `:879-893` (the fifteen
  `explainall` calls — none is `var_sqr_sym`).
- `CHRISTMAS_LIST.md:145`, `:142`, `:106-109` read → the citation, the solver cells, the legend.
- `decomps/var_sqr_sym.md`, `decomps/var_perm_sym.md`, `decomps/lex_lesseq.md`,
  `decomps/orbitope.md`, `decomps/_shapes.md:44-47,155-175`, `decomps/_shapes-seq.md:31-62`
  read → the pointer chain, the row/column/transpose reading, S5, M-row.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 75, 85, 88-90, 94-104` read → G3, G7, G17, the checked
  negative on `R`, and the `D2` withdrawal.
- **Not fetched, not written:** no paper. The two entry-specific readings in Status are
  labelled as readings in place.
