# `value_precede_chain`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `value_precede_chain`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecode `E0` (shared row with `value_precede`) |
| **Status** | `nothing generated — blocked on G7` — **and, behind it, on `G17`**, which already blocks [`value_precede`](value_precede.md) |
| **Generated** | **0** rules — there is no `cata/value_precede_chain.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:140` literature cell reads `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first

`value_precede_chain(c, x)` is `k-1` independent copies of [`value_precede`](value_precede.md),
one per consecutive pair of the value sequence `c`. `decomps/value_precede_chain.md:3-7` states
exactly that and nothing else:

> Instance of `decomps/value_precede.md` (Shape B): `value_precede_chain(c, x)` for a value
> sequence `c = [c_1,...,c_k]` is `value_precede(c_j, c_{j+1}, x)` for every consecutive pair
> `j ∈ [1,k-1]`. Same auxiliary `b_i` per pair (or one two-state chain per pair — either way,
> `k-1` independent copies of `value_precede`'s decomposition, not a new shape). Same E-code
> (E0) and same auxiliary-leak caveat. No new file needed beyond this pointer.

Everything about one copy — the S5 accumulated-state chain, the `b_i` auxiliary, why **G3 does
not apply**, why G17 does, and the W1-T10 raise — is established in
[`value_precede`](value_precede.md) and is not re-derived here.

**Which of the two wave-two claims about this family applies here.** The `D2` one, and it is
the reason this entry's binding gap differs from its base's:

- **The `D2` variable-length-chain checked negative was WITHDRAWN**, and
  `docs/DECOMP_FORMAT_NOTES.md:96-98` names `value_precede_chain` in its scope. `c` is an
  externally given sequence of values — an explicit list, not a range — which is precisely what
  `ind_set`'s `D2 of ind_name list` was supposed to carry. It has no printer:
  `printind_set` **raises** on `D2` (`explenation generator.ml:464`), and
  `docs/DECOMP_FORMAT_NOTES.md:105-107` concludes "treat variable-length chains as blocked on
  the same missing printer as G7".
- **The `R` row-index checked negative STANDS but is irrelevant here** — it is about matrices
  (`docs/DECOMP_FORMAT_NOTES.md:94-95`), and this constraint chains over values, not rows.

## Constraint

`value_precede_chain(array[int] of int: c, array[int] of var int: x)`

For each consecutive pair `c_j, c_{j+1}` of the value sequence `c`: if `c_{j+1}` occurs in `x`,
some earlier position holds `c_j`. The chained form of [`value_precede`](value_precede.md),
used to break symmetry among more than two interchangeable values at once.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:128` carries the *name* only, and this checkout holds
no `.mzn` file. `decomps/value_precede_chain.md:3-5` names the arguments in prose (`c`, `x`)
and gives their meaning (`c = [c_1,...,c_k]`, a value sequence) but no MiniZinc types; the
line above adds the types from `decomps/value_precede.md:3-4`'s `s`, `t` **par** convention
(D-0003, `docs/DECISIONS.md:52`). Treat it as recall built on an in-repo spec.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:140` reads, verbatim:

> none

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. **No published rule shape is stated in this entry, from memory or otherwise.**
No web access was used and no paper was fetched.

## Solver support

| | |
|---|---|
| Chuffed | native (`value-precede.cpp`) |
| Geas | **`[G]`** present |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:140`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. One
solver cell covers this name and `value_precede`. **Stub field corrected:** the auto-stub's
Chuffed cell read bare `native`; the row names the file. All three solver columns are filled,
which is worth stating beside a status of `nothing generated`.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes this constraint, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/value_precede_chain.md` (7 lines, a pointer to `decomps/value_precede.md`).
Shape **S5** (`decomps/_shapes.md:155-174`), listed among its twelve instances by name at
`:165-166` as the "∨ form, guarded literal `X_i = t`, E0" group.

Per pair `j`, from `decomps/value_precede.md:8-10`:

```
b_1 = false                                       base: nothing precedes position 1
b_{i+1} ⇔ b_i ∨ (X_i = c_j)     i ∈ [1,n_x-1]     rule4, fixed shift by 1
X_i = c_{j+1} → b_i             i ∈ [1,n_x]       rule3 (or its rule4 contrapositive), AC
```

and that block is repeated for `j ∈ [1,k-1]`. **The repetition is the entry.** One copy needs
nothing the engine lacks (`decomps/value_precede.md:20-22`: "mechanically nothing new is
required to *encode* this decomposition"); `k-1` copies for an instance-given `k` need an index
set the printer cannot write.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No `explainall` call names this
constraint, so there is no `cata/value_precede_chain.tex` and no
`%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`, `explenation generator.ml:869`) | — | **0** | not run: the chain's index set has no printer (G7) |

Two walls, in the order they would be met:

1. **G7 stops the general form.** The chain ranges over the given sequence `c`, an explicit
   list of values. `D2 of ind_name list` is the type-level hook and `printind_set` raises on it
   (`:464`), so the quantifier "for every consecutive pair of `c`" cannot be printed.
   **A fixed `k` would sidestep it** — `value_precede_chain` at `k = 2` *is*
   [`value_precede`](value_precede.md), and at any fixed `k` it is `k-1` separate `Decomp`
   groups written out longhand — which is exactly what `CHRISTMAS_LIST.md:144`'s neighbouring
   "one entry per variant" rider describes for the `lex_chain_*` family.
2. **G17 then stops the copies being clean**, exactly as for the single constraint: `b_i` is a
   genuine auxiliary, nothing substitutes it back, and no pass removes it afterwards. Which of
   [`value_precede`](value_precede.md#scope-of-this-entry)'s three outcomes occurs is **not
   established** — the walk unfolds to an `X`-only base case, or cuts a cycle (`R`) and loses
   the candidate, or reaches a printer with a bare `b_i` and **raises** (`:488`, `:517`,
   W1-T10). Nobody can run what nobody has encoded.

## Generated rules

**None.** There is no `cata/value_precede_chain.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G7`** — and, behind it, on **`G17`**.

The two are ordered, not alternatives. G7 blocks the *general* constraint, whose chain length
is instance data; G17 blocks *every* instance of it, fixed length or not, from producing a rule
free of `b_i`. Closing G7 alone would buy the general form and leave the auxiliary; closing
G17 alone would buy each fixed `k` and leave the general form unstatable.

This entry inherits [`value_precede`](value_precede.md)'s headline finding and narrows it:
**G3 does not apply here either** — the guarded literal is `X_i = c_j` against a parameter — so
the input format's expressiveness is not what stops this constraint, unlike every `lex_*` entry
in this family. Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:140` records no explanation for this constraint, the condition
`catalog/TEMPLATE.md` attaches to this verdict. It is a statement about the repo's literature
index — one session of web research over all 118 MiniZinc globals (`CLAUDE.md`, "Context
budget") — and not about the literature; this session did not search the web and has no access.
Three solvers ship a native propagator; a propagator is not a published rule shape and is not
evidence for or against this verdict.

There are in any case **0** generated rules on this side, so no implication order could be
stated even if a shape were sourced. **Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G7` | **the binding one, and the one that separates this entry from its base.** The chain runs over an instance-given value sequence; `D2 of ind_name list` is the right hook and raises for want of a printer (`explenation generator.ml:464`). W2-A's checked negative on this was **withdrawn**, naming this constraint (`docs/DECOMP_FORMAT_NOTES.md:96-107`) |
| `G17` | behind it: no pivot-elimination pass, so `b_i` cannot be removed from a finished rule (`:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the two printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117` |
| — | **`G3` is NOT this entry's** — the guarded literal is `X_i = c_j` against a parameter (D-0003), not `X_i = Y_i`. `decomps/_shapes.md:165-166` draws that line inside S5's own instance list |

Extensions: **E0** (`CHRISTMAS_LIST.md:140`), and per `decomps/value_precede_chain.md:6` the
chain carries "same E-code (E0) and same auxiliary-leak caveat" as the single constraint.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `ls cata/` → 16 `.tex` files, none named `value_precede_chain.tex`.
- `python3 tools/mzn_coverage.py --rank` → `B no-literature + solver-native`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:140`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:6` (`ind_set`, where `D2` lives), `:464` (the
  `D2` raise), `:488`, `:517` (the printers that raise on a bare `B`), `:622-630`
  (`filter_branches`, the `R` cut), `:869` (`xac`), `:879-893` (the fifteen `explainall`
  calls). **Every line number was checked against the current file today** (W1-T14).
- `CHRISTMAS_LIST.md:140`, `:144`, `:106-108` read → the literature, solver and route cells,
  the neighbouring "one entry per variant" rider, and the legend.
- `decomps/value_precede_chain.md` (all 7 lines), `decomps/value_precede.md`,
  `decomps/_shapes.md:155-174` read → the pointer, the decomposition, S5 and its instances.
- `docs/DECOMP_FORMAT_NOTES.md:85, 94-95, 96-107, 115-117` and `docs/DECISIONS.md:52, 78`
  read → G17, the `R` negative that stands, the `D2` one that was withdrawn, W1-T10, D-0003
  and D-0004.
- `tools/data/minizinc-2.10.1-globals.txt:128` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.

**Discrepancies noted, not fixed:** the three listed in
[`value_precede`](value_precede.md#how-this-entry-was-produced) — the stale `incr` line number
in `decomps/value_precede.md:15`, the four files that still say a bare `B` prints `"ERROR B "`,
and `CHRISTMAS_LIST.md:140`'s "already works". All apply to this entry's sources too.
