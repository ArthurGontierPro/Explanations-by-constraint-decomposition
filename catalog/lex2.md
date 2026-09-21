# `lex2`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex2`, and no claim of that kind is
> made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E0` (shared row with `lex_less`, `lex_lesseq`, `strict_lex2`, `lex2_strict`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/lex2.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — `CHRISTMAS_LIST.md:142` records that no dedicated `lex` explanation paper was found |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/*.tex`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: a matrix is a modifier, not a shape

`lex2` orders the **rows of a matrix** pairwise under `lex_lesseq`. Against
[`lex_lesseq`](lex_lesseq.md) that adds exactly one thing — a second, row-like index — and
`decomps/_shapes.md:44-47` classifies that as the modifier **M-row**, "replicate over the `R`
index family", not as a shape. `lex2` is therefore **S5 + M-row**, and everything about the
chain itself — the `tied_i` accumulated-state auxiliary, the `rule3` conjunction with a fixed
shift by 1, the `rule4` guard clause — is established in [`lex_less`](lex_less.md) and
[`lex_lesseq`](lex_lesseq.md) and not re-derived here.

**The row index is a checked negative and this session re-checked it.** `ind_name` is
`I of int | T of int | P of int | R of int` (`explenation generator.ml:5`); the index-family
enum `ind_fam` has `FR` (`:38`); `printind_name` renders `R a` as `r` (`:485`); the shipped
`table` decomposition addresses its rows with `onr` (`:862-864`) and is emitted from a
**three-index** global event, `x3ac = Global_event (true, X, [Ind (I 1, []); Ind (T 1, []);
Ind (R 1, [])], AC)` (`:875`). So a matrix's row index needs no new index family, exactly as
W2-A recorded (`docs/DECOMP_FORMAT_NOTES.md:94-95`, `decomps/_gaps-seq.md:43-46`).

**And one sharpening of that negative, measured today.** The `R` family is exercised in the
*source* and is **not witnessed in any output**: since W1-T2 refused `table`'s branch over the
undefined `D_4`, `cata/table.tex` holds **0** rules, and no shipped artifact contains an `r`
index at all (measured 2026-09-21: `grep -o '\frac'` over all 16 files gives `table` = 0, and a
search for an `r` index across `cata/*.tex` returns nothing). The negative stands — `R` is in
the type, the printer and a decomposition — but "already used by `table`" now means *used in
`table`'s source*, not *seen on a page*. Anyone landing M-row should expect the row index's
first appearance in output to be their own.

## Constraint

`lex2(array[int,int] of var int: x)`

The rows of the matrix `x` are lexicographically non-decreasing: each adjacent pair of rows
satisfies `lex_lesseq`. A standard symmetry-breaking constraint for row-and-column-symmetric
matrix models.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:77` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/lex2.md:3-4` describes the
constraint in prose ("orders the rows of a matrix pairwise under `lex_lesseq`") without giving
an argument list; the signature above is this entry's rendering of that prose. Treat it as
recall, and as the weakest line in this file.

**One thing the prose does not settle and this entry will not pretend it does.** `lex2` in
common usage orders rows *and* columns; `decomps/lex2.md` describes rows only, and
`decomps/orbitope.md:3-6` treats "rows **and** columns of the same matrix" as the *orbitope*
shape. Which of the two MiniZinc 2.10.1's `lex2` is cannot be checked here, because no `.mzn`
is vendored. **It makes no difference to this entry's verdict**: column ordering is the same
Shape B chain with the roles of `I` and `R` swapped (`decomps/orbitope.md:5-6`), so it meets
G3 identically.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:142`, literature cell, verbatim:

> Chu & Stuckey, *Symmetries and lazy clause generation* (IJCAI 2011) — static symmetry
> breaking is LCG-compatible provided the added constraints have explaining propagators; no
> dedicated `lex` explanation paper found

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session.

## Solver support

| | |
|---|---|
| Chuffed | native (`lex.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:142`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers all five names on the row, so this table is the family's; it is **not**
evidence that Chuffed's `lex.cpp` carries a distinct `lex2` propagator rather than posting a
chain of `lex_lesseq`s.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `lex2`, and none of
the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/lex2.md` (which covers `lex2`, `strict_lex2` and `lex2_strict` together);
shape **B** in `decomps/_shapes-seq.md:31-62`, renumbered **S5** in `decomps/_shapes.md:155-175`,
plus modifier **M-row** (`decomps/_shapes.md:44-47`).

The decomposition this project would use: [`lex_lesseq`](lex_lesseq.md#decomposition-used-here)'s
chain, replicated over the row index `r`, one instance per adjacent row pair —

```
tied_{r,1}  = true
tied_{r,i+1} ⇔ tied_{r,i} ∧ (X_{r,i} = X_{r+1,i})      rule3, fixed shift by 1 in i
tied_{r,i}  → X_{r,i} ≤ X_{r+1,i}                       rule4 guard
```

**The only addition versus a single `lex_lesseq` call is the second index**
(`decomps/lex2.md:8-10`). Note what that means for the blocker: the compared pair is now two
*rows of the same array* rather than two arrays, but `X_{r,i}` against `X_{r+1,i}` is still
variable-vs-variable, so **replication over rows neither adds nor removes G3**
(`decomps/lex2.md:20-22`).

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex2.tex` and therefore
no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{r,i}=t` (would be, from a three-index `xac`-style event) | — | **0** | not run: `X_{r,i} = X_{r+1,i}` has no representation (G3) |

The walls, in the order they would be met — established in
[`lex_less`](lex_less.md#scope-of-this-entry) and not re-derived: **G3** stops the first line;
**W1-T10**'s raise would make the `tied` auxiliary a loud failure rather than a silent one;
**G17** would leave `tied_{r,i}` in the premises even if a rule printed. M-row adds no fourth
wall — that is the checked negative above.

## Generated rules

**None.** There is no `cata/lex2.tex` (`ls cata/` → 16 files, none of this name; 2026-09-21).
Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

The gap is the family's, not the matrix's. That is the useful content of this entry: a reader
might reasonably expect a matrix constraint to need new engine machinery, and it does not —
`R` exists, `FR` exists, the printer handles it, and a shipped decomposition uses it. What
blocks `lex2` is the same missing literal form that blocks a single `lex_lesseq`, and it would
be a mistake to schedule matrix support as its own piece of work.

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two independent failures, either sufficient: no published shape is in the repo
(`catalog/_literature/` has no file for Chu & Stuckey 2011, and `catalog/README.md` step 2
forbids writing one from memory), and there are **0** generated rules, so there is no premise
to place in an implication order.

**A prior, recorded as a prior.** `CHRISTMAS_LIST.md:142` states that no dedicated `lex`
explanation paper was found; if that holds on reading, the eventual verdict is
`no published rule exists`. Not claimed here: the row is a previous session's note and the
paper is unread.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `X_{r,i} = X_{r+1,i}` is variable-vs-variable; the decomposition cannot be written. Replication over rows does not add or remove it |
| `G17` | no pivot-elimination pass, so `tied_{r,i}` cannot be removed from a finished rule |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printer path that now **raises** (`explenation generator.ml:488`, `:517`) |
| — | **not a gap: the row index.** `R`/`FR` exist and a shipped decomposition uses them (`:5`, `:38`, `:485`, `:862-864`, `:875`). Recorded so nobody re-derives M-row as a blocker — but see the sharpening above: no output has ever contained an `r` index |
| `G7` | **not this entry's.** `lex_chain_*`'s *instance-dependent* number of row pairs routes to `D2`'s missing printer (`docs/DECOMP_FORMAT_NOTES.md:96-104`). `lex2`'s pair count is fixed by the matrix's arity, so it does not need it |

Extensions: **E0** (`CHRISTMAS_LIST.md:142`; `decomps/lex2.md:20` agrees, "`rule3`/`rule4` per
`lex_less`, `R`-indexed replication already available"), with `decomps/lex_less.md:27-31`'s
qualification: E0 means the *schemas* exist, and here the **event vocabulary** does not.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `grep -o '\frac' cata/<f>.tex | wc -l` over **all 16** artifacts → `table` **0**,
  `regular`/`roots`/`range`/`among` 0, the rest 1-6. The basis for the "`R` is unwitnessed in
  output" sharpening.
- `ls cata/` → 16 `.tex` files, none named `lex2.tex`. A search for an `r` index across
  `cata/*.tex` → no match.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → `lex2`
  still tier `D literature + solver-native`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 142.
  Confirms the stub's tier row; D-0014 moved tier A 36 → 43 and out of scope 35 → 28 and left
  this row untouched.
- `explenation generator.ml` read, not run → `:5` (`ind_name` includes `R`), `:38` (`ind_fam`
  includes `FR`), `:485` (`printind_name` renders `R` as `r`), `:862-864` (`table`'s `onr`),
  `:875` (`x3ac`, the three-index global event), `:488`/`:517` (the raising printers),
  `:879-893` (the fifteen `explainall` calls — none is `lex2`).
- `CHRISTMAS_LIST.md:142`, `:106-109` read → the citation and the solver legend.
- `decomps/lex2.md`, `decomps/lex_less.md`, `decomps/lex_lesseq.md`, `decomps/orbitope.md`,
  `decomps/_shapes.md:44-47,155-175`, `decomps/_shapes-seq.md:31-62`,
  `decomps/_gaps-seq.md:43-46` read → the row-replication argument, M-row, S5, the checked
  negative, the rows-vs-columns question.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-104` read → G3, G17, the three families
  that hit G3, the checked negative and the `D2` withdrawal.
- **Not fetched, not written:** no paper.

**Discrepancy noted, not fixed (this session does not own that file).**
`decomps/lex2.md:15` cites `x3ac` at "line ~727". Measured 2026-09-21: **875**. The claim it
supports — that `R` already exists for a second, row-like dimension — holds at the new
line.
