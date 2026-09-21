# `lex_chain_greater`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_chain_greater`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` (shared row with the other five `lex_chain_*` names) |
| **Status** | `nothing generated — blocked on G3` — **and, for a chain of instance-dependent length, on `G7`** |
| **Generated** | **0** rules — there is no `cata/lex_chain_greater.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:144` literature cell reads `none` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/*.tex`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first

`lex_chain_greater` is [`lex_chain_less`](lex_chain_less.md) with its operands exchanged: MiniZinc defines `lex_greater(x,y)` as `lex_less(y,x)` (`CHRISTMAS_LIST.md:143`), and the chain inherits that swap pair by pair. **Everything about the chain, the matrix
dimension and the two wave-two claims is established in
[`lex_chain_lesseq`](lex_chain_lesseq.md)** — that entry is this family's base and states, once,
which of the two claims survived. In one line each, because a reader must not have to follow a
link to learn which applies:

- **the `R` row-index checked negative STANDS** — matrix row indexing is not a gap
  (`docs/DECOMP_FORMAT_NOTES.md:94-95`, re-checked against the current generator: `ind_name`
  `:5`, `ind_fam` `:38`, `printind_name` `:430`, `table`'s `onr` `:864`);
- **the `D2` variable-length-chain checked negative was WITHDRAWN** — the number of chained
  pairs is instance data, `D2` is the right hook, and `printind_set` **raises** on it
  (`explenation generator.ml:464`; `docs/DECOMP_FORMAT_NOTES.md:96-107`, "treat variable-length
  chains as blocked on the same missing printer as G7").

**What the swap costs: nothing.** `CHRISTMAS_LIST.md:143` states the reduction in its
own route cell — "an argument swap, not a new shape" — and [`lex_greater`](lex_greater.md)
carries it with its citation. Exchanging `X` and `Y` leaves `Y_i = X_i` exactly as
unrepresentable as `X_i = Y_i`, so the swap costs no gap the `_less` form does not already pay
and removes none either.

## Constraint

`lex_chain_greater(array[int,int] of var int: x)`

Each adjacent pair of `x`'s vectors is lexicographically **strictly** decreasing: every pair satisfies [`lex_greater`](lex_greater.md), which is [`lex_less`](lex_less.md) with its arguments exchanged.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:79` carries the *name* only; this checkout holds no
`.mzn` file. `decomps/lex_chain.md` describes the family in prose and gives no argument list, so
the line above is recall and is the weakest line in this file. Which dimension is chained is a
modelling detail this repo does not fix, and nothing below depends on it: a second dimension is
the modifier **M-row** either way (`decomps/_shapes.md:48`).

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:144` reads, verbatim:

> none

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. **No published rule shape is stated in this entry, from memory or otherwise.**
No web access was used and no paper was fetched. The adjacency to `CHRISTMAS_LIST.md:142`'s
Chu & Stuckey citation, and why this entry takes its own row instead, is set out in
[`lex_chain_lesseq`](lex_chain_lesseq.md#published-explanation).

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:144`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. One
solver cell covers all six names on the row. Chuffed explains the single pair with a propagator
(`lex.cpp`, row 142/143) and the chain by decomposition.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes any `lex_chain_*`,
and none of the fifteen `explainall` calls (lines 879-893) mentions one.
**Emitted by:** nothing.
**Spec:** **`decomps/lex_chain.md`** — its first line is `# lex_chain (covers `lex_chain_*`)`.

> **Stub field corrected.** The auto-stub read `**Spec:** none — this constraint has no
> `decomps/lex_chain_greater.md`.` That probe is an exact-filename `os.path.isfile` and it misses a
> spec written to cover a family under the family's name. A spec exists and this entry is
> written against it.

Shape **S5 + M-row** (`decomps/_shapes.md:155-174` and `:48`; `:165-169` lists `lex_chain`
among S5's twelve instances by name). Per adjacent pair the chain is
[`lex_chain_less`](lex_chain_less.md)'s, unchanged, and the whole block is then replicated over the
`R` index family. `tied_i` is a **genuine auxiliary**: an accumulated fact with no
`Global_devent` standing for it, unlike `increasing`'s `B_1`
(`explenation generator.ml:830-831`), which is a reification of `X_i ≥ t` in the same `Decomp`
and is substituted back before anything prints.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex_chain_greater.tex` and
therefore no `%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i,r}=t` (would be, from a three-index event like `x3ac`) | — | **0** | not run: the pairwise comparison has no representation (G3) |

Four walls, enumerated once in
[`lex_chain_lesseq`](lex_chain_lesseq.md#scope-of-this-entry) and not re-derived: **G3** stops
the pairwise comparison; **W1-T10**'s raise (`explenation generator.ml:488`, `:517`) would make
the auxiliary a loud failure writing no file; **G17** would leave `tied_i` in the premises; and
**G7** leaves the number of chained pairs unstatable. None has been run against, because the
first blocks the input.

## Generated rules

**None.** There is no `cata/lex_chain_greater.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`** — and, for a chain of instance-dependent length, on
**`G7`**.

The argument swap moves nothing: G3 is the binding gap and is not this constraint's alone
(`docs/DECOMP_FORMAT_NOTES.md:88-90`: three independent families). G7 sits beside it rather than
behind it, because the two are independent: closing G3 would let a *fixed-length* chain be
written and still leave "how many pairs" unstatable, and giving `D2` a printer would not make a
variable-vs-variable comparison expressible.

Nothing here is validated, flagged or refuted. What is a finding is what is *not* blocking —
the matrix dimension.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:144` records no explanation for this constraint, the condition
`catalog/TEMPLATE.md` attaches to this verdict. It is a statement about the repo's literature
index — one session of web research over all 118 globals (`CLAUDE.md`, "Context budget") — and
not about the literature; this session did not search the web. It differs on purpose from
[`lex_lesseq`](lex_lesseq.md)'s `pending sourcing (C2)`, whose row names a paper.

There are in any case **0** generated rules on this side, so no implication order could be
stated even if a shape were sourced. **Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** The pairwise variable-vs-variable comparison has no representation, so the decomposition cannot be written at all (`docs/DECOMP_FORMAT_NOTES.md:34-41`) |
| `G7` | the chain's length is instance data; `D2 of ind_name list` is the right hook and raises for want of a printer (`explenation generator.ml:464`). W2-A's checked negative on this was **withdrawn** (`docs/DECOMP_FORMAT_NOTES.md:96-107`) |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule (`:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117` |
| — | **row indexing is NOT a gap** — checked negative, re-checked today (`docs/DECOMP_FORMAT_NOTES.md:94-95`) |

Extensions: **E0** (`CHRISTMAS_LIST.md:144`), with the route cell's own rider, verbatim:
"**E0**, but MiniZinc's decomposition branches on instance data — one entry per variant". Read
it with `decomps/lex_less.md:27-31`'s qualification: E0 means the rule *schemas* exist; here
neither the event vocabulary nor the index-set printer does.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `grep -o '\frac' cata/table.tex | wc -l` → **0**, and a search for an `r` index across
  `cata/*.tex` returns nothing — the sharpening of the `R` negative, stated in full in
  [`lex_chain_lesseq`](lex_chain_lesseq.md#read-this-first-two-wave-two-claims-and-only-one-of-them-survived).
- `ls cata/` → 16 `.tex` files, none named `lex_chain_greater.tex`.
- `python3 tools/mzn_coverage.py --rank` → `A no-literature + solver-decomposes`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:144`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:5`, `:38`, `:430`, `:459`, `:461`, `:464`,
  `:488`, `:517`, `:766`, `:830-831`, `:862-864`, `:875`, `:879-893`. **Every line number was
  checked against the current file today** (W1-T14).
- `CHRISTMAS_LIST.md:142`, `:144`, `:106-108` read → literature, solver and route cells, legend.
- `decomps/lex_chain.md`, `decomps/lex_less.md`, `decomps/lex_less.md`,
  `decomps/_shapes.md:48, 155-174`, `decomps/_shapes-seq.md:31-62` read → the family spec, the
  chain, M-row, S5.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-95, 96-107, 115-117` and
  `docs/DECISIONS.md:78` read → the gaps, the two checked negatives, W1-T10, D-0004.
- `tools/data/minizinc-2.10.1-globals.txt:79` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.

**Discrepancies noted, not fixed:** four, listed in
[`lex_chain_lesseq`](lex_chain_lesseq.md#how-this-entry-was-produced). They apply to this entry
too and are not repeated.
