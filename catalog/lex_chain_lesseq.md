# `lex_chain_lesseq`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_chain_lesseq`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` (shared row with `lex_chain_less`, `lex_chain_greater`, `lex_chain_greatereq` and both `*_orbitope` variants) |
| **Status** | `nothing generated — blocked on G3` — **and, for a chain of instance-dependent length, on `G7`** |
| **Generated** | **0** rules — there is no `cata/lex_chain_lesseq.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:144` literature cell reads `none` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/*.tex`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: two wave-two claims, and only one of them survived

This is the entry where the family's two recorded findings have to be told apart, because they
point in opposite directions and both are about this constraint.

**1. The `R` row-index checked negative STANDS.** `docs/DECOMP_FORMAT_NOTES.md:94-95`:

> **Row/matrix indexing is NOT a gap.** The `R of int` index family, already used by `table`,
> covers a second row-like dimension for `lex2`, the orbitopes and `var_sqr_sym`. (W2-A)

Re-checked today by reading the generator: `ind_name = I of int | T of int | P of int | R of int`
(`:5`), the index-family enum `ind_fam` has `FR` (`:38`), `printind_name` renders `R a` as `r`
(`:430`), and the shipped `table` decomposition addresses its rows with `onr` (`:864`) from a
three-index global event `x3ac` (`:875`). Addressing rows needs no new index family.

**2. The `D2` chain-length checked negative was WITHDRAWN**, and it is this constraint's.
`docs/DECOMP_FORMAT_NOTES.md:96-107`, whose heading is "Instance-dependent chain length IS a
gap after all": W2-A had recorded `D2 of ind_name list` as the escape hatch for a chain of
instance-dependent length (`lex_chain_*`, `value_precede_chain`, `seq_precede_chain`), and that
is withdrawn — "treat variable-length chains as blocked on the same missing printer as G7"
(`:105-107`). Measured today: `D2` is used by no decomposition, and `printind_set`
**raises** on it (`explenation generator.ml:464`).

So: **the matrix is free and the chain is not.** `CHRISTMAS_LIST.md:144`'s route cell says
MiniZinc's own decomposition "branches on instance data — one entry per variant"; what that
costs here is gap `G7`'s missing printer, not a new index family.

**A sharpening of claim 1 that this entry can make.** The `R` family's only use in the repo
pairs it with the index set `D 4` (`onr = OpOn (FR, D 4)`, `:766`), and `D 4` is *not* a set
the printer defines — `ind_set_defined` admits `D 1 | D 2 | D 3` only (`:459`) and
`printind_set_int` raises otherwise (`:461`). That is why W1-T2 refuses `table`'s branches:
measured 2026-09-21, `grep -o '\frac' cata/table.tex | wc -l` → **0**, and no `r` index appears
anywhere in `cata/*.tex`. The negative stands — `R` is in the type, the printer and a
decomposition — but **`R` has never reached a page**, and whoever lands M-row should expect its
first appearance in output to be their own, with an index set they must also define.

## Constraint

`lex_chain_lesseq(array[int,int] of var int: x)`

The columns of the matrix `x` are lexicographically non-decreasing: each adjacent pair of
columns satisfies `lex_lesseq`. A chained symmetry-breaking constraint, the multi-vector
generalisation of a single [`lex_lesseq`](lex_lesseq.md).

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:83` carries the *name* only; this checkout holds no
`.mzn` file. `decomps/lex_chain.md` describes the family in prose ("the same row-pairwise
`lex_less`/`lex_lesseq` replication", `:11-12`) and gives no argument list. The signature above
is recall and is the weakest line in this file; **which dimension is chained — rows or
columns — is a modelling detail this repo does not fix**, and nothing below depends on it,
because [`lex2`](lex2.md) establishes that a second dimension is the modifier **M-row** either
way (`decomps/_shapes.md:48`).

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:144` reads, verbatim:

> none

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. **No published rule shape is stated in this entry, from memory or otherwise.**
No web access was used and no paper was fetched.

The neighbouring row `CHRISTMAS_LIST.md:142` cites Chu & Stuckey, *Symmetries and lazy clause
generation* (IJCAI 2011) for `lex_less`/`lex_lesseq` and says in the same cell that *no
dedicated `lex` explanation paper was found*. This constraint is filed on its own row, which
reads `none`; that is the row this entry takes, and the verdict below follows from it.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:144`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. One
solver cell covers all six names on the row. **Note the contrast with
[`lex_lesseq`](lex_lesseq.md)**, which is `native` (`lex.cpp`) `[C]`: Chuffed explains the
single pair with a propagator and the chain by decomposition.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes any `lex_chain_*`,
and none of the fifteen `explainall` calls (lines 879-893) mentions one.
**Emitted by:** nothing.
**Spec:** **`decomps/lex_chain.md`** — its first line is `# lex_chain (covers `lex_chain_*`)`.

> **Stub field corrected.** The auto-stub read `**Spec:** none — this constraint has no
> `decomps/lex_chain_lesseq.md`.` That probe is an exact-filename `os.path.isfile`, and it
> misses a spec written to cover a family under the family's name. A spec exists and this
> entry is written against it.

Shape **S5 + M-row**: the accumulated-state chain of `decomps/_shapes.md:155-174`, replicated
over the `R` index family (`:48`). `decomps/_shapes.md:165-169` lists `lex_chain` among S5's
twelve instances by name. Per adjacent column pair, the chain is
[`lex_lesseq`](lex_lesseq.md#decomposition-used-here)'s, unchanged:

```
tied_1  = true
tied_{i+1} ⇔ tied_i ∧ (X_{i,r} = X_{i,r+1})       rule3, fixed shift by 1
tied_i → X_{i,r} ≤ X_{i,r+1}                      rule4 guard, every i
tied_n is accepting                               the lesseq relaxation
```

— and then that whole block is replicated for each `r`. `tied_i` is a **genuine auxiliary**: an
accumulated fact with no `Global_devent` standing for it, unlike `increasing`'s `B_1`
(`explenation generator.ml:830-831`), which is a reification of `X_i ≥ t` in the same `Decomp`
and is substituted back before anything prints.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex_chain_lesseq.tex` and
therefore no `%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i,r}=t` (would be, from a three-index event like `x3ac`) | — | **0** | not run: `X_{i,r} = X_{i,r+1}` has no representation (G3) |

**Four walls, in the order they would be met.** The first three are
[`lex_less`](lex_less.md#scope-of-this-entry)'s and are not re-derived; the fourth is this
entry's own.

1. **G3** stops the second line: variable-vs-variable comparison has no representation.
2. **W1-T10** — the accumulated-state auxiliary meets two printers that now **raise**
   (`explenation generator.ml:488`, `:517`), so generation would fail loudly and write no file
   rather than emit the old literal `"ERROR B "`.
3. **G17** — no pivot-elimination pass, so `tied_i` would stay in the premises even if a rule
   printed, which D-0004 (`docs/DECISIONS.md:78`) forbids by default.
4. **G7** — the number of chained pairs is instance data. `D2` is the right hook and has no
   printer (`:464`), so a chain of instance-dependent length cannot be stated. **This is the
   one wall that a single [`lex_lesseq`](lex_lesseq.md) does not meet**, and it is the whole
   content of the route cell's "one entry per variant".

None of the four has been run against, because the first one blocks the input.

## Generated rules

**None.** There is no `cata/lex_chain_lesseq.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`** — and, for a chain of instance-dependent length, on
**`G7`**.

G3 is the binding one and is not this constraint's alone:
`docs/DECOMP_FORMAT_NOTES.md:88-90` records three independent families hitting it. G7 is listed
beside it rather than behind it because the two are independent — closing G3 would let a
*fixed-length* chain be written and would still leave "how many pairs" unstatable, and giving
`D2` a printer would not make `X_{i,r} = X_{i,r+1}` expressible.

Nothing here is validated, flagged or refuted. **What is a finding, and is this entry's, is
what is *not* blocking**: the matrix dimension. Claim 1 above stands, re-checked against the
current generator.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:144` records no explanation for this constraint, which is the condition
`catalog/TEMPLATE.md` attaches to this verdict. Two qualifications, so it is not read as
stronger than it is:

- **It is a statement about the repo's literature index, not about the literature.** That index
  cost one session of web research over all 118 globals (`CLAUDE.md`, "Context budget") and is
  the source this catalog is required to use; this session did not search the web.
- **It differs from [`lex_lesseq`](lex_lesseq.md)'s `pending sourcing (C2)` on purpose.** Row
  142 names a paper and row 144 does not. The catalog's distinction is between "the list records
  no explanation" and "the list records one and nobody has sourced its shape".

There are in any case **0** generated rules on this side, so no implication order could be
stated even if a shape were sourced. **Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `X_{i,r} = X_{i,r+1}` and `X_{i,r} ≤ X_{i,r+1}` have no representation, so the decomposition cannot be written at all (`docs/DECOMP_FORMAT_NOTES.md:34-41`) |
| `G7` | **this entry's own, and not [`lex_lesseq`](lex_lesseq.md)'s.** The chain's length is instance data; `D2 of ind_name list` is the right hook and has no printer, so it raises (`explenation generator.ml:464`). W2-A's checked negative on this was **withdrawn** (`docs/DECOMP_FORMAT_NOTES.md:96-107`) |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule (`:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117` |
| — | **row indexing is NOT a gap** — checked negative, re-checked today. Listed here because its absence from this table is itself the finding (`docs/DECOMP_FORMAT_NOTES.md:94-95`) |

Extensions: **E0** (`CHRISTMAS_LIST.md:144`), with the route cell's own rider, quoted verbatim:
"**E0**, but MiniZinc's decomposition branches on instance data — one entry per variant". Read
it with `decomps/lex_less.md:27-31`'s qualification: E0 means the rule *schemas* exist; here
neither the event vocabulary nor the index-set printer does.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `grep -o '\frac' cata/table.tex | wc -l` → **0**; the same over all 16 files gives the census
  quoted above. A search for an `r` index across `cata/*.tex` returns nothing.
- `ls cata/` → 16 `.tex` files, none named `lex_chain_lesseq.tex`.
- `python3 tools/mzn_coverage.py --rank` → `A no-literature + solver-decomposes`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:144`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:5` (`ind_name`), `:38` (`ind_fam`), `:430`
  (`printind_name`), `:459`, `:461`, `:464` (`ind_set_defined`, the `D_k` raise, the `D2`
  raise), `:488`, `:517` (the printers that raise on a bare `B`), `:766` (`onr = OpOn (FR, D 4)`),
  `:830-831` (`incr`, the auxiliary that *does* wash out), `:862-864` (`table`, the only user of
  `onr`), `:875` (`x3ac`), `:879-893` (the fifteen `explainall` calls). **Every line number
  above was checked against the current file today** (W1-T14).
- `CHRISTMAS_LIST.md:142`, `:144`, `:106-108` read → the literature, solver and route cells,
  and the legend.
- `decomps/lex_chain.md`, `decomps/lex_lesseq.md`, `decomps/lex_less.md`,
  `decomps/_shapes.md:48, 155-174`, `decomps/_shapes-seq.md:31-62` read → the family spec, the
  chain, M-row, S5 and its instance list.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-95, 96-107, 115-117` read → G3, G17, the
  three families, the `R` negative that stands, the `D2` one that was withdrawn, and W1-T10.
- `docs/DECISIONS.md:78` read → D-0004.
- `tools/data/minizinc-2.10.1-globals.txt:83` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`decomps/_shapes.md:373-377` says `decomps/lex_chain.md` "was not corrected" when the `D2`
   negative was withdrawn.** It was: `decomps/lex_chain.md:3-9` carries a `Correction, W3-D
   2026-09-18` banner stating exactly that withdrawal. The contradiction is stale, not wrong in
   substance.
2. **Two files still say `D2` "prints the literal string `\"setfils\"`"** —
   `decomps/_shapes.md:376` and `docs/DECOMP_FORMAT_NOTES.md:99-100`. It **raises**
   (`explenation generator.ml:464`); `docs/DECOMP_FORMAT_NOTES.md:101-103` already says so four
   lines later, so that file contradicts itself within one bullet.
3. **`decomps/_shapes.md:161-162` and `decomps/_shapes-seq.md:48-57` say a bare `B` prints as
   `"ERROR B "` at generator lines 399/428.** Both printers **raise**, at `:488` and `:517`,
   since W1-T10 (`docs/ROADMAP.md:54`, `DONE`).
4. **`catalog/lex2.md` cites `printind_name` at `explenation generator.ml:485`.** It is at
   `:430`; `:485` is inside `printglobal_event`.
