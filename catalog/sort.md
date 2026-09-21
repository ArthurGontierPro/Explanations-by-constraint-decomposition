# `sort`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `sort`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E2']` (shared row with `arg_sort`) |
| **Status** | `nothing generated — blocked on G10` — **and on G9 and G3; see Status. G10 is the wall.** |
| **Generated** | **0** rules — there is no `cata/sort.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:198` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`sort(array[int] of var int: x, array[int] of var int: y)`

`y` is `x` sorted into non-decreasing order — a permutation of `x` that is `increasing`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:113` carries the *name* only. The reading above is
`decomps/maximum.md`'s ("the output array `y` is a permutation of `x` … **and** sorted") and
is quotable as this repo's own; the MiniZinc type signature is recall.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:198`'s literature column reads, verbatim, `none`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. No web access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:198`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `decomp`.

**This is a tier-A constraint in the strict sense**: no literature *and* no native explaining
propagator anywhere in the three solvers surveyed. `docs/ROADMAP.md:55` describes tier A as
"where a derived schema is the only schema". `sort` is one of the 36 constraints in it, and
it is also one where the derivation is furthest from reach — which is the whole content of
this entry.

## Decomposition used here

**Generator value:** none. There is no `sort` value in `explenation generator.ml`
(`grep -c -i 'sort' 'explenation generator.ml'` → `0`) and no
`explainall … "cata/sort.tex"` call.
**Emitted by:** nothing.
**Spec:** `decomps/maximum.md` — titled `# maximum, minimum, arg_max, arg_min, sort,
arg_sort`, so it covers this name; `sort` has its own section there. Shape **P3** in
`decomps/_shapes-perm.md:53-100`, renumbered **S6** in `decomps/_shapes.md`, whose S6
instance list reads "`sort`, `arg_sort` (composed, and also needing S2 over the permutation
plus **G10**; sketched, not derived)".

**"Sketched, not derived" is the accurate description and this entry keeps it.** No
`Decomp` list exists for `sort` anywhere in the repo. What exists is a decomposition into
three obligations, from `decomps/maximum.md`:

1. `y` is a permutation of `x` — an `all_different`-style channel, shape **S2**;
2. `y` is sorted — `increasing` on `y`, shape **S1**, which runs today
   (`cata/increasing.tex`, 2 rules, both `SOUND and MINIMAL`);
3. each `y_j` equals some `x_i` — the `element`/`inverse` channel, shape **S6**, once per
   position pair.

Obligation 3 is where `sort` stops being a composition of things that work.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `Y_{j}=t` (would be) | — | **0** | not run: the permutation link `y_j = x_{p_j}` puts a variable in index position (G10) |

**The blocking statement, in the format's own terms.** `decomps/maximum.md` puts it as: the
permutation half "needs to say '`y` is `x` reordered by permutation `p`', which is
`y_j = x_{p_j}` — variable-valued index into `X`". Read against the source that is a wall,
not a cost: an `index` is `Ind of ind_name*ind_modifs list` (`explenation generator.ml:16`)
and `ind_name` is the closed enum `I of int | T of int | P of int | R of int` (l.5). **Every
index position in the format is an index name.** There is no constructor anywhere in
`ind_name`, `ind_modifs` or `ind_op` that puts a `var_name` in an index slot, so the atom
cannot be written at all, let alone printed. That is **G10**,
`docs/DECOMP_FORMAT_NOTES.md:78`, "no variable in index position, `X_{X_i}`", which names
`symmetric_all_different` and `sort` as the two constraints that hit it.

**G3 also applies and is not recorded against `sort` anywhere.** Obligation 2's real content
for a *sort* is `y_j ≤ y_{j+1}` between two decision variables. The shipped `increasing`
(`explenation generator.ml:830-831`, shape S1) does not do that — it is `rule1` plus one
`rule4` clause over `X_i ≥ t` literals at consecutive positions, i.e. variable-vs-domain-value
throughout, which is how it avoids G3. That suffices because a chain of threshold literals
*does* encode monotonicity over a shared value domain. Whether that suffices for `sort`'s
output array depends on obligations 1 and 3 supplying the link to `x`, and they are the ones
blocked. **This paragraph is reasoning read off `explenation generator.ml:830-831` and
`cata/increasing.tex`, not a measurement**, and it is recorded as an open question rather
than a finding: it is not obvious that `sort` needs G3, and no file in the repo claims it
does.

## Generated rules

**None.** There is no `cata/sort.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G10`**

Three gaps, one of them a wall:

- **G10 is the wall.** A variable in index position cannot be expressed: `ind_name` is a
  closed enum of four index families (l.5) and no constructor admits a `var_name`. Without
  it there is no way to say `y` is `x` under a permutation, and therefore no way to relate
  the two arrays at all.
- **G9 is a cost**, as it is for [`inverse`](inverse.md): obligation 3's channel would
  re-derive `element`'s multi-`Decomp` detour, once per position pair
  (`docs/DECOMP_FORMAT_NOTES.md:77`, which names `sort`).
- **G2 applies to the name**, as it does for `inverse` and `write`: `var_name`
  (l.3) has no letter for a second user array, so `Y` must borrow one.

**What a G10 fix would and would not buy.** It would make obligation 1's and 3's atoms
writable. It would not by itself produce a `sort` entry: `decomps/maximum.md` is explicit
that `sort` composes three distinct shapes and is "sketched, not derived … because the
[G10] half has no representable starting point". Somebody still has to write the
decomposition, and nobody has. That is the same second step [`inverse`](inverse.md) needs
and `inverse` needs *only* that step.

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:198`'s literature column reads `none`. Per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`, not `pending sourcing` (which is for a row
citing something unread) and not `out of reach` (which needs a published premise to be out
of reach of). Nothing was searched and no comparison is fabricated.

**And unlike `inverse` or `element`, there is no implementation to gesture at either.** The
solver row is `decomp` with no `[G]` and no `[C]`: whatever explanations a solver produces
for `sort` come from the primitive propagators its decomposition flattens to
(`CHRISTMAS_LIST.md:106-109`, legend). So for this constraint the catalog's three sources —
literature, solver, this method — are empty, absent and blocked respectively. **That is the
honest headline and it is a coverage result, not a defect of any of the three.**

## Gaps

| gap | what it blocks here |
|---|---|
| `G10` | **the wall.** No variable in index position, `X_{X_i}` — so `y_j = x_{p_j}` cannot be written. `ind_name` is a closed 4-family enum (l.5) and index slots take nothing else (`docs/DECOMP_FORMAT_NOTES.md:78`, which names `sort`) |
| `G9` | a **cost**: no `Global ⇔ Global` channel schema, so obligation 3 re-derives `element`'s detour once per position pair (`docs/DECOMP_FORMAT_NOTES.md:77`, which names `sort`) |
| `G2` | **not in this constraint's spec; read off the source.** `var_name` (l.3) has no letter for the second user array |
| `G3` | **open question, not a recorded finding.** Variable-vs-variable comparison, if `y_j ≤ y_{j+1}` is needed directly rather than through `increasing`'s threshold-literal chain. See Scope; no file in the repo claims `sort` needs G3 |
| `G17` | no pivot-elimination pass. Would bite once a permutation auxiliary exists, which today it cannot |

Extensions: **E2** (`CHRISTMAS_LIST.md:198`), whose route cell reads, verbatim, "**E2**
(composes `element`)". That cell is right about the shape and silent about G10, which is the
part that blocks.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

**Numbering warning.** `decomps/maximum.md` predates the consolidation and says `sort`
"hits G7 and G8 both". Consolidated, those are **G9** and **G10**
(`docs/DECOMP_FORMAT_NOTES.md:77-78`, "was" column: `perm G7` → G9, `perm G8` → G10). Read
literally today, that sentence points at the value-set gap and the subrange gap instead.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `sort` in `A no-literature +
  solver-decomposes`, `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 198, section
  `9. Ordering, sorting, channelling`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `sort.tex`. `grep -c -i 'sort' 'explenation generator.ml'` → 0.
- `explenation generator.ml` read, not run → `var_name` at **3**, `ind_name` at **5**,
  `index` at **16** (the evidence that index slots take index names only, i.e. G10 is a
  wall); `incr` at **830-831** for the `increasing` comparison.
- `CHRISTMAS_LIST.md:198` and `:106-109` read → the literature cell (`none`), the solver
  cell (`decomp`, no `[G]`, no `[C]`), the E2 route cell, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:113` read → the name.
- `decomps/maximum.md` (its `sort, arg_sort` section) and `decomps/_shapes-perm.md:53-100`,
  `decomps/_shapes.md` (S6, and the "five with no shape" table) read → the three
  obligations, "sketched, not derived", the local gap numbering.
- `docs/DECOMP_FORMAT_NOTES.md:77-78` read → G9, G10 and the "was" column.
- `docs/ROADMAP.md:55` read → the tier-A characterisation quoted in Solver support.
- **The G3 paragraph is reasoning over the source, labelled as such in place**, and is
  recorded as an open question. Nothing was compiled and no decomposition was written.

**Discrepancies noted, and the one in this file fixed.**

1. **Wrong stub field, fixed here: `Spec: none — this constraint has no `decomps/sort.md`.`**
   It is covered by `decomps/maximum.md`, whose title line is `# maximum, minimum, arg_max,
   arg_min, sort, arg_sort`. `tools/catalog_stub.py` matches filenames only.
2. **`decomps/maximum.md` uses pre-consolidation gap numbers** for `sort` ("G7 and G8" are
   G9 and G10).
3. **`catalog/sort_fn.md` resolves to this file and quotes its Status row as
   `not reviewed`.** That quotation is stale as of this commit. Recorded under
   `## Cross-session requests` in `WORKLOG.md`; `sort_fn.md` is not this session's.
