# `arg_sort`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `arg_sort`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E2']` (shared row with `sort`) |
| **Status** | `nothing generated — blocked on G10` — **twice over; see Status.** |
| **Generated** | **0** rules — there is no `cata/arg_sort.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:198` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`arg_sort(array[int] of var int: x, array[int] of var int: p)`

`p` is the permutation that sorts `x`: `x[p[1]] ≤ x[p[2]] ≤ …`. It is
[`sort`](sort.md) with the *permutation* reported instead of, or as well as, the sorted
array.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:27` carries the *name* only. The reading above is
`decomps/maximum.md`'s (`arg_max`/`arg_min` need "a second channel from the winning index
back to a reported position variable", and `arg_sort` is grouped with `sort`); the MiniZinc
type signature is recall, and **this repo nowhere states `arg_sort`'s tie-breaking rule**,
which is the part a real decomposition would have to pin down.

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
cell reads, verbatim: `decomp`. As with [`sort`](sort.md), all three of the catalog's
sources are empty here: no paper, no native explaining propagator, no generated rule.

## Decomposition used here

**Generator value:** none. There is no `arg_sort` value in `explenation generator.ml`
(`grep -c -i 'sort' 'explenation generator.ml'` → `0`) and no
`explainall … "cata/arg_sort.tex"` call.
**Emitted by:** nothing.
**Spec:** `decomps/maximum.md` — titled `# maximum, minimum, arg_max, arg_min, sort,
arg_sort`, so it covers this name, in the section shared with `sort`. Shape **P3** in
`decomps/_shapes-perm.md`, renumbered **S6** in `decomps/_shapes.md`, whose S6 instance list
reads "`sort`, `arg_sort` (composed, and also needing S2 over the permutation plus **G10**;
sketched, not derived)".

No `Decomp` list exists. What exists is [`sort`](sort.md)'s three obligations — permutation
(S2), sortedness (S1), value channel (S6) — **plus** the reporting of `p` itself as a user
variable rather than an internal device.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `P_{j}=i` (would be) | — | **0** | not run: `x_{p_j}` puts a variable in index position, twice (G10) |

**Where `arg_sort` is worse than `sort`, and it is the reason it gets its own entry rather
than a pointer to one.** For `sort`, the permutation `p` is an *internal* device: a
decomposition could in principle avoid naming it if it could relate `x` and `y` some other
way. For `arg_sort`, `p` is the **output**, so every rule the method would emit has to
conclude or premise something about `P_j`, and the only thing that makes `P_j = i` true is
`x_{p_j}`'s position in the order — a variable in index position (**G10**) on the very atom
the constraint exists to report. `decomps/maximum.md` makes the same structural point about
`arg_max`/`arg_min`: they need what `maximum` needs "**plus** a second channel from the
winning index back to a reported position variable", and "since the first half is already
blocked, this doesn't reach the second half".

**A correction this entry has to make, because a task brief carried it in.** `arg_sort` is
**not** one of the constraints `decomps/_shapes.md` records as having no shape at all. That
list is exactly five — `maximum`, `minimum`, `arg_max`, `arg_min`, `span`, in the "Not
covered by any shape" table, all attributed to **G3** — and `arg_sort` is not in it;
`decomps/_shapes.md` lists `arg_sort` under **S6**, among the eight instances of the channel
shape. So the in-repo position is that `arg_sort` *has* a shape and is blocked on **G9 and
G10**, not that it is unshaped and blocked on G3. This entry follows the repo.

**Whether G3 also applies is an open question**, for the same reason as in
[`sort`](sort.md)'s Scope section: `arg_sort`'s sortedness obligation is
`x_{p_j} ≤ x_{p_{j+1}}`, which compares two decision variables directly and cannot obviously
be routed through `increasing`'s threshold-literal chain the way `sort`'s can, because the
two sides are indexed by *different* variable-valued positions. **That is reasoning, not a
recorded finding**, and no file in the repo states it.

## Generated rules

**None.** There is no `cata/arg_sort.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G10`**

G10 — "no variable in index position, `X_{X_i}`", `docs/DECOMP_FORMAT_NOTES.md:78` — is a
wall for the same source-level reason as in [`sort`](sort.md): `index` is
`Ind of ind_name*ind_modifs list` (`explenation generator.ml:16`) and `ind_name` is the
closed enum `I | T | P | R of int` (l.5), so an index slot takes an index name and nothing
else. There is no `var_name` anywhere in the index grammar.

**It bites twice here.** Once in the value channel, as for `sort`; once more because `p` is
an output, so the reported atom `P_j = i` is itself about a variable-valued index. Closing
G10 would make `sort`'s atoms writable; it would additionally have to make them *reportable
in the user's own vocabulary* for `arg_sort`, which is a stronger requirement and is not
what G10's one-line statement promises.

**G9 is a cost** (the channel re-derives `element`'s detour, once per position pair) and
**G2 applies to the name** (`var_name`, l.3, has no letter for a second user array). Neither
would stop a value being written; G10 would stop it emitting. And, as for `sort`, closing
every gap would still leave the decomposition unwritten: `decomps/maximum.md` calls it
"sketched, not derived".

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:198`'s literature column reads `none`, and per `catalog/TEMPLATE.md`'s
vocabulary that is the verdict `no published rule exists` — not `pending sourcing`, not
`out of reach`. Nothing was searched, no paper is characterised, and no comparison is
fabricated.

The solver cell is `decomp` with no `[G]` and no `[C]`, so there is not even an unpublished
implementation to note the existence of, as there is for [`inverse`](inverse.md) and
`element`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G10` | **the wall, twice.** No variable in index position: `x_{p_j}` in the channel, and `P_j = i` as the reported output. `ind_name` is a closed 4-family enum (l.5) and index slots take nothing else (`docs/DECOMP_FORMAT_NOTES.md:78`) |
| `G9` | a **cost**: no `Global ⇔ Global` channel schema (`docs/DECOMP_FORMAT_NOTES.md:77`, which names `arg_sort`) |
| `G2` | **not in this constraint's spec; read off the source.** `var_name` (l.3) has no letter for a second user array |
| `G3` | **open question, not a recorded finding.** `x_{p_j} ≤ x_{p_{j+1}}` compares two decision variables at two variable-valued positions. See Scope |
| `G17` | no pivot-elimination pass. Would bite once a permutation auxiliary exists, which today it cannot |
| — | **not "no shape".** `decomps/_shapes.md`'s five unshaped constraints are `maximum`, `minimum`, `arg_max`, `arg_min`, `span`; `arg_sort` is an S6 instance there. See Scope |

Extensions: **E2** (`CHRISTMAS_LIST.md:198`, route cell "**E2** (composes `element`)").
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

**Numbering warning.** `decomps/maximum.md` predates the consolidation and says `sort` and
`arg_sort` hit "G7 and G8". Consolidated, those are **G9** and **G10**
(`docs/DECOMP_FORMAT_NOTES.md:77-78`, "was" column).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `arg_sort` in `A no-literature +
  solver-decomposes`, `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 198, section
  `9. Ordering, sorting, channelling`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `arg_sort.tex`. `grep -c -i 'sort' 'explenation generator.ml'`
  → 0.
- `explenation generator.ml` read, not run → `var_name` at **3**, `ind_name` at **5**,
  `index` at **16** — the evidence that G10 is a wall.
- `CHRISTMAS_LIST.md:198` and `:106-109` read → the literature cell (`none`), the solver
  cell (`decomp`), the E2 route cell, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:27` read → the name.
- `decomps/maximum.md` (its `sort, arg_sort` and `arg_max, arg_min` sections),
  `decomps/_shapes-perm.md` (P3), `decomps/_shapes.md` (S6's instance list **and** the "Not
  covered by any shape" table) read → the shape attribution and the correction above.
- `docs/DECOMP_FORMAT_NOTES.md:77-78` read → G9, G10 and the "was" column.
- **The "G10 bites twice" and G3 paragraphs are reasoning over the source, labelled as such
  in place.** Nothing was compiled and no decomposition was written.

**Discrepancies noted, and the one in this file fixed.**

1. **Wrong stub field, fixed here: `Spec: none — this constraint has no
   `decomps/arg_sort.md`.`** It is covered by `decomps/maximum.md`.
2. **A brief given to this session said `arg_sort` is among the five constraints
   `decomps/_shapes.md` records as having no shape, blocked by G3.** It is not; the five are
   `maximum`, `minimum`, `arg_max`, `arg_min`, `span`. Corrected in Scope, and reported.
3. **`decomps/maximum.md` uses pre-consolidation gap numbers** ("G7 and G8" are G9 and G10).
