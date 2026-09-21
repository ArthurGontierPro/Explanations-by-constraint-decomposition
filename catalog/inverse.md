# `inverse`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `inverse`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecodes `['E0', 'E2']` (shared row with `inverse_in_range`) |
| **Status** | **`encodable today, not encoded`** — no gap blocks this decomposition; nobody has written it. G9 makes it verbose and G2 makes it read badly, and neither stops it. **See Status for a caveat about this value.** |
| **Generated** | **0** rules — there is no `cata/inverse.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:199` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`inverse(array[int] of var int: x, array[int] of var int: y)`

The two arrays are inverse permutations of each other: `x[i] = j ⇔ y[j] = i`, for
`i, j ∈ [1,n]`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:72` carries the *name* only. The biconditional above
is quoted from `CHRISTMAS_LIST.md:199`'s route cell ("channelling `x[i]=j <-> y[j]=i`") and
restated in `decomps/inverse.md`; the MiniZinc type signature is recall.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:199`'s literature column reads, verbatim, `none`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only, and there is no paper here to put in it. No web access was used and no
search was made.

## Solver support

| | |
|---|---|
| Chuffed | native — the row reads `native (inverse per Chuffed docs)` |
| Geas | `[G]` present |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:199`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.

**An explaining implementation exists in three solvers and no paper describes it.** That is
the same position `element` is in (`catalog/element.md`, Calibration), and it is why the
calibration verdict below is `no published rule` rather than `out of reach`: there is
nothing to be out of reach *of*, in the literature, even though three implementations exist.
None is vendored here, so none can be compared against from this repo.

## Decomposition used here

**Generator value:** none. `inverse` appears nowhere in `explenation generator.ml`'s
`(*Decompositions*)` block, and there is no `explainall … "cata/inverse.tex"` call.
(`grep -n -i 'inverse' 'explenation generator.ml'` returns 8 lines and **all 8 are
`invert_op` and its comments** — l.32, 84, 126, 131, 138, 143, 181, 182 — which is a good
example of why the check has to be read rather than counted.)
**Emitted by:** nothing.
**Spec:** `decomps/inverse.md` — titled `# inverse, inverse_in_range`, so it covers both
names. Shape **P3** in `decomps/_shapes-perm.md:53-100`, renumbered **S6** ("cross-variable
channel by paired OR-clauses") in `decomps/_shapes.md`.

The decomposition authored there, in that file's own terms:

- `B1_{i,j} ⇔ X_i = j`, `rule1`, AC, `(i,j) ∈ [1,n]×[1,n]`;
- `B2_{j,i} ⇔ Y_j = i`, `rule1`, AC, the same index set read the other way round;
- `¬B1_{i,j} ∨ B2_{j,i}` and `¬B2_{j,i} ∨ B1_{i,j}` — two `rule4` clauses, together the
  biconditional.

**This is `element`'s shape with the third variable removed**, and the removal matters:
`element`'s `I` and `V` are *scalars*, which is where its four `VACUOUS` rules come from
(`catalog/element.md`, "The defect"). Both of `inverse`'s sides are already array-indexed, so
the scalar-quantifier trap that costs `element` two thirds of its output **does not arise
here**. `decomps/inverse.md` and `decomps/_shapes-perm.md:88-92` both say so, independently.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=j` / `X_{i} ≠ j` (would be, from an `xac`-like event) | — | **0** | not run: no generator value exists |

**What is missing is not a gap, and this is the entry's main finding.** `element` is the
existence proof that S6 can be written in the current format: five `Decomp`s, three
reifications and two `rule4` clauses, shipped and generating rules today
(`explenation generator.ml:834-838`). `inverse` needs *four* `Decomp`s of the same kinds.
Nobody has written them. The gaps below make that writing more verbose and the result less
readable; none of them stops it.

## Generated rules

**None.** There is no `cata/inverse.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`encodable today, not encoded`**

**A caveat on the value itself, measured rather than assumed.** The orchestrator records
this as a new status defined in `catalog/README.md` and `catalog/TEMPLATE.md`. As of this
commit it is **not in either file**: `catalog/README.md`'s status legend still lists six
values, the last being `nothing generated — blocked on G<n>` with "the gap number is
required, not optional", and `grep -rn 'encodable today' catalog/` finds the phrase only in
prose — `catalog/strictly_increasing.md:184` and `catalog/strictly_decreasing.md:186` ("a
state the legend has no word for"), `catalog/value_precede.md:26`, and this slice's
[`member.md`](member.md). R5's own shipped Status row for `strictly_increasing` reads
`**nothing generated** — and **no status-legend value fits**`. So this entry uses the value
the orchestrator directs and records that **the legend entry defining it has not landed**.
Reported, not fixed: `catalog/README.md` is not this session's.

**Why this entry qualifies, and it turns on a letter.** Earlier drafting of this slice
treated `inverse` as blocked-with-a-cost, on the reading that `var_name` has no letter for a
second user array. **That reading was wrong and is corrected here.** `var_name` is
`X | B of int | T | I | V | N | O` (`explenation generator.ml:3`), and `O` is a genuine
second array letter: `printvartex` renders it as `"O"^printglobal_eventtex v` (l.522) — an
indexed array literal, the same printer path `X` uses — and `gccn` already carries it as a
real user global, `Global_devent (true, O, id, id, BC)` at l.829. So `Y` can be encoded
today. It prints as `O`, which is `gcc`'s occurrence array wearing `inverse`'s meaning, and
that is **G2**: a legibility cost, not a wall.

**G9 is likewise a cost, not an absolute blocker.** `docs/DECOMP_FORMAT_NOTES.md:77` states it as "no
`Global ⇔ Global` channel schema; `rule1` is fixed to `Global ⇔ Reified`, so every
array-to-array channel re-derives `element`'s five-`Decomp` detour", and names `inverse`,
`sort` and `arg_sort` as the constraints that hit it. What that costs `inverse` is the
detour, not the constraint: the detour is writable and `element` writes it. So the honest
reading of the zero in the **Generated** row is *nobody has added the value to the
generator*, and G9 is why doing so is boilerplate rather than three lines.

**A second gap the spec does not record, read off the source: G2, and it bites on the name
rather than on the writing.** `decomps/write.md` records G2 for `write`'s second array and
says the second array "would print as a Boolean auxiliary", which for `B of int` is worse
than it sounds — `printvartex` **raises** on `B i` (l.517), so that encoding aborts the run
rather than printing badly. **But `B` is not the only candidate and `O` is available**, per
the paragraph above, so the correct statement for a two-array constraint is: encodable, with
one array printing under a letter that means something else. **`decomps/inverse.md` does not
mention G2 at all**, and `decomps/write.md` mentions it without noticing `O`. Both are read
off `explenation generator.ml:3, 517, 522, 829`, not measured.

**So the honest reading of the zero is: the value has not been written.** No gap refuses it,
`make validate` has nothing to look at, and the work is one `let inverse = [...]` of four
`Decomp`s plus an `explainall` line. **Nothing here is validated, flagged or refuted** —
there is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:199`'s literature column reads `none`. Per `catalog/README.md` step 2 and
the vocabulary in `catalog/TEMPLATE.md`, that is the verdict `no published rule exists`, not
a failure to compare and not `pending sourcing`: `pending sourcing` is for a row that cites
something nobody has read, and this row cites nothing.

No comparison is fabricated. Note, as with `element`, that "no literature" here does **not**
mean "no explaining implementation": Chuffed, Geas and Choco LCG all have one
(`CHRISTMAS_LIST.md:199`). Calibrating against an implementation is not possible from this
repo — no solver source is vendored, and `CLAUDE.md` forbids web-searching ahead of the
index.

## Gaps

| gap | what it blocks here |
|---|---|
| `G9` | the recorded one, and a **cost**: no `Global ⇔ Global` channel schema, so the two-array channel re-derives `element`'s multi-`Decomp` detour by hand (`docs/DECOMP_FORMAT_NOTES.md:77`) |
| `G2` | **not in this constraint's spec; read off the source here.** `var_name` (l.3) has no letter *meaning* a second user array, so `Y` borrows `O` and prints as `gcc`'s occurrence array (`printvartex` l.522, `gccn` l.829). A legibility cost, not a wall — and **not** the `B i` raise at l.517 that `decomps/write.md`'s phrasing implies |
| `G17` | no pivot-elimination pass. Not biting: `B1`/`B2` are pure reification scaffolding and wash out, exactly as `element`'s do (`decomps/inverse.md`, "Auxiliaries") |
| — | **not G8.** `inverse` channels over the whole of `[1,n]`; the subrange gap belongs to [`inverse_in_range`](inverse_in_range.md), which shares this row and this spec |

Extensions: **E0, E2** (`CHRISTMAS_LIST.md:199`, ecodes as parsed by
`tools/mzn_coverage.py`). The row's own assessment — "two reified families, close to **E0**"
— agrees with the Status section above: the shape is within reach of the schemas that exist.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

**Numbering warning.** `decomps/inverse.md` was written before the wave-two consolidation and
uses its own local numbers: it calls the channel gap **"G7"** and the subrange gap **"G6"**.
Consolidated, those are **G9** and **G8** (`docs/DECOMP_FORMAT_NOTES.md:76-77`, "was" column:
`perm G7` → G9, `perm G6` → G8). A reader taking that file's numbers at face value today
would land on the value-set gap and the subrange gap instead.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `inverse` in `B no-literature +
  solver-native`, `ecodes: ['E0', 'E2']`, `CHRISTMAS_LIST.md` line 199, section
  `9. Ordering, sorting, channelling`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one; totals **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope**. Nothing in the run mentions `inverse`.
- `ls cata/` → 16 files; no `inverse.tex`.
- `grep -n -i 'inverse' 'explenation generator.ml'` → 8 lines, every one of them
  `invert_op` or a comment about it (l.32, 84, 126, 131, 138, 143, 181, 182). No
  decomposition value, no `explainall` call. Run, then read; the count alone would have
  been misleading.
- `CHRISTMAS_LIST.md:199` and `:106-109` read → the literature cell (`none`), the solver
  cell, the E2 route cell, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:72` read → the name.
- `decomps/inverse.md` read → the authored decomposition, the `element` comparison, the
  local gap numbering.
- `decomps/_shapes-perm.md:53-100` (P3) and `decomps/_shapes.md` (S6) read → the shape and
  its renumbering; `decomps/_shapes-perm.md:88-92` for the "no third variable, so no scalar
  trap" point.
- `explenation generator.ml` read, not run → `var_name`'s closed enum at **3**;
  `printvartex`'s `B i` raise at **517** and its `O` case at **522**; `gccn`'s
  `Global_devent (true, O, …)` at **829** — together the evidence that a second user array
  is encodable today under a borrowed letter; `:834-838` → `elem`, the existence proof that
  S6 is writable.
- `grep -rn 'encodable today' catalog/` and `sed -n '/^## Status legend/,/^## /p'
  catalog/README.md` → the new status value is used in prose in four entries and is **not**
  in the legend. That is a run, not a reading.
- `docs/DECOMP_FORMAT_NOTES.md:76-77` read → G8, G9 and the "was" column that translates
  `decomps/inverse.md`'s local numbers.
- **The G2 observation is reasoning over the source, labelled as such in place.** Nothing
  was compiled and no decomposition was written.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`catalog/inverse.md`'s stub said the spec exists; `catalog/inverse_in_range.md`'s said
   it does not.** Both are covered by the one file `decomps/inverse.md`, whose title line is
   `# inverse, inverse_in_range`. `tools/catalog_stub.py` tests `os.path.isfile("decomps/<name>.md")`
   by exact filename, so every constraint covered by a multi-constraint spec is recorded as
   having none. Corrected in both entries.
2. **`decomps/inverse.md` uses pre-consolidation gap numbers** (its "G7" is G9, its "G6" is
   G8). W1-T14's sibling problem, for gap labels rather than line numbers.
3. **`catalog/inverse_fn.md` resolves to this file and quotes its Status row as
   `not reviewed`.** That quotation is stale as of this commit. Recorded under
   `## Cross-session requests` in `WORKLOG.md`; `inverse_fn.md` is not this session's.
4. **`encodable today, not encoded` is used by this entry and is not defined in
   `catalog/README.md`'s legend or in `catalog/TEMPLATE.md`.** Measured 2026-09-21; see
   Status.
5. **`decomps/write.md`'s G2 paragraph says a second user array "would print as a Boolean
   auxiliary".** With `B of int` it does not print at all — `printvartex` raises (l.517) —
   and `O` is an available alternative the paragraph does not mention. Both halves matter
   to anyone encoding a two-array constraint.
