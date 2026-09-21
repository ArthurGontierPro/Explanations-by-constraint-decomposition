# `write`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `write`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E2']` (shared row with `writes`, `writes_seq`) |
| **Status** | `nothing generated — blocked on G18` — **and G18 is about the *quantifier* form; a clause-per-position workaround is recorded. See Status.** |
| **Generated** | **0** rules — there is no `cata/write.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:216` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`write(array[int] of var int: a, var int: i, var int: v, array[int] of var int: b)`

`b` is `a` with position `i` overwritten by `v`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:132` carries the *name* only. The signature above is
quoted from `decomps/write.md`'s "Signature" line, which records it without a citation of
its own; treat it as recall. `CHRISTMAS_LIST.md:216` files the name under
`11. Maths and misc` and its route cell reads, verbatim, "**E2** (array update = `element`
family)".

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:216`'s literature column reads, verbatim, `none`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. No web access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:216`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `decomp`. No native explaining propagator in any of the three solvers
surveyed; all three of the catalog's sources are empty for this constraint.

## Decomposition used here

**Generator value:** none. There is no `write` value in `explenation generator.ml` — the
four matches for the string are `write_footer` and a comment about writing to stderr
(l.645, 716, 727, 741) — and there is no `explainall … "cata/write.tex"` call.
**Emitted by:** nothing.
**Spec:** `decomps/write.md` — titled `# write, writes, writes_seq`, covering all three.
Shape **S6** ("cross-variable channel by paired OR-clauses") in `decomps/_shapes.md`, the
same shape `element` and `inverse` instantiate; its "what varies" row names this case as the
one that "excludes a **variable** position (`write`, G18)".

The decomposition authored there has **two halves, and only the first is `element`**:

- **The written cell** — S6 verbatim: `B_i ⇔ I = i`, `B_t ⇔ V = t`, `B1_{i,t} ⇔ B_i = t`,
  then the two `rule4` clauses `¬B_i ∨ ¬B_t ∨ B1_{i,t}` and `¬B_i ∨ B_t ∨ ¬B1_{i,t}`.
- **Every other cell** — `∀j ≠ I: B_j = A_j`, an array-to-array channel *guarded by a
  disequality against a decision variable*.

**Status of that spec, in its own words: "authored, not generated, not validated."**

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `A_{j}=t` / `B_{j}=t` (would be) | — | **0** | not run: the unwritten-cells channel quantifies over `∀j ≠ I` with `I` a decision variable (G18) |

**G18 is this constraint's own gap — it was produced here and nowhere else.**
`docs/DECOMP_FORMAT_NOTES.md:86` states it as "quantification over an index set with a
variable-determined exclusion, `∀j ≠ I` for `I` a decision variable", and its "hit by" column
is exactly `write`, `writes`, `writes_seq`. The wave-three addendum at
`docs/DECOMP_FORMAT_NOTES.md:106-112` records that §11 of `CHRISTMAS_LIST.md` was the last
in-scope family and added **one** gap — this one — "which is itself the useful result: the
gap list converged before the corpus ran out".

**What it is not.** `docs/DECOMP_FORMAT_NOTES.md:86` distinguishes it from two neighbours in
the same sentence: **G8** covers a range minus a *constant* (`all_different_except`,
[`inverse_in_range`](inverse_in_range.md)), and **G14** covers a *summation* whose extent a
variable determines (`cumulatives`). Neither covers a universally quantified **channel** with
a variable-determined hole.

Verified against the source: `ind_modifs` (l.9-14) has `Set : ind_name*ind_symbols*ind_set`
for membership and `Rel : ind_name*ind_symbols*ind_name` for a relation **between two index
names**, and `ind_set` is `D of int | D2 of ind_name list` (l.6). So "`j ≠ i`" is writable —
`prim_node` builds exactly that `Rel` (l.97) — and "`j ≠ I` for `I` a *variable*" is not,
because `Rel`'s second argument is an `ind_name` and `I` here is a `var_name`. **The same
type-level wall as G10**, arrived at from the quantifier side rather than the index-position
side.

## Generated rules

**None.** There is no `cata/write.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G18`**

And the gap statement is narrower than the status row can show: **G18 is about the
*quantifier* form**, and `decomps/write.md` records a workaround for the same content.
Quoted rather than paraphrased, because the distinction is the entry's main finding:

> "The auxiliary-free workaround that works for `cumulatives` — reify `M_i = k` and conjoin
> it — applies here too (`B_j = A_j ∨ I = j`, a `rule4` clause per `j`), and it is probably
> the right decomposition; recorded as the intended one, with G18 noted because the
> *quantifier* form is what the format cannot write."

**So the honest reading of the zero has three parts, and only one of them is G18.**

1. The clause-per-position form `B_j = A_j ∨ I = j` uses `rule4` and `rule1` only, both of
   which run today. If it is sound — `decomps/write.md` says "probably the right
   decomposition" and does not prove it — then G18 blocks the *notation*, not the content.
   **Nothing in this repo has checked that workaround**, and this entry does not assert it.
2. **G9 costs the detour.** The unwritten-cells half is an array-to-array channel, so it
   re-derives `element`'s multi-`Decomp` structure by hand, once per position
   (`docs/DECOMP_FORMAT_NOTES.md:77`).
3. **G2 costs the name, and `decomps/write.md` says it bites harder here than anywhere
   recorded.** `var_name` is `X | B of int | T | I | V | N | O` (`explenation generator.ml:3`)
   and `write` has **two** user arrays, `a` and `b`. The spec's words: the second array "has
   no letter — the `var_name` enum is `X | B of int | T | I | V | N | O` and `B of int` is
   the Boolean-auxiliary family, so a second user array would print as a Boolean auxiliary.
   That is **G2** on a new constraint, and it is sharper here than in the cases already
   recorded, because the collision is with the auxiliary family rather than with another
   constraint's letter." **And it would be printed, not raised**: `printvartex` raises on
   `B i` (l.517) precisely because a `B` that reaches the printer means no `Global_devent`
   turned it back into a solver literal — which is exactly what a user array named `B` would
   do. So encoding `b` as `B 1` does not merely read badly; on the current printer it aborts
   the run. That is W1-T10's fix working as intended and it is a hard stop for this
   constraint's naming. **Read off the source, not run.**

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:216`'s literature column reads `none`, and per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing` (no paper is cited),
not `out of reach` (no published premise to be out of reach of). Nothing was searched and no
comparison is fabricated.

The solver cell is `decomp` with no `[G]` and no `[C]`, so there is not even an unpublished
implementation to note, as there is for [`inverse`](inverse.md) and `element`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G18` | **the recorded one, and it is about the quantifier form.** `∀j ≠ I` with `I` a decision variable: `Rel`'s second argument is an `ind_name` (l.10), not a `var_name`. Distinct from G8 (constant exclusion) and G14 (variable-determined summation extent) — `docs/DECOMP_FORMAT_NOTES.md:86`, whose "hit by" column is this constraint and its two siblings |
| `G2` | **a hard stop on naming, sharper here than anywhere else recorded.** Two user arrays, one letter. Encoding the second as `B 1` makes `printvartex` raise (l.517), not merely print badly |
| `G9` | a **cost**: no `Global ⇔ Global` channel schema, so the unwritten-cells channel re-derives `element`'s detour (`docs/DECOMP_FORMAT_NOTES.md:77`) |
| — | **the workaround is unchecked, not blocked.** `B_j = A_j ∨ I = j` per position needs only `rule1` + `rule4`. `decomps/write.md` calls it "probably the right decomposition"; nothing has tested it |
| `G17` | no pivot-elimination pass. Not biting: `B_i`, `B_t`, `B1_{i,t}` are reification scaffolding |

Extensions: **E2** (`CHRISTMAS_LIST.md:216`, route cell "**E2** (array update = `element`
family)"). `CHRISTMAS_LIST.md:232-233` names `write*` among the constraints E2 unlocks.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering (G18 is wave three's
single addition, `:86` and `:106-112`).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `write` in `A no-literature +
  solver-decomposes`, `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 216, section
  `11. Maths and misc`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `write.tex`. `grep -n -i 'write' 'explenation generator.ml'` →
  4 lines, all `write_footer` or a comment about stderr (l.645, 716, 727, 741). No
  decomposition value, no `explainall` call.
- `explenation generator.ml` read, not run → `var_name` at **3**, `ind_set` at **6**,
  `ind_modifs` at **9-14** (`Rel` at **10**), `prim_node` at **97**, `printvartex`'s `B i`
  raise at **517**.
- `CHRISTMAS_LIST.md:216`, `:106-109` and `:232-233` read → the literature cell (`none`),
  the solver cell (`decomp`), the E2 route cell, the legend, the E2-unlock list.
- `tools/data/minizinc-2.10.1-globals.txt:132` read → the name.
- `decomps/write.md` read → the two-halves decomposition, the workaround, the G2 paragraph,
  the "authored, not generated, not validated" status; `decomps/_shapes.md` (S6) read → the
  shape and its "what varies" row.
- `docs/DECOMP_FORMAT_NOTES.md:77, 86, 106-112` read → G9, G18 and the wave-three addendum.
- **The `printvartex` consequence in Status item 3 is reasoning over the source, labelled as
  such in place.** Nothing was compiled and no decomposition was written.
