# `writes_seq`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `writes_seq`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E2']` (shared row with `write`, `writes`) |
| **Status** | `nothing generated — blocked on G18` — **plus a second guarded channel for "later write wins". See Status.** |
| **Generated** | **0** rules — there is no `cata/writes_seq.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:216` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`writes_seq(array[int] of var int: a, array[int] of var int: i, array[int] of var int: v, array[int] of var int: b)`

[`writes`](writes.md) with the updates applied **in sequence**, so that when two updates
name the same position the later one wins.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:134` carries the *name* only. `decomps/write.md`
states only that "`writes_seq` applies them in sequence, so it is `writes` with the later
updates taking precedence"; **the argument list above is recall extrapolated from
`write`'s** and is flagged rather than presented as sourced. `CHRISTMAS_LIST.md:216` files
the name under `11. Maths and misc`.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:216`'s literature column reads, verbatim, `none`,
for the row shared with `write` and `writes`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. No web access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:216`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `decomp`, and it is a **row-level** cell covering three names.

## Decomposition used here

**Generator value:** none. There is no such value in `explenation generator.ml` and no
`explainall … "cata/writes_seq.tex"` call. (The four matches for the string `write` in that
file are `write_footer` and a comment about stderr, l.645, 716, 727, 741.)
**Emitted by:** nothing.
**Spec:** `decomps/write.md` — titled `# write, writes, writes_seq`, so it covers this name,
in its "What differs per variant" section. Shape **S6** in `decomps/_shapes.md`.

`decomps/write.md`'s statement for this variant, quoted in full:

> "`writes_seq` — same as `writes` with a priority order among colliding indices, i.e. the
> later write wins. Expressing 'later wins' needs, per position, a disjunction over *which*
> update was last to touch it, which is a second guarded channel of the same kind. No new
> shape, no new gap beyond G18."

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `A_{j}=t` / `B_{j}=t` (would be) | — | **0** | not run: two guarded channels, both with variable-determined exclusions (G18) |

**Everything in [`write`](write.md)'s and [`writes`](writes.md)'s Scope applies and is not
repeated.** G18 (`docs/DECOMP_FORMAT_NOTES.md:86`) is the family's own gap; the type-level
reason it is a wall is that `Rel`'s second argument is an `ind_name` (l.10) while the
excluded position is a `var_name`.

**What is different here.** "Later wins" is not a side condition on the index array (that is
`writes`' `all_different` obligation, and `writes_seq` drops it — collisions are *allowed*
and resolved by order). It is a per-position statement of the form "update `m` touched `j`
and no update after `m` did", which `decomps/write.md` calls "a second guarded channel of
the same kind". **Its exclusion is doubly variable-determined**: the set excluded is
`{I_{m+1}..I_k}`, whose *members* are decision variables and whose *extent* depends on which
`m` is being asserted. G8 covers a constant exclusion, G14 a variable-determined summation
extent, G18 a variable-determined hole in a quantified channel; **a variable-determined hole
whose extent is itself determined by the quantified position is not obviously any of the
three.** `decomps/write.md` says "no new gap beyond G18". **This entry does not contradict
that and does not confirm it** — it records that the claim is stated and unargued, and that
it is the one place in the `write` family where a new gap number is plausible.

## Generated rules

**None.** There is no `cata/writes_seq.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G18`**

The family's shared position, unchanged: G18 blocks the *quantifier* form;
`decomps/write.md`'s clause-per-position workaround needs only `rule1` and `rule4` and
**has never been tested**; G9 costs the channel detour; and G2 costs the second user array its own name — `B 1` makes
`printvartex` **raise** (l.517), while `O` prints as an indexed array (l.522, used by
`gccn` at l.829), so the array is encodable today wearing `gcc`'s name.

**This variant's own difficulty is order, and it is a modelling question before it is a
format question.** The workaround for a single write is `B_j = A_j ∨ I = j`. For a sequence
it becomes, per position `j` and per update `m`, something like "`B_j = V_m` if `I_m = j`
and `I_{m'} ≠ j` for every `m' > m`", which is a clause whose width and whose *content*
both depend on `m`. Nothing in this repo has written that out, so **how many `rule4` clauses
it is, and whether they are expressible with the existing schemas once G18 lands, is
unknown here.** `decomps/write.md`'s "no new gap beyond G18" is the only claim on record and
it carries no derivation.

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:216`'s literature column reads `none`; per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing` (no paper is cited),
not `out of reach` (no published premise to be out of reach of). Nothing was searched and no
comparison is fabricated.

The solver cell is `decomp` with no `[G]` and no `[C]`: no unpublished implementation to
note either. All three of the catalog's sources are empty for this constraint.

## Gaps

| gap | what it blocks here |
|---|---|
| `G18` | **the recorded one**, on both guarded channels. `Rel`'s second argument is an `ind_name` (l.10) and the excluded positions are `var_name`s — `docs/DECOMP_FORMAT_NOTES.md:86`, whose "hit by" column is this constraint and its two siblings |
| — | **possible new gap, flagged not claimed.** The "later wins" channel's exclusion set `{I_{m+1}..I_k}` has variable *members* and an extent that depends on the update being asserted. `decomps/write.md` says "no new gap beyond G18" without argument; see Scope |
| `G2` | **a legibility cost.** Two user arrays; `B 1` makes `printvartex` **raise** (l.517), but `O` is a genuine second-array letter (l.522, `gccn` l.829), so the array is encodable today wearing `gcc`'s name. `decomps/write.md`'s "would print as a Boolean auxiliary" is wrong in both directions |
| `G9` | a **cost**: no `Global ⇔ Global` channel schema (`docs/DECOMP_FORMAT_NOTES.md:77`) |
| — | **not G1.** `writes_seq` drops `writes`' `all_different` obligation on the index array — collisions are allowed and resolved by order — so the threshold gap that `writes` inherits does not apply |
| — | **the workaround is unchecked, not blocked**, and its shape for a sequence has never been written out |

Extensions: **E2** (`CHRISTMAS_LIST.md:216`, route cell "**E2** (array update = `element`
family)"); `CHRISTMAS_LIST.md:232-233` names `write*` among the constraints E2 unlocks.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering; G18 is wave three's
single addition (`:86`, `:106-112`).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `writes_seq` in `A no-literature +
  solver-decomposes`, `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 216, section
  `11. Maths and misc`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `writes_seq.tex`. `grep -n -i 'write' 'explenation generator.ml'`
  → 4 lines, all `write_footer` or a stderr comment (l.645, 716, 727, 741).
- `explenation generator.ml` read, not run → `var_name` at **3**, `Rel` at **10**,
  `printvartex`'s `B i` raise at **517** and its `O` case at **522**, `gccn`'s
  `Global_devent (true, O, …)` at **829**.
- `CHRISTMAS_LIST.md:216`, `:106-109`, `:232-233` read → the literature, solver and route
  cells, the legend, the E2-unlock list.
- `tools/data/minizinc-2.10.1-globals.txt:134` read → the name.
- `decomps/write.md` ("What differs per variant") read → the "later wins" statement and the
  "no new gap beyond G18" claim; `decomps/_shapes.md` (S6) read → the shape.
- `docs/DECOMP_FORMAT_NOTES.md:77, 86, 106-112` read → G9, G18, the wave-three addendum.
- **The Scope and Status paragraphs on the ordering channel are reasoning, labelled as such
  in place.** Nothing was compiled and no decomposition was written.

**Discrepancies noted, and the one in this file fixed.**

1. **Wrong stub field, fixed here: `Spec: none — this constraint has no
   `decomps/writes_seq.md`.`** It is covered by `decomps/write.md`, whose title line is
   `# write, writes, writes_seq`. `tools/catalog_stub.py` matches filenames only.
