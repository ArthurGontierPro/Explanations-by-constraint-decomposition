# `symmetric_all_different`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `symmetric_all_different`, and no
> claim of that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the
> catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E0']` |
| **Status** | `nothing generated — blocked on G10` — **on the self-inverse half only; the `alldifferent` half already ships. See Status.** |
| **Generated** | **0** rules — there is no `cata/symmetric_all_different.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:118` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`symmetric_all_different(array[int] of var int: x)`

`x` is an all-different self-inverse permutation: `alldifferent(x)` **and** `∀i: x[x_i] = i`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:124` carries the *name* only. The two-conjunct
reading above is quoted from `decomps/all_different.md`'s
`## symmetric_all_different` section, which is in-repo; the MiniZinc type signature is
recall. `CHRISTMAS_LIST.md:118` files the name under `1. AllDifferent family` and its route
cell reads, verbatim, "**E0** + `inverse` channelling".

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:118`'s literature column reads, verbatim, `none`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. **Note that `catalog/_literature/alldifferent.md` exists and is
not about this constraint**: `symmetric_all_different` is a different global with its own
empty literature cell, and nothing sourced for `alldifferent` transfers to it here. No web
access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:118`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `decomp`. No native explaining propagator in any of the three solvers
surveyed.

## Decomposition used here

**Generator value:** none. There is no such value in `explenation generator.ml`
(`grep -c -i 'symmetric' 'explenation generator.ml'` → `0`) and no
`explainall … "cata/symmetric_all_different.tex"` call.
**Emitted by:** nothing.
**Spec:** `decomps/all_different.md` — titled `# all_different, all_different_except,
all_different_except_0, symmetric_all_different`, so it covers this name, in its
`## symmetric_all_different` section.
**Shape: half of one.** The `alldifferent` conjunct is shape **P1** in
`decomps/_shapes-perm.md`, renumbered **S2** ("reify-and-count: Boolean sum against a bare
threshold") in `decomps/_shapes.md`, whose S2 instance list names
"`symmetric_all_different`'s `alldifferent` half" explicitly. The self-inverse conjunct has
no shape.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `X_{i} ≠ t` (would be, from `xac`) | — | **0** | not run: the self-inverse conjunct `x[x_i] = i` puts a variable in index position (G10) |

**One conjunct already runs and the other cannot be typed, and the split is the entry.**

- **`alldifferent(x)` ships.** It is the `alldiff` value at `explenation generator.ml:808-809`
  — `rule1` + `rule5`, a Boolean sum ≤ — and `cata/alldifferent.tex` holds one rule, measured
  `SOUND and MINIMAL` by `make validate` on 2026-09-21. `catalog/alldifferent.md` also
  records the floor caveat that matters when reusing it: that rule only ever fires at `n = 2`.
- **`∀i: x[x_i] = i` cannot be written at all.** `decomps/all_different.md` puts it as:
  "`Global_event`'s index positions are `ind_name` values (`I`/`T`/`P`/`R`), and there is no
  way to write 'the index is itself the *value* of another occurrence of `X`'." Verified
  against the source: `index` is `Ind of ind_name*ind_modifs list` (l.16), `ind_name` is the
  closed enum `I | T | P | R of int` (l.5), and no constructor in `ind_modifs` (l.9-14) or
  `ind_op` (l.39-49) admits a `var_name`. That is **G10**,
  `docs/DECOMP_FORMAT_NOTES.md:78`, which names `symmetric_all_different` first.

**"Recorded rather than derived" is the accurate description of the second half**, and
`decomps/all_different.md` says so itself: "there is no partial decomposition to write down
— the blocking point is the very first index position." This entry does not improve on that,
because there is nothing to improve on; it confirms it at the type level.

## Generated rules

**None.** There is no `cata/symmetric_all_different.tex` (`ls cata/` → 16 files, none of
that name), so `grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G10`**

G10 — "no variable in index position, `X_{X_i}`" — is a wall for the self-inverse conjunct,
for the type-level reason above. Nothing smaller helps: this is not a printer omission and
not an index-set naming problem; the atom has no representation.

**Why a half-entry would be worse than none, and this is a judgement this entry makes
explicitly.** It would be easy to point `symmetric_all_different` at
`cata/alldifferent.tex` and report one `SOUND and MINIMAL` rule. That would be wrong twice
over: the rule would be *sound for a weaker constraint*, so presenting it as an explanation
of `symmetric_all_different` overstates nothing about soundness but everything about
coverage; and `catalog/README.md`'s banner exists precisely to stop an entry listing some
rules from reading as if it lists all of them. **The half that ships explains
`alldifferent`; the half that is the point of this constraint explains nothing.** The
`Generated` row therefore reads 0, not 1.

**`CHRISTMAS_LIST.md:118`'s route cell prices this at "E0 + `inverse` channelling", and
that is optimistic in a specific way.** `inverse` channelling relates *two* arrays
(`x[i] = j ⇔ y[j] = i`) and is blocked only by G9's verbosity — see
[`inverse`](inverse.md). Self-inverse channelling relates one array **to itself through its
own values**, which is not the same operation: it is `x[x_i] = i`, not `x[i] = j ⇔ x[j] = i`.
The second form *is* expressible in `inverse`'s vocabulary and the first is not.
**Whether the two are interchangeable for this constraint is not settled in this repo**, and
this entry does not settle it: `decomps/all_different.md` states the blocker on the first
form and says nothing about the second. Flagged as an open question, because if they are
interchangeable then `symmetric_all_different` drops from G10 to G9 and becomes as writable
as `inverse`. **That is reasoning, not a finding.**

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:118`'s literature column reads `none`, and per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing` (no paper is cited),
not `out of reach` (no published premise to be out of reach of). Nothing was searched.

**`alldifferent`'s sourced literature does not transfer**, and the temptation to let it is
worth naming since the two entries sit in the same `CHRISTMAS_LIST.md` section.
`catalog/_literature/alldifferent.md` is about `alldifferent`, and
`catalog/alldifferent.md`'s calibration against Downing et al. §4/§5/§6 is a comparison of
*that* constraint's rules. `symmetric_all_different` has its own row, its own empty
literature cell, and no rules to compare.

## Gaps

| gap | what it blocks here |
|---|---|
| `G10` | **the wall.** No variable in index position: `x[x_i] = i` cannot be typed. `index` takes an `ind_name` (l.5, l.16) and nothing in `ind_modifs` (l.9-14) or `ind_op` (l.39-49) admits a `var_name` (`docs/DECOMP_FORMAT_NOTES.md:78`, which names this constraint first) |
| `G1` | inherited from the `alldifferent` half: shape S2's threshold lives only as the choice of `rule5`, so the implicit "at most 1" never reaches the page (`docs/DECOMP_FORMAT_NOTES.md:10`; `cata/alldifferent.tex` demonstrates it) |
| `G9` | **only under the open question in Status.** If the self-inverse conjunct can be restated as an `inverse`-style two-sided channel on one array, G10 drops out and G9's detour is what remains. Unsettled here |
| `G17` | no pivot-elimination pass. Not biting: the reification booleans wash out, as `decomps/all_different.md` says |

Extensions: **E0** (`CHRISTMAS_LIST.md:118`, route cell "**E0** + `inverse` channelling").
E0 means no extension needed, which is right for the `alldifferent` half and, per Status,
not obviously right for the other.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

**Numbering warning.** `decomps/all_different.md` predates the consolidation and calls this
gap **"G8", "distinct from G7"**. Consolidated, those are **G10** and **G9**
(`docs/DECOMP_FORMAT_NOTES.md:77-78`, "was" column: `perm G7` → G9, `perm G8` → G10). Read
literally today, that sentence points at the subrange gap.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `symmetric_all_different` in
  `A no-literature + solver-decomposes`, `ecodes: ['E0']`, `CHRISTMAS_LIST.md` line 118,
  section `1. AllDifferent family`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one; `cata/alldifferent.tex (1 rules)` with `VERDICT : SOUND and MINIMAL`, which
  is the `alldifferent` half quoted above. Totals: **34 rules checked in 11 entries: 13
  SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `symmetric_all_different.tex`.
  `grep -c -i 'symmetric' 'explenation generator.ml'` → 0.
- `explenation generator.ml` read, not run → `ind_name` at **5**, `ind_modifs` at **9-14**,
  `index` at **16**, `ind_op` at **39-49** (the G10 typing argument); `alldiff` at
  **808-809** (the half that ships).
- `CHRISTMAS_LIST.md:118` and `:106-109` read → the literature cell (`none`), the solver
  cell (`decomp`), the "E0 + `inverse` channelling" route cell, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:124` read → the name.
- `decomps/all_different.md` (its `## symmetric_all_different` section) read → the
  two-conjunct reading, the blocker, the local gap numbering; `decomps/_shapes-perm.md`
  (P1) and `decomps/_shapes.md` (S2's instance list) read → the shape of the half that
  ships.
- `catalog/alldifferent.md` read → the `SOUND and MINIMAL` verdict and the "only fires at
  n = 2" floor caveat.
- `docs/DECOMP_FORMAT_NOTES.md:10, 77-78` read → G1, G9, G10 and the "was" column.
- **The "half-entry would be worse than none" judgement and the `inverse`-channelling open
  question are reasoning, labelled as such in place.** Nothing was compiled and no
  decomposition was written.

**Discrepancies noted, and the one in this file fixed.**

1. **Wrong stub field, fixed here: `Spec: none — this constraint has no
   `decomps/symmetric_all_different.md`.`** It is covered by `decomps/all_different.md`,
   whose title line is `# all_different, all_different_except, all_different_except_0,
   symmetric_all_different`. `tools/catalog_stub.py` matches filenames only.
2. **`decomps/all_different.md` uses pre-consolidation gap numbers** (its "G8" is G10, its
   "G7" is G9).
