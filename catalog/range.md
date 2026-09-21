# `range`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `range`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E5`, section `10. Set constraints`. Out of scope for the *ranking*, not for the catalog: `catalog/README.md` requires an entry for all 118 globals |
| **Status** | `nothing generated — blocked on G8` |
| **Generated** | **0** rules in `cata/range.tex` |
| **Validator** | out of scope. Machine-printed reason: "index sets D_5, D_6 are never defined by the printer (W1-T2); this is Bessiere's set RANGE and its set variables appear in no atom (gccat's range_ctr is an unrelated constraint — docs/GCCAT.md s5.2)" |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:206` records `none` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/range.tex \| wc -l`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`range(array[int] of var int: x, var set of int: s, var set of int: t)`

`t` is the image of the index set `s` under `x`: `t = { x[i] : i ∈ s }`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:102` carries the *name* only, and no `decomps/range.md`
exists. The signature above is recall and is marked as such. What is quotable in-repo is
`CHRISTMAS_LIST.md:206`: MiniZinc's `range` "take[s] `var set of int`" and has "**no library
decomposition** (declared solver-native)".

**Two different constraints are called `range`, and this entry is about the first.** W3-C
disambiguated them and both `CHRISTMAS_LIST.md:206` and `docs/GCCAT.md:165-167` carry the
result: `cata/range.tex` is **Bessiere et al.'s set-variable RANGE**, matching the MiniZinc
global; gccat's **`range_ctr`** is an unrelated arithmetic constraint on `max(X) − min(X) + 1`
over an index range. Nothing in this entry is a claim about `range_ctr`. (The Bessiere
attribution is itself in-repo only — `CHRISTMAS_LIST.md:206`, `docs/GCCAT.md:165`,
`docs/VALIDATOR.md:331`, `validator.ml:1093` — with no paper cited and none in
`catalog/_literature/`. It is repeated here as this repo's identification of the formulation,
not as a citation.)

**What the shipped decomposition actually encodes cannot be recovered from the artifact, and
that is the entry's main finding.** See "Decomposition used here".

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:206`'s `Lit.` column for the `range`, `roots` row is the
literal string `none`.

**Rule shape:** nothing to source, and no `catalog/_literature/range.md` is expected. The
Bessiere attribution above names a *formulation*, not an explanation paper, and no explanation
rule for `range` is recorded anywhere in this repo.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | absent (no `[C]`, no `[C✗]`) |

Source: `CHRISTMAS_LIST.md:206`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The row
adds that MiniZinc declares `range` solver-native with no library decomposition — so "decomp"
here describes the fallback, not a shipped `fzn_range`.

## Decomposition used here

**Generator value:** `range`, `explenation generator.ml:859-861`
**Emitted by:** `explainall [xac] range "cata/range.tex"`, line 892
**Spec:** **none.** There is no `decomps/range.md`. `decomps/_shapes.md:104-113` classes it
"Also shipped and unspecified" under shape **S2**, and `decomps/_shapes.md:306-307` reads the
chain off the source.

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule6, [Decomp_devent (true, (B 1), id, ontin (D 5))]);
Decomp (2, rule7, [Decomp_devent (true, (B 1), id, ontin (D 6))])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency.
- **step 2a, `rule6`** — a Boolean sum in the `≥` direction over a *value-restricted* family:
  `ontin (D 5)` is `OpOn (FT, D 5)`, which replaces the index list with one fresh `t` ranging
  over `D_5` (`explenation generator.ml:41`), so the sum is `Σ_{t ∈ D_5} B1_{i,t} ≥ c`.
- **step 2b, `rule7`** — the same with `=` over `D_6`: `Σ_{t ∈ D_6} B1_{i,t} = c`.
  Both carry `Decomp` id `2`, i.e. two clauses of one constraint.

**The decomposition is not identifiable as `range`, and the artifact does not let anyone check
whether it is.** Four things are missing at once, and none of them is a printer problem:

1. **Neither set variable has a channel.** `range`'s content is `s` and `t`; the decomposition
   has no `rule1` step for either, no `var_name` constructor standing for a set, and
   correspondingly no atom mentioning one. This is the validator's own reason, and it is a
   statement about the *decomposition*, not about the `D_k` printer.
2. **Both sums are restricted on the `t` family**, i.e. on *values*. `range`'s `s` is a set of
   *indices*, so a faithful encoding would need an `i`-restricted sum somewhere; there is none.
3. **Neither sum's threshold reaches the page.** Each `Decomp` has a single `Decomp_devent`
   and no `Reified_devent`, so `reified_devent` returns the placeholder `T`
   (`explenation generator.ml:245-246`) and `rule5/6/7`'s `c` argument is the `Decomp` record,
   not a constant — **G1**. What `Σ_{t ∈ D_5} B1_{i,t}` is compared *against* is nowhere in the
   artifact.
4. **`D_5` and `D_6` are index sets, i.e. parameters.** `docs/GCCAT.md:143-146` records the
   reading: this repo's `range` and `roots` "already eliminated the sets by hand into index
   sets `D_5`/`D_6`". Under that reading the shipped object is a *parameterised special case*,
   not `range`, whose whole point is that `s` and `t` are decision variables.

`decomps/_shapes.md:355-365` reached the same place from a different direction: `span` was
claimed E0 "reusing `range`/`roots`" as a ∀-bound-plus-∃-tight pair, and reading the source
withdrew that — "`range`/`roots` are Boolean **sums** over a value-restricted family, not a
∀/∃ pair, so they are no precedent for min/max at all". Two sessions have now read this value
and neither could make it mean what its filename says.

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i = t` and `X_i ≠ t`, from the `xac`
global event (arc consistency, `explenation generator.ml:869`). Nothing was asked about `s` or
`t`, and nothing could have been: there is no literal for either (point 1 above).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 2 | **0** | `dropped F 0, cycle 0, duplicate 0, undefined index set 2` (`D6, D5`) |
| `X_{i} \neq t` | 2 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 1` (`D6`) |

Verbatim from the artifact:

```
%%   ** REFUSED for X_{i}=t: 2 branch(es) reference undefined index set(s) D6, D5; emitting
%%      them would state a rule over a set the artifact never defines (W1-T2) **
%%   ** NO RULE EMITTED for X_{i}=t: 2 candidate(s), all blocked **
```

The asymmetry is real and worth reading: `X_i = t` loses both candidates to the refusal, while
`X_i ≠ t` loses one to a legitimate `F` discard (a branch reaching a constraint that is not
reified) and one to the refusal. Three refusals, one `F`, zero rules.

**What would change it — and it is two different things, at two different prices.**

- **For the artifact as written** (the hand-eliminated, parameter reading): **G8**, `ind_set`
  names only whole predefined ranges, no subrange and no exclusion
  (`docs/DECOMP_FORMAT_NOTES.md:76`). `D_5` and `D_6` are named subsets of `[1,m]`, so the
  format needs a way to name a value subset. This is the status row's gap, because it is the
  gap that blocks *this file* from containing a rule. Note what it buys: rules about a
  parameterised special case, whose relation to `range` nobody has stated.
- **For `range` itself**: **E5**, set → Boolean channelling (`docs/DECISIONS.md:122`), so that
  `s` and `t` become variables with literals of their own, plus **G14** — no summation over a
  variable-determined index set (`docs/DECOMP_FORMAT_NOTES.md:82`, hit from the scheduling side
  by `cumulatives`) — because with `s` a variable the sum's *extent* is chosen by a decision
  variable. G8 alone does not reach this and would quietly ship the special case under the
  general name.

**Before either, someone has to write `decomps/range.md`.** Of all five entries this session
wrote, this and `roots` are the only two with no spec at all, and they are the two where the
shipped decomposition cannot be matched to its name. That ordering is not a coincidence.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/range.tex`.

## Generated rules

**None.** `grep -o '\\frac' cata/range.tex | wc -l` → `0`. The file is the diagnostics footer
and nothing else. It held **3** rules before W1-T2 (`docs/VALIDATOR.md:331`; `docs/ROADMAP.md:48`
books the change as `range 3→0`), all quantified over `D_5`/`D_6`.

## Status

**`nothing generated — blocked on G8`**

Four candidate branches reduce to zero rules: three W1-T2 refusals naming `D_5`/`D_6` and one
legitimate `F` discard. The gap in the status line is the one that blocks *this file*; it is not
the gap that would make this file about `range`. Nothing here is validated, flagged or refuted,
and the useful content of the entry is negative: **the shipped decomposition has no literal for
either set variable, no visible threshold on either sum, and no spec, so even restoring its
three rules would not produce a checkable claim about `range`.** `docs/VALIDATOR.md:335-338`
makes the same point in its own words — a reading "*could* have been invented for each ... and
each would have produced verdicts. None of them would have been about the shipped artifact."

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:206` gives `none` in the literature column for the `range`, `roots` row. With
no published shape and **0** generated rules, there is nothing on either side of an implication
comparison.

**The Bessiere attribution is not a citation and must not be promoted into one.** Four in-repo
documents call `cata/range.tex` "Bessiere et al.'s set RANGE" and none of them names a paper,
a venue or a year; `catalog/_literature/` has no file. Anyone later tempted to calibrate against
"the RANGE propagator" should source it first under `catalog/_literature/README.md`'s
convention, and should expect the calibration to be blocked one step earlier anyway, by the
identification problem in "Decomposition used here": you cannot compare a published rule for
`range` against a decomposition nobody has shown to be `range`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one for the artifact.** `ind_set` names only whole predefined ranges, so `D_5`/`D_6` — named value subsets — have no expression and W1-T2 refuses every branch through them |
| `G1` | neither sum's threshold reaches the page, so even with G8 the printed rule would not say what `Σ_{t ∈ D_5} B1_{i,t}` is compared against |
| `G14` | **for `range` proper.** No summation over a variable-determined index set; `s` is a set *variable*, so it determines the sum's extent |
| `G2` | `var_name` has no constructor for a constraint's own set argument, so `s` and `t` have no printable name even once E5 exists |
| — | no `decomps/range.md`. Not a gap; a missing spec, and the prerequisite for numbering the rest honestly |

Extensions: **E5** (`CHRISTMAS_LIST.md:206`), set → Boolean channelling per `docs/DECISIONS.md:122`.
Closing G8 is part of **E2** / W2-T1 (`explenation generator.ml:431-458`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, output redirected then grepped) → `cata/range.tex
  (0 rules, parses)` in the out-of-scope block, reason string quoted verbatim in the header
  table. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules
  in 5 entries out of scope.**
- `grep -o '\\frac' cata/range.tex | wc -l` → `0`.
- `python3 tools/mzn_coverage.py --rank --json` → `range` in `- out of scope`, ecodes `["E5"]`,
  `CHRISTMAS_LIST.md` line 206, section `10. Set constraints`.
- `cata/range.tex` read, not run → the diagnostics footer, quoted above.
- `explenation generator.ml:859-861, 869, 892` read, not run → the decomposition, the global
  event, the emitting call; `:41` for `OpOn`'s meaning, `:245-246` for the placeholder
  `reified_devent`, `:459` for `ind_set_defined`, `:431-458` for the W1-T2 rationale.
- `CHRISTMAS_LIST.md:206` and `:106-109` read → citation row, the `var set of int` /
  solver-native note, the W3-C disambiguation, the solver legend.
- `docs/GCCAT.md:143-146, 165-167` read → the hand-elimination of the sets into `D_5`/`D_6`, and
  the `range` / `range_ctr` disambiguation.
- `docs/VALIDATOR.md:331, 335-338` read → the pre-W1-T2 rule count (3) and the "a reading could
  have been invented" paragraph.
- `docs/DECOMP_FORMAT_NOTES.md:76, 82` and `docs/DECISIONS.md:122` read → G8, G14, E5.
- `decomps/_shapes.md:104-113, 306-307, 355-365` read → the S2 classification, the schema chain,
  and the withdrawal of `span`'s "reusing `range`/`roots`" claim.
- `docs/ROADMAP.md:48` read → W1-T2 `DONE`, with `range 3→0 rules` booked as the intended cost.
- The split between **G8** (this artifact) and **E5 + G14** (`range` itself) is **reasoning
  about the two readings of `D_5`/`D_6`, not a measurement**, and rests on
  `docs/GCCAT.md:143-146`'s statement that the sets were eliminated by hand.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **Stale line numbers.** `CHRISTMAS_LIST.md:206` and `docs/GCCAT.md:144` cite the
   `range`/`roots` decompositions at "Generator l.423–428"; `decomps/_shapes.md:104` and `:306`
   cite "l.717–719" for `range`. Measured today: `range` is at **859-861** and `roots` at
   **856-858**.
2. **`docs/VALIDATOR.md`'s reason string** leads with the undefined `D_5`/`D_6`, which explains
   why the branches were refused rather than why a 0-rule file cannot be validated. Already open
   as `docs/ROADMAP.md:55` (W1-T11 (a)); recorded here only as still true on 2026-09-21. Its
   second clause — the set variables appear in no atom — is the part that still bites, and it is
   about the decomposition, not the printer.
