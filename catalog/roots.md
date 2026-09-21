# `roots`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `roots`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E5`, section `10. Set constraints`. Out of scope for the *ranking*, not for the catalog: `catalog/README.md` requires an entry for all 118 globals |
| **Status** | `nothing generated — blocked on G8` |
| **Generated** | **0** rules in `cata/roots.tex` |
| **Validator** | out of scope. Machine-printed reason: "index sets D_5, D_6 are never defined by the printer (W1-T2); the set variables S and T appear in no atom" |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:206` records `none` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/roots.tex \| wc -l`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`roots(array[int] of var int: x, var set of int: s, var set of int: t)`

`s` is exactly the set of indices whose variable takes a value in `t`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:108` carries the *name* only, and no `decomps/roots.md`
exists. The signature above is recall. What *is* quotable in-repo is the semantics, from
`docs/GCCAT.md:143-144`: "`roots` is a set constraint here (`S`, `T` are sets; decomposition
`i ∈ S ⇔ X_i ∈ T`)" — read out of gccat by W3-C. And `CHRISTMAS_LIST.md:206`: MiniZinc's
`roots` "take[s] `var set of int`" and has "**no library decomposition** (declared
solver-native)".

**What the shipped decomposition actually encodes cannot be recovered from the artifact, and
that is the entry's main finding.** See "Decomposition used here".

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:206`'s `Lit.` column for the `range`, `roots` row is the
literal string `none`. No `catalog/_literature/roots.md` is expected.

**Rule shape:** nothing to source. `docs/GCCAT.md:143-144` supplies a *decomposition*
(`i ∈ S ⇔ X_i ∈ T`) read out of gccat, which is a modelling statement and not an explanation
rule; it is used below as the yardstick the shipped value fails, never as a published
explanation.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | absent (no `[C]`, no `[C✗]`) |

Source: `CHRISTMAS_LIST.md:206`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. As with
`range`, MiniZinc declares `roots` solver-native with no library decomposition, so "decomp"
names the fallback rather than a shipped `fzn_roots`.

## Decomposition used here

**Generator value:** `roots`, `explenation generator.ml:856-858`
**Emitted by:** `explainall [xac] roots "cata/roots.tex"`, line 891
**Spec:** **none.** There is no `decomps/roots.md`. `decomps/_shapes.md:104-113` classes it
"Also shipped and unspecified" under shape **S2**, and `decomps/_shapes.md:306-307` reads the
chain off the source: "`roots` is `rule1` + `rule7` + `rule7`".

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule7, [Decomp_devent (true, (B 1), id, ontin (D 5))]);
Decomp (2, rule7, [Decomp_devent (true, (B 1), id, ontin (D 6))])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency.
- **steps 2a and 2b, `rule7` twice** — two Boolean sums with `=`, each over a *value-restricted*
  family: `ontin (D 5)` is `OpOn (FT, D 5)`, which discards the index list and replaces it with
  one fresh `t` ranging over `D_5` (`explenation generator.ml:41`), giving
  `Σ_{t ∈ D_5} B1_{i,t} = c` and `Σ_{t ∈ D_6} B1_{i,t} = c`. Both carry `Decomp` id `2`, i.e.
  two clauses of one constraint.

**This is `range`'s value with `rule6` replaced by a second `rule7`, and that is the only
difference between the two shipped decompositions.** Compare
`explenation generator.ml:859-861`.

**It is not identifiable as `roots`.** The yardstick is in-repo: gccat's decomposition is
`i ∈ S ⇔ X_i ∈ T` (`docs/GCCAT.md:143-144`). Four things stand between that and the shipped
value, and none of them is a printer problem:

1. **Neither set variable has a channel.** No `rule1` step for `S` or `T`, no `var_name`
   constructor standing for a set, and so no atom mentioning one. That is the validator's own
   reason, verbatim in the header table, and it is a statement about the decomposition.
2. **The biconditional's left-hand side is missing entirely.** `i ∈ S` is a predicate on an
   *index*; both shipped sums are restricted on the **value** family `FT`. There is no
   `i`-restricted sum and nothing that could stand for `S`.
3. **Neither sum's threshold reaches the page.** Each `Decomp` has a single `Decomp_devent` and
   no `Reified_devent`, so `reified_devent` returns the placeholder `T`
   (`explenation generator.ml:245-246`) and `rule5/6/7` take the `Decomp` record as their `c`
   argument, never a constant — **G1**. `Σ_{t ∈ D_5} B1_{i,t} = ?` is genuinely unanswerable
   from the artifact. The one reading that fits the shape — threshold `1`, so each sum says
   "`X_i` takes exactly one value in `D_k`", i.e. `X_i ∈ D_k` — is a **hypothesis of this
   session's**, consistent with `alldifferent`'s identical single-`Decomp_devent` shape for its
   implicit `≤ 1`, and it is not written anywhere in the repo. Under it, the shipped value says
   `X_i ∈ D_5 ∧ X_i ∈ D_6` for every `i`, which is not `roots` under any reading.
4. **`D_5` and `D_6` are index sets, i.e. parameters.** `docs/GCCAT.md:143-146` records that
   this repo's `roots` and `range` "already eliminated the sets by hand into index sets
   `D_5`/`D_6`", and tells the next reader not to re-import the set formulation. Under that
   reading the shipped object is a parameterised special case, and `roots`'s whole content —
   that `S` and `T` are decision variables — is gone.

`decomps/_shapes.md:355-365` independently withdrew a claim that rested on misreading this
value: `span` was priced E0 "reusing `range`/`roots`" as a ∀-bound-plus-∃-tight pair, and
reading the source showed these are Boolean **sums** over a value-restricted family, "no
precedent for min/max at all". This entry is the third reading of the same value and reaches
the same place.

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i = t` and `X_i ≠ t`, from the `xac`
global event (arc consistency, `explenation generator.ml:869`). Nothing was asked about `S` or
`T`; there is no literal for either (point 1 above).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 2 | **0** | `dropped F 0, cycle 0, duplicate 0, undefined index set 2` (`D6, D5`) |
| `X_{i} \neq t` | 2 | **0** | `dropped F 0, cycle 0, duplicate 0, undefined index set 2` (`D6, D5`) |

Verbatim from the artifact:

```
%%   ** REFUSED for X_{i} \neq t: 2 branch(es) reference undefined index set(s) D6, D5;
%%      emitting them would state a rule over a set the artifact never defines (W1-T2) **
%%   ** NO RULE EMITTED for X_{i} \neq t: 2 candidate(s), all blocked **
```

**This is the cleanest of the four refused entries.** Four candidates, four refusals, zero `F`
discards, zero cycles, zero duplicates — the symmetry between the two events follows from the
two `rule7` steps being identical apart from their value set. Every lost branch was lost to the
same cause, which is why `roots` is the entry where W1-T2's cost is easiest to read off.

**What would change it — and it is two different things, at two different prices.**

- **For the artifact as written** (the hand-eliminated, parameter reading): **G8**, `ind_set`
  names only whole predefined ranges, no subrange and no exclusion
  (`docs/DECOMP_FORMAT_NOTES.md:76`). `D_5` and `D_6` are named subsets of `[1,m]`. This is the
  status row's gap, because it is the one blocking *this file*. It buys four rules about a
  special case whose relation to `roots` nobody has stated, and — because of G1 — rules that
  still would not print what either sum is compared against.
- **For `roots` itself**: **E5**, set → Boolean channelling (`docs/DECISIONS.md:122`), giving
  `S` and `T` literals of their own; **G2**, because `var_name` has no constructor for a
  constraint's own set argument; and **G14**, no summation over a variable-determined index
  set (`docs/DECOMP_FORMAT_NOTES.md:82`), because with `T` a variable the sum `Σ_{t ∈ T}` has a
  variable-determined extent. G8 alone reaches none of this and would ship the special case
  under the general name.

**Before either, someone has to write `decomps/roots.md`.** `roots` and `range` are the only
two of this session's five with no spec at all, and they are the two whose shipped
decomposition cannot be matched to its name.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/roots.tex`.

## Generated rules

**None.** `grep -o '\\frac' cata/roots.tex | wc -l` → `0`. The file is the diagnostics footer
and nothing else. It held **4** rules before W1-T2 (`docs/VALIDATOR.md:333`;
`docs/ROADMAP.md:48` books the change as `roots 4→0`) — the largest single loss of the five
entries W1-T2 emptied — all quantified over `D_5`/`D_6`.

## Status

**`nothing generated — blocked on G8`**

Four candidate branches, four W1-T2 refusals, zero rules. The gap in the status line is the one
that blocks this file; it is not the gap that would make this file about `roots`. Nothing is
validated, flagged or refuted here. The useful content is negative and, unusually, is *about
the decomposition rather than the engine*: with no literal for `S` or for `T`, no `i`-restricted
sum to carry `i ∈ S`, and no visible threshold on either sum, restoring the four pre-W1-T2 rules
would produce four checkable statements about something, and nobody can currently say about
what. `docs/VALIDATOR.md:335-338` puts the same judgement in general terms — a reading "*could*
have been invented for each ... None of them would have been about the shipped artifact."

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:206` gives `none` in the literature column for the `range`, `roots` row, so
there is no published explanation to compare against, and with **0** generated rules there is
nothing on this side either.

Two things that are *not* a calibration and should not be mistaken for one later:

- **gccat's `i ∈ S ⇔ X_i ∈ T`** (`docs/GCCAT.md:143-144`) is a decomposition, not an
  explanation. Comparing the shipped value against it, as "Decomposition used here" does, is an
  *identification* check — does this encode `roots`? — not a comparison of explanation strength.
  The two axes are different and this entry keeps them apart.
- **The shipped value's kinship with `range`** (identical but for `rule6` → `rule7`) is a fact
  about two files in this repo. It says nothing about either constraint's literature.

Were a paper to surface, calibration would still be blocked one step earlier, by the
identification problem: no implication comparison can be stated between a published rule for
`roots` and a decomposition nobody has shown to be `roots`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one for the artifact.** `ind_set` names only whole predefined ranges, so the value subsets `D_5`/`D_6` have no expression and W1-T2 refuses all four branches |
| `G1` | neither `rule7`'s threshold reaches the page; even after G8 the rules would not state what either sum equals |
| `G2` | `var_name` has no constructor for a constraint's own set argument, so `S` and `T` have no printable name even once E5 exists |
| `G14` | **for `roots` proper.** No summation over a variable-determined index set; `T` is a set *variable*, so it fixes the extent of `Σ_{t ∈ T}` |
| — | no `decomps/roots.md`. Not a gap; a missing spec, and the prerequisite for numbering the rest honestly |

Extensions: **E5** (`CHRISTMAS_LIST.md:206`), set → Boolean channelling per
`docs/DECISIONS.md:122`. Closing G8 is part of **E2** / W2-T1
(`explenation generator.ml:431-458`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, output redirected then grepped) → `cata/roots.tex
  (0 rules, parses)` in the out-of-scope block, reason string quoted verbatim in the header
  table. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules
  in 5 entries out of scope.**
- `grep -o '\\frac' cata/roots.tex | wc -l` → `0`.
- `python3 tools/mzn_coverage.py --rank --json` → `roots` in `- out of scope`, ecodes `["E5"]`,
  `CHRISTMAS_LIST.md` line 206, section `10. Set constraints`.
- `cata/roots.tex` read, not run → the diagnostics footer, quoted above.
- `explenation generator.ml:856-858, 869, 891` read, not run → the decomposition, the global
  event, the emitting call; `:41` for `OpOn`'s meaning, `:245-246` for the placeholder
  `reified_devent`, `:459` for `ind_set_defined`, `:431-458` for the W1-T2 rationale,
  `:859-861` for the `range` comparison.
- `CHRISTMAS_LIST.md:206` and `:106-109` read → citation row, the `var set of int` /
  solver-native note, the solver legend.
- `docs/GCCAT.md:143-146` read → gccat's `i ∈ S ⇔ X_i ∈ T` and the hand-elimination of the sets.
- `docs/VALIDATOR.md:333, 335-338` read → the pre-W1-T2 rule count (4) and the "a reading could
  have been invented" paragraph.
- `docs/DECOMP_FORMAT_NOTES.md:76, 82` and `docs/DECISIONS.md:122` read → G8, G14, E5.
- `decomps/_shapes.md:104-113, 306-307, 355-365` read → the S2 classification, the
  `rule1 + rule7 + rule7` chain, and the withdrawal of `span`'s claim.
- `docs/ROADMAP.md:48` read → W1-T2 `DONE`, with `roots 4→0 rules` booked as the intended cost.
- The **threshold-`1` hypothesis** in "Decomposition used here" point 3, and the split between
  **G8** (this artifact) and **E5 + G2 + G14** (`roots` itself), are **reasoning, labelled as
  such in place**, not measurements.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **Stale line numbers.** `CHRISTMAS_LIST.md:206` and `docs/GCCAT.md:144` cite the
   `range`/`roots` decompositions at "Generator l.423–428"; `decomps/_shapes.md:104` and `:306`
   cite "l.714–716" for `roots`. Measured today: `roots` is at **856-858**, `range` at
   **859-861**.
2. **`docs/VALIDATOR.md`'s reason string** leads with the undefined `D_5`/`D_6`, describing why
   the branches were refused rather than why a 0-rule file cannot be validated — already open as
   `docs/ROADMAP.md:55` (W1-T11 (a)), recorded here only as still true on 2026-09-21. Its second
   clause, "the set variables `S` and `T` appear in no atom", is the part that still bites, and
   it is about the decomposition, not the printer.
