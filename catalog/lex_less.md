# `lex_less`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_less`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E0` (same tier row for `lex_lesseq`, `lex2`, `strict_lex2`, `lex2_strict`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/lex_less.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex`, and this constraint has no artifact in `cata/` |
| **Calibration** | **pending sourcing (C2)** — and see below: `CHRISTMAS_LIST.md:142` records that *no dedicated `lex` explanation paper was found* |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`lex_less(array[int] of var int: x, array[int] of var int: y)`

`x` is lexicographically strictly less than `y`; both arrays are the same length, and **both
are arrays of decision variables**.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:87` carries the *name* only, and this checkout holds no
`.mzn` file at all (`find . -name '*.mzn'` → empty, 2026-09-21). The signature above is
transcribed from `decomps/lex_less.md`, "Signature", which records it without a citation of its
own; treat it as recall.

**That both operands are variable arrays is the whole entry.** It is what separates `lex_less`
from every shipped decomposition in `cata/`, each of which compares a variable against a
*domain value* `t`. See Gaps, G3.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:142`, literature cell, verbatim:

> Chu & Stuckey, *Symmetries and lazy clause generation* (IJCAI 2011) — static symmetry
> breaking is LCG-compatible provided the added constraints have explaining propagators; no
> dedicated `lex` explanation paper found

**Rule shape:** **pending sourcing — see `catalog/_literature/`.** That directory holds
`alldifferent`, `cumulative` and `gcc` only; there is no `lex_less.md` in it. Per
`catalog/_literature/README.md`'s provenance convention and `catalog/README.md` step 2,
**no published rule shape is stated in this entry, from memory or otherwise.** No web access
was used and no paper was fetched by this session.

**The row's own second clause matters and is quoted rather than paraphrased above.** It says
the citation is for static symmetry breaking being LCG-compatible *given* explaining
propagators, and that no `lex`-specific explanation paper was found. `decomps/lex_less.md:37-39`
repeats that warning for the same reason. So the cited paper may well contain no `lex` rule at
all to calibrate against — but that is a statement about an unread paper, and the Calibration
section records it as a prior rather than converting it into the verdict
`no published rule exists`.

## Solver support

| | |
|---|---|
| Chuffed | native (`lex.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:142`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.
`CHRISTMAS_LIST.md:143` records that `lex_greater`/`lex_greatereq` come from the same
`lex.cpp`, as an argument swap rather than a new shape.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `lex_less`, and no
`explainall` call mentions it (the fifteen `explainall` calls are at lines 879-893).
**Emitted by:** nothing.
**Spec:** `decomps/lex_less.md`; shape **B** in `decomps/_shapes-seq.md:31-62`, which
`decomps/_shapes.md:155-175` renumbers to **S5** — "accumulated-state chain (genuine
auxiliary)", the largest shape in the corpus at 12 constraints.

The decomposition this project would use, from `decomps/lex_less.md:8-25`:

```
tied_1  = true                                    base case: nothing compared yet
tied_{i+1} ⇔ tied_i ∧ (X_i = Y_i)                 i ∈ [1,n-1]     rule3
tied_i → X_i ≤ Y_i                                every i         rule4 (guard clause)
∃ i : tied_i ∧ X_i < Y_i                          rule4, one clause per position
```

Mapped onto the seven schemas: step 2 is `rule3` (conjunction) with a fixed shift by 1 — the
same mechanics as `incr`'s `rule4` chain at `explenation generator.ml:830-831`, with AND for
OR — and steps 3 and 4 are `rule4` disjunctions per position.

**The schema shapes exist; the event vocabulary does not.** This distinction is
`decomps/lex_less.md:27-31`'s and it is the reason `CHRISTMAS_LIST.md`'s **E0** ("the schemas
exist") is not the same as "this can be encoded today". `rule1`'s channel is
`B ⇔ X_i op t` for `t` a domain value; there is no counterpart for `B ⇔ X_i = Y_i`.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The generator was never asked
anything about `lex_less`, because the decomposition above cannot be written in the input
format. There is no `cata/lex_less.tex`, so there is no `%% generator diagnostics (W1-T3)`
footer to read and no candidate count to report.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`) | — | **0** | not run: the decomposition is not encodable (G3) |

**What would be asked, if it were encodable**, and what each would meet — this is the part of
the entry that is a finding rather than an absence:

1. **G3 stops it before the first line.** `Global_event` and `ind_modifs`
   (`explenation generator.ml:50`, `:9-12`) express `X_i = t` against an index-derived domain
   value and nothing else. `X_i = Y_i` has no representation, so `tied_{i+1} ⇔ tied_i ∧
   (X_i = Y_i)` cannot be typed, never mind run.
2. **If G3 landed, the auxiliary would be the next wall, and it now fails loudly.**
   `tied_i` is an *accumulated* fact with **no `Global_devent` standing for it** — unlike
   `increasing`'s `B_1`, which is defined in the same `Decomp` as a reification of `X_i ≥ t`
   and is therefore substituted back before anything prints
   (`decomps/_shapes-seq.md:26-29`). W1-T10 changed what happens next: both printers now
   **raise** `Generator_failure` on a bare `B` instead of emitting the literal string
   `"ERROR B "` (`explenation generator.ml:488` and `:517`, measured today by reading both
   lines). `docs/ROADMAP.md:54` records the probe: the old generator exited 0 and wrote
   `$$\frac{ERROR B }{X_i=t}$$`; the new one exits 2, names the failure and **writes no file**.

   So the honest statement for this entry's future is: **generation would fail loudly, not
   silently.** Three outcomes are possible and *which one occurs is not established*, because
   nobody can run it:
   - `find`'s AND/OR walk unfolds the recursion to an `X`-only base case and a rule prints;
   - the walk meets the recursion as a cycle and cuts it — `R`, which `filter_branches`
     (`explenation generator.ml:622-630`) counts as a warning and drops, losing the candidate;
   - a bare `B` reaches `printvartex` and the generator raises, writing nothing.

   `decomps/_gaps-seq.md:18-24` left this open ("not established, not run") when the failure
   mode was a broken string. It is still open; only the consequence changed.
3. **Removing `tied_i` from a finished rule needs G17.** There is no pivot-elimination pass, so
   even the first outcome above prints premises about an auxiliary the user did not write —
   which D-0004 forbids by default. That is why this shape is "cheap for the engine and
   expensive for the catalog" (`decomps/_shapes.md:206-225`, said there of S8; it applies to
   S5 for the same reason).

**Not "nothing is explainable about `lex_less`".** A decomposition exists, is written down, and
is standard; what is missing is one literal form and one elimination pass.

## Generated rules

**None.** There is no `cata/lex_less.tex` (`ls cata/` → 16 files, none of them this;
2026-09-21). Nothing is rendered here, and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

The gap number is the binding one: variable-vs-variable comparison. It is not a defect of this
constraint's spec — `decomps/lex_less.md` is complete and states the decomposition in four
lines — but of the encoding the generator reads. Two further gaps sit behind it and are listed
below; **closing G3 alone would produce either a rule with an auxiliary in its premises or a
named failure**, not a finished catalog entry.

Nothing here is validated, flagged or refuted. G3's weight is itself a measured-by-reading
result: `docs/DECOMP_FORMAT_NOTES.md:88-90` records that three independent families hit it
(the counting pilot's variable `v`, `maximum`/`minimum`/`arg_max`/`arg_min`, and this one),
which is what makes it load-bearing rather than one constraint's complaint.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions fail independently, and either alone would be enough:

1. **No published shape is in the repo.** `CHRISTMAS_LIST.md:142` cites Chu & Stuckey 2011 and
   `catalog/_literature/` has no file for it. Writing a rule shape from memory is forbidden by
   `catalog/README.md` step 2 and `catalog/_literature/README.md`, and no paper was fetched.
2. **No generated rule exists on this side.** With **0** rules there is no premise to place in
   an implication order even if the shape were sourced.

**A prior, recorded as a prior and not as a verdict.** `CHRISTMAS_LIST.md:142` states in its own
words that *no dedicated `lex` explanation paper was found*, and the cited paper is about
static symmetry breaking being compatible with LCG *given* explaining propagators. If that
holds up on reading, the eventual verdict is `no published rule exists` — the verdict this
catalog defines for "`CHRISTMAS_LIST.md` records no explanation for this constraint". This
entry does **not** claim it, because the row is a note by a previous session and the paper is
unread, and "the list says so" is not the same evidence as "the paper says so".

**Not compared on minimality**, here or anywhere: `catalog/README.md` records that none of the
three papers sourced so far proves any explanation minimal, so the axis when it opens is
implication strength.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** Only variable-vs-domain-value comparisons exist; `X_i = Y_i` and `X_i < Y_i` have no representation, so the decomposition cannot be written at all. Reinforced by two other families (`docs/DECOMP_FORMAT_NOTES.md:88-90`) |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule. This is what would make a generated `lex_less` rule *bad* rather than absent — D-0004's cost in coverage, not just in rule length |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printer path that now **raises** `Generator_failure` (`explenation generator.ml:488`, `:517`). `docs/DECOMP_FORMAT_NOTES.md:112-114` explains why this is a bug and not a format gap |
| `G7` | **not this entry's, but the family's.** `lex_chain_*` needs an instance-dependent number of chained pairs, which routes to `D2`'s missing printer — the same wall as G7 (`docs/DECOMP_FORMAT_NOTES.md:96-104`). Plain `lex_less` is a single pair and does not need it |

Extensions: **E0** (`CHRISTMAS_LIST.md:142`) — but read `decomps/lex_less.md:27-31`'s
qualification with it: E0 means the *rule schemas* exist, and here the **event vocabulary**
does not. An E-code of E0 beside a status of `nothing generated` is not a contradiction; it is
the distinction that spec makes.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → 16 entries considered, none named
  `lex_less`; run totals **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2
  rules in 5 entries out of scope**. This entry contributes to none of those counts.
- `ls cata/` → 16 `.tex` files, no `lex_less.tex`.
- `python3 tools/mzn_coverage.py --rank --json` → `lex_less` in tier
  `D literature + solver-native`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 142, section
  `3. Value ordering, precedence, symmetry`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:3` (`var_name`), `:5-12` (`ind_name`, `ind_set`,
  `ind_const`, `ind_modifs`), `:50` (`Global_event`), `:298-340` (`rule1`/`rule3`/`rule4`),
  `:488` and `:517` (the two printers that raise on a bare `B`), `:622-630`
  (`filter_branches`, the `R` cut), `:830-831` (`incr`'s chain, the AND/OR-shift precedent),
  `:879-893` (the fifteen `explainall` calls — none is `lex_less`).
- `CHRISTMAS_LIST.md:142`, `:143`, `:106-109` read → the citation, the solver cells, the legend.
- `decomps/lex_less.md`, `decomps/_shapes-seq.md:31-62`, `decomps/_gaps-seq.md:9-24`,
  `decomps/_shapes.md:155-175` read → the four-line decomposition, Shape B / S5, the auxiliary
  risk, the shape numbering.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 96-104, 112-114` read → G3, G17, the three
  families that hit G3, the `D2` withdrawal, and why `"ERROR B "` is W1-T10 and not a gap.
- `docs/ROADMAP.md:54` read → W1-T10 `DONE`, with the probe that shows the new behaviour is a
  named failure and no file.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
- The three-outcome analysis in "Scope of this entry" is **reasoning, labelled as such in
  place**, from the printer lines and `filter_branches`. Nothing about it was run; it cannot be,
  because G3 blocks the input.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`decomps/_gaps-seq.md:9-24` and `decomps/_shapes-seq.md:48-57` both state that `B` "prints
   as the literal string `\"ERROR B \"`".** Measured 2026-09-21: both printers **raise**
   (`explenation generator.ml:488`, `:517`), fixed under W1-T10 on 2026-09-18. The risk those
   files describe is real and unchanged; its observable is now an exception and no output file.
2. **`decomps/_gaps-seq.md` numbers this bug `G6`** and its own `G7`/`G8` are `G12`/`G13` in the
   consolidated list. `docs/DECOMP_FORMAT_NOTES.md:63-71` already says the per-file numbers are
   superseded; noted here only because a reader arriving from that file will see three
   conflicting `G6`s.
