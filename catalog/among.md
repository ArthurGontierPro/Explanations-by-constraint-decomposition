# `among`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `among`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` |
| **Status** | `nothing generated — blocked on G8` |
| **Generated** | **0** rules in `cata/among.tex` |
| **Validator** | out of scope. Machine-printed reason: "index set D_4 is never defined by the printer (W1-T2), AND among's count variable appears in no atom, so the rules constrain X alone while `among` restricts X only jointly with that count" |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:129` records `none` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/among.tex \| wc -l`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`among(var int: n, array[int] of var int: x, set of int: v)`

`n` is the number of indices `i` with `x[i] ∈ v`.

**Provenance of the signature:** not vendored in this repo. `tools/data/minizinc-2.10.1-globals.txt:23`
carries the *name* only. The signature line above is copied from `decomps/among.md`
("Signature", which spells the parameter set `s`), which is itself recorded there without a
citation; treat it as recall, not as a citation. What is quotable in-repo is
`CHRISTMAS_LIST.md:129`, which gives literature, solver and route and no signature.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:129` reads
`| `among` | none | decomp | **E0** — already in `cata/among.tex` |` — the `Lit.` column is the
literal string `none`.

**Rule shape:** there is nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only, and no file for `among` is expected, because the index records no
paper to make one from.

This is a **tier A** constraint in the ranking's own words — `A no-literature +
solver-decomposes` — which is the tier where a derived schema would be the *only* schema. That
is what makes the empty output below worth reporting rather than skipping.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | absent (no `[C]`, no `[C✗]`) |

Source: `CHRISTMAS_LIST.md:129`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**Generator value:** `among`, `explenation generator.ml:851-853`
**Emitted by:** `explainall [xac] among "cata/among.tex"`, line 889
**Spec:** `decomps/among.md` (shape **S3** in `decomps/_shapes.md`)

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule4, [Decomp_devent (true, (B 1), id, ontin (D 4)); Reified_devent (true, (B 2), id, t_out)]);
Decomp (3, rule7, [Decomp_devent (true, (B 2), id, oni)])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency: the shared per-`(i,t)`
  channelling grid that `gcc` and `nvalue` also use.
- **step 2, `rule4`** — a disjunction over the *parameter set*: `B2_i ⇔ ⋁_{t ∈ D_4} B1_{i,t}`,
  i.e. "`X_i` takes a value in `v`". `D 4` is where the constraint's own set argument went.
- **step 3, `rule7`** — a Boolean sum with `=`: `Σ_i B2_i` against the count.

**Two things about step 3, both read off the source, both already recorded elsewhere.** It is
a *single* `Decomp_devent` with no `Reified_devent`, the same "implicit constant" shape
`alldifferent` uses for its own `≤ 1`. So (a) the threshold never reaches the page — `rule5/6/7`
take the `Decomp` as their `c` argument, not a constant, and there is no path in the schema
that mentions one (**G1**, `docs/DECOMP_FORMAT_NOTES.md:9-21`); and (b) `reified_devent`
returns the placeholder `T` for a constraint carrying none (`explenation generator.ml:245-246`), so
the branch that would *conclude* something about `n` never fires (**G5**,
`docs/DECOMP_FORMAT_NOTES.md:52-59`, and `decomps/among.md`'s closing "Finding"). `nvalues`
(`explenation generator.ml:839-842`) shows the two-step `N`-channel shape that would fix this
without an engine change.

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i = t` and `X_i ≠ t`, from the `xac`
global event (arc consistency, `explenation generator.ml:869`). **Nothing was asked about `n`,
and nothing could have been:** there is no `N`-channel step, so the event vocabulary has no
literal to name the count with (G5 above).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **0** | `dropped F 0, cycle 0, duplicate 0, undefined index set 1` |
| `X_{i} \neq t` | 1 | **0** | `dropped F 0, cycle 0, duplicate 0, undefined index set 1` |

The file states its own refusal, twice, verbatim:

```
%%   ** REFUSED for X_{i}=t: 1 branch(es) reference undefined index set(s) D4; emitting them
%%      would state a rule over a set the artifact never defines (W1-T2) **
%%   ** NO RULE EMITTED for X_{i}=t: 1 candidate(s), all blocked **
```

**Why both events produce nothing.** Every candidate branch runs through step 2, whose index
set is `D 4`. `ind_set_defined` (`explenation generator.ml:459`) admits `D 1`, `D 2` and `D 3`
and nothing else, so `filter_branches` refuses the branch rather than printing a set the
document never defines. **This is the cost of W1-T2, and the roadmap booked it in advance:**
`docs/ROADMAP.md:48` records `among 2→0 rules` as intended. The two rules that used to ship
were quantified over `D_4`; `decomps/among.md` was written against a still earlier generator
and says `cata/among.tex` "contains four `\frac{...}` rules" — stale twice over.

**What would change it.** `D 4` here is the constraint's own parameter set `v`, a *named subset
of the value range* — not a set indexed by another index (that is `regular`'s `G7`) and not a
run-time object. The blocking gap is **G8**: `ind_set` names only whole predefined ranges, with
no subrange and no exclusion (`docs/DECOMP_FORMAT_NOTES.md:76`). G8 is normally cited for
`all_different_except*`; `among` is the same wall approached from the counting side, and W1-T2's
own comment (`explenation generator.ml:440-446`) says why the printer must not simply define
`D_4`: the counter is chosen *per decomposition*, so `D_4` is the row set in `table.tex` and the
value set here, and one printer definition would name two different sets alike. Naming the sets
properly is a property of the input format, so it is **W2-T1 / E2**, not a printer patch.

**Even with G8 closed, this entry would still not explain `n`.** That is G1 + G5, and it is a
separate repair in a separate place.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/among.tex`.

## Generated rules

**None.** `grep -o '\\frac' cata/among.tex | wc -l` → `0`. The file consists of the diagnostics
footer quoted above and nothing else.

For the avoidance of the reading this catalog exists to prevent: zero rules here does **not**
mean `among` has no explanations. It means this decomposition, asked about these two events,
produced two candidate branches and the generator refused both rather than quantify over an
undefined set.

## Status

**`nothing generated — blocked on G8`**

Two candidate branches exist and are refused, one per event; the refusal is recorded in the
artifact with the offending set named. Nothing about `among`'s explanations is established or
refuted here — `not validatable` would be the wrong label, because there are no rules to fail
to validate, and `flagged` would be wrong for the same reason. What *is* established is
negative and precise: the shipped decomposition cannot state a rule today, and it cannot state
a rule about its own count variable even after G8, because of G1 + G5.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:129` gives `none` in the literature column, so there is no published shape to
compare against and no `catalog/_literature/among.md` to read. This is the verdict the
vocabulary reserves for exactly this case, and it is not a stand-in for "not compared yet": the
index was built by a full session of web research (`CLAUDE.md`, "Context budget") and its `none`
is an assertion, not a blank.

Nothing else can be said, in either direction. With **0** generated rules there is no premise on
this side either, so even if a paper surfaced, the comparison would be between a published rule
and an empty set of rules — which is not a statement about implication strength.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one.** `ind_set` names only whole predefined ranges, so the parameter set `v` has no expression; it is written `D 4` and refused by W1-T2 |
| `G1` | no bare integer threshold reaches the printed rule, so `rule7`'s comparison constant is invisible |
| `G5` | the shipped step 3 uses the single-`Decomp_devent` shape, so no branch ever concludes anything about `n` — an authoring mistake in the decomposition, not a format gap (`nvalues` does it correctly) |
| `G3` | only if `among`'s general MiniZinc signature is wanted, where the channel elements may be variables rather than a parameter set. D-0003 and `decomps/among.md` both take the parameter reading, so this is not binding today |

Extensions: **E0** (`CHRISTMAS_LIST.md:129`, "already in `cata/among.tex`" — a claim written
before W1-T2 and now true only of the *decomposition*, not of the output). Closing G8 is part of
**E2** / W2-T1, per `explenation generator.ml:431-458`.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, output redirected then grepped, not skimmed) →
  `cata/among.tex  (0 rules, parses)` in the out-of-scope block, with the reason string quoted
  verbatim in the header table. Run totals: **34 rules checked in 11 entries: 13 SOUND and
  MINIMAL, 21 flagged; 2 rules in 5 entries out of scope.**
- `grep -o '\\frac' cata/among.tex | wc -l` → `0`.
- `python3 tools/mzn_coverage.py --rank --json` → `among`, tier `A no-literature +
  solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 129, section
  `2. Counting and cardinality`.
- `cata/among.tex` read, not run → the diagnostics footer, quoted above.
- `explenation generator.ml:851-853, 869, 889` read, not run → the decomposition, the global
  event, the emitting call. `:245-246`, `:459`, `:431-458`, `:839-842` read for the placeholder
  `reified_devent`, `ind_set_defined`, the W1-T2 rationale and `nvalues`' `N`-channel.
- `CHRISTMAS_LIST.md:129` and `:106-109` read → citation row and solver legend.
- `docs/DECOMP_FORMAT_NOTES.md:9-21, 52-59, 76` read → G1, G5, G8.
- `docs/ROADMAP.md:48` read → W1-T2 `DONE`, with `among 2→0 rules` recorded as the intended cost.
- The identification of **G8** (rather than G7) as the binding gap is **reasoning about the
  index set, not a measurement**: `D 4` here is a named subset of the value range, with no
  dependence on another index, which is G8's wording and not G7's.

**Discrepancies noted, not fixed (this session does not own those files).**

1. `decomps/among.md` states "`cata/among.tex` contains four `\frac{...}` rules and every one
   concludes `X_i=t` or `X_i \neq t`". Measured today: **0** rules. The *finding* it rests that
   sentence on (G5 — no branch concludes anything about `n`) is unaffected, because the
   branches that were refused were `X`-concluding branches.
2. `decomps/among.md` cites the decomposition at "generator lines 418-420" and the E-code at
   `CHRISTMAS_LIST.md:126`. Both are stale: the value is at **851-853** and line 126 is a
   table-separator row (`|---|---|---|---|`); the `among` row is **129**.
3. `docs/DECOMP_FORMAT_NOTES.md:52` (G5) likewise cites "generator lines 418-420" and
   "generator lines 406-409" for `nvalues`; the current values are **851-853** and **839-842**.
