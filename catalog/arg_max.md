# `arg_max`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `arg_max`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` per `tools/mzn_coverage.py --rank` (section `9. Ordering, sorting, channelling`), ecode `E2+E7`. **Checked against D-0014 (2026-09-21) and left here deliberately** — see "Is that classification right?" below |
| **Status** | **`generated, unvalidated`** *by this catalog's instrument* for the **int/bool** variant — `make validate` cannot see this file (**W1-T18**). Measured by a second instrument: all **7** rules **SOUND** and **MINIMAL** at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**, under **both** tie-breaking readings. **The `float` variant is untouched and stays E7.** Was `nothing generated — blocked on E2 / E7` until 2026-09-22; **the E2 half of that is retracted** |
| **Generated** | **7** rules in `cata/arg_max.tex` — **new 2026-09-22** (session A-1), from generator value `argmax`. The decomposition is **authored here**: there is no `decomps/arg_max.md` |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `arg_max` entry, in scope or out: `validator.ml`'s lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:197` cites none. (Was `out of reach`, which is the wrong verdict twice over: it needs a *published premise* to be out of reach of, and the "0 rules generated" reason it gave no longer holds) |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `make validate`, `grep -o '\frac' cata/arg_max.tex \| wc -l`, and this session's own exhaustive assignment sweep under two tie-breaking readings, with per-premise droppability. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Constraint

`arg_max` — no MiniZinc signature is vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt` lists `arg_max` as a global of MiniZinc 2.10.1
(name only). `CHRISTMAS_LIST.md:197` files it under section `9. Ordering, sorting, channelling`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:197`, literature cell, verbatim:

> none

No paper is sourced in `catalog/_literature/` for `arg_max`.

## Solver support

`CHRISTMAS_LIST.md:197`, solver cell, verbatim:

> native for bool (`bool_arg_max.cpp`)

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**Generator value:** `argmax`, `explenation generator.ml:1294`.
**Emitted by:** `explainall [xbc;mbc;i] argmax "cata/arg_max.tex"`, line **1631**. All three seeds already
existed: `xbc` (2020), `mbc` ([`maximum`](maximum.md)'s scalar bound, 2026-09-22) and `i`
([`element`](element.md)'s index variable, 2020).

**There is still no `decomps/arg_max.md`.** This decomposition was **authored in the generator**,
not transcribed from a spec, which makes this the only entry in the catalog whose decomposition
has no spec file behind it. That is recorded rather than smoothed over: the spec corpus and the
generator have diverged in this one place, and the spec is the side that is missing.

| ctr | schema | meaning |
|---|---|---|
| 1 | `rule1` | `X_i ≥ t ⇔ B1_{i,t}` (BC) |
| 2 | `rule4` | `B2_t ⇔ ⋁_{i} B1_{i,t}` |
| 3 | `rule1` | `O ≥ t ⇔ B2_t` (BC) |
| 4 | `rule1` | `I = i ⇔ B3_i` (AC) |
| 5 | `rule1` | `O ≥ t ⇔ B4_t` (BC) — **a second name for the same literal** |
| 6 | `rule1` | `X_i ≥ t ⇔ B5_{i,t}` (BC) — **likewise** |
| 7 | `rule4` | the clause: `I = i ∧ O ≥ t → X_i ≥ t` (with the signs the max direction needs) |

Constraints 1–3 are [`maximum`](maximum.md)'s channel verbatim. Constraint 7 is
[`element`](element.md)'s three-literal clause: the index variable says *which* `x` carries the
bound the channel already computes.

**Why B4 and B5 exist, rather than reusing B1 and B2.** Hanging the clause directly on `B1` and
`B2` would put those auxiliaries in **three** constraints each — and that is the configuration
that makes `find` loop forever, measured on
[`global_cardinality_closed`](global_cardinality_closed.md). With the duplicate reifications
every auxiliary appears in exactly two constraints, as in `elem`, and the traversal terminates.

### `pointt`/`pointi`, not `forallt`/`foralli` — and what that says about `element`

**This is the finding this entry exists for.** Constraint 7's two index operators are
`OpPoint`, not `OpForall`. Written with [`element`](element.md)'s own operators, the same
decomposition emits, in place of rules 6 and 7:

```
{∀i: X_i < t}, {∀i: I = i}   ⊢  O < t
{∀t: X_i < t}, {∀t: O ≥ t}   ⊢  I ≠ i
```

whose premises cannot be satisfied — `I` cannot equal *every* `i`, and no `X_i` is below
*every* `t`. **Measured, not predicted:** the first draft of this value used those operators,
both rules were emitted, and both fire **0** times.

The clause is quantified over `(i,t)` at the **constraint** level, so a rule built from it is a
schema valid for each pair separately: `i` and `t` are free parameters of the schema, not
things the premise quantifies. `OpPoint` emits exactly that (W1-T9 called it "ranged but
unbound"); `OpForall` does not.

**This is W1-T9 defect 3 for the third time** — `gcc`'s `pointp` repair was the first,
[`count`](count.md)'s `rule7` the second — **and it is shipped in `cata/element.tex` right
now.** That file's rules 3–6 carry precisely these binders, and `make validate` scores all four
**VACUOUS**: 4 of the 21 flagged rules in the whole catalog, from one operator choice. The same
one-word repair applies to `elem`. **It was not made**, because changing it would move a shipped
golden and this session's gate forbids that; it is reported instead.

### Tie-breaking, stated

MiniZinc's `arg_max` returns the **first** maximal index; this decomposition says only that `I` is
**a** maximal index. The decomposition is therefore a **relaxation** of the constraint, and a
rule sound for a relaxation is sound for the constraint. Both readings were swept anyway rather
than relying on that argument, and the rules are sound under both.

## Historical: the scope question this entry was filed under

**Why it was filed out of scope.** `tools/mzn_coverage.py --rank` puts `arg_max`
under `- out of scope`. `docs/ROADMAP.md:103-107` explains the ranking tool needed a
*section* filter (Packing/geometry, Graph/reachability, Sets, Maths-and-misc-floats) "because
geometry rows are coded E2/E8 rather than E5/E6/E7" (this task's own brief, corroborated by
the row below). `arg_max` is in section `9. Ordering, sorting, channelling`, so it is caught by that section filter.

**Is that classification right for `arg_max`?** **Partly.** `CHRISTMAS_LIST.md:197`'s route cell reads `E2; float variants E7`, and the row's solver cell notes a **native Boolean propagator already exists** (`bool_arg_max.cpp`) — which is the E2 case, not E7. That puts this constraint in the same position as `maximum`/`minimum` on the line just above it (`CHRISTMAS_LIST.md:196`, native `minimum.cpp`, route `E2`), which is **tier B** ("no-literature + solver-native"), not out of scope. `arg_max`/`arg_min` are polymorphic in MiniZinc — int and float array variants share a name — and only the **float** variant is genuinely E7 (out of scope, `docs/ROADMAP.md:106`); the **int/Boolean** variant, for which a native explaining propagator already exists per this row, is E2-reachable now, same as `maximum`/`minimum`. Filing the whole name under 'out of scope' conflates the two variants.

**What would bring it in scope.** For the int/Boolean variant: E2 (var-var atoms), same as `maximum`/`minimum` — arguably should sit in tier B alongside them rather than out of scope. For the float variant: E7, genuinely out of scope per `docs/ROADMAP.md:106`. Recommend splitting this row's tier judgement by variant rather than filing the name as one entry.

**Resolution (D-0014, 2026-09-21).** This finding was raised alongside the `diffn`/`bin_packing*`
misclassifications in the same review pass. The orchestrator checked all three and accepted
`diffn`/`bin_packing*` outright (`docs/DECISIONS.md` D-0014, tier A count 36→43); `arg_max`/
`arg_min` were decided differently and **left out of scope**, with the reason recorded rather
than silently dropped: `tools/mzn_coverage.py` classifies by constraint *name*, and MiniZinc's
`arg_max`/`arg_min` is one name covering two variants with two different mechanisms (E2 for
int/bool, E7 for float) — the tool cannot file half a name in one tier and half in another.
Splitting it would need the tool to know which call site is which, which is outside what the
vendored `tools/data/minizinc-2.10.1-globals.txt` (names only) can tell it. So this entry
stays `- out of scope` as a name-level approximation, with the int/bool-vs-float split stated
here rather than the index pretending the name is uniformly one thing or the other.

## Scope of this entry

**Events the generator was asked to explain:** **six** — `X_i ≥ t`, `X_i < t`, `O ≥ t`,
`O < t`, `I = i`, `I ≠ i`. Read off the `%% generator diagnostics (W1-T3)` footer of
`cata/arg_max.tex`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 2 | **2** | none |
| `X_{i}<t` | 2 | **1** | `F` 1 |
| `O_{} \geq t` | 2 | **1** | `F` 1 |
| `O_{}<t` | 2 | **2** | none |
| `I=i` | 1 | **0** | `F` 1 — `** NO RULE EMITTED **` |
| `I \neq i` | 1 | **1** | none |

**`I = i` gets no rule, and that is the constraint, not a failure.** Nothing in the
decomposition can conclude that the argmax *is* a given index — only that it is not. This is
exactly what [`element`](element.md)'s own `I = i` event does (2 candidates, 2 `F` discards,
no rule), and session X-max predicted it when it first looked at this family. The negative
direction, rule 7, is the useful one.

## Generated rules

`grep -o '\frac' cata/arg_max.tex | wc -l` → **7**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `∀i'≠i: X_{i'} < t`, `O ≥ t`  ⊢  `X_i ≥ t` | **SOUND**, **MINIMAL** |
| 2 | `O ≥ t`, `I = i`  ⊢  `X_i ≥ t` | **SOUND**, **MINIMAL** |
| 3 | `O < t`  ⊢  `X_i < t` | **SOUND**, **MINIMAL** |
| 4 | `∃i: X_i ≥ t`  ⊢  `O ≥ t` | **SOUND**, **MINIMAL** |
| 5 | `∀i: X_i < t`  ⊢  `O < t` | **SOUND**, **MINIMAL** |
| 6 | `X_i < t`, `I = i`  ⊢  `O < t` | **SOUND**, **MINIMAL** |
| 7 | `X_i < t`, `O ≥ t`  ⊢  `I ≠ i` | **SOUND**, **MINIMAL** |

Rule 7 is the one that does real work: a variable shown to be below a threshold the bound already reaches cannot be the argmax.

### How the verdicts were obtained

**This session's own sweep, not `make validate`.** Exhaustive enumeration of every
`X ∈ [1,m]^n` with `O = max_i X_i` and `I` an index achieving it, for every
`n, m ∈ {1,2,3,4,5}` — **`n = 1` included** — and **separately** under MiniZinc's first-index
tie-break. Both readings were swept rather than relying on the relaxation argument.

**0 counterexamples on all seven rules, under both readings, at every size swept.** Firings in
file order, any-maximal-index reading, at `n,m ≤ 4`: **359 / 2438 / 1225 / 2438 / 349 / 349 / 2262**; at `n,m ≤ 5`: **4173 / 37329 / 19226 / 37329 / 4158 / 4158 / 53196**. Under the
first-index reading at `n,m ≤ 5`: **4173 / 23903 / 10488 / 23903 / 2296 / 2296 / 37950**. **All seven minimal** over the range.

**At `n = 1`** firings are **35 / 35 / 20 / 35 / 20 / 20 / 0** and no rule fails. Rule 7 fires **0** times there *for a
reason*: with one variable, `X_1` **is** the bound, so its premise cannot hold. Rules 1, 2 and 6 have a
premise that goes droppable at `n = 1` alone, so their minimality is a claim about the range
swept — the same qualification [`minimum`](minimum.md) and [`member`](member.md) carry.

## Status

**`generated, unvalidated`** for the **int/bool** variant — by this catalog's instrument;
`make validate` cannot see the file (**W1-T18**), and the verdicts above come from a sweep
written for this entry. **The `float` variant is untouched and its E7 routing stands.**

**The E2 half of the old status is retracted.** `E2` is "var-var atoms", and this decomposition
has none: every atom is a variable against a threshold `t`, which is what `BC` events already
are. The constraint is **E0** on this evidence, exactly as `docs/G3-AUDIT.md` found for
`maximum`, `minimum` and `span`. `CHRISTMAS_LIST.md:197`'s `E2` cell is reported, not edited.

**What has *not* changed: the tier row.** D-0014 left this name `- out of scope` because
`tools/mzn_coverage.py` classifies by constraint *name* and cannot file half a name in one tier
and half in another. That reasoning is untouched by this entry — the int/bool variant now has
rules and the float variant still does not — and it is arguably *strengthened*, since the two
halves are now demonstrably in different states.

**Historical, kept.**

No decomposition has been attempted or encoded. Unlike the E5/E6/E7 entries in this batch,
this is **not** a scope decision recorded in `docs/ROADMAP.md`'s "Explicitly out of scope"
list (`docs/ROADMAP.md:103-107` names only sets/E5, graphs/E6, geometry-and-packing, and
floats/E7 — see the misclassification note above for why "geometry and packing" as a *section
label* overshoots the actual blocker here).

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:197` cites no paper for this family. **The previous verdict, `out of reach`,
was wrong twice over** and is retracted rather than updated: `catalog/README.md` reserves
`out of reach` for the case where a *published* premise is indexed by a run-time object, so it
needs a published rule to be out of reach *of*; and the reason it gave — "0 rules generated" —
is a fact about this side of the comparison, not the other, and no longer holds.

**Worth recording beside it:** `CHRISTMAS_LIST.md:197`'s solver cell names a native explaining
propagator, `bool_arg_max.cpp`. So, as with [`element`](element.md), [`maximum`](maximum.md)
and [`inverse`](inverse.md), an explaining implementation exists without a paper describing it.
Calibrating against it is not possible from this repo: no solver source is vendored.

## Gaps

| gap | what it blocks here |
|---|---|
| `E2` | **nothing, for the int/bool variant. Retracted.** No atom in the shipped decomposition compares two variables; every one is a variable against a threshold. On this evidence the int/bool variant is **E0** |
| `E7` | **the float variant, unchanged.** `docs/ROADMAP.md:106` puts floats out of scope and nothing here touches that |
| — (unnumbered) | **`OpForall` where `OpPoint` is meant makes a clause-derived rule vacuous.** Measured here on a first draft, and **shipped in `cata/element.tex`**, whose rules 3–6 are all `VACUOUS` for this reason — 4 of the catalog's 21 flagged rules. Avoided in this entry, **not fixed** in `elem`, because that would move a golden. It is a **rule-engine** matter, not a format gap |
| — (unnumbered) | **an auxiliary in three constraints can make `find` non-terminating.** Why this decomposition carries `B4` and `B5` as duplicate reifications; measured on [`global_cardinality_closed`](global_cardinality_closed.md) |
| `G2` | the usual borrowed letters: `O` for the bound (no `var_name` for a constraint's own scalar) and `I` for the index variable, which is `element`'s. `O` prints as `O_{} ≥ t` with empty subscript braces, inherited from [`maximum`](maximum.md) |

Extensions: **E0** for the int/bool variant on this evidence; **E7** for floats.
`CHRISTMAS_LIST.md:197` says `E2+E7`; the `E2` half is reported as superseded, not edited.
Source: `docs/ROADMAP.md:103-107`; `CHRISTMAS_LIST.md:227-244` ("What to actually ask for").

## How this entry was produced

### 2026-09-22 (session A-1) — what changed

- `explenation generator.ml` edited (this session owns it): decomposition value at the line in
  "Decomposition used here", `caveat` block and `explainall` call at the line given there, plus
  a source comment recording the `OpPoint`/`OpForall` measurement. **No seed was added** — all
  three already existed. Run under OCaml 5.1.1 in the `baguette` switch; exit 0, empty stderr.
- **A first draft using `element`'s `forallt`/`foralli` was written and run**, and its rules 6
  and 7 fire 0 times. That is the measurement behind the `OpPoint` finding; it is not an
  inference from the code.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, no `FAIL`;
  every pre-existing non-orphaned `cata/*.tex` byte-identical, orphan set unchanged. Warning
  census after the two `arg_*` values: 0 / 6 / 43 / 68, up two from the previous commit — new
  `I` and `O` constructor sites, ambiguous between `ind_name` and `var_name` as all such sites
  are. The census reports; it does not fail.
- `make validate` (run 2026-09-22, redirected then grepped) → unchanged totals, no line for this
  name (W1-T18). **It is also the source of the `element` figure quoted above:** that run scores
  `cata/element.tex` rules 3–6 `VACUOUS`, 4 of 6.
- An exhaustive assignment sweep under **two** tie-breaking readings, `n,m ∈ {1,2,3,4,5}`,
  `n = 1` included, with per-premise droppability. Written and run by this session.
- `grep -o '\frac' cata/arg_max.tex | wc -l` → **7**.
- Line numbers checked by `grep -n` after the final edit (W1-T14).

### 2026-09-21 — the original entry

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `arg_max` under tier `- out of scope`,
  ecode(s) `E2+E7`, section `9. Ordering, sorting, channelling`.
- `CHRISTMAS_LIST.md:197` read → literature, solver and route cells quoted above, verbatim.
- `CHRISTMAS_LIST.md:227-244` read → the "What to actually ask for" priority list, which is
  where the misclassification argument above comes from (comparing `arg_max`'s named extension
  against constraints the same list treats as near-term, in-scope work).
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement, which names
  categories, not E-codes, and does not name `E2+E7` as excluded on its own.
- `os.path.isfile("decomps/arg_max.md")` → False. `os.path.isfile("cata/arg_max.tex")` → False.
- `docs/DECISIONS.md` D-0014 read → the orchestrator's ruling that `arg_max`/`arg_min` stay
  out of scope at the name level, with the int/bool-vs-float split recorded in this entry
  rather than resolved by re-tiering.
- Nothing was compiled, run or validated. The variant-split argument is this session's own
  reading, checked and left standing by D-0014 — not asserted as a tier change.
