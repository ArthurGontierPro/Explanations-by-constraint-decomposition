# `minimum`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `minimum`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecodes `['E2']` (shared row with `maximum`) |
| **Status** | `generated, unvalidated` *by this catalog's instrument* — `make validate` cannot see this file (**W1-T18**). Measured by a second instrument: all **4** rules **SOUND** over every assignment at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**, and all **4** **MINIMAL** over that range. See Validator. Was `encodable today, not encoded` until this session encoded it |
| **Generated** | **4** rules in `cata/minimum.tex` — **new 2026-09-22** (session A-1), the artifact X-max ran in scratch and could not commit |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `minimum` entry, in scope or out: `validator.ml`'s entry lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:196` records the literature column as `none found` |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `grep -o '\frac' cata/minimum.tex \| wc -l`, and this session's own exhaustive assignment sweep with per-premise droppability. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Constraint

`minimum(var int: m, array[int] of var int: x)`

`m = min_i(x_i)`: `m` is the smallest element of `x`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:94` carries the *name* only. The MiniZinc type
signature and argument order above are recall.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:196`'s literature column reads, verbatim,
`none found`.

**That phrasing is not the same as the bare `none` used on most rows**, and the difference
is recorded rather than smoothed over: `catalog/element.md` reads `none found` as "a
searched-and-empty finding", i.e. somebody looked. Either way the verdict below is the
same, because `catalog/README.md` and `catalog/TEMPLATE.md` give one verdict for an empty
literature cell.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. No web access was used and no search was made by this
session.

## Solver support

| | |
|---|---|
| Chuffed | native (`minimum.cpp`) |
| Geas | absent |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:196`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: **native** (`minimum.cpp`) **[C]**. Unlike its row-mate
[`maximum`](maximum.md), *this* name is the one the parenthetical actually supports.

## Decomposition used here

**Generator value:** `minim`, `explenation generator.ml:1086`.
**Emitted by:** `explainall [xbc;mbc] minim "cata/minimum.tex"`, line **1204**. The seed
`mbc` — the constraint's own bound variable as a one-index `BC` event — is line **1106**; it
was added for [`maximum`](maximum.md) and is not `maximum`-specific, which is the whole
reason this entry cost one line.
**Spec:** `decomps/maximum.md`, which covers this name and, since 2026-09-22, states the
decomposition rather than declaring it impossible.
**Shape:** [`maximum`](maximum.md)'s three-step channel with `rule3` (∧) in place of `rule4`
(∨):

| ctr | schema | meaning |
|---|---|---|
| 1 | `rule1` | `X_i ≥ t ⇔ B1_{i,t}` (BC) |
| 2 | `rule3` | `B2_t ⇔ ⋀_{i ∈ [[1,n]]} B1_{i,t}` |
| 3 | `rule1` | `O ≥ t ⇔ B2_t` (BC) |

**The dual is `m ≥ t ⇔ ⋀_i (x_i ≥ t)`, and this was checked rather than assumed** — the
natural-looking `m ≤ t ⇔ ⋀_i x_i ≤ t` is **false**, since `min_i x_i ≤ t` holds iff *some*
`x_i ≤ t`. The generator's positive `BC` atom is `≥`, not `≤`, so the conjunctive form is the
one that fits the language, and `rule3` is the constructor that expresses it. One line, one
word changed from `maxi`.

## Scope of this entry

**Events the generator was asked to explain:** four — `X_i ≥ t`, `X_i < t`, `O ≥ t`, `O < t`
— the same two seeds `maximum` uses, `xbc` and `mbc`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 1 | **1** | none |
| `X_{i}<t` | 1 | **1** | none |
| `O_{} \geq t` | 1 | **1** | none |
| `O_{}<t` | 1 | **1** | none |

No `F` discard, no branch cut by cycle detection, no duplicate, no undefined index set, no
empty premise, no index bound twice — the same clean sheet [`maximum`](maximum.md) has, read
off the `%% generator diagnostics (W1-T3)` footer of `cata/minimum.tex`.

### The claim this entry overturns

The previous version of this file said, quoting `decomps/maximum.md`:

> "No decomposition can be authored in the current encoding — this is not a derivation gap,
> it is a missing primitive."

**That is false**, for `minimum` exactly as for `maximum`, and for the same reason: it
reasoned from the direct decomposition (`∀i: m ≤ x_i`, `∃i: m = x_i`) and concluded about the
constraint. The generator's `BC` literals already are the order encoding, under which the
comparison between `m` and `x_i` **factors through a shared threshold** and every atom becomes
variable-against-value. The full argument is in [`maximum`](maximum.md), "The claim this entry
overturns, and why it was wrong"; it is not repeated here.

## Generated rules

`grep -o '\frac' cata/minimum.tex | wc -l` → **4**, measured 2026-09-22.

The exact duals of `maximum`'s, in file order:

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `O ≥ t`  ⊢  `X_i ≥ t` | **SOUND**, **MINIMAL** |
| 2 | `∀i'≠i ∈ [[1,n]]: X_{i'} ≥ t`, `O < t`  ⊢  `X_i < t` | **SOUND**, **MINIMAL** |
| 3 | `∀i ∈ [[1,n]]: X_i ≥ t`  ⊢  `O ≥ t` | **SOUND**, **MINIMAL** |
| 4 | `∃i ∈ [[1,n]]: X_i < t`  ⊢  `O < t` | **SOUND**, **MINIMAL** |

Rule 2 is the useful one and is the mirror of `maximum`'s rule 1: the bound is strictly below
`t` and every *other* variable is at least `t`, so this variable must carry the bound. Rules 3
and 4 are the bound's own two directions; rule 1 is the cheap downward propagation.

### How the verdicts were obtained

**This session's own sweep, not `make validate`, and not X-max's numbers quoted.** Exhaustive
enumeration of every assignment satisfying `O = min_i X_i` with `X_i ∈ [1,m]`, for every
`n, m ∈ {1,2,3,4,5}` — **`n = 1` included**, which is where the shipped `alldifferent` rule
was found to fail (`catalog/README.md`, W1-T19).

**0 counterexamples on all four rules, at every size swept.** Firing counts at `n,m ≤ 4`:
**2438 / 349 / 686 / 1098**; at `n,m ≤ 5`: **37329 / 4158 / 7995 / 18204**; at `n = 1` alone:
**35 / 20 / 35 / 20** firings, **0** failures.

A firing is one *(assignment, free index)* pair, and an index the rule itself quantifies is
**not** free: rules 3 and 4 range over `t` only, rules 1 and 2 over `(i,t)`. Stating this
matters — counting rules 3 and 4 over `(i,t)` as well inflates them to 37329 / 86388 and is
the first number this session computed before fixing the instrument. With the convention
fixed, the `n,m ≤ 5` counts reproduce session X-max's scratch figures **exactly**, which is
the cross-check that the two instruments agree.

**Minimality** was measured by dropping each premise in turn and re-running: every drop
produces a counterexample, so no premise is droppable and all four rules are minimal over the
range swept. Drop counts at `n,m ≤ 5`: rule 1 **48438** failures, rule 2 **37950** and
**37329**, rule 3 **86388**, rule 4 **7995**. The `i ∈ [[1,n]]` conjunct is the range
declaration of the conclusion's own free index, not a premise literal, and is not counted —
the reading `catalog/maximum.md` and `catalog/at_most.md` both state.

**One qualification `maximum` does not need.** Restricted to `n = 1` **alone**, rule 2's first
premise `∀i'≠i: X_{i'} ≥ t` is vacuously true and therefore droppable, so rule 2's minimality
is a statement about the range swept and not about `n = 1` in isolation. Soundness at `n = 1`
is unaffected — the other premise `O < t` carries the content, exactly as `maximum`'s rule 1
is saved at `n = 1` by its `O ≥ t`. This is said out loud because the catalog has been burned
by an `n = 1` hole once already.

## Status

**`generated, unvalidated`** — by this catalog's instrument, exactly as
[`maximum`](maximum.md) is, and for the same reason: `make validate` cannot see the file.

Three things this status does and does not say:

1. **It is not `validated: sound and minimal at n,m ∈ {2,3,4}`.** That legend entry means
   every rule got `SOUND and MINIMAL` from `make validate`, and no rule here went through
   `make validate` at all. Borrowing the string would misattribute the measurement.
2. **It is not the legend's plain "nobody has looked" either.** Somebody looked, over a wider
   range than the validator's (`{1,2,3,4,5}` rather than `{2,3,4}`), with per-premise
   droppability. The catalog has no status for that; inventing a seventh is not the fix,
   making `make validate` see new entries (**W1-T18**) is.
3. **It is no longer `encodable today, not encoded`**, which is what this file said between
   2026-09-22 morning and this session, nor `nothing generated — blocked on G3`, which is what
   it said before that. The first retraction was X-max's, the second is this session's, and
   they are different kinds: G3 was a claim about the *language*, `not encoded` a claim about
   the *repository*. Only the second was ever fixable by typing.

**`encodable today, not encoded` was a true status that stayed true for a few hours.** That is
the pattern worth recording: it names work nobody has done, so it is the one status in the
legend that a session can close by doing it rather than by discovering something.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:196`'s literature column reads `none found`. Per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing`: no paper is cited.
Not `out of reach`: that verdict needs a published premise to be out of reach of.

**Worth recording beside it:** `minimum` has a native explaining propagator in Chuffed —
here the citation is direct, `minimum.cpp` — and a `[C]` in Choco LCG. So explaining
implementations exist without a paper describing them. Calibrating against an implementation
is not possible from this repo: no solver source is vendored, and `CLAUDE.md` forbids
web-searching ahead of the index.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **nothing. Refuted for this constraint** by the shipped artifact, on the same evidence as [`maximum`](maximum.md). `m ≤ x_i` factors through a shared threshold; the order encoding performs the factoring; no variable-vs-variable atom survives |
| `G2` | the **legibility cost**, inherited and now actually paid: `m` **does** print as `O` (`var_name`, `explenation generator.ml:3`, has no constructor for a constraint's own scalar bound) and **does** print as `O_{} ≥ t` with empty subscript braces. Both LaTeX no-ops, neither a blocker |
| — | **not a gap: `make validate` cannot see this entry.** That is **W1-T18**, a tool limitation |

Extensions: `CHRISTMAS_LIST.md:196` routes this constraint through **E2** ("var-var atoms").
On this evidence **`minimum` needs no extension** — it is E0, and the E2 routing is a
consequence of the retracted claim. `CHRISTMAS_LIST.md` is not this session's file to edit;
the discrepancy is reported.

## How this entry was produced

- `explenation generator.ml` edited (this session owns it): decomposition value `minim` added
  at line **1086**, `caveat` block and `explainall` call at **1204**. Run under OCaml 5.1.1 in
  the `baguette` switch; exit 0, empty stderr; `cata/minimum.tex` produced and committed.
- An exhaustive assignment sweep over `O = min_i X_i` for every `n,m ∈ {1,2,3,4,5}`,
  including `n = 1`, with per-premise droppability, **written and run by this session**;
  counts quoted from the run, not from X-max's report. They agree with X-max's at `n,m ≤ 5`.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, **20**
  `ok` lines and no `FAIL`. All **18** pre-existing non-orphaned `cata/*.tex` reproduce
  byte-for-byte, as does `exp.tex`; `minimum.tex` is the 19th and is new, reported at 4
  frac-occurrences; the orphan set is unchanged (`sum.tex`, still skipped). **The warning
  census did not move**: 0 / 6 / 36 / 61, identical to the pre-change run — `minim` introduces
  no new constructor site.
- `make validate` (run 2026-09-22, redirected then grepped) → **34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged; 4 rules in 5 entries out of scope.** Identical to
  the run before this change, and `grep -ci minimum` over it → **0**: the validator never names
  this entry. That is the direct measurement of W1-T18.
- `CHRISTMAS_LIST.md:196`, `:106-109` read → the literature cell, the solver cell and its
  `minimum.cpp` parenthetical, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:94` read → the name.
- `explenation generator.ml` read → `var_name` at line **3**, `maxi` at **1059**, `minim` at
  **1086**, `mbc` at **1106**. Line numbers verified by `grep -n` after this session's final
  edit, per W1-T14. **`mbc` moved from 1079 to 1106** when `minim` and its comment were
  inserted above it; the previous version of this file quoted 1079 and was right when written.
- **The Tier row was not re-measured**; it is carried from the 2026-09-21
  `python3 tools/mzn_coverage.py --rank --json` run recorded in the previous version of this
  file.

**Discrepancies noted.**

1. **This file's own previous claim, retracted above.** Stated rather than overwritten.
2. **`CHRISTMAS_LIST.md:196` routes `minimum` through E2.** On this evidence it is E0. Not
   edited; reported.
3. **`decomps/_shapes.md`'s "Not covered by any shape" table** still lists `minimum` among
   five G3-blocked constraints. Not edited; reported.
5. **The `Makefile`'s validator comment** says "2 rules in 5 entries" out of scope; measured
   today it is **4**, unchanged by this entry. Stale number, not this session's file.
4. **Inherited and kept from the previous version:** the stub's `Spec: none` field was wrong —
   this constraint is covered by `decomps/maximum.md`, whose title line names it.
   `tools/catalog_stub.py` matches filenames only.
