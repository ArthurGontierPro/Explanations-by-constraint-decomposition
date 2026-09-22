# `maximum`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `maximum`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecodes `['E2']` (shared row with `minimum`) |
| **Status** | `generated, unvalidated` *by this catalog's instrument* — `make validate` cannot see this file (**W1-T18**). Measured by a second instrument: all **4** rules **SOUND** and **MINIMAL** over every assignment at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**. See Validator |
| **Generated** | **4** rules in `cata/maximum.tex` — **new 2026-09-22**, the artifact that refuted `G3` for this family |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `maximum` entry, in scope or out: `validator.ml`'s entry lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:196` records the literature column as `none found` |
| **Last measured** | 2026-09-22, `make check`, `make validate`, `grep -o '\frac' cata/maximum.tex \| wc -l`, an exhaustive assignment sweep and a domain-store sweep written for this entry. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

**Where the soundness numbers in this entry come from, once, so no line below repeats it.**
`cata/maximum.tex` is **not** validated by `make validate`. Every soundness and minimality
figure here is session X-max's own exhaustive check, carried into the artifact's `%% CAVEAT`
footer by the generator's `caveat` mechanism and quoted from there. It is a measurement, by a
different instrument from the one the rest of this catalog uses, and it is **not** a validator
verdict. Nothing here is "validated" in `catalog/README.md`'s sense, and nothing here is
"correct".

## Constraint

`maximum(var int: m, array[int] of var int: x)`

`m = max_i(x_i)`: `m` is the largest element of `x`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:90` carries the *name* only. The MiniZinc type
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
| Chuffed | native — see the caveat below |
| Geas | absent |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:196`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: **native** (`minimum.cpp`) **[C]**.

**The named file is `minimum.cpp` and the row carries two constraint names.** So the
citation directly supports "`minimum` has a native explaining propagator in Chuffed"; that
`maximum` does too is an inference from the shared row, not from the parenthetical. It is a
very likely inference — a max propagator is a min propagator with the sign flipped — but
this entry marks it as an inference rather than letting the stub's flat `Chuffed | native`
stand for a citation.

## Decomposition used here

**Generator value:** `maxi`, `explenation generator.ml:1059`.
**Emitted by:** `explainall [xbc;mbc] maxi "cata/maximum.tex"`, line **1149**. The seed
`mbc` — `maximum`'s own bound variable as a one-index `BC` event — is line **1079**.
**Spec:** `decomps/maximum.md`, first section.
**Shape:** `gccn`'s three-step channel (`explenation generator.ml:909`) with `rule4` (∨)
where `gccn` has `rule6` (Boolean sum ≥).

| ctr | schema | meaning |
|---|---|---|
| 1 | `rule1` | `X_i ≥ t ⇔ B1_{i,t}` (BC) |
| 2 | `rule4` | `B2_t ⇔ ⋁_{i ∈ [[1,n]]} B1_{i,t}` |
| 3 | `rule1` | `O ≥ t ⇔ B2_t` (BC) |

Constraint 2 is `nvalues`' constraint 2 (`:921`) with a `BC` `B1` instead of an `AC` one;
constraint 3 is `gccn`'s constraint 3 with one value index instead of `(t,p)`. **Nothing was
added to the language to make this work** — no constructor, no rule schema, no printer case,
no index operator — which is the point of the entry.

## Scope of this entry

**Events the generator was asked to explain:** four — `X_i ≥ t`, `X_i < t`, `O ≥ t`, `O < t`.
Every one produced exactly one rule, from exactly one candidate branch. Read off the
`%% generator diagnostics (W1-T3)` footer of `cata/maximum.tex`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 1 | **1** | none |
| `X_{i}<t` | 1 | **1** | none |
| `O_{} \geq t` | 1 | **1** | none |
| `O_{}<t` | 1 | **1** | none |

No `F` discard, no branch cut by cycle detection, no duplicate, no undefined index set, no
empty premise, no index bound twice. This is the only entry in the catalog with a clean
sheet on every diagnostic.

### The claim this entry overturns, and why it was wrong

Both `decomps/maximum.md` and the previous version of *this file* stated:

> "Both conjuncts compare two decision variables (`m` and `x_i`), never a variable against a
> domain-derived value. … **No decomposition can be authored in the current encoding — this is
> not a derivation gap, it is a missing primitive.**"

**That is false.** The reading of the type definitions behind it was accurate; the inference
from it was not. It established that *one* decomposition of `maximum` —

```
∀i: m ≥ x_i        and        ∃i: m = x_i
```

— cannot be typed, and concluded that *the constraint* cannot be decomposed. The generator's
`BC` literals **are already the order encoding**, and under the order encoding

```
m ≥ t   ⇔   ⋁_i (x_i ≥ t)
```

contains no variable-versus-variable atom at all: every side is a variable against a
threshold, which is precisely what `Global_event (_,_,_,BC)` means. The comparison between
`m` and `x_i` is not removed, it is **factored through a shared threshold `t`** — and `t` is a
constraint-level parameter, which the format already carries and the printer already prints.

The claim's shape is worth recording separately from its content: *a negative result about
one encoding of a constraint was reported as a negative result about the constraint.*

## Generated rules

`grep -o '\frac' cata/maximum.tex | wc -l` → **4**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `∀i'≠i ∈ [[1,n]]: X_{i'} < t`, `O ≥ t`  ⊢  `X_i ≥ t` | **SOUND**, **MINIMAL** |
| 2 | `O < t`  ⊢  `X_i < t` | **SOUND**, **MINIMAL** |
| 3 | `∃i ∈ [[1,n]]: X_i ≥ t`  ⊢  `O ≥ t` | **SOUND**, **MINIMAL** |
| 4 | `∀i ∈ [[1,n]]: X_i < t`  ⊢  `O < t` | **SOUND**, **MINIMAL** |

Rule 1 is the useful one, and it is the textbook `maximum` explanation: the bound is at least
`t` and every *other* variable is strictly below `t`, so this variable must carry the bound.
Rules 3 and 4 are the bound's own two directions. Rule 2 is the cheap downward propagation.

**Unlike `alldifferent`, this entry's minimality is not a floor with nothing above it.** Rule 1
fires at every `n`, not only at `n = 2`: its premise needs the other `n−1` variables below `t`,
which is an ordinary state during search rather than a fully pinned assignment.

### How the verdicts were obtained

Two independent sweeps, both written for this entry, neither of them `make validate`:

1. **Assignment enumeration.** Every assignment satisfying `O = max_i X_i` with `X_i ∈ [1,m]`,
   for every `n, m ∈ {1,2,3,4,5}` — **`n = 1` included**. `docs/VALIDATOR.md`'s singleton
   reduction makes this equivalent to the store semantics for anti-monotone premises, which
   all of these are. Result: **0 counterexamples** for all four rules. Firing counts at
   `n,m ≤ 4`: **359 / 652 / 1592 / 192**; at `n,m ≤ 5`: **4173 / 10488 / 23903 / 2296**; at
   `n = 1` alone: **20 / 10 / 20 / 10** firings, **0** failures.
2. **Domain-store sweep.** Every store assigning each `X_i` and `O` a non-empty subset of
   `[1,m]`, for every `n, m ∈ {1,2,3}`, premises read as store facts per
   `docs/VALIDATOR.md`'s table. **277 / 1908 / 4379 / 196 firing stores, 0 counterexamples.**
   The two instruments agree, as `docs/VALIDATOR.md` requires of its own pair.

**Minimality** was measured by dropping each premise in turn and re-running sweep 1: every
drop produces a counterexample, so no premise is droppable and all four rules are minimal.
The `i ∈ [[1,n]]` conjunct is the range declaration of the conclusion's own free index, not a
premise literal, and is not counted — the same reading `catalog/at_most.md` states for its own
`i ∈ S`, where it *is* droppable and is flagged.

**`n = 1` is stated explicitly because it is where this catalog has been burned.**
`catalog/README.md` records that G-1's sweep found 30 counterexamples at `n = 1` for the very
`alldifferent` rule `make validate` certifies. Here `n = 1` is safe, and for a reason: rule 1's
universal premise is vacuous at `n = 1`, but its *other* premise `O ≥ t` still carries the
content, so the rule does not conclude from nothing.

## Status

**`generated, unvalidated`** — by this catalog's instrument. Three things this status does
and does not say:

1. **It is not `validated: sound and minimal at n,m ∈ {2,3,4}`.** That legend entry means
   "every generated rule in the entry got `SOUND and MINIMAL` from `make validate`", and no
   rule here went through `make validate` at all. Borrowing the string would misattribute the
   measurement.
2. **It is not the legend's plain "nobody has looked" either**, and the Status cell says so.
   Somebody looked, with a sharper range than the validator's (`{1,2,3,4,5}` rather than
   `{2,3,4}`) and a second instrument agreeing. The catalog has no status for that, which is
   itself the W1-T18 problem: the honest fix is to make `make validate` see new entries, not
   to invent a seventh status.
3. **It is emphatically not `nothing generated — blocked on G3`**, which is what this file
   said before 2026-09-22.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:196`'s literature column reads `none found`. Per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists` — the searched-and-empty phrasing is stronger
evidence for it than a bare `none`, not weaker. Not `pending sourcing`: no paper is cited.
Not `out of reach`: that verdict needs a published premise to be out of reach of.

**Worth recording beside it, because it changes what "no literature" means here:**
`maximum` has a native explaining propagator in Chuffed and a `[C]` in Choco LCG. So, as
with `element` and [`inverse`](inverse.md), explaining implementations exist without a paper
describing them. Calibrating against an implementation is not possible from this repo: no
solver source is vendored, and `CLAUDE.md` forbids web-searching ahead of the index.

Informally — and this is an observation, not a calibration verdict — rule 1 is the
explanation a hand-written `maximum` propagator would give for raising a variable's lower
bound, so an eventual calibration against `minimum.cpp` has a plausible target.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **nothing. Refuted for this constraint**, by this entry. The wall stands only for comparisons that do not factor through a shared threshold — see the note below |
| `G2` | a **legibility cost, paid twice**: `m` is printed as `O` (`var_name`, line **3**, has no constructor for a constraint's own scalar bound, so `gcc`'s occurrence letter is borrowed), and it prints as `O_{} ≥ t` with empty subscript braces because `m` has no array position and `printglobal_eventtex` (line **584**) emits the subscript unconditionally. Empty braces are a LaTeX no-op, so the artifact is well-formed |
| — | **not a gap: `make validate` cannot see this entry.** That is **W1-T18**, a tool limitation, and it is why the Status row reads as it does |

**The sharpened statement of G3, which this entry exists to produce.** G3 as written —
"only variable-vs-domain-value comparisons exist, never variable-vs-variable" — describes the
*type definitions* correctly and the *blocked set* incorrectly. A var-var comparison blocks a
decomposition only when it **does not factor through a shared threshold**:

- `m ≥ x_i` **factors**. For each `t`, both `m ≥ t` and `x_i ≥ t` are expressible atoms, and
  the order encoding recovers the comparison from them. `maximum`, `minimum`, `arg_max`,
  `arg_min` and `span`'s min/max are all in this class.
- `x_i = y_{p_i}` **does not factor**. The obstruction is a variable-valued *index*, and no
  choice of `t` states both sides independently. `sort`, `arg_sort` and
  `symmetric_all_different` are in this class, and their gap is **G8**/**G7**, not G3.

`decomps/_shapes.md`'s "Not covered by any shape" table lists five constraints — `maximum`,
`minimum`, `arg_max`, `arg_min`, `span` — all attributed to G3 and all, on this evidence, in
the factoring class. That table is not this session's to edit; it is reported.

Extensions: `CHRISTMAS_LIST.md:196` routes this constraint through **E2** ("var-var atoms").
On this evidence **`maximum` needs no extension at all** — it is E0. The E2 routing for this
row is a consequence of the retracted claim and should be re-examined; `CHRISTMAS_LIST.md` is
not this session's to edit.

## How this entry was produced

- `explenation generator.ml` edited (this session owns it): decomposition value `maxi` added
  at line **1059**, seed `mbc` at **1079**, `explainall` call at **1149**. Line numbers
  verified by `grep -n` after the final edit, per W1-T14.
- `make check` (run 2026-09-22, redirected to a file then grepped) → **GATE PASSED**,
  exit 0, 19 `ok` lines and no `FAIL`. All **17** non-orphaned pre-existing `cata/*.tex`
  reproduce byte-for-byte, as does `exp.tex`; `maximum.tex` is the 18th and is new, reported
  at 4 frac-occurrences; the orphan set is unchanged (`sum.tex`, still skipped). The warning census moved by
  exactly one at `-w +40+41+42` (35 → 36) and at `-w +a` (60 → 61) — the new `O` constructor
  site, ambiguous between `ind_name` and `var_name` like every other one. The census
  *reports*, it does not fail, and the Makefile's expected-value line is now one behind; the
  Makefile is not this session's to edit.
- `make validate` (run 2026-09-22, redirected then grepped) → **34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged; 4 rules in 5 entries out of scope.** Run twice,
  once with `cata/maximum.tex` present and once with it moved aside: **byte-identical
  totals**, and `grep -c maximum` over the redirected run → **0**: the validator never names
  this entry at all. That is the direct measurement of W1-T18 — the validator does not scan `cata/`.
  (Note for whoever owns the docs: `CLAUDE.md` and the `Makefile` both say "2 rules in 5
  entries" out of scope; measured today it is **4**, with or without this entry. A stale
  number, not a regression, and not this session's file.)
- The two sweeps described under "Generated rules", written for this entry and run to
  completion; their counts are quoted from the run, not estimated.
- `cata/maximum.tex` read → the four rules and the diagnostics footer.
- `CHRISTMAS_LIST.md:196`, `:106-109` read → the literature cell, the solver cell and its
  `minimum.cpp` parenthetical, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:90` read → the name.
- **The Tier row was not re-measured**; it is carried from the 2026-09-21
  `python3 tools/mzn_coverage.py --rank --json` run recorded in the previous version of this
  file.

**Discrepancies noted.**

1. **This file's own previous claim, retracted above.** It is not silently overwritten: the
   "Scope of this entry" section states what it said, why it was wrong, and what kind of error
   it was.
2. **`CHRISTMAS_LIST.md:196` routes `maximum` through E2.** On this evidence it is E0. Not
   edited; reported.
3. **`decomps/_shapes.md`'s "Not covered by any shape" table** still lists `maximum`. Not
   edited; reported.
4. **The `Makefile`'s warning-census expectation line** is one behind after this change.
   Not edited; reported.
5. **Inherited and kept: `Chuffed | native`** is an inference from a shared row whose
   parenthetical names `minimum.cpp`, not a citation for this name.
