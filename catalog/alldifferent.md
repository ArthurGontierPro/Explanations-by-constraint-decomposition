# `alldifferent`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `alldifferent`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **D** — literature + native explaining propagator |
| **Status** | `validated: sound and minimal at n,m <= 4` |
| **Generated** | 1 rule in `cata/alldifferent.tex` |
| **Validator** | 1 `SOUND and MINIMAL`, 0 flagged |
| **Calibration** | pending C2 |
| **Last measured** | 2026-09-21, `make validate` and `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`all_different(array [$X] of var int: x)`

Every `x[i]` takes a different value.

**Provenance of the signature:** not vendored in this repo. `tools/data/minizinc-2.10.1-globals.txt:17`
carries the *name* only; the snapshot has no signatures. The signature above is the MiniZinc
standard-library one and is recorded here as recall, not as a citation.

## Published explanation

**Citation:** Downing, Feydy, Stuckey 2012, *Explaining alldifferent*, ACSC 2012 —
`CHRISTMAS_LIST.md:116`, PDF link at `CHRISTMAS_LIST.md:266`. The row summarises it as
comparing value-, bounds- and domain-consistent propagators and their explanations, and
finding no single one best.

**Rule shape:** <!-- C2: sourced rule shapes go in catalog/_literature/alldifferent.md -->
**pending C2** — see [`catalog/_literature/alldifferent.md`](_literature/alldifferent.md) once
it exists. Nothing about the paper's rule shapes is stated here, because nothing about them has
been read in this repo.

One thing *is* in-repo and quotable: `CHRISTMAS_LIST.md:116` says the Hall-set explanation
needs **E4** — "decompose via occurrence cardinalities `Σ_i [x_i=v] ≤ 1` and reason across
them" — and calls `alldifferent` "the single best test case for the whole project". That is
this repo's own assessment of the gap, not a claim about what the paper says.

## Solver support

| | |
|---|---|
| Chuffed | native (`alldiff.cpp`) |
| Geas | `[G]` present |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:116`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.
`CHRISTMAS_LIST.md:82` adds that domain-consistent `alldifferent` is not fully LCG-ready in
Choco either.

## Decomposition used here

**Generator value:** `alldiff`, `explenation generator.ml:808-809`
**Emitted by:** `explainall [xac] alldiff "cata/alldifferent.tex"`, line 880
**Spec:** `decomps/all_different.md` (Shape P1, pairwise-sum guard, `decomps/_shapes-perm.md`)

Two steps, and they are the whole decomposition:

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule5, [Decomp_devent (true, (B 1), id, oni)])
```

- **step 1, `rule1`** — reified equivalence `B1_{i,t} ⇔ X_i = t`, arc consistency.
- **step 2, `rule5`** — a Boolean sum with the **`≤` direction only**: `Σ_i B1_{i,t} ≤ 1`
  for each value `t`, i.e. no value is used twice.

The auxiliary `B1` washes out: only `X` literals reach the printed rule (D-0004 satisfied).

## Scope of this entry

**Events the generator was asked to explain:** `X_i = t` and `X_i ≠ t` (the `xac` global
event, arc consistency, `explenation generator.ml:869`).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **0** | `F 1`, cycle 0, duplicate 0, undefined index set 0 |
| `X_{i} ≠ t` | 1 | 1 | none |

`cata/alldifferent.tex` carries the generator's own note for the empty one:
`** NO RULE EMITTED for X_{i}=t: 1 candidate(s), all blocked **`.

**Why `X_i = t` produces nothing, and why that is not a defect.** The decomposition is
`rule1` + `rule5` alone — a Boolean sum in the `≤` direction. `X_i = t` is not derivable from
a `≤`: knowing that a value is used at most once never forces a variable *onto* a value.
Getting that direction requires counting across several cardinality constraints (Hall sets),
which is **E4** in D-0006's taxonomy — the research item, not a bug. An earlier `CLAUDE.md`
reported this entry as "one rule where it should have two" and was wrong; W1-S retired that
claim in `b93644a`. The measurement that settled it: instrumenting the old silent filter over
all 16 entries found every dropped branch to be an `F` — no `IM`, `FE` or `R` ever occurred,
so nothing was lost to the silence. (The *count* of those branches is reported inconsistently
in this repo — `CLAUDE.md:156`, `docs/ROADMAP.md:49` and `WORKLOG.md:337` say 22;
`explenation generator.ml:549` says 25. The all-`F` finding, which is the part this paragraph
relies on, is the same in both. Today's shipped catalog drops 21, measured 2026-09-21 by
summing the `dropped F` fields of every `cata/*.tex` diagnostics block — a different generator
and so not comparable to either.)

**One rule is the complete output of this decomposition for these two events. It is not the
complete set of explanations of `alldifferent`.**

## Generated rules

Rendered from `cata/alldifferent.tex` (single line, no trailing newline;
`grep -o '\\frac' cata/alldifferent.tex | wc -l` → 1).

### Rule 1 — `X_i ≠ t`

```
X_{i'} = t ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
------------------------------------------------------ ⊢
X_{i} ≠ t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** 1 reading (1 sound, 0 unsound) — `forall i'`. Store sweep agrees with
the singleton reduction.

**It is nearly useless, and that is the point of the entry.** The premise is
`∀i' ≠ i: X_{i'} = t` — *every* other variable takes value `t`. Under `alldifferent` that is
unsatisfiable as soon as `n ≥ 3`, so the rule fires only at `n = 2`. The strictly stronger
`∃i' ≠ i: X_{i'} = t` is also sound, and the validator cannot prefer it, because minimality
is premise-droppability, not strength (`docs/VALIDATOR.md`, "sound and minimal does not mean
good"). This is the clearest example in the repo of the floor/strength distinction.

## Status

**`validated: sound and minimal at n,m <= 4`**

The one generated rule is sound and minimal at the sizes `docs/VALIDATOR.md` enumerates
(`n, m ∈ {2,3,4}`, all nine pairs, with a store sweep at `n, m ≤ 3`). That is a floor: no
premise is droppable, and the rule is still weak enough to fire only at `n = 2`. The
soundness verdict also rests on a **hand-encoded** ground semantics (`all X_i distinct`,
transcribed from `explenation generator.ml:808-809` and cross-checked against gccat's
`Calldifferent` closure properties), not on one derived from the generator's `ind_op` data —
`docs/VALIDATOR.md` names that as the outstanding exposure for every verdict it issues.

## Calibration (W3-T5, D-0013)

**Verdict: pending C2.**

The comparison cannot be written until the published rule shape is sourced into
`catalog/_literature/alldifferent.md`. What can be said without it, from this repo alone:
`CHRISTMAS_LIST.md:116` prices the weak pairwise rule at **E0** (works today) and the Hall-set
explanation at **E4**, so the repo's own prior is that the generated rule will come out
*weaker* than the published one. That prior is written down here so that the eventual
calibration either confirms or contradicts something, rather than being read off the result.
Per D-0013, "generated rule is sound but strictly weaker" is a **result**, not a failure.

## Gaps

| gap | what it blocks here |
|---|---|
| — | nothing blocks the rule that ships; the decomposition is fully encodable today |
| `G8` | `all_different_except`/`_except_0`: `ind_set` names only whole predefined ranges — it cannot express "a named range minus one point" |
| `G10` | `symmetric_all_different`: no variable in index position, `X_{X_i}` |

Extensions: **E0** for the shipped rule, **E4** for the Hall-set explanation
(`CHRISTMAS_LIST.md:116`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering. `decomps/all_different.md`
argues both gaps but numbers them under its own pre-consolidation scheme (`G6`, `G8`); the
numbers above are the consolidated ones and supersede those labels.

## How this entry was produced

- `make validate` (run 2026-09-21, this session) → `---- cata/alldifferent.tex (1 rules) ----`,
  `rule 1/1 X_i != t <= X_i' = t`, `VERDICT : SOUND and MINIMAL`. Run totals: **34 rules
  checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of
  scope**, 19/19 encoding invariants holding, all 11 controls behaving.
- `python3 tools/mzn_coverage.py --rank --json` → `all_different` in
  `D literature + solver-native`, ecodes `E0`, `E4`.
- `grep -o '\\frac' cata/alldifferent.tex | wc -l` → 1.
- `cata/alldifferent.tex` read, not run → the rule text and the `%% generator diagnostics`
  footer quoted above.
- `explenation generator.ml:808-809, 869, 880` read, not run → the decomposition and the
  emitting call.
- `CHRISTMAS_LIST.md:116, 266` read → citation and solver columns.

**Discrepancy noted, not fixed (this session does not own those files).**
`decomps/all_different.md` states the shipped rule as `X_i ≠ t ← ∃i'≠i: X_i'=t` and cites
`alldiff` at "lines 678-679". Both are stale: the shipped premise is `∀i'` (measured above,
and `docs/VALIDATOR.md` turns on exactly that quantifier), and `alldiff` is now at lines
808-809.
