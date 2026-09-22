# `alldifferent`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `alldifferent`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **D** — literature + native explaining propagator |
| **Status** | `validated: sound and minimal at n,m ∈ {2,3,4}` |
| **Generated** | 1 rule in `cata/alldifferent.tex` |
| **Validator** | 1 `SOUND and MINIMAL`, 0 flagged |
| **Calibration** | **weaker than published** (Downing et al. §4); the §5 and §6 rules are **out of reach** |
| **Last measured** | 2026-09-21, `make validate` (re-run by C3, same verdicts) and `python3 tools/mzn_coverage.py --rank --json` |

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

**Rule shape:** sourced into
[`catalog/_literature/alldifferent.md`](_literature/alldifferent.md). Summarised here with C2's
provenance tags carried across unchanged; the paper is not restated at length.

The paper gives **four** explanation forms, and only two of them are schemas:

| paper | rule | event | schema? | tag |
|---|---|---|---|---|
| §4 value-consistent | `[x_h = v] → [x_i ≠ v]` — a **single** premise literal | value removal | **schema** | `QUOTED` |
| §5 bounds-consistent | `[x_i ≥ a] ∧ ⋀_{h∈H} ([x_h ≥ a] ∧ [x_h ≤ b]) → [x_i ≥ b+1]`, `H` a Hall set with `V = a..b` | lower-bound increase | per-propagation (union-find) | `QUOTED` |
| §6 domain-consistent | eq. (1), `⋀_{h∈H, d∈E\V} [x_h ≠ d] → [x_i ≠ j]`; also fixes equalities and failure | value removal / equality / failure | per-propagation (matching + SCC) | `QUOTED`; the failure form `DERIVED` |
| §7 Feydy decomposition | prefix-sum decomposition of `alldifferent`; worked instance `[x2 ≥ 2] ∧ [x3 ≥ 2] → [x1 ≤ 1]` | bound change | **schema**, needs E1 + E4 | `QUOTED` |

**The paper proves no explanation minimal**, and that is measured, not assumed: C2's
`grep -c -i 'minimal'` over the preprint returns **1** hit, "minimal change" to an algorithm
(`_literature/alldifferent.md`, "How this file was produced"). The calibration below therefore
compares on **implication strength**, not on the validator's minimality.

**Citation correction carried from C2.** The Hall-set explanations are in *this* paper (ACSC
2012), not in *Explaining flow-based propagation* (CPAIOR 2012); the CPAIOR paper touches
`alldifferent` only as an instance of a `gcc` flow network, and that is [`gcc.md`](gcc.md)'s
Example 4. `CHRISTMAS_LIST.md:116` was already right. `QUOTED` (both papers fetched).

Alongside the sourced shapes, this repo's own pricing: `CHRISTMAS_LIST.md:116` says the Hall-set explanation
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

**`validated: sound and minimal at n,m ∈ {2,3,4}`**

The one generated rule is sound and minimal at the sizes `docs/VALIDATOR.md` enumerates
(`n, m ∈ {2,3,4}`, all nine pairs, with a store sweep at `n, m ≤ 3`). That is a floor: no
premise is droppable, and the rule is still weak enough to fire only at `n = 2` — strictly
weaker than Downing, Feydy and Stuckey's §4 rule for every `n ≥ 3`, which the Calibration
section below establishes and which no verdict this validator can issue would have revealed. The
soundness verdict also rests on a **hand-encoded** ground semantics (`all X_i distinct`,
transcribed from `explenation generator.ml:808-809` and cross-checked against gccat's
`Calldifferent` closure properties), not on one derived from the generator's `ind_op` data —
`docs/VALIDATOR.md` names that as the outstanding exposure for every verdict it issues.

**`n = 1` is unchecked, and here that is load-bearing.** `docs/VALIDATOR.md:184` enumerates the literal set `n, m ∈ {2,3,4}`, so the certificate above is silent about a one-element array (W1-T19). G-1's independent exhaustive sweep, which does run `n = 1`, found **30 counterexamples at `n = 1` for this very rule** — at `n = 1` the universally quantified premise is vacuously true and the rule concludes from nothing. Quoted from `cata/alldifferent_except.tex`'s `%% CAVEAT (G-1, 2026-09-22)` footer, which states it of "the SHIPPED alldifferent rule"; it is **not** a `make validate` figure, and it does not contradict one. Two instruments, two ranges.

## Calibration (W3-T5, D-0013)

**Verdict: weaker than published.** Against §4 — the one published rule this method could
have matched. §5 and §6 are **out of reach**, and §7 is a near miss behind E1 + E4.

**The axis is implication strength** (the papers' own order; the minimality axis was retired
when C2 measured that no paper claims it — `docs/ROADMAP.md:99`).

| | premise | conclusion |
|---|---|---|
| published, §4 | `X_h = t` for **one** `h ≠ i` | `X_i ≠ t` |
| generated, rule 1 | `X_{i'} = t` for **every** `i' ≠ i` | `X_i ≠ t` |

Our premise implies theirs — a conjunction over all `i' ≠ i` entails the single literal at any
witness `h`. Theirs does not imply ours once there are two other variables. So the published
rule fires whenever ours does and, for `n ≥ 3`, in strictly more states: **ours is strictly
weaker**, and the comparison is settled at every arity, not sampled.

- **`n = 2`** — the two rules **coincide**. The conjunction has exactly one conjunct.
- **`n ≥ 3`** — strictly weaker, and in the sharpest way available: the premise asserts that
  `n−1 ≥ 2` variables all take `t`, which **contradicts `alldifferent` itself**. The rule is
  sound and can never fire. The published rule fires on the first variable fixed.

**The validator cannot see any of this, and that is the wave's headline.** Rule 1 is
`SOUND and MINIMAL` at `n,m ∈ {2,3,4}` (my own run, below) and is dead at every `n ≥ 3`. It escapes
even the `VACUOUS` flag, because that flag asks whether *any* store in the enumerated scope
satisfies the premises (`docs/VALIDATOR.md:227-228`) and `n = 2` is in scope. **Sound and
minimal is a floor, not strength** — `catalog/README.md` asserts that sentence, and this is the
measurement behind it, against Downing, Feydy and Stuckey §4.

**§5 and §6: out of reach, and E4 is necessary but not sufficient.** Both quantify their
premises over an object that exists only at propagation time — a Hall set `H` with endpoints
`a, b` found by a union-find sweep (§5), and the node sets of an SCC of the residual graph of a
bipartite matching (§6). C2 classifies both `per-propagation`. The printer quantifies over
declared index sets and has no expression for either. Counting across sums (E4) would supply
the *counting* argument; it would not supply a run-time set to quantify over. Same negative
result as [`gcc.md`](gcc.md) reaches for the flow rule.

**This sharpens the Scope section above.** That section says `X_i = t` is unreachable here and
that E4 is what it needs. True of a rule of *this method's kind*; but the published rule that
concludes an equality is §6, Example 6.4 (`[x1 ≠ 2] → [x1 = 1]`, `QUOTED`), and it comes from an
SCC, not from a sum. E4 is not the route to the published equality rule.

**§7 is the near miss**, and the only published `alldifferent` explanation that comes out of a
decomposition at all. It needs **E1** (integer auxiliaries `c[i]`, `s[i]`) **plus E4**
(`c[i] = Σ_j bool2int(x[j] = i)` reasons across two sums of the same Booleans) — C2's reading,
independently matched by `CHRISTMAS_LIST.md:116`. Its reach is stated in the paper: value
consistency plus Hall intervals aligned to the ends of `min(E)..max(E)` (`QUOTED`) — so even
reaching §7 would not reach §5.

Per D-0013, "sound but strictly weaker than Downing's" is a **result**, not a failure.

## Gaps

| gap | what it blocks here |
|---|---|
| — | nothing blocks the rule that ships; the decomposition is fully encodable today |
| `G8` | `all_different_except`/`_except_0`: `ind_set` names only whole predefined ranges — it cannot express "a named range minus one point" |
| `G10` | `symmetric_all_different`: no variable in index position, `X_{X_i}` |
| — | the published §5/§6 rules are blocked by no *gap*: they quantify over run-time objects, so **E4 is necessary but not sufficient** (calibration, from C2) |
| — | the published §7 rule needs **E1** (integer auxiliaries) **plus E4**, not E4 alone |

Extensions: **E0** for the shipped rule, **E4** for the Hall-set explanation
(`CHRISTMAS_LIST.md:116`) — with the calibration caveat above, which sharpens that pricing
rather than contradicting it.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering. `decomps/all_different.md`
argues both gaps but numbers them under its own pre-consolidation scheme (`G6`, `G8`); the
numbers above are the consolidated ones and supersede those labels.

## How this entry was produced

- `make validate` (re-run 2026-09-21 by session C3; verdicts identical to C1's run)
  → `---- cata/alldifferent.tex (1 rules) ----`,
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
- `catalog/_literature/alldifferent.md` read, not fetched → every statement about the paper in
  the "Published explanation" and "Calibration" sections, with C2's tags carried across. **No
  paper was fetched by this session**, and no provenance tag was upgraded.
- The `n = 2` / `n ≥ 3` split in Calibration is **reasoning about the two premises, not a
  measurement**: our premise is a conjunction over `i' ≠ i`, theirs is one conjunct of it.

**Discrepancy noted, not fixed (this session does not own those files).**
`decomps/all_different.md` states the shipped rule as `X_i ≠ t ← ∃i'≠i: X_i'=t` and cites
`alldiff` at "lines 678-679". Both are stale: the shipped premise is `∀i'` (measured above,
and `docs/VALIDATOR.md` turns on exactly that quantifier), and `alldiff` is now at lines
808-809.
