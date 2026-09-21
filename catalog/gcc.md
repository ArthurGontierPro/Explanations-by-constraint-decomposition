# `gcc` (`global_cardinality`)

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `global_cardinality`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the
> catalog claims".

| | |
|---|---|
| **Tier** | **C** — literature exists, solvers decompose it anyway |
| **Status** | `validated: sound and minimal at n,m <= 4` |
| **Generated** | 4 rules in `cata/gcc.tex` |
| **Validator** | 4 `SOUND and MINIMAL`, 0 flagged — **the only fully validated entry in the repo** |
| **Calibration** | **out of reach** — the published rule is a run-time flow cut / SCC; these 4 rules answer a different question |
| **Last measured** | 2026-09-21, `make validate` (re-run by C3, same verdicts) and `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`global_cardinality(array[$X] of var int: x, array[$Y] of int: cover, array[$Y] of var int: counts)`

`counts[j]` is the number of `x[i]` equal to `cover[j]`.

**Provenance of the signature:** not vendored in this repo —
`tools/data/minizinc-2.10.1-globals.txt:64` carries the name only. What *is* quotable is the
FlatZinc-level definition at `CHRISTMAS_LIST.md:127`:
`fzn_global_cardinality` is `forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)`.
The signature line above is recall; the decomposition line is a citation.

**What this catalog entry actually covers.** The generator's decomposition is the
**unrestricted** form over a value range `[1,m]` with one occurrence variable `O_t` per
value — i.e. `counts` as free variables, no `low`/`up` bounds, no `closed`. The MiniZinc
variants `_closed`, `_low_up`, `_low_up_closed` are **not** covered by this entry.

## Published explanation

**Citation:** Downing, Feydy, Stuckey 2012, *Explaining flow-based propagation*, CPAIOR,
LNCS 7298:146–162 — `CHRISTMAS_LIST.md:127`. The row describes it as a generic explaining
flow propagator that explicitly replaces a specialised **gcc** propagator.

**Rule shape:** sourced into [`catalog/_literature/gcc.md`](_literature/gcc.md). Summarised
here with C2's provenance tags carried across unchanged.

**There is no `gcc`-specific explanation rule in the paper.** `gcc` is encoded as a flow
network (Régin's encoding, with `f_{i,v} = bool2int([x_i = v])`) and what is explained is the
**generic** network-flow propagator. `QUOTED`, §3 Example 1.

| paper | rule | event | schema? | tag |
|---|---|---|---|---|
| §4.1 failure | `⋀ ⟦f_uv ≥ l_uv⟧` over arcs **leaving** the cut `C` `∧ ⋀ ⟦f_uv ≤ u_uv⟧` over arcs **entering** it `→ false`, `C` = the nodes searched for an augmenting path | failure | per-propagation (Ford-Fulkerson cut) | `QUOTED` |
| §4.2 pruning | the same, with an **SCC** of the residual graph as the cut-set | value removal / bound change (the same thing on Boolean arcs) | per-propagation (Tarjan) | `QUOTED` |

Worked instance, §4.2 Example 4 — `alldifferent(x1,x2,x3)` as a `gcc` network,
`[x3 ≠ 4] ∧ [c2 ≤ 1] ∧ [c3 ≤ 1] → [x1 ≠ 2]`, "or after removing redundant bounds
`[x3 ≠ 4] → [x1 ≠ 2]`". `QUOTED`.

**The paper does not claim its explanation minimal or strongest**, and says so in its own
words: it is "the base explanation", improvable "by using lifting methods". Example 4's
hand-stripping of "redundant bounds" is premise-droppability left as an optional post-pass.
`QUOTED`. So calibration below compares on **implication strength**, not minimality.

In-repo and quotable: `CHRISTMAS_LIST.md:127` prices `_low_up` at **E0**, full
`global_cardinality` at **E3** — sharpened to **E9** by D-0011, because the trailing
`sum(count)` is over *integer* variables — and the flow explanation itself at **E4**.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:127`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.
This is what makes it tier C rather than tier D: the literature exists, and Chuffed still
decomposes.

## Decomposition used here

**Generator value:** `gccn`, `explenation generator.ml:827-829`
**Emitted by:** `explainall [xac;ngbc] gccn "cata/gcc.tex"`, line 882
**Spec:** none — there is no `decomps/global_cardinality.md`. The nearest relative is
`decomps/count.md` (`count(x, v, c)`), which is `gcc` at a single value.

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule6, [Decomp_devent (true, (B 1), id, oni);
                   Reified_devent (true, (B 2), imap [foralli;p_out], imap [i_out;pointp])]);
Decomp (3, rule1, [Global_devent (true, O, id, id, BC); Reified_devent (true, (B 2), id, id)])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency.
- **step 2, `rule6`** — the `≥` direction of a Boolean sum, guarded:
  `B2_{t,p} ⇔ (Σ_i B1_{i,t} ≥ p)`.
- **step 3, `rule1`** — `B2_{t,p} ⇔ O_t ≥ p`, bounds consistency, channelling the occurrence
  variable `O_t` to the counting layer.

`B1` and `B2` both wash out; the printed rules mention only `X` and `O` literals (D-0004).

**A second value, `gcc`, exists at `explenation generator.ml:813-814`** — `rule1` + `rule7`
(a Boolean sum `=`) with no occurrence variable. **Nothing emits it.** `cata/gcc.tex` comes
from `gccn`. Anyone reading the source should not mistake the shorter definition for the
shipped one.

**And `gccn` is itself a repair.** The comment block at `explenation generator.ml:815-826`
records W1-T9 defect 3: `B2`'s ascending modification used to be `imap [i_out;forallp]`,
which prepended a universally bound `p`, printing `∀p ∈ [1,n]: O_t ≥ p`. That collapses to
`O_t ≥ n` and contradicts the companion premise, so rules 1–2 were `VACUOUS`. `p` is
quantified at the *constraint* level, so an explanation built from `B2` is a schema valid for
each `p` separately; `pointp` emits `p` with its range and no binder. That change is why this
entry is 4/4 rather than 2/4.

## Scope of this entry

**Events the generator was asked to explain:** four — `X_i = t`, `X_i ≠ t` (from `xac`,
arc consistency, `explenation generator.ml:869`) and `O_t ≥ p`, `O_t < p` (from `ngbc`,
bounds consistency, line 874).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | 1 | none |
| `X_{i} ≠ t` | 1 | 1 | none |
| `O_{t} ≥ p` | 1 | 1 | none — but flagged `DEFECT ... binds an index name twice (D-0009)` |
| `O_{t}<p` | 1 | 1 | none — same defect flag |

Nothing was dropped and no candidate was blocked: for these four events, over this
decomposition, four rules is the generator's complete output. **It is not the complete set of
explanations of `global_cardinality`** — in particular nothing here explains a *bound* on
`counts`, because the decomposition has no `low`/`up`, and nothing reasons across values,
which is the flow argument (E4).

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/gcc.tex`.

## Generated rules

Rendered from `cata/gcc.tex` (`grep -o '\\frac' cata/gcc.tex | wc -l` → 4).
`[1,n]` is the variable index set, `[1,m]` the value set; `p` ranges over `[1,n]`.

### Rule 1 — `X_i = t`

```
X_{i'} ≠ t ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
O_{t} ≥ p ,  p ∈ [1,n]
------------------------------------------------------ ⊢
X_{i} = t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** 1 (1 sound, 0 unsound) — `forall i' ; exists p`. Store sweep agrees.

At `p = 1` this reads: if every other variable avoids `t` and `t` must occur at least once,
then `X_i = t`. Note this is the direction `alldifferent` cannot produce — `gcc` gets it
because `rule6` gives it the `≥` side of the sum and an occurrence variable to hang it on.

### Rule 2 — `X_i ≠ t`

```
X_{i'} = t ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
O_{t} < p ,  p ∈ [1,n]
------------------------------------------------------ ⊢
X_{i} ≠ t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** 1 (1 sound, 0 unsound) — `forall i' ; exists p`. Store sweep agrees.

The counting analogue of `alldifferent`'s rule, and it inherits the same weakness: the first
premise names *every* other variable.

### Rule 3 — `O_t ≥ p`

```
X_{i} = t ,  ∀i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n]
----------------------------------------------- ⊢
O_{t} ≥ p
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** 1 (1 sound, 0 unsound) — `forall i`. Store sweep agrees.

**Two checks disagree in emphasis here, and both are reported.** The generator's own
diagnostics flag this rule:
`** DEFECT: 1 emitted rule(s) for O_{t} \geq p bind an index name twice; the LaTeX is
ambiguous (D-0009) **` — `∀i, i ∈ [1,n]` is printed twice, an artifact of composed index
modifications. The validator, which checks *every consistent reading* of an ambiguous prefix,
finds only one reading and it is sound. So the verdict stands, and the rendering defect stands
too: the `.tex` is redundant, not indeterminate, in this instance.

### Rule 4 — `O_t < p`

```
X_{i} ≠ t ,  ∀i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n]
----------------------------------------------- ⊢
O_{t} < p
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** 1 (1 sound, 0 unsound) — `forall i`. Store sweep agrees.
Same D-0009 double-binder flag as rule 3.

## Status

**`validated: sound and minimal at n,m <= 4`**

All four generated rules are sound and minimal at the enumerated sizes — `n, m ∈ {2,3,4}` for
the assignment enumeration, with the store sweep held at `n = m = 2` because the occurrence
variables multiply the store space (`docs/VALIDATOR.md`, "Sizes enumerated"). **This is the
only entry in the repo where every rule passes.**

Three caveats, all of which apply to that sentence:

1. **Floor, not strength.** Rules 1 and 2 quantify over all `n-1` other variables; a flow or
   Hall-type argument would name a subset. Minimality does not detect that.
2. **Hand-encoded semantics.** `O_t = #{i : X_i = t}` was transcribed from
   `explenation generator.ml:827-829` into `validator.ml`, not derived from it. It is
   cross-checked against gccat's `Cglobal_cardinality` ("`NOCCURRENCE` functionally determined
   by VARIABLES and VAL", holding) and against `alldifferent => every gcc count <= 1` (holding),
   but `docs/VALIDATOR.md` is explicit that no verdict from this tool is final until the ground
   semantics is derived from the `ind_op` data.
3. **One control overlaps this entry.** `docs/VALIDATOR.md` records it openly: the "O-atom
   sound+minimal" control says the same thing as rule 3. Its expected verdict was written from
   the semantics before the run, not copied from it — but the overlap means the controls are
   slightly less independent of this entry than of the others.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.** Not `weaker`, not `incomparable`: the two rules cannot be placed in
an implication order at all, because the published premise set is not expressible in this
method's vocabulary of index sets. "Out of reach" is a first-class verdict (D-0013), and this
entry is the clean instance of it.

**Why no implication comparison can even be stated.** Three obstacles, all from C2's reading
of §4.1-§4.2, and each independently fatal:

1. **No index-set expression for the premise's range.** The premises are indexed by "the arcs
   crossing the cut `C`", where `C` is the set of nodes searched for an augmenting path, or a
   strongly connected component of the *residual* graph. The printer quantifies over `[1,n]`,
   `[1,m]` and an undefined `D_k` beyond (`CLAUDE.md`, "Traps"); `C` is the output of a graph
   algorithm run at propagation time.
2. **Premise polarity depends on arc direction relative to the cut** (`≥ l` outflow, `≤ u`
   inflow), and direction is a property of the residual graph, which flips arcs as flows reach
   their bounds. A schema over indices has no such notion.
3. **The rule is an explanation of an explanation** — equation (2), cut-conservation, is
   synthesised per propagation and then explained as a linear constraint. This engine explains
   a fixed decomposition.

**It is not a vocabulary gap, and that distinction is worth keeping.** This entry *does* carry
occurrence-count atoms (`O_t ≥ p`, `O_t < p`), and the published worked instance's premises are
exactly of that kind — `[x3 ≠ 4] ∧ [c2 ≤ 1] ∧ [c3 ≤ 1]` mixes user-variable literals with
cardinality-bound literals. What is out of reach is the **quantification**, not the literals.
(This paragraph is C3's reading, built on C2's `QUOTED` Example 4; it is not a claim about the
paper.)

**The four rules answer a different question, and scoring them against the flow rule would
hide that.** They channel between `X` literals and bounds on one occurrence variable, within a
single sum, for one value `t` at a time. The published rule reasons *across* values, through
the flow network — which is why it prunes where these cannot. `4 SOUND and MINIMAL at n,m ≤ 4`
(my own run, below) is a complete answer to the first question and says nothing about the
second. It is also the floor, not strength: rules 1 and 2 still name every other variable.

**E4 is necessary but not sufficient**, sharpening `CHRISTMAS_LIST.md:127`, which prices the
flow explanation at E4. Counting across sums would give access to the cardinality literals; it
would not give a cut of a residual graph. C2 puts it as a negative result rather than a gap to
close, and this entry adopts that.

**Two priors recorded by C1, now settled.** C1 expected `weaker`, with "incomparable —
different constraint" as a second axis. Sourcing resolves both to `out of reach`: the
constraint mismatch is real (the paper's network carries cardinality *bounds*, this
decomposition has none) but it is not the binding reason — the binding reason is structural,
and it would still hold if the bounds were added.

## Gaps

| gap | what it blocks here |
|---|---|
| `G1` | a bare integer threshold cannot reach the printed rule — so `low`/`up` bounds have nowhere to go |
| `G4` | one Boolean-sum family per rule (hard failure otherwise): the `_low_up` form wants two |
| `G11` | no weighted Boolean sum |
| `G12`/`G13` | `length(xs) >= sum(count)` sums *integer* variables — a fourth kind of schema (E9, D-0011), not a generalisation of `rule5/6/7` |
| — | the published flow rule is blocked by no *gap* on this list: its premises are indexed by a run-time graph cut, so **E4 is necessary but not sufficient** (calibration, from C2) |

Extensions: **E0** for `_low_up`'s shape, **E3** + **E9** for the full form, **E4** for the flow
explanation (`CHRISTMAS_LIST.md:127`, with the E3→E9 correction at D-0011) — E4 with the
calibration caveat above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (re-run 2026-09-21 by session C3; verdicts identical to C1's run)
  → `---- cata/gcc.tex (4 rules) ----`, four
  `VERDICT : SOUND and MINIMAL` lines, each with `store sweep agrees with singleton reduction`.
  Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope**, 19/19 encoding invariants holding, all 11 controls behaving.
- `python3 tools/mzn_coverage.py --rank --json` → `global_cardinality` in
  `C literature + solver-decomposes`, ecodes `E0`, `E3`, `E4`, `E9`.
- `grep -o '\\frac' cata/gcc.tex | wc -l` → 4.
- `cata/gcc.tex` read, not run → the four rules and the `%% generator diagnostics` footer,
  including the two D-0009 defect lines quoted above.
- `explenation generator.ml:813-814, 815-826, 827-829, 869, 874, 882` read, not run → the
  unused `gcc` value, the W1-T9 repair comment, the shipped `gccn`, the global events and the
  emitting call.
- `CHRISTMAS_LIST.md:127` read → citation, solver columns, and the `fzn_global_cardinality`
  decomposition quoted verbatim.
- `catalog/_literature/gcc.md` read, not fetched → every statement about the paper in the
  "Published explanation" and "Calibration" sections, with C2's tags carried across. **No paper
  was fetched by this session** and no provenance tag was upgraded.
- The "out of reach" verdict is **reasoning about the two premise forms, not a measurement**:
  the published premise is indexed by a residual-graph cut and the printer has no such index
  set, so no implication either way is statable.

**Noted, not fixed:** there is no `decomps/global_cardinality.md`. This is the one entry of
the three with no `decomps/` spec, and the decomposition above was read straight off the
generator.
