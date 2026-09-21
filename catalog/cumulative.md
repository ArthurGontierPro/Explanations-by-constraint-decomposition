# `cumulative`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `cumulative`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **D** — literature + native explaining propagator |
| **Status** | `not validatable` |
| **Generated** | 2 rules in `cata/cumulative.tex` |
| **Validator** | out of scope: `UNPARSED: index equation offset: t'=t-d_{i}`, and the capacity appears in no atom |
| **Calibration** | pending C2 — and see the warning below, the shipped entry is not `cumulative` |
| **Last measured** | 2026-09-21, `make validate` and `python3 tools/mzn_coverage.py --rank --json` |

## Read this before the rest of the entry

**`cata/cumulative.tex` is really `disjunctive`.** The decomposition's final step is a single
*unweighted* Boolean sum with an *implicit* bound of 1
(`rule5`, `explenation generator.ml:812`). That is a unary resource: at most one task runs at
any time point. There are no resource requirements `r_i`, and there is no capacity `b`
anywhere in the decomposition or in the printed rules. The file name is the only thing in the
artifact that says `cumulative`.

This is the most misleading thing in the current catalog, and it is why this entry leads with
it rather than footnoting it. `CHRISTMAS_LIST.md:167` says the same ("the repo's entry is the
**unary-resource special case** and names all *n* tasks"), as do `decomps/cumulative.md` and
`decomps/disjunctive.md`.

The two rules below are therefore evidence about `disjunctive` with constant durations, filed
under `cumulative`'s name. A `catalog/disjunctive.md` entry should cite this one rather than
re-render the same `.tex`.

## Constraint

`cumulative(array[int] of var int: s, array[int] of var int: d, array[int] of var int: r, var int: b)`

At every time point, the total resource used by the running tasks is at most `b`.

**Provenance of the signature:** `decomps/cumulative.md`, "Signature" line — in-repo.

What the decomposition encodes instead:

`disjunctive(array[int] of var int: s, array[int] of var int: d)` — tasks with starts `s_i`
and constant durations `d_i` do not overlap (`decomps/disjunctive.md`, "Signature").

## Published explanation

**Citation:** Schutt, Feydy, Stuckey, Wallace 2011, *Explaining the cumulative propagator*,
Constraints 16(3):250–282 — time-table filtering with window-based explanations. Also Schutt,
Feydy, Stuckey, CPAIOR 2013, *Explaining time-table-edge-finding propagation* (arXiv:1208.3015).
Both at `CHRISTMAS_LIST.md:167`.

**Rule shape:** <!-- C2: sourced rule shapes go in catalog/_literature/cumulative.md -->
**pending C2** — see [`catalog/_literature/cumulative.md`](_literature/cumulative.md) once it
exists. Nothing about either paper's rule shapes is stated here.

In-repo and quotable, from `CHRISTMAS_LIST.md:167`: "Schutt names a small window with a
capacity argument", and the route is **E2** (variable durations/resources) plus **E4** (the
capacity/counting argument). `CHRISTMAS_LIST.md:167` also calls `cumulative` "the other key
test case" alongside `alldifferent`.

## Solver support

| | |
|---|---|
| Chuffed | native (`cumulative.cpp`, `cumulativeCalendar.cpp`) |
| Geas | `[G]` present |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:167`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**Generator value:** `cumul`, `explenation generator.ml:810-812`
**Emitted by:** `explainall [xbc] cumul "cata/cumulative.tex"`, line 881
**Spec:** `decomps/cumulative.md` (which calls the intended shape `SCH-2`) and
`decomps/disjunctive.md` (which calls the *shipped* shape `SCH-1`, in `decomps/_shapes-ext.md`)

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule3, [Decomp_devent (true, (B 1), tplusci (C 1), tmoinci (C 1));
                   Decomp_devent (false, (B 1), id, id);
                   Reified_devent (true, (B 2), id, id)]);
Decomp (3, rule5, [Decomp_devent (true, (B 2), id, oni)])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i ≥ t`, **bounds** consistency. This is the one bounds
  decomposition among the three entries written so far.
- **step 2, `rule3`** (conjunction) — `B2_{i,t} ⇔ B1` at a duration-shifted time point
  `∧ ¬B1_{i,t}`, i.e. "task `i` is running at time `t`" (the reading `decomps/disjunctive.md`
  gives it). The duration enters through `tplusci (C 1)` / `tmoinci (C 1)`, an `OpShiftC`
  carrying `d_i` as an `ind_const` **symbol inside index arithmetic**. The exact sign of the
  shift is not restated here: it is the descending/ascending op pair, and which one defines
  the clause is precisely the thing an opaque index composition makes hard to read off
  (D-0006's first item).
- **step 3, `rule5`** — `Σ_i B2_{i,t} ≤ 1`. One unweighted family, implicit bound 1. **This
  is the line that makes the entry `disjunctive`.**

`B1` and `B2` wash out; only `X_i ≥ t` and `X_i < t` literals plus index equations are printed
(D-0004 satisfied).

## Scope of this entry

**Events the generator was asked to explain:** `X_i ≥ t` and `X_i < t` (the `xbc` global
event, bounds consistency, `explenation generator.ml:868`).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} ≥ t` | 3 | 1 | `F 2`, cycle 0, duplicate 0, undefined index set 0 |
| `X_{i}<t` | 3 | 1 | `F 2`, cycle 0, duplicate 0, undefined index set 0 |

Four of the six candidate branches were discarded as `F`. `explenation generator.ml:539-541`
defines that case: the constraint carrying the branch is not reified, so "this constraint is
false" is not a fact anything can explain — the branch is genuinely unsatisfiable and dropping
it is correct. W1-T3's `filter_branches` counts these instead of silencing them. No `IM`, `FE`
or `R` drop occurred here, so nothing was lost to the old silent filter.

**Two rules is the generator's output for these two events over this decomposition. It is not
the complete set of explanations of `disjunctive`, and it is not an explanation of
`cumulative` at all** — no rule below mentions a capacity or a resource requirement, because
the decomposition has neither.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/cumulative.tex`.

## Generated rules

Rendered from `cata/cumulative.tex` (`grep -o '\\frac' cata/cumulative.tex | wc -l` → 2).
`d_i` is an uninterpreted symbol: the artifact never says what kind of thing it is.

### Rule 1 — `X_i ≥ t`

```
X_{i}  ≥ t' ,  t' = t − d_{i}
X_{i'} < t  ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
X_{i'} ≥ t' ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t' = t − d_{i'}
--------------------------------------------------------------------------- ⊢
X_{i} ≥ t
```

**Verdict:** none — the entry is out of scope for the validator (see Status).

**The `.tex` binds `t'` twice**, once as `t − d_i` in premise 1 and once as `t − d_{i'}` in
premise 3. The rendering above is faithful to the artifact, including the collision. Whether
the two `t'` are meant to be the same symbol is not determined by the string; this is the same
class of defect as D-0009's repeated index binding.

Read charitably — one task `i` cannot start before `t`, every other task is both finished
before `t` and running through its own window — the shape is a time-table argument that names
**all `n` tasks**.

### Rule 2 — `X_i < t`

```
X_{i}  < t'  ,  t' = t + d_{i}
X_{i'} < t'  ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t' = t + d_{i}
X_{i'} ≥ t'' ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t'' = t' − d_{i'} ,  t' = t + d_{i}
------------------------------------------------------------------------------------------------ ⊢
X_{i} < t
```

**Verdict:** none — out of scope.

Here `t'` and `t''` are distinct, and the chain `t'' = t' − d_{i'}`, `t' = t + d_i` composes
two shifts. Again every other task is named.

## Status

**`not validatable`**

`make validate` (this session, 2026-09-21) reports the entry out of scope with a
machine-printed reason, not a skip:

```
cata/cumulative.tex  (2 rules, UNPARSED: index equation offset: t'=t-d_{i})
  reason: the durations d_i appear as uninterpreted symbols inside index equations
  (t'=t-d_i), AND the resource capacity appears in no atom, so the rule is schematic
  over a parameter the artifact never states
```

Two independent obstacles, and both must go before a verdict is possible:

1. **`d_i` is uninterpreted.** It is an `ind_const` symbol threaded through index arithmetic,
   standing in for arithmetic on variable *values*. The parser reports it rather than guessing
   — this is the one out-of-scope entry caught mechanically rather than by an undefined `D_k`.
2. **The capacity appears in no atom.** Nothing in the rule distinguishes this from any other
   bound, which is exactly why this entry and a `disjunctive` entry would be indistinguishable
   (gap G1).

A reading *could* have been invented for `d_i` and a capacity pulled out of the air, and both
rules would then have verdicts. Those verdicts would not be about the shipped artifact.
`docs/VALIDATOR.md` makes that refusal explicit and this entry inherits it.

The status is `not validatable`, **not** `generated, unvalidated`: the difference is that
somebody looked and the artifact is underspecified, which is itself the evidence for W1-T2.

## Calibration (W3-T5, D-0013)

**Verdict: pending C2 — and likely `incomparable` rather than `weaker`.**

The comparison is not written until `catalog/_literature/cumulative.md` exists. Two things
should be said when it is, and they are separable:

1. **Different constraint.** The published explanations are for `cumulative` with resource
   requirements and a capacity. The shipped rules are for `disjunctive`. Comparing them as
   though they explained the same constraint would be the error this entry exists to prevent.
   The honest comparison is against the unary special case of the same papers.
2. **Weaker even there, on the axis the papers are about.** Both shipped rules explain by
   `∀i' ≠ i, i' ∈ [1,n]` — *every* other task. `CHRISTMAS_LIST.md:167` and
   `decomps/disjunctive.md` both record that Schutt names a **small time window and a task
   subset**. `rule5` reasons within a single sum; the window argument reasons across time
   points, which is D-0006's **E4**. So the expected calibration is "sound in shape but names
   `n` tasks where the published rule names a subset" — a result, per D-0013, not a failure.

Neither point can be turned into a soundness claim today, because the entry has no verdict.

## Gaps

| gap | what it blocks here |
|---|---|
| `G15` | no arithmetic relating variable values to indices — **this is the measured** `UNPARSED: t'=t-d_i`. Named `X9` in `decomps/cumulative.md` |
| `G1` | a bare integer threshold cannot reach the printed rule, so the capacity `b` appears in no atom. Named `X4` in `decomps/cumulative.md` |
| `G11` | no weighted Boolean sum: `r_i · B2_{i,t}` has no encoding. This is **E8** (D-0011), *not* E3 — there is one sum per time point, so the `failwith "sommes multiples"` site is never reached |
| `G3` | only variable-vs-domain-value comparisons, never variable-vs-variable — needed for `fzn_disjunctive`'s general form with variable durations |
| — | and beyond all of those, the window/subset argument is **E4**, which D-0006 calls the research |

Extensions: **E2** + **E4** (`CHRISTMAS_LIST.md:167`); `decomps/cumulative.md` refines the
first into **E8** for weights specifically. G11's E8 relabelling is D-0011.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

`decomps/cumulative.md` puts it exactly right and it is worth repeating: gaps 1–3 make
`cumulative` *expressible*; **E4** makes it *good*.

## How this entry was produced

- `make validate` (run 2026-09-21, this session) → `cata/cumulative.tex` listed under
  `== out of scope: what could not be validated, and why ==` with the reason quoted verbatim
  above. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2
  rules in 5 entries out of scope**, 19/19 encoding invariants holding, all 11 controls
  behaving. The 2 out-of-scope *rules* are this entry's two.
- `python3 tools/mzn_coverage.py --rank --json` → `cumulative` in `D literature + solver-native`,
  ecodes `E2`, `E4`.
- `grep -o '\\frac' cata/cumulative.tex | wc -l` → 2.
- `cata/cumulative.tex` read, not run → both rules and the `%% generator diagnostics` footer.
- `explenation generator.ml:810-812, 868, 881` read, not run → the decomposition, the `xbc`
  global event and the emitting call. The `rule5` claim in "Read this before the rest of the
  entry" is read off line 812.
- `CHRISTMAS_LIST.md:167`, `decomps/cumulative.md`, `decomps/disjunctive.md` read → citations,
  solver columns, shape names, gap numbering.

**Discrepancy noted, not fixed (this session does not own those files).** Both
`decomps/cumulative.md` and `decomps/disjunctive.md` cite the `cumul` decomposition at
`explenation generator.ml` "l.680-682" / "l.682". It is now at lines 810-812. The claim they
make about it — `rule5`, one unweighted family, implicit bound 1 — is correct at the new lines;
only the numbers are stale. `CLAUDE.md` carries the same stale pair ("generator l.680-682").
