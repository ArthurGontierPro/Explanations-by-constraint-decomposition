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
| **Calibration** | **out of reach** — but, uniquely among the three entries, out of reach by *gaps* (G11, G15), not by structure |
| **Last measured** | 2026-09-21, `make validate` (re-run by C3, same out-of-scope reason) and `python3 tools/mzn_coverage.py --rank --json` |

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

**Rule shape:** the Constraints 2011 paper is sourced into
[`catalog/_literature/cumulative.md`](_literature/cumulative.md); the CPAIOR 2013
time-table-edge-finding paper is **not sourced** and nothing about it is stated here.
Summarised below with C2's provenance tags carried across unchanged.

| paper | rule | event | tag |
|---|---|---|---|
| §6.1 A1 naïve | `⋀_{i∈Ω} ⟦lb(s_i) ≤ s_i⟧ ∧ ⟦s_i ≤ ub(s_i)⟧ → false` | failure (overload) | `QUOTED` |
| §6.1 A2 big-step | `⋀_{i∈Ω} ⟦e − d_i ≤ s_i⟧ ∧ ⟦s_i ≤ s⟧ → false`, over the overload window `[s..e−1]` | failure | `QUOTED` |
| §6.1 A3 pointwise | A2 with `t` for `s` and `t+1` for `e` | failure | `DERIVED` (substitution stated in prose, checked against the paper's Example 8) |
| §6.2 B1-B3 | naïve / big-step / per-profile lower-bound pushes over a profile sequence | lower-bound increase | `QUOTED` |
| §6.2 B4 pointwise | `⟦t+1−d_j ≤ s_j⟧ ∧ ⋀_{k∈B} (⟦t+1−d_k ≤ s_k⟧ ∧ ⟦s_k ≤ t⟧) → ⟦t+1 ≤ s_j⟧` — **the one the paper uses** | lower-bound increase | `QUOTED`; two index-hygiene corrections in the display are C2's `COMPARISON` |
| §5.1 **TimeD decomposition** | `B_it ↔ ⟦s_i ≤ t⟧ ∧ ¬⟦s_i ≤ t − d_i⟧` and `Σ_i r_i · B_it ≤ c` | — (a decomposition, not a rule) | `QUOTED` |

Two things from the paper matter more than the formulas, and both are `QUOTED`:

- **Its "stronger" is implication between clause sets** (§3): `C1` is stronger than `C2` if
  `C1` implies `C2`, and Example 4 exhibits two incomparable explanations of one propagation.
  That is the axis calibration uses — and it is *not* the validator's minimality.
- **It proves nothing minimal and leaves two minimality questions open**: which time point to
  pick, and which subset `Ω′` of an over-large task set to use ("it is an open question which
  subset is the best"). Example 8's label "a minimal explanation" is on an instance, not a
  theorem.

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

**Verdict: out of reach** — and this is the one entry of the three where that verdict is about
**gaps this project has numbered**, not about structure. No implication comparison is stated,
for two independent reasons: the shipped rules explain `disjunctive`, not `cumulative`, and
they have **no verdict at all** (`not validatable`), so there is nothing established to compare.

**What makes it the interesting case: the paper's own decomposition is this generator's exact
shape.** Schutt et al. §5.1's TimeD is

```
B_it  ↔  ⟦s_i ≤ t⟧ ∧ ¬⟦s_i ≤ t − d_i⟧            (a rule1 reified equivalence over a rule3 ∧)
Σ_i r_i · B_it  ≤  c                              (a rule5 Boolean sum ≤)
```

and the shipped `cumul` chain (`explenation generator.ml:810-812`) is `rule1` → `rule3` →
`rule5` in exactly that order, over exactly that pair of auxiliaries: a reified bound literal,
a conjunction of a duration-shifted literal with the negation of an unshifted one, and a
Boolean sum `≤`. **The shipped decomposition is TimeD at `r_i = 1`, `c = 1`** — TimeD
specialised to a unary resource, with the bound implicit.

*This identification is C3's reading*, from C2's `QUOTED` display of TimeD set beside the
generator source. C2 states the structural match as `COMPARISON` ("structurally *exactly* the
shape this repo's generator consumes"); nothing here upgrades that tag. Two caveats on it: the
literal polarity differs (our `B1` is `X_i ≥ t`, TimeD's is `⟦s_i ≤ t⟧`, and the negated
conjunct swaps with it), and the *direction* of the duration shift cannot be read off the
source at all, because the index functions are opaque closures (D-0006's first item).

**And the paper states what that shape reaches**, `QUOTED`, §6.2: "The global cumulative using
time-table filtering and the TimeD decomposition have the same propagation strength." That
sentence is about TimeD in general; the paper does not separately state the unary case, and
this entry does not claim it does.

**So the verdict is a gap between the shape and the entry, and the gap is two items long.**
What separates the shipped artifact from TimeD is exactly:

- **G11** — the sum is unweighted. TimeD's is `Σ_i r_i · B_it`; there is no encoding for
  `r_i · B_it` (E8 under D-0011).
- **G15** — the threshold shift `t − d_i` is arithmetic on a variable's *value*, and the
  artifact carries `d_i` as an uninterpreted `ind_const` symbol. That is the same defect the
  validator reports mechanically as `UNPARSED: index equation offset: t'=t-d_{i}`, so it
  blocks the verdict and the calibration for one reason.

Close those two and the generator is on TimeD, whose propagation strength the paper equates to
the global time-table propagator's. **That is the strongest positive statement available
anywhere in this wave, and it is conditional**: nothing is measured, no rule here has a
verdict, and the claim is about a shape the generator cannot yet emit.

**Two routes, different blockers — do not merge them.** C1's prior (recorded here before C2's
sourcing) expected "weaker: names `n` tasks where Schutt names a subset". That is right about
the **global** §6.2 explanations, whose premises are quantified over a compulsory-part set `B`
and a chosen sequence of time points — run-time objects, out of reach for the same structural
reason as [`gcc.md`](gcc.md)'s cut, and needing **E4** on top. It does **not** transfer to the
TimeD route: TimeD quantifies over *all* times `t` and lets `B_it` be false where the task is
not compulsory, so no run-time subset is ever named (C2, `COMPARISON`). One paper, two targets:
the global rule is structurally out of reach, the decomposition is two gaps away.

**One correction to C1's prior.** It proposed comparing "against the unary special case of the
same papers". The sourced paper gives no unary special case of its explanations; the
comparable object is TimeD, and the unary specialisation is this repo's, not Schutt et al.'s.

## Gaps

| gap | what it blocks here |
|---|---|
| `G15` | no arithmetic relating variable values to indices — **this is the measured** `UNPARSED: t'=t-d_i`. Named `X9` in `decomps/cumulative.md` |
| `G1` | a bare integer threshold cannot reach the printed rule, so the capacity `b` appears in no atom. Named `X4` in `decomps/cumulative.md` |
| `G11` | no weighted Boolean sum: `r_i · B2_{i,t}` has no encoding. This is **E8** (D-0011), *not* E3 — there is one sum per time point, so the `failwith "sommes multiples"` site is never reached |
| `G3` | only variable-vs-domain-value comparisons, never variable-vs-variable — needed for `fzn_disjunctive`'s general form with variable durations |
| — | and beyond all of those, the **global** window/subset argument is **E4**, which D-0006 calls the research — but see Calibration: the paper's own **TimeD** decomposition needs only `G11` + `G15`, not `E4`, and the paper equates its propagation strength with the global propagator's |

Extensions: **E2** + **E4** (`CHRISTMAS_LIST.md:167`); `decomps/cumulative.md` refines the
first into **E8** for weights specifically. G11's E8 relabelling is D-0011.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

`decomps/cumulative.md` puts it exactly right and it is worth repeating: gaps 1–3 make
`cumulative` *expressible*; **E4** makes it *good*.

**Calibration qualifies that second half, and the qualification is the wave's one piece of
good news.** Schutt et al. state (`QUOTED`, §6.2, via `_literature/cumulative.md`) that their
**TimeD** decomposition and the global time-table propagator have *the same propagation
strength* — and TimeD needs `G11` and `G15`, not `E4`. So on the evidence sourced so far, E4
is what the **global** window explanation needs; it is not established that this method needs
E4 to be good at `cumulative`. `decomps/cumulative.md` is not this session's file and is not
edited; this is a discrepancy noted, not fixed.

## How this entry was produced

- `make validate` (re-run 2026-09-21 by session C3; same out-of-scope reason, same totals)
  → `cata/cumulative.tex` listed under
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
- `catalog/_literature/cumulative.md` read, not fetched → every statement about the paper in
  the "Published explanation" and "Calibration" sections, with C2's tags carried across. **No
  paper was fetched by this session** and no provenance tag was upgraded. The CPAIOR 2013
  time-table-edge-finding paper cited above was **not sourced** and stays that way.
- `explenation generator.ml:810-812` read, not run, **beside** C2's quoted TimeD display →
  the `rule1`/`rule3`/`rule5` correspondence in Calibration. That is a reading of two texts
  side by side, not a measurement, and it is labelled as such there.

**Discrepancy noted, not fixed (this session does not own those files).** Both
`decomps/cumulative.md` and `decomps/disjunctive.md` cite the `cumul` decomposition at
`explenation generator.ml` "l.680-682" / "l.682". It is now at lines 810-812. The claim they
make about it — `rule5`, one unweighted family, implicit bound 1 — is correct at the new lines;
only the numbers are stale. `CLAUDE.md` carries the same stale pair ("generator l.680-682").
