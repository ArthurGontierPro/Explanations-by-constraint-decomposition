# `disjunctive`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `disjunctive`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` |
| **Status** | `not validatable` |
| **Generated** | **2** rules — in `cata/cumulative.tex`, **not** in a file of this name. See the section below |
| **Validator** | out of scope. Machine-printed reason: "the durations d_i appear as uninterpreted symbols inside index equations (t'=t-d_i), AND the resource capacity appears in no atom, so the rule is schematic over a parameter the artifact never states" |
| **Calibration** | **out of reach** — by *gaps* (G15, G1), not by structure; and the gap list here is one item shorter than `cumulative`'s |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/cumulative.tex \| wc -l`, `python3 tools/mzn_coverage.py --rank --json` |

## Read this before the rest of the entry

**`cata/cumulative.tex` is this constraint's artifact.** The shipped decomposition named
`cumul` (`explenation generator.ml:810-812`) ends in a single **unweighted** Boolean sum with
an **implicit** bound of 1 (`rule5`, line 812). That is a unary resource: at most one task
runs at any time point. There are no resource requirements `r_i` and no capacity `b` anywhere
in the decomposition or in either printed rule. **The file name is the only thing in the
artifact that says `cumulative`.**

**Established by this session, not taken on trust.** `rule5`'s definition
(`explenation generator.ml:343-355`) takes *no capacity argument at all* — the comparison
bound appears nowhere in the schema's code, only in its comment `(*Bool sum<=c*)`. So the "1"
is not a parameter that happened to be set to 1; there is no parameter. Compare `alldiff`
(line 808-809), which uses the same `rule1` + `rule5` pair for its own implicit "at most 1".

So: **`disjunctive` is the one constraint in tier D's unreviewed set that is already
generated, under another entry's name.** `catalog/cumulative.md` says the same from the other
side and asks a `disjunctive` entry to cite it rather than re-render the artifact; this entry
renders the two rules only in compressed form and sends the reader there for the full
treatment, the per-premise reading and the `t'`-binding defect.

What this does **not** license: there is no `cata/disjunctive.tex`, the generator has no value
named `disjunctive`, and no run of this repo has ever emitted a file under this name. The
**Generated** row above says `cata/cumulative.tex` for that reason.

## Constraint

`disjunctive(array[int] of var int: s, array[int] of var int: d)`

Tasks with start times `s_i` and durations `d_i` do not overlap in time.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:55` carries the *name* only, and this checkout holds no
`.mzn` file at all (`find . -name '*.mzn'` → empty, 2026-09-21). The signature above is
transcribed from `decomps/disjunctive.md`, "Signature", which records it without a citation of
its own; treat it as recall. That spec also states the restriction the shipped decomposition
works under: **`d_i` is a constant.**

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:169`, literature cell, verbatim:

> implied by the cumulative papers (unary is the special case)

which points at `CHRISTMAS_LIST.md:167` — **Schutt, Feydy, Stuckey, Wallace 2011**, *Explaining
the cumulative propagator*, Constraints 16(3):250–282, and **Schutt, Feydy, Stuckey, CPAIOR
2013**, *Explaining time-table-edge-finding propagation* (arXiv:1208.3015).

**Rule shape:** the Constraints 2011 paper **is** sourced, in
[`catalog/_literature/cumulative.md`](_literature/cumulative.md). This entry uses only what is
in that file, with C2's provenance tags carried across unchanged, and states nothing about the
CPAIOR 2013 paper, which is **not sourced**. No paper was fetched by this session and no
provenance tag is upgraded here.

The two items from that file this entry depends on:

| item | content | tag |
|---|---|---|
| §5.1 **TimeD** decomposition | `∀t,∀i: B_it ↔ ⟦s[i] ≤ t⟧ ∧ ¬⟦s[i] ≤ t − d[i]⟧` and `∀t: Σ_i r[i]·B_it ≤ c` | `QUOTED` |
| §6.2 verdict on it | "The global cumulative using time-table filtering and the TimeD decomposition have the same propagation strength." | `QUOTED` |

**A caution the sourced file states in its own words, and this entry does not go round it:**
the paper gives *no unary special case of its explanations*. `CHRISTMAS_LIST.md:169`'s "unary
is the special case" is this repo's routing note, not the paper's claim. The unary
specialisation below is this repo's.

## Solver support

| | |
|---|---|
| Chuffed | native (`disjunctive.cpp`) |
| Geas | **`[G]`** present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:169`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.
Note the contrast with `cumulative` (`:167`), which additionally carries `[C]`: the unary case
is the one of the pair that Choco LCG's column does not mark.

## Decomposition used here

**Generator value:** `cumul`, `explenation generator.ml:810-812`
**Emitted by:** `explainall [xbc] cumul "cata/cumulative.tex"`, line 881
**Spec:** `decomps/disjunctive.md`; shape **SCH-1** in `decomps/_shapes-ext.md:238-271`, which
`decomps/_shapes.md:226-238` renumbers to **S9**

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule3, [Decomp_devent (true,  (B 1), tplusci (C 1), tmoinci (C 1));
                   Decomp_devent (false, (B 1), id, id);
                   Reified_devent (true, (B 2), id, id)]);
Decomp (3, rule5, [Decomp_devent (true, (B 2), id, oni)])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i ≥ t`, **bounds** consistency (`BC`). This is the only
  bounds decomposition among the sixteen shipped entries.
- **step 2, `rule3`** (conjunction, three-element list) — `B2_{i,t} ⇔ B1` at a duration-shifted
  time point `∧ ¬B1_{i,t}`: "task `i` is running at `t`". The duration enters as
  `tplusci (C 1)` / `tmoinci (C 1)`, i.e. `C 1` — an `ind_const` (type at line 7) whose printer
  is `printind_const` (line 466), which renders *any* `ind_const` as the letter `d`. The
  artifact therefore never says what kind of object `d_i` is.
- **step 3, `rule5`** — `Σ_i B2_{i,t} ≤ 1`, one unweighted family, no capacity argument.
  **This is the line that makes the entry `disjunctive` and not `cumulative`.**

`B1` and `B2` both wash out — the printed rules contain only `X_i ≥ t` / `X_i < t` literals and
index equations, so D-0004 is satisfied without argument. That is a property of *this* shape and
does not transfer: the lex family (S5) has an auxiliary with nothing to wash back into, and that
is why [`lex_less.md`](lex_less.md) generates nothing.

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i ≥ t` and `X_i < t`, from the `xbc`
global event (bounds consistency, `explenation generator.ml:868`). Nothing else. In particular
**no event about a capacity or a resource was asked, because the decomposition contains
neither**, so a reader must not read the two rules below as the method's answer on `cumulative`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 3 | 1 | `dropped F 2, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i}<t` | 3 | 1 | `dropped F 2, cycle 0, duplicate 0, undefined index set 0` |

Four of the six candidates were dropped as `F` — the constraint carrying the branch is not
reified, so "this constraint is false" is not a fact anything can explain
(`explenation generator.ml:539-541`, and `filter_branches` at line 622 counts them instead of
silencing them). No `R`, `IM` or `FE` drop occurred, so nothing was lost to the pre-W1-T3
silent filter, and no branch referenced an undefined index set.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/cumulative.tex`.

## Generated rules

Rendered from `cata/cumulative.tex` (`grep -o '\frac' cata/cumulative.tex | wc -l` → **2**).
**Both are rendered in full, premise by premise, in
[`catalog/cumulative.md`](cumulative.md#generated-rules)**; they are compressed here rather
than duplicated, because there is one artifact and two entries must not drift apart.

### Rule 1 — `X_i ≥ t`

```
X_{i}  ≥ t' ,  t' = t − d_{i}
X_{i'} < t  ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
X_{i'} ≥ t' ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t' = t − d_{i'}
--------------------------------------------------------------------------- ⊢
X_{i} ≥ t
```

**Verdict:** none — out of scope for the validator (see Status).
**Reading(s) checked:** none; the rule was never reached by a reading.
**The `.tex` binds `t'` twice** (as `t − d_i` in premise 1 and `t − d_{i'}` in premise 3);
the render is faithful to the artifact, collision included. That is D-0009's class of defect.

### Rule 2 — `X_i < t`

```
X_{i}  < t'  ,  t' = t + d_{i}
X_{i'} < t'  ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t' = t + d_{i}
X_{i'} ≥ t'' ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t'' = t' − d_{i'} ,  t' = t + d_{i}
------------------------------------------------------------------------------------------------ ⊢
X_{i} < t
```

**Verdict:** none — out of scope.
**Reading(s) checked:** none.

**Both rules name every other task** (`∀i', i' ≠ i, i' ∈ [1,n]`). That is a property worth
stating plainly because it is what the Calibration section is about, and it is *not* a
minimality claim in either direction — no verdict exists for either rule.

## Status

**`not validatable`**

`make validate`, run by this session on 2026-09-21 with output redirected and then grepped
(never skimmed from a pipe, per `CLAUDE.md`), lists the artifact under
`== out of scope: what could not be validated, and why ==`:

```
  cata/cumulative.tex  (2 rules, UNPARSED: index equation offset: t'=t-d_{i})
    undefined index sets referenced: (none)
    reason: the durations d_i appear as uninterpreted symbols inside index equations
    (t'=t-d_i), AND the resource capacity appears in no atom, so the rule is schematic
    over a parameter the artifact never states
```

Run totals, same run: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2
rules in 5 entries out of scope.** The 2 out-of-scope *rules* in that line are this entry's two.

`not validatable`, not `generated, unvalidated`: somebody looked, and the artifact is
underspecified. Two obstacles, independent of each other — `d_i` is an uninterpreted
`ind_const` symbol threaded through index arithmetic, and the bound of the sum appears in no
atom (G1). The second of those is **not** cosmetic here: it is precisely what makes a
`disjunctive` artifact and a `cumulative` artifact indistinguishable on the page.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach** — by gaps this project has numbered, not by structure, and **the
gap list is one item shorter than [`cumulative.md`](cumulative.md)'s**.

No implication comparison is stated, for one blocking reason: the two rules have **no verdict
at all**, so there is nothing established on this side to place in an order. That is the same
position `cumulative.md` reaches, and it is inherited rather than re-derived.

**Where this entry differs from `cumulative.md`, and it is the useful part.** That entry
identifies the shipped `cumul` chain with the paper's own **TimeD** decomposition specialised
to `r_i = 1`, `c = 1`, and lists two gaps between artifact and TimeD:

- **G11** — TimeD's sum is `Σ_i r_i · B_it` and `rule5` has no coefficients;
- **G15** — `t − d_i` is arithmetic the artifact carries as an uninterpreted symbol.

**For `disjunctive`, G11 falls away.** The unary resource *is* `r_i = 1`, so an unweighted sum
is not an approximation of the target — it is the target. What separates
`cata/cumulative.tex` from TimeD-at-`r=1,c=1` is **G15** (the shift) and **G1** (the bound `1`
never reaching the page). So on the sourced evidence, `disjunctive` is the constraint in this
corpus **closest to a published explanation shape**: the shipped decomposition is already the
right shape, and what is missing is the ability to *say* two constants.

Three limits on that sentence, all of them load-bearing:

1. **It is a reading of two texts side by side, not a measurement.** `catalog/_literature/`'s
   TimeD display (`QUOTED`) set beside `explenation generator.ml:810-812`. C2 tags the
   structural match `COMPARISON` and nothing here upgrades that tag.

   **One thing `catalog/cumulative.md` says at this point is no longer true, and this entry
   states the corrected version.** That entry adds that "the *direction* of the duration shift
   cannot be read off the source at all, because the index functions are opaque closures
   (D-0006's first item)". **W1-T7 replaced the closures with first-order data**
   (`explenation generator.ml:19-37`, the type `ind_op` at `:39-49`, `invert_op` at `:145`,
   `print_op` used by `print_devent` at `:173-183`). Measured by reading the aliases: step 2's
   descending op is `tplusci (C 1) = OpShiftC (FT, PLUS, C 1, FI)` (`:796`) and its ascending
   op is `tmoinci (C 1) = OpShiftC (FT, MINUS, C 1, FI)` (`:797`). **The direction is in the
   data and is readable**: the symbol is `PLUS`/`MINUS` in the constructor, and the printed
   rules agree — `t' = t + d_i` in rule 2, `t' = t − d_i` in rule 1.

   What remains true is the *substantive* half of the caution: our `B1` is `X_i ≥ t` where
   TimeD's is `⟦s_i ≤ t⟧`, so the polarity differs and the negated conjunct swaps with it.
   That is a difference in the decomposition, not an unreadable one.
2. **"Same propagation strength" is about TimeD in general**, at any `r` and `c`. The paper
   does not separately state the unary case, and this entry does not claim it does.
3. **The paper's *global* §6 explanations stay out of reach, structurally.** Their premises are
   quantified over a compulsory-part set `B`, a profile sequence and a chosen list of time
   points — objects built at propagation time by scanning the time-table profile
   (`catalog/_literature/cumulative.md`, "Schema or per-propagation?", `QUOTED`). That is the
   same kind of run-time object as `alldifferent`'s Hall set and `gcc`'s cut, and no
   implication either way is statable against it. Closing G1 and G15 does not change this;
   reaching the §6 rules needs **E4**.

**Not compared on minimality.** No verdict exists here, and `catalog/_literature/cumulative.md`
records (`QUOTED`, preprint p.13) that the paper proves nothing minimal and leaves two
minimality questions open. The axis, when it opens, is implication strength.

## Gaps

| gap | what it blocks here |
|---|---|
| `G15` | **the measured one.** No arithmetic relating variable values to indices — the validator's `UNPARSED: index equation offset: t'=t-d_{i}` is this gap, reported mechanically |
| `G1` | a bare integer threshold never reaches the printed rule, so the sum's bound `1` appears in no atom. Not cosmetic: it is why this artifact and a `cumulative` artifact are indistinguishable, and why the file's name is doing the work its content should |
| `G3` | **`fzn_disjunctive`'s general form only.** `CHRISTMAS_LIST.md:169` gives it as `d_i=0 \/ d_j=0 \/ s_i+d_i<=s_j \/ s_j+d_j<=s_i`, i.e. variable-vs-variable linear atoms. With constant `d_i` — the version the shipped decomposition covers — this gap does not arise |
| `G11` | **not this entry's.** Weighted sums are `cumulative`'s wall; a unary resource has no weights |
| — | the **global** window-and-subset explanation is **E4**, which D-0006 calls the research. See Calibration: it is what the §6 rules need, and it is *not* what TimeD needs |

Extensions: **E2** (`CHRISTMAS_LIST.md:169`, for the variable-duration form).
`decomps/disjunctive.md` prices the *constant-duration* form at **E0** — "the schemas exist and
run" — which the shipped artifact bears out.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21 by this session, output redirected to a file and grepped) →
  the out-of-scope block quoted verbatim above, and the run totals.
- `grep -o '\frac' cata/cumulative.tex | wc -l` → **2**.
- `python3 tools/mzn_coverage.py --rank --json` → `disjunctive` in tier
  `D literature + solver-native`, ecodes `["E2"]`, `CHRISTMAS_LIST.md` line 169, section
  `6. Scheduling`. Confirms the stub's tier row; nothing in it needed correcting.
- `explenation generator.ml` read, not run → `:810-812` (the `cumul` value), `:868` (`xbc`),
  `:881` (the emitting call), **`:343-355` (`rule5` takes no capacity argument — the claim in
  "Read this before the rest of the entry" is read off these lines)**, `:466`
  (`printind_const` renders every `ind_const` as `d`), `:539-541` and `:622` (the `F` drop and
  `filter_branches`), `:808-809` (`alldiff`'s identical implicit-1 use of `rule5`).
- `cata/cumulative.tex` read, not run → both rules and the `%% generator diagnostics` footer.
- `CHRISTMAS_LIST.md:169`, `:167`, `:106-109` read → the literature and solver cells, the
  E2 route, the cumulative citations, the solver legend.
- `catalog/_literature/cumulative.md:225-270` read, **not fetched** → the TimeD display, the
  §6.2 propagation-strength sentence, the per-propagation finding and the open minimality
  questions. C2's tags carried across unchanged.
- `catalog/cumulative.md` read → the identification of the shipped chain with TimeD, and its
  request that this entry cite rather than re-render.
- `decomps/disjunctive.md`, `decomps/_shapes-ext.md:238-271`, `decomps/_shapes.md:226-238` read
  → the signature, SCH-1/S9's maths, the shape numbering.
- `find . -name '*.mzn'` → empty; the basis for the provenance line.
- The G11-falls-away argument in Calibration is **reasoning, labelled as such in place**, from
  C2's `QUOTED` TimeD display and the generator source. It is not a measurement.

**Discrepancies noted, not fixed (this session does not own those files).**

0. **The "index functions are opaque closures" trap is stale**, in `CLAUDE.md`'s Traps section
   and in `catalog/cumulative.md:244`. W1-T7 made them first-order `ind_op` data with an
   interpreter, a printer and an inverter (`explenation generator.ml:19-49`, `:145`, `:173-183`),
   and the generator's own comment there says so. The consequence for this entry is in
   Calibration, limit 1: the duration shift's direction *is* readable, off `:796-797`.
   D-0006's first item is the record that should be revisited, not this entry.

1. **Stale line numbers.** `decomps/_shapes-ext.md:240` and `decomps/_shapes.md:234` both cite
   the `cumul` value at "l.680–682"; `decomps/disjunctive.md:8` says "l.810–812", which is
   right. Measured 2026-09-21: **810-812**. `CLAUDE.md` carries the same stale pair.
2. **`decomps/disjunctive.md:26` gives the status as "generated, unvalidated — and in fact not
   checkable".** `catalog/README.md`'s legend has a value for exactly that state and it is
   `not validatable`; the two halves of that sentence are the two different statuses, and only
   the second is right. This entry uses `not validatable`.
