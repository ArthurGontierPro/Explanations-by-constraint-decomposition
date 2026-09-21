# `global_cardinality_low_up`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `global_cardinality_low_up`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E0`, `E3`, `E4`, `E9`; the row is shared with `global_cardinality` at `CHRISTMAS_LIST.md:127` |
| **Status** | `nothing generated — blocked on G1` |
| **Generated** | **0** — there is no `cata/global_cardinality_low_up.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears nowhere in the 2026-09-21 run, neither in the 11 in-scope entries nor in the 5 out-of-scope ones |
| **Calibration** | **out of reach** — inherited from [`gcc.md`](gcc.md) and *reinforced* here: there is also no generated premise on this side to compare |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json`, and reads of `explenation generator.ml` and `CHRISTMAS_LIST.md:127` |

## Read this before the rest of the entry

**The shipped `gcc` decomposition does not cover this constraint, and
[`catalog/gcc.md`](gcc.md) says so in as many words.** That entry's "What this catalog entry
actually covers" paragraph reads: the generator's decomposition is the **unrestricted** form over
a value range `[1,m]` with one occurrence variable `O_t` per value — counts as free variables,
no `low`/`up`, no `closed` — and "the MiniZinc variants `_closed`, `_low_up`,
`_low_up_closed` are **not** covered by this entry".

So `cata/gcc.tex`'s four rules are **not** evidence about `global_cardinality_low_up`, and this entry does not
re-render them. What it establishes is the narrower thing that is true: which feature or
features of
`global_cardinality_low_up` the format cannot express, and which numbered gaps those are.

## Constraint

`global_cardinality_low_up(array[$X] of var int: x, array[$Y] of int: cover, array[$Y] of int: lb, array[$Y] of int: ub)`

For each value `cover[j]`, the number of `x[i]` equal to it lies between the **constants**
`lb[j]` and `ub[j]`. The counts are not variables of the model: the bounds are, and they are
parameters.

**Provenance of the signature:** **not vendored in this repo.**
`tools/data/minizinc-2.10.1-globals.txt:68` carries the *name* only, and `docs/COVERAGE.md`
is explicit that the snapshot is names only. The signature line above is **recall and is marked
as such**; treat it exactly as [`gcc.md`](gcc.md) treats its own, which says "the signature line
above is recall; the decomposition line is a citation".

What *is* a citation is the FlatZinc-level definition of the base constraint, quoted at
`CHRISTMAS_LIST.md:127`: `fzn_global_cardinality` is
`forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)`. The list gives no
FlatZinc body for the `global_cardinality_low_up` variant, so nothing is quoted for the `lb`/`ub` bounds.

## Published explanation

**Citation:** Downing, Feydy, Stuckey 2012, *Explaining flow-based propagation*, CPAIOR,
LNCS 7298:146–162 — `CHRISTMAS_LIST.md:127`. The row covers `global_cardinality`, `_closed`,
`_low_up` and `_low_up_closed` together and describes the work as a generic explaining flow
propagator that explicitly replaces a specialised **gcc** propagator.

**Rule shape:** sourced into [`catalog/_literature/gcc.md`](_literature/gcc.md) by session C2.
**Nothing is restated here**; [`gcc.md`](gcc.md) renders C2's summary with its provenance tags
intact, and a second copy in this file would be a copy with the tags one step further from the
paper.

**One thing about that source does bear directly on this entry, and it is a point in this
variant's favour rather than against it.** C2's reading, carried through `gcc.md`: there is no
`gcc`-specific explanation rule in the paper at all — `gcc` is encoded as a flow network and
what is explained is the **generic** network-flow propagator, whose premises are
`⋀ ⟦f_uv ≥ l_uv⟧` over arcs leaving a cut and `⋀ ⟦f_uv ≤ u_uv⟧` over arcs entering it.
**Those `l_uv`/`u_uv` are exactly the kind of object `global_cardinality_low_up` supplies** — `lb`/`ub` are the network's lower and upper arc capacities, which is what `l_uv` and `u_uv` *are*.
So the published treatment is, if anything, *more* directly about this variant than about the
unrestricted form the generator ships. That does not make it comparable; see Calibration.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:127`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The row's
solver cell reads `decomp **[G]**` and covers all four `global_cardinality` names at once, so
this table is the *family's* support, not a separate measurement for `global_cardinality_low_up`. That
combination — published literature and Chuffed still decomposing — is what puts the whole row
in tier C.

## Decomposition used here

**Generator value:** **none.** `explenation generator.ml` defines two values for this
family and neither is this constraint: `gcc` at line **813** (`rule1` + `rule7`, a Boolean sum `=`,
with no occurrence variable) and `gccn` at line **827** (`rule1` → `rule6` → `rule1`, the
occurrence-variable channel). Both encode the **unrestricted** form. Nothing emits `gcc`;
`cata/gcc.tex` comes from `gccn`.
**Emitted by:** nothing under this name. The only emitting call for the family is line **882**,
`explainall [xac;ngbc] gccn "cata/gcc.tex"`.
**Spec:** none — there is no `decomps/global_cardinality_low_up.md`, and there is no `decomps/global_cardinality.md`
either. The nearest relative is `decomps/count.md` (`count(x, v, c)`, i.e. `gcc` at a single
value), which [`gcc.md`](gcc.md) already names.

[`gcc.md`](gcc.md)'s **Decomposition used here** section renders `gccn`'s three steps and the
W1-T9 `pointp` repair in full; they are not copied here. What matters for this entry is the one
feature of `global_cardinality_low_up` that has no encoding, and that is the Status section below.

## Scope of this entry

**Events the generator was asked to explain:** **none under this name.** No `explainall` call in
`explenation generator.ml` names a `global_cardinality_low_up` decomposition; line 882 is
`explainall [xac;ngbc] gccn "cata/gcc.tex"` and it is the only call in the file that concerns
this family (verified 2026-09-21 by `grep -n 'explainall' 'explenation generator.ml'`, which
prints 15 emitting calls at lines 879–893).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact, so no `%% generator diagnostics (W1-T3)` footer exists |

**The events that *would* be asked, if the decomposition existed**, are the base's four:
`X_i = t`, `X_i ≠ t` from `xac`, and `O_t ≥ p`, `O_t < p` from `ngbc`
(`explenation generator.ml:869, 874`). Replacing the count variables by constant bounds **removes** two of them: with no `counts`
array there is no `O_t` to ask `O_t ≥ p` or `O_t < p` about, so a `global_cardinality_low_up`
entry would be asked about `X_i = t` and `X_i ≠ t` only. That is a smaller question than the
base's, not a larger one, and it is the reason the next section says this variant is the
*closest* of the three to being reachable.

## Generated rules

**None.** There is no `cata/global_cardinality_low_up.tex` to count, so `grep -o '\\frac'` has no input. This is
not the same as `regular`'s zero — there the generator ran and refused every branch; here it
was never asked, because no decomposition value for this variant is encodable (below).

## Status

**`nothing generated — blocked on G1`**

**The bounds are bare integer constants, and G1 is precisely the gap that no bare integer
constant reaches the printed rule.** `docs/DECOMP_FORMAT_NOTES.md`'s G1 states it and gives the
mechanism: on an empty remainder, `reified_devent` defaults to a placeholder that never matches a
real variable, "so the rule schema has no path that ever mentions the constant", and it is
"confirmed empirically: `cata/alldifferent.tex`'s one rule never prints its own implicit 'at most
1'". `lb[j]` and `ub[j]` are that constant, once per value.

**But this variant is the closest of the three to being reachable, and the shipped artifact
already shows the shape.** `gccn`'s step 2 is `rule6`, the `≥` direction of a Boolean sum,
guarded by a free parameter `p`: `B2_{t,p} ⇔ (Σ_i B1_{i,t} ≥ p)`. `cata/gcc.tex` prints rules
whose premises carry `p ∈ [1,n]` with `p` *unbound* — the W1-T9 `pointp` repair recorded at
`explenation generator.ml:815-826`, which is why [`gcc.md`](gcc.md) is 4/4 rather than 2/4. A
`low_up` rule is that schema at `p := lb_t` (and its dual at `p := ub_t + 1`). **What is missing
is not the reasoning step; it is the ability to write `p = lb_t` in the premise** — an indexed
constant symbol in the printed rule, which is G1's second half. *This paragraph is reasoning read
off `explenation generator.ml:827-829` and `cata/gcc.tex` via [`gcc.md`](gcc.md), not a
measurement.*

That reading is consistent with `CHRISTMAS_LIST.md:127`, which prices `_low_up` at **E0** — no
extension, i.e. nothing beyond the existing schemas. It is *not* consistent with one line of
[`gcc.md`](gcc.md)'s Gaps table; see the discrepancy note below, where the disagreement is stated
rather than silently resolved.

Nothing here is validated, flagged or refuted: with no artifact there is nothing for
`make validate` to judge, and the 2026-09-21 run's totals (**34 rules checked in 11 entries: 13
SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**) contain no line for this
name.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.**

Two independent reasons, and the first is the one that would survive even if the second were
fixed:

1. **Structural, inherited from [`gcc.md`](gcc.md) and unchanged by this variant.** The
   published premise is indexed by "the arcs crossing the cut `C`", where `C` is the set of
   nodes searched for an augmenting path or an SCC of the *residual* graph. The printer
   quantifies over `[1,n]`, `[1,m]` and an undefined `D_k` beyond (`CLAUDE.md`, "Traps"); `C` is
   the output of a graph algorithm run at propagation time. `gcc.md` gives three such obstacles
   and calls each independently fatal. **None of them is about the missing bounds**, which is
   precisely why adding the bounds would not close the comparison.
2. **There is no premise on this side.** Zero generated rules means nothing to place in an
   implication order even if (1) were resolved.

**And this entry sharpens `gcc.md`'s own prediction, which is the reason to say it here.** That
entry records, as its settled reading of C2's sourcing: "the constraint mismatch is real (the
paper's network carries cardinality *bounds*, this decomposition has none) but it is not the
binding reason — the binding reason is structural, and **it would still hold if the bounds
were added**." `global_cardinality_low_up` is the constraint that *has* the bounds. So the prediction is now
attached to the name it was about, and it remains a prediction rather than a measurement,
because nothing is generated here to test it against. **`E4` is necessary but not sufficient**
(`gcc.md`, from C2): counting across sums would reach the cardinality literals; it would not
produce a cut of a residual graph.

**Not `no published rule exists`, and not `incomparable`.** A paper is cited on this row, so the
first is false; and `incomparable` requires both sides expressible in a common vocabulary, which
`gcc.md` establishes is not the case. `out of reach` is a first-class verdict (D-0013), not a
failure to compare.

## Gaps

| gap | what it blocks here |
|---|---|
| **`G1`** | **the binding one.** No way to carry a bare integer threshold into the printed rule: `lb[j]`/`ub[j]` are never captured as an `event`, an index or anything else the printer walks. `docs/DECOMP_FORMAT_NOTES.md` G1, whose empirical confirmation is `cata/alldifferent.tex`'s unprinted implicit "1" |
| `G2` | adjacent, and worth naming: `var_name` is the closed variant `X \| B of int \| T \| I \| V \| N \| O` with no slot for "this constraint's own parameter", so even an *indexed* constant `lb_t` has no letter of its own. G1 is why it cannot be printed; G2 is why it cannot be named |
| `G4`? | [`gcc.md`](gcc.md) lists this ("one Boolean-sum family per rule; the `_low_up` form wants two"). **This entry disagrees and says so** — see the discrepancy note. `rule5` and `rule6` give the two directions in two separate rules over one family, and the `failwith` site is reached only by several *families* in one step |
| `G12`/`G13` | inherited from the family: `length(xs) >= sum(count)` sums *integer* variables (E9, D-0011). Arguably absent from `_low_up`, which has no `counts` array to sum |
| — | the published flow rule is blocked by **no gap on this list** — **E4 is necessary but not sufficient** (Calibration) |

Extensions: **E0** for `_low_up`'s shape, **E3** + **E9** for the full form, **E4** for the flow
explanation — `CHRISTMAS_LIST.md:127`, with the E3→E9 sharpening at **D-0011** (the trailing
`sum(count)` is over *integer* variables). E4 carries the calibration caveat above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `global_cardinality_low_up` in
  `C literature + solver-decomposes`, ecodes `E0`, `E3`, `E4`, `E9`, `CHRISTMAS_LIST.md` line 127,
  section `2. Counting and cardinality`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`
  and `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions
  this name**, which is the measurement behind the **Validator** row.
- `ls cata/` → 16 `.tex` files; `global_cardinality_low_up.tex` is not among them.
- `grep -n 'explainall' 'explenation generator.ml'` → 15 emitting calls, lines 879–893; the only
  one for this family is line **882**, `explainall [xac;ngbc] gccn "cata/gcc.tex"`.
- `grep -n '^let gccn\|^let gcc ' 'explenation generator.ml'` → `gcc` at **813**, `gccn` at
  **827** (both re-measured today; they match `gcc.md` and are recorded because line numbers in
  this repo rot).
- `grep -n 'ind_set_defined' 'explenation generator.ml'` → line **459**,
  `let ind_set_defined s = match s with D 1 | D 2 | D 3 -> true | D _ -> false | D2 _ -> false`.
- `grep -n 'sommes multiples' 'explenation generator.ml'` → lines **355, 369, 383** (see the
  discrepancy note below).
- `CHRISTMAS_LIST.md:127` read → the citation, the solver cells, the E-route and the
  `fzn_global_cardinality` body quoted above.
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `catalog/gcc.md` read, not run → the coverage disclaimer, the decomposition chain, the
  `out of reach` verdict and its three obstacles, and the "would still hold if the bounds were
  added" prediction. **No statement about the Downing et al. paper originates in this file**;
  every one is C2's, via `gcc.md`, with its tags left where they are.
- `tools/data/minizinc-2.10.1-globals.txt:68` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- **The "closest of the three" argument and the G4 disagreement are reasoning, labelled as such
  in place.** They rest on `gccn`'s `rule6` step and the `pointp` repair comment as
  [`gcc.md`](gcc.md) renders them, plus the measured location of the `failwith` site; no code was
  run and no rule was generated.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **[`gcc.md`](gcc.md) and `CHRISTMAS_LIST.md:127` disagree about `_low_up`, and this entry
   takes the list's side.** `gcc.md`'s Gaps table lists `G4` — "one Boolean-sum family per rule
   (hard failure otherwise): the `_low_up` form wants two". `CHRISTMAS_LIST.md:127` prices
   `_low_up` at **E0**, i.e. needing no extension at all. R2's reading, offered as reasoning and
   not as a measurement: the two bounds are two *thresholds on one sum*, and `rule5`/`rule6`
   already give the `≤` and `≥` directions as separate rules over the same family — the
   `failwith "sommes multiples pas encore implémentés"` site (measured today at lines **355, 369,
   383**) is reached by several summed *families* in one reasoning step, which `_low_up` does not
   need. On that reading the residual obstacle is **G1**, not G4, and E0 is right. **Neither
   `gcc.md` nor `CHRISTMAS_LIST.md` was edited**; the disagreement is recorded so it can be
   settled by whoever owns them.
2. **Two in-repo line numbers for the `failwith` site, and both are wrong.**
   `docs/DECOMP_FORMAT_NOTES.md` says "generator lines 177-219", `decomps/_shapes-ext.md` says
   "source l.320/334/348"; measured today, **355, 369, 383**.
3. **There is no `decomps/global_cardinality_low_up.md`**, nor one for the base
   `global_cardinality`. [`gcc.md`](gcc.md) records the second; the first is recorded here.
