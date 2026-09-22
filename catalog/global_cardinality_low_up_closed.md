# `global_cardinality_low_up_closed`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `global_cardinality_low_up_closed`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E0`, `E3`, `E4`, `E9`; the row is shared with `global_cardinality` at `CHRISTMAS_LIST.md:127` |
| **Status** | `nothing generated — blocked on G1` — **still, after G1's partial closure and G8's full closure on 2026-09-22**: the `lb` direction needs a symbolic `n − lb_t`. Re-checked by U2, 2026-09-22. See Status |
| **Generated** | **0** — there is no `cata/global_cardinality_low_up_closed.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears nowhere in the 2026-09-21 run, neither in the 11 in-scope entries nor in the 5 out-of-scope ones |
| **Calibration** | **out of reach** — inherited from [`gcc.md`](gcc.md) and *reinforced* here: there is also no generated premise on this side to compare |
| **Last measured** | 2026-09-21 for the tier, validator and calibration rows. **Status re-checked 2026-09-22 (U2)** against `explenation generator.ml` after commits `4547daf`/`1e747ee`; unchanged, and no new run |

## Read this before the rest of the entry

**The shipped `gcc` decomposition does not cover this constraint, and
[`catalog/gcc.md`](gcc.md) says so in as many words.** That entry's "What this catalog entry
actually covers" paragraph reads: the generator's decomposition is the **unrestricted** form over
a value range `[1,m]` with one occurrence variable `O_t` per value — counts as free variables,
no `low`/`up`, no `closed` — and "the MiniZinc variants `_closed`, `_low_up`,
`_low_up_closed` are **not** covered by this entry".

So `cata/gcc.tex`'s four rules are **not** evidence about `global_cardinality_low_up_closed`, and this entry does not
re-render them. What it establishes is the narrower thing that is true: which feature or
features of
`global_cardinality_low_up_closed` the format cannot express, and which numbered gaps those are.

## Constraint

`global_cardinality_low_up_closed(array[$X] of var int: x, array[$Y] of int: cover, array[$Y] of int: lb, array[$Y] of int: ub)`

`global_cardinality_low_up` **and** closedness: each value `cover[j]` occurs between `lb[j]`
and `ub[j]` times, **and** every `x[i]` takes a value appearing in `cover`.

**Provenance of the signature:** **not vendored in this repo.**
`tools/data/minizinc-2.10.1-globals.txt:69` carries the *name* only, and `docs/COVERAGE.md`
is explicit that the snapshot is names only. The signature line above is **recall and is marked
as such**; treat it exactly as [`gcc.md`](gcc.md) treats its own, which says "the signature line
above is recall; the decomposition line is a citation".

What *is* a citation is the FlatZinc-level definition of the base constraint, quoted at
`CHRISTMAS_LIST.md:127`: `fzn_global_cardinality` is
`forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)`. The list gives no
FlatZinc body for the `global_cardinality_low_up_closed` variant, so nothing is quoted for the `lb`/`ub` bounds or the closedness conjunct.

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
**Those `l_uv`/`u_uv` are exactly the kind of object `global_cardinality_low_up_closed` supplies** — `lb`/`ub` are the network's arc capacities — what `l_uv` and `u_uv` *are* — and closedness is its sink-side structure.
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
this table is the *family's* support, not a separate measurement for `global_cardinality_low_up_closed`. That
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
**Spec:** none — there is no `decomps/global_cardinality_low_up_closed.md`, and there is no `decomps/global_cardinality.md`
either. The nearest relative is `decomps/count.md` (`count(x, v, c)`, i.e. `gcc` at a single
value), which [`gcc.md`](gcc.md) already names.

[`gcc.md`](gcc.md)'s **Decomposition used here** section renders `gccn`'s three steps and the
W1-T9 `pointp` repair in full; they are not copied here. What matters for this entry is the one
feature of `global_cardinality_low_up_closed` that has no encoding, and that is the Status section below.

## Scope of this entry

**Events the generator was asked to explain:** **none under this name.** No `explainall` call in
`explenation generator.ml` names a `global_cardinality_low_up_closed` decomposition; line 882 is
`explainall [xac;ngbc] gccn "cata/gcc.tex"` and it is the only call in the file that concerns
this family (verified 2026-09-21 by `grep -n 'explainall' 'explenation generator.ml'`, which
prints 15 emitting calls at lines 879–893).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact, so no `%% generator diagnostics (W1-T3)` footer exists |

**The events that *would* be asked, if the decomposition existed**, are the base's four:
`X_i = t`, `X_i ≠ t` from `xac`, and `O_t ≥ p`, `O_t < p` from `ngbc`
(`explenation generator.ml:869, 874`). As for `_low_up`, the constant bounds **remove** the `counts` array and with it the `O_t ≥ p`
and `O_t < p` events; closedness adds no variable and so adds no event. A hypothetical entry
here would be asked about `X_i = t` and `X_i ≠ t` only.

## Generated rules

**None.** There is no `cata/global_cardinality_low_up_closed.tex` to count, so `grep -o '\\frac'` has no input. This is
not the same as `regular`'s zero — there the generator ran and refused every branch; here it
was never asked, because no decomposition value for this variant is encodable (below).

## Status

**`nothing generated — blocked on G1`**

**This variant is the conjunction of the other two, and it inherits both blockers with nothing
new of its own.**

- From [`global_cardinality_low_up`](global_cardinality_low_up.md): the bounds `lb[j]`, `ub[j]`
  are bare integer constants, and **G1** is exactly "no way to carry a bare integer threshold into
  the printed rule", confirmed empirically by `cata/alldifferent.tex`'s unprinted implicit "1".
- From [`global_cardinality_closed`](global_cardinality_closed.md): closedness is
  `∀i: ⋁_{t ∈ cover} B1_{i,t}`, a `rule4` disjunction over a value *subset*, and **G8** is
  "`ind_set` names only whole predefined ranges — no subrange, no exclusion"
  (`docs/DECOMP_FORMAT_NOTES.md:76`; `ind_set_defined`, line **459**, admits `D 1`, `D 2`, `D 3`).

**G1 is named as the status gap rather than G8 for a reason worth stating**: G8 can be sidestepped
by an instance whose `cover` is the whole value range, in which case closedness is vacuous and
this constraint degenerates to `_low_up`. G1 cannot be sidestepped by any instance with a
non-trivial bound, which is every instance anyone would write. So G1 binds strictly more often.
*That is reasoning about the two gaps, not a measurement.*

**Nothing about the combination is harder than its parts.** The two constructs touch different
parts of the format — one a threshold on a sum, one the index set of a disjunction — and
neither interferes with the other. This is the one place where the four-way suffix combination
turns out to cost nothing extra, in contrast with `cumulatives_opt`, where it does.

**Re-checked 2026-09-22 (U2), after G-1's commits `4547daf` and `1e747ee`. The status is
unchanged and the paragraph above is the reason the re-check was quick: the parts move
independently, so one of the two can close without the status moving.** What happened is that
one and a half of them did.

- **G8 is CLOSED**, and with it the borrowed half from
  [`global_cardinality_closed`](global_cardinality_closed.md), which is now
  `encodable today, not encoded`. `DPar (name, parent)` names a parameter subset and prints its
  own containment (`explenation generator.ml:51`, `:536`), which is `cover`; `DSub` writes a
  literal subrange (`:534`). Neither is a `D_4` — they define themselves by being printed — so
  `ind_set_defined` admits them (`:520-525`) without relaxing W1-T2.
- **G1 is half closed, and this entry needs the unclosed half.** `DCard` puts a threshold on a
  named witness set (`:52`, printed `:537`), which `at_most(c)` uses as
  `DCard ("S", D 1, EQ, BPar ("c", 1))` (`:995`) — the sum's `≤` direction, so `ub[j]` is now
  writable. `lb[j]` is not: its witness set has size `n − lb_t`, and `ind_bound` is
  `BInt of int | BPar of string*int` (`:46`), printed at `:161-164` as a name plus or minus a
  literal integer. One symbol minus another is not an `ind_bound`, and **G-1 named exactly this
  case when it left `at_least`/`exactly` undone** (`WORKLOG.md:1615-1616`).

**So the status's own justification survives intact, for the same reason it was written.** This
entry named G1 rather than G8 because "G8 can be sidestepped by an instance whose `cover` is the
whole value range … G1 cannot be sidestepped by any instance with a non-trivial bound." G8 has
now been closed outright rather than sidestepped, and G1's binding half has not. *A reading of
the generator's types and printers, not a measurement; nothing was run.*

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
were added**." `global_cardinality_low_up_closed` is the constraint that *has* the bounds. So the prediction is now
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
| **`G1`** | **the binding one, and now half closed** (2026-09-22). `DCard` reaches the printed rule for a sum's `≤` direction, so `ub[j]` is writable (`cata/at_most.tex` is the demonstrator). `lb[j]` is not: `n − lb_t` is not an `ind_bound` (`explenation generator.ml:46`, `:161-164`). Still cannot be sidestepped by any instance with a real lower bound |
| **`G8`** | **CLOSED 2026-09-22** (`4547daf`, `1e747ee`). Closedness is a disjunction over a value *subset*, which `ind_set` could not name; `DPar`/`DSub` now name it (`explenation generator.ml:51`, `:534`, `:536`). `docs/DECOMP_FORMAT_NOTES.md` still lists it as open; that file is not this session's to edit |
| `G2` | `var_name` has no slot for this constraint's own parameter, so `lb_t` has no letter even once G1 lets it be printed |
| `G4`? | [`gcc.md`](gcc.md) attributes this to the `_low_up` shape. [`global_cardinality_low_up`](global_cardinality_low_up.md) disagrees and gives the argument; the same applies here |
| — | the published flow rule is blocked by **no gap on this list** — **E4 is necessary but not sufficient** (Calibration) |

Extensions: **E0** for `_low_up`'s shape, **E3** + **E9** for the full form, **E4** for the flow
explanation — `CHRISTMAS_LIST.md:127`, with the E3→E9 sharpening at **D-0011** (the trailing
`sum(count)` is over *integer* variables). E4 carries the calibration caveat above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `global_cardinality_low_up_closed` in
  `C literature + solver-decomposes`, ecodes `E0`, `E3`, `E4`, `E9`, `CHRISTMAS_LIST.md` line 127,
  section `2. Counting and cardinality`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`
  and `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions
  this name**, which is the measurement behind the **Validator** row.
- `ls cata/` → 16 `.tex` files; `global_cardinality_low_up_closed.tex` is not among them.
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
- `tools/data/minizinc-2.10.1-globals.txt:69` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- **The inheritance argument, the choice of G1 over G8 as the status gap, and "the combination
  costs nothing extra" are all reasoning, labelled as such in place.** They rest on
  `docs/DECOMP_FORMAT_NOTES.md`'s G1 and G8 and on `explenation generator.ml:459`; no code was run.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`CHRISTMAS_LIST.md:127` prices `_low_up` at E0 but gives no separate price for
   `_low_up_closed`.** The row covers all four names with one route cell. On this entry's reading
   the closed suffix costs **G8** on top, which is not E0; whether that changes the row's E-code
   is for whoever owns `CHRISTMAS_LIST.md`. **Not edited here.**
2. **Two in-repo line numbers for the `failwith "sommes multiples pas encore implémentés"` site,
   and both are wrong.** `docs/DECOMP_FORMAT_NOTES.md` says "generator lines 177-219",
   `decomps/_shapes-ext.md` says "source l.320/334/348"; measured today with
   `grep -n 'sommes multiples'`, **355, 369, 383**.
3. **There is no `decomps/` spec for this name or for the base `global_cardinality`.**
   [`gcc.md`](gcc.md) records the second as "noted, not fixed".
