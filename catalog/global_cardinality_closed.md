# `global_cardinality_closed`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `global_cardinality_closed`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E0`, `E3`, `E4`, `E9`; the row is shared with `global_cardinality` at `CHRISTMAS_LIST.md:127` |
| **Status** | `encodable today, not encoded` — **G8 closed on 2026-09-22, and this entry's own text said it was the whole of the difficulty.** Re-decided by U2, 2026-09-22. See Status |
| **Generated** | **0** — there is no `cata/global_cardinality_closed.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears nowhere in the 2026-09-21 run, neither in the 11 in-scope entries nor in the 5 out-of-scope ones |
| **Calibration** | **out of reach** — inherited from [`gcc.md`](gcc.md) and *reinforced* here: there is also no generated premise on this side to compare |
| **Last measured** | 2026-09-21 for the tier, validator and calibration. **Status re-decided 2026-09-22 (U2)** against `explenation generator.ml` after commits `4547daf`/`1e747ee`; no new run |

## Read this before the rest of the entry

**The shipped `gcc` decomposition does not cover this constraint, and
[`catalog/gcc.md`](gcc.md) says so in as many words.** That entry's "What this catalog entry
actually covers" paragraph reads: the generator's decomposition is the **unrestricted** form over
a value range `[1,m]` with one occurrence variable `O_t` per value — counts as free variables,
no `low`/`up`, no `closed` — and "the MiniZinc variants `_closed`, `_low_up`,
`_low_up_closed` are **not** covered by this entry".

So `cata/gcc.tex`'s four rules are **not** evidence about `global_cardinality_closed`, and this entry does not
re-render them. What it establishes is the narrower thing that is true: which feature or
features of
`global_cardinality_closed` the format cannot express, and which numbered gaps those are.

## Constraint

`global_cardinality_closed(array[$X] of var int: x, array[$Y] of int: cover, array[$Y] of var int: counts)`

As `global_cardinality` — `counts[j]` is the number of `x[i]` equal to `cover[j]` — **plus
closedness: every `x[i]` must take a value that appears in `cover`.** The unrestricted form lets
an `x[i]` take a value nobody counts; the closed form forbids it.

**Provenance of the signature:** **not vendored in this repo.**
`tools/data/minizinc-2.10.1-globals.txt:65` carries the *name* only, and `docs/COVERAGE.md`
is explicit that the snapshot is names only. The signature line above is **recall and is marked
as such**; treat it exactly as [`gcc.md`](gcc.md) treats its own, which says "the signature line
above is recall; the decomposition line is a citation".

What *is* a citation is the FlatZinc-level definition of the base constraint, quoted at
`CHRISTMAS_LIST.md:127`: `fzn_global_cardinality` is
`forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)`. The list gives no
FlatZinc body for the `global_cardinality_closed` variant, so nothing is quoted for the closedness conjunct.

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
**Those `l_uv`/`u_uv` are exactly the kind of object `global_cardinality_closed` supplies** — closedness is the flow network's *sink-side* structure, the statement that every unit of flow leaving a variable node reaches a counted value.
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
this table is the *family's* support, not a separate measurement for `global_cardinality_closed`. That
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
**Spec:** none — there is no `decomps/global_cardinality_closed.md`, and there is no `decomps/global_cardinality.md`
either. The nearest relative is `decomps/count.md` (`count(x, v, c)`, i.e. `gcc` at a single
value), which [`gcc.md`](gcc.md) already names.

[`gcc.md`](gcc.md)'s **Decomposition used here** section renders `gccn`'s three steps and the
W1-T9 `pointp` repair in full; they are not copied here. What matters for this entry is the one
feature of `global_cardinality_closed` that has no encoding, and that is the Status section below.

## Scope of this entry

**Events the generator was asked to explain:** **none under this name.** No `explainall` call in
`explenation generator.ml` names a `global_cardinality_closed` decomposition; line 882 is
`explainall [xac;ngbc] gccn "cata/gcc.tex"` and it is the only call in the file that concerns
this family (verified 2026-09-21 by `grep -n 'explainall' 'explenation generator.ml'`, which
prints 15 emitting calls at lines 879–893).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact, so no `%% generator diagnostics (W1-T3)` footer exists |

**The events that *would* be asked, if the decomposition existed**, are the base's four:
`X_i = t`, `X_i ≠ t` from `xac`, and `O_t ≥ p`, `O_t < p` from `ngbc`
(`explenation generator.ml:869, 874`). Closedness adds no new variable and therefore no fifth event; it restricts which
assignments are legal, not which literals exist. So the event list of a hypothetical
``global_cardinality_closed`` entry would be the base's four, and the *rules* would differ, not the questions.

## Generated rules

**None.** There is no `cata/global_cardinality_closed.tex` to count, so `grep -o '\\frac'` has no input. This is
not the same as `regular`'s zero — there the generator ran and refused every branch; here it
was never asked, because no decomposition value for this variant is encodable (below).

## Status

**`encodable today, not encoded`**

**This status changed on 2026-09-22.** The previous one — `nothing generated — blocked on G8` —
is retired because G8 closed that day (session G-1, commits `4547daf` and `1e747ee`), and this
entry had already argued that G8 was *the whole* of the difficulty. That argument is quoted
below and it is now an argument for the new status rather than the old one. There is no gap left
to name, which is the legend condition `catalog/README.md` attaches to this value.

**What the block was.** The one feature this variant adds is a disjunction over a value
*subset*. Closedness is `∀i: ⋁_{t ∈ cover} B1_{i,t}` — mechanically a `rule4` disjunction over
the value family, a schema the generator already has and already uses (`regular`). What it did
not have was a way to say `t ∈ cover` when `cover` is a proper subset of the printer's value
range: **G8** was "`ind_set` names only whole predefined ranges — no subrange, no exclusion"
(`docs/DECOMP_FORMAT_NOTES.md:76`).

**Why it is gone.** `ind_set` now carries four further formers (`explenation generator.ml:48-52`)
and two of them write exactly this set. `DPar (name, parent)` names a parameter subset and
prints its own containment — `"cover,~cover \\subseteq \\llbracket1,m\\rrbracket"`
(`:536`) — which is the faithful reading of MiniZinc's `cover` argument, a parameter array of
covered values. `DSub (parent,a,b)` would write it instead as a literal subrange if an instance
warranted one (`:534`). Either is admitted by `ind_set_defined` (`:520-525`), and admitted
*without* relaxing W1-T2: these formers define themselves by being printed, so they are not
`D_4`. `D of int` beyond 3 and `D2` are untouched and still refused, which is why `range`,
`roots`, `regular` and `table` still emit nothing.

**And the degenerate case, which is why G8 was the whole of it.** If `cover` is the entire value
range `[1,m]`, closedness is vacuous and `global_cardinality_closed` *is* `global_cardinality` —
the shipped `gccn` would already be it. Everything separating this entry from [`gcc.md`](gcc.md)
sat in the one construct G8 named.

**What would have to be written.** The `gccn` value at `explenation generator.ml:909` unchanged,
plus one `Decomp (_, rule4, …)` over the `B1` family whose value index ranges over
`DPar ("cover", D 2)`, and one `explainall` line. `oni`/`ont` and their set-taking siblings
`oniin`/`ontin` already accept an `ind_set` argument, which is the interface `at_most`
(`:994-995`) and `among` (`:942-943`) use. **Nothing was run**: no value was authored, no
artifact produced, no rule of this constraint seen or judged. Two sobering precedents apply and
neither is predicted away here — `among` got two rules from G8's closure and both are measured
**UNSOUND**, and this entry's Calibration below stays `out of reach` for reasons G8 never
touched.

This is on top of, not instead of, everything that already blocks the base entry from reaching
the published rule: `gcc.md`'s own Gaps table lists G1, G4, G11 and G12/G13, and its calibration
is `out of reach` for reasons G8 does not touch.

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
were added**." `global_cardinality_closed` is the constraint that *has* the bounds. So the prediction is now
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
| **`G8`** | **CLOSED 2026-09-22** (`4547daf`, `1e747ee`). It was the binding one and the only one unique to this variant: `ind_set` named only whole predefined ranges, so `⋁_{t ∈ cover} B1_{i,t}` had no encoding. `DPar`/`DSub` now write it — see Status. `docs/DECOMP_FORMAT_NOTES.md:76` still lists this gap as open; that file is not this session's to edit |
| `G1` | inherited from [`gcc.md`](gcc.md): a bare integer threshold cannot reach the printed rule. Not binding *here* — `_closed` adds no threshold — but it still blocks the family's `low`/`up` siblings |
| `G12`/`G13` | inherited: `length(xs) >= sum(count)` sums *integer* variables, a fourth kind of schema (E9, D-0011) |
| — | the published flow rule is blocked by **no gap on this list**: its premises are indexed by a run-time graph cut, so **E4 is necessary but not sufficient** (Calibration, from C2 via `gcc.md`) |

Extensions: **E0** for `_low_up`'s shape, **E3** + **E9** for the full form, **E4** for the flow
explanation — `CHRISTMAS_LIST.md:127`, with the E3→E9 sharpening at **D-0011** (the trailing
`sum(count)` is over *integer* variables). E4 carries the calibration caveat above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `global_cardinality_closed` in
  `C literature + solver-decomposes`, ecodes `E0`, `E3`, `E4`, `E9`, `CHRISTMAS_LIST.md` line 127,
  section `2. Counting and cardinality`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`
  and `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions
  this name**, which is the measurement behind the **Validator** row.
- `ls cata/` → 16 `.tex` files; `global_cardinality_closed.tex` is not among them.
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
- `tools/data/minizinc-2.10.1-globals.txt:65` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- **The G8 attribution and the degenerate-case argument are reasoning, labelled as such in
  place.** They are read off `docs/DECOMP_FORMAT_NOTES.md:76`, `explenation generator.ml:459` and
  the semantics of closedness; no code was run and no rule was generated to check them.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **Two in-repo line numbers for the `failwith "sommes multiples pas encore implémentés"`
   site, and both are wrong.** `docs/DECOMP_FORMAT_NOTES.md` says "generator lines 177-219" and
   `decomps/_shapes-ext.md` says "source l.320/334/348". Measured today with
   `grep -n 'sommes multiples'`: **355, 369, 383**. The gap (G4) is unaffected; only its pointers
   have rotted.
2. **There is no `decomps/global_cardinality_closed.md`**, nor any `decomps/` spec for the base
   `global_cardinality`. [`gcc.md`](gcc.md) already records the second as "noted, not fixed"; the
   first is recorded here for the same reason. `decomps/count.md` is the nearest relative
   (`count(x, v, c)` is `gcc` at a single value) and says nothing about closedness.
