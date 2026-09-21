# `cumulatives`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `cumulatives`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E2`, `E4`; `CHRISTMAS_LIST.md:168`, section `6. Scheduling` |
| **Status** | `nothing generated — blocked on G14` — **and on everything that already blocks `cumulative`**: `G11`, `G15`, `G1`, `G3`. See Status |
| **Generated** | **0** — there is no `cata/cumulatives.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears in no line of the 2026-09-21 run |
| **Calibration** | **out of reach** — and, unlike [`cumulative.md`](cumulative.md), *not* rescued by the TimeD route: see Calibration |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json`, and reads of `explenation generator.ml`, `CHRISTMAS_LIST.md:167-168`, `decomps/cumulatives.md` and `catalog/cumulative.md` |

## Read this before the rest of the entry

**Two things are true at once here and an entry that states only one of them misleads.**

1. **Nothing is generated for this name.** There is no `cata/cumulatives.tex` and no decomposition
   value in `explenation generator.ml` for it.
2. **The file that looks closest, `cata/cumulative.tex`, is not `cumulative` either.**
   [`catalog/cumulative.md`](cumulative.md) leads with it: the shipped chain's final step is a
   single *unweighted* Boolean sum with an *implicit* bound of 1 (`rule5`,
   `explenation generator.ml:812`), which is a **unary** resource. There are no resource
   requirements `r_i` and no capacity anywhere in it. So it is `disjunctive` with constant
   durations, filed under `cumulative`'s name.

Put together: this entry has no artifact of its own, **and** it must not borrow the one next
door, which is two steps away rather than one. What it does establish is the exact distance —
which constructs `cumulatives` needs that the format has no encoding for, each pinned to a numbered
gap.

## Constraint

`cumulatives(array[int] of var int: s, array[int] of var int: d, array[int] of var int: r, array[int] of var int: m, array[int] of var int: b)`

Tasks are **assigned to machines** and each machine's capacity is respected: at every time
point, for every machine `k`, the total requirement of the tasks running on `k` is at most
`b[k]`.

**Provenance of the signature:** **in-repo, and quotable.** `decomps/cumulatives.md` carries this signature under its
"Signature" heading, without a citation of its own — so it is this repo's transcription rather
than a vendored line. `tools/data/minizinc-2.10.1-globals.txt:46` carries the name only.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:168`'s literature cell reads **`as above`**, pointing at the
`cumulative` row one line up, `CHRISTMAS_LIST.md:167`, which cites two papers:

- **Schutt, Feydy, Stuckey, Wallace 2011**, *Explaining the cumulative propagator*,
  Constraints 16(3):250–282 — time-table filtering with window-based explanations;
- **Schutt, Feydy, Stuckey, CPAIOR 2013**, *Explaining time-table-edge-finding propagation*
  (arXiv:1208.3015).

The row adds, of `cumulatives`/`cumulative_opt`/`cumulatives_opt`, "same route as `cumulatives`,
**no new literature**" — so the citation is inherited, and **no paper sourced in this repo is
about the multi-machine form**.

**Rule shape:** sourced into [`catalog/_literature/cumulative.md`](_literature/cumulative.md) by
session C2, and rendered in [`catalog/cumulative.md`](cumulative.md). **Nothing is restated
here.** In particular the TimeD decomposition C2 quotes, and the §6.2 sentence equating its
propagation strength with the global propagator's, are statements about **`cumulative`**; this
entry does not extend either to the multi-machine form, because no source in this repo does. Anything of
that kind would be UNSOURCED, and so it is not written.

No paper was fetched by this session and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:168`, whose solver cell reads `decomp`; legend at
`CHRISTMAS_LIST.md:106-109`. **This is the tier-C signature and it is worth reading against the
row above it:** `cumulative` itself is `native (cumulative.cpp, cumulativeCalendar.cpp) [G] [C]`
at `CHRISTMAS_LIST.md:167` — tier **D**. The variant on this page has the same literature and
*no* native propagator anywhere, which is exactly the gap tier C measures.

## Decomposition used here

**Generator value:** **none.** `grep -n 'explainall' 'explenation generator.ml'` (2026-09-21)
prints 15 emitting calls at lines 879–893 and the only scheduling one is line **881**,
`explainall [xbc] cumul "cata/cumulative.tex"`, over the value `cumul` at lines **810-812**.
That value is SCH-1, the unary resource (see "Read this" above).
**Emitted by:** nothing under this name.
**Spec:** [`decomps/cumulatives.md`](../decomps/cumulatives.md) — **read by this session**, 24 lines.

**Shape: `SCH-2` + modifier `M-mach`** (`decomps/_shapes-ext.md`): the sum at machine `k` and
time `t` ranges over `{ i : M_i = k }`. Spelled out:

- `B1_{i,t} ⇔ X_i ≥ t` — `rule1`, **BC**;
- `B2_{i,t} ⇔ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1}` — `rule3`, "task `i` is running at time `t`";
- `Σ_{i : M_i = k} r_i · B2_{i,t} ≤ b_k` — one weighted sum **per (machine, time point)**.

**The spec's own workaround is the most useful thing on this page and it is not obvious.** A
summation whose *extent* depends on a decision variable has no encoding (that is G14). But
`decomps/cumulatives.md` observes that an auxiliary-free reformulation is expressible **in the
existing schemas**: introduce `B3_{i,k,t} ⇔ (M_i = k) ∧ B2_{i,t}` by `rule3`, then sum `B3`
over `i` at fixed `(k,t)`. `M_i = k` is an ordinary arc-consistency literal on a user variable,
so **nothing leaks under D-0004**. The variable-determined extent becomes an ordinary conjunct,
and G14 is *traded*, not paid.

**What it is traded for is G16**, and that is why the trade does not close the entry: see
Status.

## Scope of this entry

**Events the generator was asked to explain:** **none under this name** — the generator was
never invoked for it, so there is no `%% generator diagnostics (W1-T3)` footer to quote.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**The events that *would* be asked** are the family's: `X_i ≥ t` and `X_i < t`, from the `xbc`
bounds-consistency global event (`explenation generator.ml:881` passes `[xbc]` for `cumul`).
The machine assignment adds `M_i = k` and `M_i ≠ k`, ordinary arc-consistency literals on a
user variable, so a complete entry would ask for those too and print rules concluding them.
Unlike `cumulative_opt`'s `Ex_i`, these need no new `var_name` constructor in principle — they
need an index family, which is the gap below.

## Generated rules

**None.** There is no `cata/cumulatives.tex`, so `grep -o '\\frac'` has no input. This is a different
zero from `regular`'s: there the generator ran and refused every branch over an undefined index
set; here it was never asked, because no decomposition value for this constraint is encodable.

## Status

**`nothing generated — blocked on G14`**

**The gap unique to this variant is `G14` — no summation over a variable-determined index set.**
`docs/DECOMP_FORMAT_NOTES.md` names `cumulatives` as the constraint that hit it, and
`decomps/cumulatives.md` gives the mechanism: `ind_set` and every `ind_op` are static, and
"nothing in the format has an extent that depends on a decision variable". The sum
`Σ_{i : M_i = k}` is exactly that.

**And then the spec hands back a workaround that makes G14 avoidable — at the price of `G16`,
which is not.** Reformulating as `B3_{i,k,t} ⇔ (M_i = k) ∧ B2_{i,t}` and summing `B3` over `i`
turns the variable extent into a `rule3` conjunct. But `B3` is indexed by **four** families:
task `i`, time `t`, machine `k`, and the value family the `M_i = k` reification consumes. And
`ind_fam` is the closed enum `FI | FT | FP | FR` with hardcoded printers `i`/`t`/`p`/`r`
(`decomps/cumulatives.md` cites "source l.38, l.373"), so a machine index "would have to print
as `p` or `r`" — colliding with a family already in use. That is **G16**, which
`docs/DECOMP_FORMAT_NOTES.md` records as hit by `regular`'s general form, with the note that
"§5/§6 exhaust" the enum.

**So the honest reading of this entry is: `G14` is the gap the constraint presents, `G16` is the
gap that survives the best known reformulation, and neither is optional.** *This is reasoning
over `decomps/cumulatives.md` and `docs/DECOMP_FORMAT_NOTES.md`, not a measurement* — no
four-family decomposition was written, and nothing was run.

**The number of gaps is also the finding about tier C here.** `cumulative` — tier D, a native
explaining propagator in Chuffed — is two gaps from TimeD. `cumulatives` has no native
propagator anywhere (`CHRISTMAS_LIST.md:168`: `decomp`) and is at least four, which is the gap
tier C is supposed to be measuring, pointing the opposite way from what "tier C ranks higher than
tier D" might suggest. Tier ranks *the size of the hole in the literature-plus-solver picture*,
never difficulty; `tools/mzn_coverage.py`'s own header says so ("It ranks the size of the gap,
not difficulty and not interest").

**The shared blockers are not a footnote.** Everything [`catalog/cumulative.md`](cumulative.md)
lists applies here unchanged, and each is load-bearing:

- **`G11`** — no weighted Boolean sum. `rule5/6/7` count occurrences with no coefficients, and
  `Σ_i r_i · B2_{i,t} ≤ c` is the line that makes a resource *cumulative* rather than unary.
  **E8** under D-0011, not E3: there is one sum per time point, so the
  `failwith "sommes multiples pas encore implémentés"` site (measured today at lines **355, 369,
  383**) is never reached.
- **`G15`** — no arithmetic relating variable values to indices. This is the one the validator
  reports mechanically on the shipped artifact as `UNPARSED: index equation offset: t'=t-d_{i}`,
  which is why [`cumulative.md`](cumulative.md) is `not validatable` rather than flagged.
- **`G1`** — a bare integer threshold cannot reach the printed rule, so the capacity `b` appears
  in no atom. `decomps/cumulative.md` calls this `X4`.
- **`G3`** — only variable-vs-domain-value comparisons, never variable-vs-variable, which the
  general form needs for variable durations and requirements.

Nothing here is validated, flagged or refuted. The 2026-09-21 `make validate` run
(**34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of
scope**) contains no line for this name.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.**

**The reason to state it separately from [`cumulative.md`](cumulative.md), rather than inherit
it, is that the base entry's one piece of good news does not transfer.** That entry's calibration
is the strongest positive statement in wave three, and it is conditional and specific: Schutt et
al.'s own **TimeD** decomposition is structurally the shape this generator consumes
(`rule1` → `rule3` → `rule5`), it needs only `G11` + `G15`, and the paper states (`QUOTED`,
§6.2, via C2) that TimeD and the global time-table propagator "have the same propagation
strength". So for `cumulative` the verdict is `out of reach` *by two numbered gaps*, not by
structure.

**For `cumulatives` that route is not established, and this entry declines to assume it.** Three
reasons, in decreasing order of how much they are this repo's business:

1. **No source here says anything about the multi-machine form.** `CHRISTMAS_LIST.md:168` says explicitly
   "no new literature", and `catalog/_literature/cumulative.md` is C2's reading of the
   `cumulative` papers. Extending §6.2's equivalence to the multi-machine form would be a claim about two
   papers nobody in this repo has read for that purpose — UNSOURCED, and therefore not written.
2. ****The workaround changes the decomposition, so it changes the object to be compared.** TimeD as C2 quotes it is a single-resource decomposition with no machine index; whether §6.2's strength equivalence survives one sum per (machine, time point) is a question about the paper, and nothing in this repo answers it.**
3. **The *global* window explanation is out of reach structurally, here as there.**
   [`cumulative.md`](cumulative.md) records it: the §6.2 global explanations quantify over a
   compulsory-part set and a chosen sequence of time points — run-time objects, out of reach for
   the same reason as [`gcc.md`](gcc.md)'s flow cut, and needing **E4** on top. That half is
   inherited and unchanged.

**Not `no published rule exists`** — a paper is cited on this row, by reference. **Not `weaker`
or `incomparable`** — both need a premise on this side, and there are zero generated rules.
`out of reach` is a first-class verdict (D-0013), not a failure to compare.

## Gaps

| gap | what it blocks here |
|---|---|
| **`G14`** | **the gap this constraint presents.** No summation over a variable-determined index set: `Σ_{i : M_i = k}` has an extent that depends on a decision variable and `ind_set`/`ind_op` are static. `X6` in `decomps/cumulatives.md` |
| **`G16`** | **the gap that survives the workaround.** `ind_fam` is the closed enum `FI \| FT \| FP \| FR` with hardcoded printers, and the `B3_{i,k,t}` reformulation needs four families at once. `X7` |
| `G11` | shared with `cumulative`: no weighted Boolean sum, `Σ r_i · B2_{i,t}`. **E8** (D-0011), one sum per (machine, time point), so the `failwith` site is never reached. `X5` |
| `G15` | shared: no arithmetic relating variable values to indices; the measured `UNPARSED: t'=t-d_{i}`. `X9` |
| `G1` | shared: the capacity reaches no printed atom — now once per machine. `X4` |
| `G3` | shared: no variable-vs-variable comparison. Sharper here, since `cumulatives`' `d`, `r` and `b` are all `var int` arrays in the signature |
| — | and beyond those, the **global** window argument is **E4**. See Calibration: `cumulative`'s TimeD escape route is **not** established for the multi-machine case |

Extensions: **E2 + E4** (`CHRISTMAS_LIST.md:168`), refined by `decomps/cumulatives.md` and D-0011 into
**E8** for the weights specifically (G11) and **E1** for nothing here — `cumulatives` needs no new family *name*, it needs a new family *slot* (G16).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

`decomps/cumulative.md`'s formulation is worth carrying over: gaps 1–3 make the constraint
*expressible*; **E4** makes it *good*. [`cumulative.md`](cumulative.md)'s calibration qualifies
the second half for `cumulative` via TimeD — **and, per Calibration above, that qualification is
not established for this variant.**

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `cumulatives` in
  `C literature + solver-decomposes`, ecodes `E2`, `E4`, `CHRISTMAS_LIST.md` line 168, section
  `6. Scheduling`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`,
  `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions this
  name.**
- `ls cata/` → 16 `.tex` files; `cumulatives.tex` is not among them.
- `grep -n 'explainall' 'explenation generator.ml'` → 15 calls, lines 879–893; the only
  scheduling one is **881**, `explainall [xbc] cumul "cata/cumulative.tex"`.
- `grep -n '^let cumul' 'explenation generator.ml'` → **810**. (Re-measured: `decomps/_shapes-ext.md`
  cites "generator l.680–682" for the same value — see the discrepancy note.)
- `grep -n 'sommes multiples' 'explenation generator.ml'` → lines **355, 369, 383**.
- `CHRISTMAS_LIST.md:167-168` read → the citations, the `as above` / `no new literature` cells,
  the solver columns and the `E2 + E4` route.
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `decomps/cumulatives.md` read → the signature quoted above, the `SCH-2 + M-mach` shape, the `B3_{i,k,t}` workaround, `X6`, `X7`, and the sentence that everything `cumulative.md` says about `X4`/`X5`/`X10` applies here "once per machine".
- `decomps/_shapes-ext.md` read → SCH-1, SCH-2 and the modifier definitions quoted in
  "Decomposition used here".
- `docs/DECOMP_FORMAT_NOTES.md` read → G1, G2, G3, G11, G14, G15, G16 and the consolidated
  wave-two numbering that maps `decomps/`'s `X`-labels onto them.
- `catalog/cumulative.md` read, not run → the "really `disjunctive`" lead, the `not validatable`
  status, the TimeD calibration and its two gaps. **No statement about either Schutt et al. paper
  originates in this file**; all of them are C2's, reached through that entry, and none is
  extended to this constraint.
- `tools/data/minizinc-2.10.1-globals.txt:46` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- ****The G14-traded-for-G16 reading and the tier-C observation are reasoning, labelled as such in
  place.** They rest on `decomps/cumulatives.md`'s stated workaround and `ind_fam`'s enum as that
  file and `docs/DECOMP_FORMAT_NOTES.md` describe them; no decomposition was written and no code
  was run.**

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/_shapes-ext.md` cites the shipped `cumul` value at "generator l.680–682".**
   Measured today: **810**.
2. **Two in-repo line numbers for the `failwith "sommes multiples"` site and both are wrong.**
   `docs/DECOMP_FORMAT_NOTES.md`: "generator lines 177-219"; `decomps/_shapes-ext.md`:
   "source l.320/334/348". Measured today: **355, 369, 383**.
3. **`decomps/cumulatives.md` cites `ind_fam` and its printers at "source l.38, l.373".** Not
   re-measured by this session, and flagged only because every other generator line number this
   session checked in `decomps/` had rotted. A reader should verify before quoting it.
