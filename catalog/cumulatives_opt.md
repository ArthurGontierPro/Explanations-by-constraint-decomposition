# `cumulatives_opt`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `cumulatives_opt`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E2`, `E4`; `CHRISTMAS_LIST.md:168`, section `6. Scheduling` |
| **Status** | `nothing generated — blocked on G14` — **and on everything that already blocks `cumulative`**: `G11`, `G15`, `G1`, `G3`. See Status |
| **Generated** | **0** — there is no `cata/cumulatives_opt.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears in no line of the 2026-09-21 run |
| **Calibration** | **out of reach** — and, unlike [`cumulative.md`](cumulative.md), *not* rescued by the TimeD route: see Calibration |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json`, and reads of `explenation generator.ml`, `CHRISTMAS_LIST.md:167-168`, `decomps/cumulatives.md` and `catalog/cumulative.md` |

## Read this before the rest of the entry

**Two things are true at once here and an entry that states only one of them misleads.**

1. **Nothing is generated for this name.** There is no `cata/cumulatives_opt.tex` and no decomposition
   value in `explenation generator.ml` for it.
2. **The file that looks closest, `cata/cumulative.tex`, is not `cumulative` either.**
   [`catalog/cumulative.md`](cumulative.md) leads with it: the shipped chain's final step is a
   single *unweighted* Boolean sum with an *implicit* bound of 1 (`rule5`,
   `explenation generator.ml:812`), which is a **unary** resource. There are no resource
   requirements `r_i` and no capacity anywhere in it. So it is `disjunctive` with constant
   durations, filed under `cumulative`'s name.

Put together: this entry has no artifact of its own, **and** it must not borrow the one next
door, which is two steps away rather than one. What it does establish is the exact distance —
which constructs `cumulatives_opt` needs that the format has no encoding for, each pinned to a numbered
gap.

## Constraint

`cumulatives_opt(array[int] of var opt int: s, array[int] of var int: d, array[int] of var int: r, array[int] of var int: m, array[int] of var int: b)`

`cumulatives` over **optional** tasks: tasks are assigned to machines, each machine's capacity
is respected, and an absent task consumes nothing on any machine.

**Provenance of the signature:** **not vendored in this repo, and not specified here either.**
`tools/data/minizinc-2.10.1-globals.txt:47` carries the name only, and unlike its two siblings
this constraint has **no `decomps/` spec at all**. The line above is **recall**, marked as such,
assembled from `decomps/cumulatives.md`'s signature plus `decomps/cumulative_opt.md`'s one-line
"with optional tasks". Treat it as a reconstruction, not a citation.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:168`'s literature cell reads **`as above`**, pointing at the
`cumulative` row one line up, `CHRISTMAS_LIST.md:167`, which cites two papers:

- **Schutt, Feydy, Stuckey, Wallace 2011**, *Explaining the cumulative propagator*,
  Constraints 16(3):250–282 — time-table filtering with window-based explanations;
- **Schutt, Feydy, Stuckey, CPAIOR 2013**, *Explaining time-table-edge-finding propagation*
  (arXiv:1208.3015).

The row adds, of `cumulatives`/`cumulative_opt`/`cumulatives_opt`, "same route as `cumulatives`,
**no new literature**" — so the citation is inherited, and **no paper sourced in this repo is
about the multi-machine or optional forms**.

**Rule shape:** sourced into [`catalog/_literature/cumulative.md`](_literature/cumulative.md) by
session C2, and rendered in [`catalog/cumulative.md`](cumulative.md). **Nothing is restated
here.** In particular the TimeD decomposition C2 quotes, and the §6.2 sentence equating its
propagation strength with the global propagator's, are statements about **`cumulative`**; this
entry does not extend either to the multi-machine or optional forms, because no source in this repo does. Anything of
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
**Spec:** **none** — there is no `decomps/cumulatives_opt.md`. The two specs that between them cover it are
[`decomps/cumulatives.md`](../decomps/cumulatives.md) (`SCH-2 + M-mach`) and
[`decomps/cumulative_opt.md`](../decomps/cumulative_opt.md) (`SCH-2 + M-opt`), **both read by this
session**.

**This name exists because of a naming accident that the list itself records**, and it is worth
repeating here because it is the reason the spec is missing. `CHRISTMAS_LIST.md:168` notes that
`cumulatives_opt` was "added 2026-09-18, W3-C — the `_strict`/`_opt`-style shorthand used
elsewhere in this table does not compose past two suffixes, so the four-way combination was
silently missing". The same shorthand gap is recorded one row down for `disjunctive_strict_opt`.
`decomps/` was written before that correction and still has no file for this name.

**Shape: `SCH-2` + **both** modifiers, `M-mach` and `M-opt`.** Composing the two specs:

- `B1_{i,t} ⇔ X_i ≥ t` — `rule1`, **BC**;
- `B2_{i,t} ⇔ Ex_i ∧ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1}` — `rule3` with the optionality conjunct;
- `Σ_{i : M_i = k} r_i · B2_{i,t} ≤ b_k` — one weighted sum per (machine, time point).

**This composition is R2's, not a spec's**, and it is written down so it can be checked or
replaced rather than re-derived. The only question it raises that neither parent spec answers is
whether the two modifiers interact, and on this reading they do not: `M-opt` adds a conjunct
inside `B2`, `M-mach` changes the extent of the sum over `B2`, and neither touches the other's
construct. **That is an argument, not a measurement.**

## Scope of this entry

**Events the generator was asked to explain:** **none under this name** — the generator was
never invoked for it, so there is no `%% generator diagnostics (W1-T3)` footer to quote.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**The events that *would* be asked** are the family's: `X_i ≥ t` and `X_i < t`, from the `xbc`
bounds-consistency global event (`explenation generator.ml:881` passes `[xbc]` for `cumul`).
Both modifiers contribute: `Ex_i`/`¬Ex_i` from optionality and `M_i = k`/`M_i ≠ k` from the
machine assignment, all four on variables the user wrote. A complete entry would ask for six
events where [`cumulative.md`](cumulative.md)'s artifact was asked for two.

## Generated rules

**None.** There is no `cata/cumulatives_opt.tex`, so `grep -o '\\frac'` has no input. This is a different
zero from `regular`'s: there the generator ran and refused every branch over an undefined index
set; here it was never asked, because no decomposition value for this constraint is encodable.

## Status

**`nothing generated — blocked on G14`**

**This variant inherits both siblings' gaps and adds none of its own.** `G14` is named as the
status gap because it is the one that blocks hardest; the full picture is:

- **`G14`**, from [`cumulatives`](cumulatives.md) — no summation over a variable-determined index
  set. `decomps/cumulatives.md`'s `B3_{i,k,t}` reformulation trades it for **`G16`** (`ind_fam` is
  the closed enum `FI | FT | FP | FR` and the reformulation needs four families), so one of the
  two must be paid.
- **`G2`**, from [`cumulative_opt`](cumulative_opt.md) — `var_name` has no constructor for an
  optionality family `Ex_i`, and `B` prints as the literal `"ERROR B "` (`CLAUDE.md`, Traps).
- the four shared with `cumulative`, below.

**Do the two modifiers compose without extra cost?** On this entry's reading, yes — `M-opt` adds
a conjunct inside `B2` and `M-mach` changes the extent of the sum over `B2`, so neither touches
the other's construct. **But this is exactly where a naming shorthand already failed once**, and
that is the reason to say it explicitly rather than leave it implied. `CHRISTMAS_LIST.md:168`
records that `cumulatives_opt` was missing from the list entirely until 2026-09-18 because the
`_strict`/`_opt` shorthand "does not compose past two suffixes". A composition assumed rather
than checked is how that happened. **So: composition is R2's argument, labelled as an argument,
and no `decomps/cumulatives_opt.md` exists to check it against.** `docs/ROADMAP.md` would be the
place to book writing one; this session does not own it.

**One interaction that is worth naming even under "they compose".** `G2` is about a *name* and
`G16` is about a *slot*: `Ex_i` needs a `var_name` constructor, the machine index needs an
`ind_fam` constructor. Both are closed enums, both are described in this repo as exhausted —
`docs/DECOMP_FORMAT_NOTES.md` says of `ind_fam` that "§5/§6 exhaust it". This is the constraint in
the corpus that needs a new constructor in *two different* closed enums at once, which is a
statement about **E1** ("open `var_name`") being necessary here in both of its senses. *Reasoning,
not a measurement.*

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

**For `cumulatives_opt` that route is not established, and this entry declines to assume it.** Three
reasons, in decreasing order of how much they are this repo's business:

1. **No source here says anything about the multi-machine or optional forms.** `CHRISTMAS_LIST.md:168` says explicitly
   "no new literature", and `catalog/_literature/cumulative.md` is C2's reading of the
   `cumulative` papers. Extending §6.2's equivalence to the multi-machine or optional forms would be a claim about two
   papers nobody in this repo has read for that purpose — UNSOURCED, and therefore not written.
2. ****Both modifiers change the decomposition, so they change the object to be compared** — and this variant applies both. TimeD as C2 quotes it has neither an optionality conjunct nor a machine index; a TimeD for optional multi-machine tasks is a different decomposition, and whether §6.2's strength equivalence survives is a question about the paper that nothing in this repo answers.**
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
| **`G14`** | **named as the status gap.** No summation over a variable-determined index set, `Σ_{i : M_i = k}`. Inherited from [`cumulatives`](cumulatives.md) |
| **`G16`** | what `decomps/cumulatives.md`'s `B3_{i,k,t}` reformulation trades G14 *for*: `ind_fam` is the closed enum `FI \| FT \| FP \| FR` and the reformulation needs four families |
| **`G2`** | inherited from [`cumulative_opt`](cumulative_opt.md): `var_name` has no slot for the optionality family `Ex_i`, and `B` prints as the literal `"ERROR B "` (`CLAUDE.md`, Traps) |
| `G11` | shared with `cumulative`: no weighted Boolean sum. **E8** (D-0011) |
| `G15` | shared: no arithmetic relating variable values to indices; the measured `UNPARSED: t'=t-d_{i}` |
| `G1` | shared: the capacity reaches no printed atom, now once per machine |
| `G3` | shared: no variable-vs-variable comparison, and `d`, `r`, `b` are all variable arrays here |
| — | and beyond those, the **global** window argument is **E4**. `cumulative`'s TimeD escape route is **not** established for either modifier, let alone both |

Extensions: **E2 + E4** (`CHRISTMAS_LIST.md:168`), refined by `decomps/cumulatives.md` and D-0011 into
**E8** for the weights specifically (G11) and **E1** for the `Ex_i` family name (G2) — and, uniquely in this corpus, **E1 in both its senses at once**: a new `var_name` constructor *and* a new `ind_fam` constructor (G16).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

`decomps/cumulative.md`'s formulation is worth carrying over: gaps 1–3 make the constraint
*expressible*; **E4** makes it *good*. [`cumulative.md`](cumulative.md)'s calibration qualifies
the second half for `cumulative` via TimeD — **and, per Calibration above, that qualification is
not established for this variant.**

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `cumulatives_opt` in
  `C literature + solver-decomposes`, ecodes `E2`, `E4`, `CHRISTMAS_LIST.md` line 168, section
  `6. Scheduling`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`,
  `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions this
  name.**
- `ls cata/` → 16 `.tex` files; `cumulatives_opt.tex` is not among them.
- `grep -n 'explainall' 'explenation generator.ml'` → 15 calls, lines 879–893; the only
  scheduling one is **881**, `explainall [xbc] cumul "cata/cumulative.tex"`.
- `grep -n '^let cumul' 'explenation generator.ml'` → **810**. (Re-measured: `decomps/_shapes-ext.md`
  cites "generator l.680–682" for the same value — see the discrepancy note.)
- `grep -n 'sommes multiples' 'explenation generator.ml'` → lines **355, 369, 383**.
- `CHRISTMAS_LIST.md:167-168` read → the citations, the `as above` / `no new literature` cells,
  the solver columns and the `E2 + E4` route.
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `decomps/cumulatives.md` read → the `SCH-2 + M-mach` shape, the `B3_{i,k,t}` workaround, `X6`/`X7`; and `decomps/cumulative_opt.md` → the `SCH-2 + M-opt` shape and the `Ex_i` conjunct. **There is no spec for this name**; the composition above is this session's.
- `decomps/_shapes-ext.md` read → SCH-1, SCH-2 and the modifier definitions quoted in
  "Decomposition used here".
- `docs/DECOMP_FORMAT_NOTES.md` read → G1, G2, G3, G11, G14, G15, G16 and the consolidated
  wave-two numbering that maps `decomps/`'s `X`-labels onto them.
- `catalog/cumulative.md` read, not run → the "really `disjunctive`" lead, the `not validatable`
  status, the TimeD calibration and its two gaps. **No statement about either Schutt et al. paper
  originates in this file**; all of them are C2's, reached through that entry, and none is
  extended to this constraint.
- `tools/data/minizinc-2.10.1-globals.txt:47` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- ****The composition of the two modifiers, the claim that they do not interact, and the
  two-closed-enums observation are all R2's reasoning, labelled as such in place.** There is no
  `decomps/cumulatives_opt.md` to check them against; they are built from the two parent specs and
  from `docs/DECOMP_FORMAT_NOTES.md`. No code was run and no decomposition was written.**

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **There is no `decomps/cumulatives_opt.md`.** Its two siblings have specs; the four-way
   suffix combination does not, for the same shorthand reason that kept the name out of
   `CHRISTMAS_LIST.md` until 2026-09-18 (W3-C). The composition in this entry is R2's and is
   labelled as such. **Reported, not written** — `decomps/` is not this session's.
2. **`decomps/_shapes-ext.md`'s `M-opt` and `M-mach` entries list their instantiating constraints
   and neither names `cumulatives_opt`.** `M-opt` names `disjunctive_opt`, `cumulative_opt`;
   `M-mach` names `cumulatives`. The four-way combination is absent from the shapes file too.
3. **`decomps/_shapes-ext.md` cites the shipped `cumul` value at "generator l.680–682".**
   Measured today: **810**.
4. **Two in-repo line numbers for the `failwith "sommes multiples"` site and both are wrong.**
   `docs/DECOMP_FORMAT_NOTES.md`: "generator lines 177-219"; `decomps/_shapes-ext.md`:
   "source l.320/334/348". Measured today: **355, 369, 383**.
