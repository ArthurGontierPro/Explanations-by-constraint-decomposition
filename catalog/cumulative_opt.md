# `cumulative_opt`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `cumulative_opt`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E2`, `E4`; `CHRISTMAS_LIST.md:168`, section `6. Scheduling` |
| **Status** | `nothing generated — blocked on G2` — **and on everything that already blocks `cumulative`**: `G11`, `G15`, `G1`, `G3`. See Status |
| **Generated** | **0** — there is no `cata/cumulative_opt.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears in no line of the 2026-09-21 run |
| **Calibration** | **out of reach** — and, unlike [`cumulative.md`](cumulative.md), *not* rescued by the TimeD route: see Calibration |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json`, and reads of `explenation generator.ml`, `CHRISTMAS_LIST.md:167-168`, `decomps/cumulative_opt.md` and `catalog/cumulative.md` |

## Read this before the rest of the entry

**Two things are true at once here and an entry that states only one of them misleads.**

1. **Nothing is generated for this name.** There is no `cata/cumulative_opt.tex` and no decomposition
   value in `explenation generator.ml` for it.
2. **The file that looks closest, `cata/cumulative.tex`, is not `cumulative` either.**
   [`catalog/cumulative.md`](cumulative.md) leads with it: the shipped chain's final step is a
   single *unweighted* Boolean sum with an *implicit* bound of 1 (`rule5`,
   `explenation generator.ml:812`), which is a **unary** resource. There are no resource
   requirements `r_i` and no capacity anywhere in it. So it is `disjunctive` with constant
   durations, filed under `cumulative`'s name.

Put together: this entry has no artifact of its own, **and** it must not borrow the one next
door, which is two steps away rather than one. What it does establish is the exact distance —
which constructs `cumulative_opt` needs that the format has no encoding for, each pinned to a numbered
gap.

## Constraint

`cumulative_opt(array[int] of var opt int: s, array[int] of var int: d, array[int] of var int: r, var int: b)`

`cumulative` over **optional** tasks: a task that is absent consumes no resource and imposes no
overlap. At every time point the total requirement of the *present* running tasks is at most `b`.

**Provenance of the signature:** **not vendored in this repo** — `tools/data/minizinc-2.10.1-globals.txt:45` carries the name
only. The line above is **recall**, marked as such, and follows the shape
[`cumulative.md`](cumulative.md) records for the base. What *is* in-repo is
`decomps/cumulative_opt.md`'s one-line signature note: "As `cumulative`, with optional tasks."

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:168`'s literature cell reads **`as above`**, pointing at the
`cumulative` row one line up, `CHRISTMAS_LIST.md:167`, which cites two papers:

- **Schutt, Feydy, Stuckey, Wallace 2011**, *Explaining the cumulative propagator*,
  Constraints 16(3):250–282 — time-table filtering with window-based explanations;
- **Schutt, Feydy, Stuckey, CPAIOR 2013**, *Explaining time-table-edge-finding propagation*
  (arXiv:1208.3015).

The row adds, of `cumulatives`/`cumulative_opt`/`cumulatives_opt`, "same route as `cumulatives`,
**no new literature**" — so the citation is inherited, and **no paper sourced in this repo is
about optional tasks**.

**Rule shape:** sourced into [`catalog/_literature/cumulative.md`](_literature/cumulative.md) by
session C2, and rendered in [`catalog/cumulative.md`](cumulative.md). **Nothing is restated
here.** In particular the TimeD decomposition C2 quotes, and the §6.2 sentence equating its
propagation strength with the global propagator's, are statements about **`cumulative`**; this
entry does not extend either to optional tasks, because no source in this repo does. Anything of
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
**Spec:** [`decomps/cumulative_opt.md`](../decomps/cumulative_opt.md) — **read by this session**, 10 lines.

**Shape: `SCH-2` + modifier `M-opt`** (`decomps/_shapes-ext.md`). The spec is explicit that this
"differs from `cumulative` only by the `Ex_i` conjunct in `B2_{i,t}`, exactly as
`disjunctive_opt` differs from `disjunctive`". Spelled out from `_shapes-ext.md`'s SCH-1/SCH-2
and the `M-opt` modifier:

- `B1_{i,t} ⇔ X_i ≥ t` — `rule1`, **BC** (the one family in the section that is a bounds
  decomposition rather than an arc-consistency one);
- `B2_{i,t} ⇔ Ex_i ∧ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1}` — "task `i` is present *and* running at
  time `t`", `rule3` over three `Decomp_devent`s;
- `Σ_{i} r_i · B2_{i,t} ≤ b` — the weighted sum, one per time point.

**The `M-opt` modifier itself is cheap and the format almost has it.** `rule3` already takes a
three-element `Decomp_devent` list, so the *schema* for the extra conjunct is **E0** — nothing
new. And `Ex_i` is a variable the user wrote, so it leaks into premises **legitimately** under
D-0004, which is not true of every auxiliary in this corpus. What it lacks is a *name*: see
Status.

## Scope of this entry

**Events the generator was asked to explain:** **none under this name** — the generator was
never invoked for it, so there is no `%% generator diagnostics (W1-T3)` footer to quote.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**The events that *would* be asked** are the family's: `X_i ≥ t` and `X_i < t`, from the `xbc`
bounds-consistency global event (`explenation generator.ml:881` passes `[xbc]` for `cumul`).
Optional tasks add one more, and it is a user-visible variable rather than an auxiliary:
`Ex_i` — "task `i` is present" — appears in the MiniZinc signature, so a complete entry would
ask for `Ex_i` and `¬Ex_i` too, and print rules concluding them. There is no `var_name`
constructor to carry it (G2, below), so today the question cannot even be posed.

## Generated rules

**None.** There is no `cata/cumulative_opt.tex`, so `grep -o '\\frac'` has no input. This is a different
zero from `regular`'s: there the generator ran and refused every branch over an undefined index
set; here it was never asked, because no decomposition value for this constraint is encodable.

## Status

**`nothing generated — blocked on G2`**

**The gap unique to this variant is `G2`, and it is a naming gap rather than a reasoning gap.**
`decomps/cumulative_opt.md` prices the `Ex_i` conjunct at **E1** for exactly this reason, and
`docs/DECOMP_FORMAT_NOTES.md`'s G2 states the mechanism: `var_name` is the closed variant
`X | B of int | T | I | V | N | O` and none of its constructors means "this constraint's own
optionality flag". `_shapes-ext.md`'s `M-opt` entry adds the consequence in one clause: reusing
`O` "borrows `global_cardinality`'s printed letter".

**Why that is worse than cosmetic in this project specifically.** `CLAUDE.md`'s Traps section
records that `var_name`'s `B` prints as the literal string `"ERROR B "` (generator l.399, l.428)
and that it is *printed*, not raised — no shipped entry triggers it only because every `B` there
resolves to a `Global_devent` first. An optionality family is precisely the kind of
accumulated-state auxiliary that would surface it. So G2 is not "pick a letter"; it is the
difference between a rule about `Ex_i` and a `.tex` file with an error string in it.

**But G2 is the cheapest thing on this page, and saying so is the point of the entry.** It buys
one enum constructor and one printer case. The constructs that actually stand between this method
and `cumulative_opt` are the four it shares with `cumulative`, listed next, and `G11` and `G15`
are the two that [`cumulative.md`](cumulative.md)'s calibration identifies as separating the
generator from Schutt et al.'s own TimeD decomposition.

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

**For `cumulative_opt` that route is not established, and this entry declines to assume it.** Three
reasons, in decreasing order of how much they are this repo's business:

1. **No source here says anything about optional tasks.** `CHRISTMAS_LIST.md:168` says explicitly
   "no new literature", and `catalog/_literature/cumulative.md` is C2's reading of the
   `cumulative` papers. Extending §6.2's equivalence to optional tasks would be a claim about two
   papers nobody in this repo has read for that purpose — UNSOURCED, and therefore not written.
2. ****The `Ex_i` conjunct changes the decomposition, so it changes the object to be compared.** TimeD as C2 quotes it has no optionality conjunct; a TimeD-for-optional-tasks is a different decomposition, and whether the paper's strength equivalence survives the change is a question about the paper, not about this repo.**
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
| **`G2`** | **the one unique to this variant.** `var_name` is a closed variant with no slot for a constraint's own parameter, so the optionality family `Ex_i` cannot be named — and `B` prints as the literal `"ERROR B "` (`CLAUDE.md`, Traps; generator l.399, l.428). `decomps/cumulative_opt.md` prices it **E1** |
| `G11` | shared with `cumulative`: no weighted Boolean sum. `Σ_i r_i · B2_{i,t} ≤ b` has no encoding. **E8** (D-0011), *not* E3 — one sum per time point, so the `failwith` site is never reached. `X5` in `decomps/cumulative.md` |
| `G15` | shared: no arithmetic relating variable values to indices. The measured `UNPARSED: t'=t-d_{i}`. `X9` |
| `G1` | shared: the capacity `b` reaches no printed atom. `X4` |
| `G3` | shared: no variable-vs-variable comparison, needed for variable durations and requirements |
| — | and beyond all of those, the **global** window/subset argument is **E4**. But see Calibration: for `cumulative` the paper's own TimeD needs only G11 + G15 — **and that result is not established for the optional case** |

Extensions: **E2 + E4** (`CHRISTMAS_LIST.md:168`), refined by `decomps/cumulative_opt.md` and D-0011 into
**E8** for the weights specifically (G11) and **E1** for the `Ex_i` family name (G2).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

`decomps/cumulative.md`'s formulation is worth carrying over: gaps 1–3 make the constraint
*expressible*; **E4** makes it *good*. [`cumulative.md`](cumulative.md)'s calibration qualifies
the second half for `cumulative` via TimeD — **and, per Calibration above, that qualification is
not established for this variant.**

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `cumulative_opt` in
  `C literature + solver-decomposes`, ecodes `E2`, `E4`, `CHRISTMAS_LIST.md` line 168, section
  `6. Scheduling`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`,
  `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions this
  name.**
- `ls cata/` → 16 `.tex` files; `cumulative_opt.tex` is not among them.
- `grep -n 'explainall' 'explenation generator.ml'` → 15 calls, lines 879–893; the only
  scheduling one is **881**, `explainall [xbc] cumul "cata/cumulative.tex"`.
- `grep -n '^let cumul' 'explenation generator.ml'` → **810**. (Re-measured: `decomps/_shapes-ext.md`
  cites "generator l.680–682" for the same value — see the discrepancy note.)
- `grep -n 'sommes multiples' 'explenation generator.ml'` → lines **355, 369, 383**.
- `CHRISTMAS_LIST.md:167-168` read → the citations, the `as above` / `no new literature` cells,
  the solver columns and the `E2 + E4` route.
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `decomps/cumulative_opt.md` read → the `SCH-2 + M-opt` shape, the "differs from `cumulative` only by the `Ex_i` conjunct" sentence, the `E2 + E4` plus `E1`/G2 pricing, and `X4`/`X5`.
- `decomps/_shapes-ext.md` read → SCH-1, SCH-2 and the modifier definitions quoted in
  "Decomposition used here".
- `docs/DECOMP_FORMAT_NOTES.md` read → G1, G2, G3, G11, G14, G15, G16 and the consolidated
  wave-two numbering that maps `decomps/`'s `X`-labels onto them.
- `catalog/cumulative.md` read, not run → the "really `disjunctive`" lead, the `not validatable`
  status, the TimeD calibration and its two gaps. **No statement about either Schutt et al. paper
  originates in this file**; all of them are C2's, reached through that entry, and none is
  extended to this constraint.
- `tools/data/minizinc-2.10.1-globals.txt:45` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- ****The reading that G2 is "the cheapest thing on this page", and the connection to the
  `"ERROR B "` trap, are reasoning, labelled as such in place.** They rest on
  `docs/DECOMP_FORMAT_NOTES.md`'s G2, `decomps/_shapes-ext.md`'s `M-opt` entry and `CLAUDE.md`'s
  Traps section; no code was run and no rule was generated.**

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/_shapes-ext.md` cites the shipped `cumul` value at "generator l.680–682".**
   Measured today with `grep -n '^let cumul'`: **810**. [`catalog/cumulative.md`](cumulative.md)
   already carries the corrected number; the spec file does not.
2. **Two in-repo line numbers for the `failwith "sommes multiples pas encore implémentés"` site
   and both are wrong.** `docs/DECOMP_FORMAT_NOTES.md` says "generator lines 177-219";
   `decomps/_shapes-ext.md` says "source l.320/334/348". Measured today: **355, 369, 383**.
3. **`decomps/cumulative_opt.md` names gaps `X4` and `X5` in `decomps/`'s own numbering.** The
   consolidated wave-two list in `docs/DECOMP_FORMAT_NOTES.md` maps ext `X5` → **G11** and
   `X9` → **G15**, but `X4` (the capacity never printing) has no row in the consolidated table
   under that label; it is **G1** by its content. Recorded because a reader following `X4`
   forward will not find it.
