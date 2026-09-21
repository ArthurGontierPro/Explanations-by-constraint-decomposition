# `disjunctive_strict_opt`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `disjunctive_strict_opt`, and no
> claim of that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the
> catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` (shared row with `disjunctive`, `_strict`, `_opt`) |
| **Status** | `nothing generated — blocked on G2` |
| **Generated** | **0** rules. There is no `cata/disjunctive_strict_opt.tex` |
| **Validator** | out of scope: nothing of this name to validate |
| **Calibration** | **out of reach** — the published §6 explanations are indexed by a run-time compulsory-part set, and there is no generated rule on this side either |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `ls decomps/`, `python3 tools/mzn_coverage.py --rank --json` |

## Read this first: this is the four-way combination, and it is two modifiers, not a shape

`disjunctive_strict_opt` is `disjunctive` with **both** suffixes: zero-duration tasks are
strict, and each task carries an existence Boolean. In this project's vocabulary that is

> **S9** (`decomps/_shapes.md:226-238`) + the `_strict` boundary condition + modifier
> **M-opt** (`decomps/_shapes-ext.md:310-317`)

and **no new shape**. Two of its three parts are reviewed separately and this entry does not
re-derive them:

| part | entry | blocking gap |
|---|---|---|
| the unary resource itself | [`disjunctive`](disjunctive.md) | `G15`, `G1` (rules exist, `not validatable`) |
| the `d_i = 0` boundary | [`disjunctive_strict`](disjunctive_strict.md) | `G1` — a predicate on a duration constant |
| the existence Boolean `Ex_i` | [`disjunctive_opt`](disjunctive_opt.md) | `G2` — `var_name` has no free letter for it |

**The blockers are independent and both must close.** Neither gap subsumes the other: G1 is
about a constant that cannot reach a rule, G2 about a variable that cannot be named. The
status names **G2** because it is the one that blocks a *user-visible variable* from printing
at all, which under D-0004 is the harder failure; G1 is listed immediately beside it and is
equally binding.

**This constraint is also the one the family's own shorthand kept missing.**
`CHRISTMAS_LIST.md:169` records it, verbatim: `disjunctive_strict_opt` was "named explicitly
2026-09-18, W3-C — the `_strict`/`_opt` shorthand reaches each suffix separately but not their
four-way combination; same route". `decomps/` shows the same hole from the other side: it has
`disjunctive.md`, `disjunctive_opt.md` and `disjunctive_strict.md`, and **no
`disjunctive_strict_opt.md`** (`ls decomps/`, 2026-09-21). So of this session's fifteen
constraints, this is the only one with no spec file of any kind, and the reason is a naming
shorthand rather than a judgement that it needs none.

## Constraint

`disjunctive_strict_opt(array[int] of var int: s, array[int] of var int: d, array[int] of var bool: occ)`

As `disjunctive`, with zero-duration tasks forbidden from overlapping (the `_strict` reading of
`decomps/disjunctive_strict.md:3`) and with a Boolean per task saying whether it occurs at all
(the `_opt` reading of `decomps/disjunctive_opt.md:3`).

**Provenance of the signature:** not vendored in this repo, and **weaker than the other three
entries in this family.** `tools/data/minizinc-2.10.1-globals.txt:58` carries the *name* only;
this checkout holds no `.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21); and unlike its
three siblings there is **no `decomps/` spec to transcribe from**. The line above is this
entry's composition of the two sibling specs' prose, not a transcription of anything. Treat it
as the weakest line in this file.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:169`, literature cell, verbatim:

> implied by the cumulative papers (unary is the special case)

pointing at Schutt, Feydy, Stuckey, Wallace 2011 and Schutt, Feydy, Stuckey CPAIOR 2013
(`CHRISTMAS_LIST.md:167`).

**Rule shape:** the Constraints 2011 paper is sourced in
[`catalog/_literature/cumulative.md`](_literature/cumulative.md) and rendered, with C2's tags,
in [`catalog/disjunctive.md`](disjunctive.md#published-explanation). It is not repeated here.
**That file covers neither optional tasks nor a zero-duration case**, so there is nothing in
the repo's sourced literature that speaks to either suffix. No paper was fetched by this
session, and no statement about any paper's content is made here.

## Solver support

| | |
|---|---|
| Chuffed | native (`disjunctive.cpp`) |
| Geas | **`[G]`** present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:169`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers all four `disjunctive*` names, so this table is the family's, not this
name's specifically — worth stating for the one name that the row had to be amended to include.

## Decomposition used here

**Generator value:** none. The nearest is `cumul`, `explenation generator.ml:810-812`, which
has neither the strictness clause nor an existence family.
**Emitted by:** nothing under this name.
**Spec:** **none — this constraint has no `decomps/disjunctive_strict_opt.md`.** Its parts are
specified in `decomps/disjunctive.md`, `decomps/disjunctive_strict.md` and
`decomps/disjunctive_opt.md`.

The chain, if it could be written — and every line of it is a sibling entry's:

- **step 1, `rule1`** (BC) — `B1_{i,t} ⇔ X_i ≥ t`, unchanged from `disjunctive`.
- **step 2, `rule3`**, now **four** summands — `B2_{i,t} ⇔ Ex_i ∧ (strict overlap)`. The
  any-length summand branch (`explenation generator.ml:313-317`) takes four as readily as two,
  and `cumul` already exercises the multi-summand path at `:811`; so the arity is not the
  problem in either modifier.
- **step 3, `rule5`** — `Σ_i B2_{i,t} ≤ 1`, unweighted, because a unary resource has no
  weights.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_i ≥ t` / `X_i < t` (would be, from `xbc`) | — | **0** | not run: neither the `d_i = 0` clause (G1) nor the existence family (G2) is encodable |
| `Ex_i` (would be a third event) | — | **0** | not run: G2 blocks it as a conclusion as well as a premise — see [`disjunctive_opt`](disjunctive_opt.md#scope-of-this-entry) |

## Generated rules

**None.** There is no `cata/disjunctive_strict_opt.tex` (`ls cata/` → 16 files, none of this
name; 2026-09-21). The two rules in `cata/cumulative.tex` belong to the plain, non-strict,
non-optional sibling and are rendered in
[`catalog/disjunctive.md`](disjunctive.md#generated-rules).

## Status

**`nothing generated — blocked on G2`**

Nothing was generated. The gap number is G2 (the existence Boolean cannot be named) with
**G1 equally binding** (the `d_i = 0` predicate cannot be stated); the status legend takes one
number and the Gaps table carries both. Neither is a missing shape: S9 runs today, and the
multi-summand `rule3` both modifiers need is exercised by the shipped `cumul`.

**Two suffixes, two different kinds of gap, and that is the finding.** `_strict` fails on a
*constant* that cannot be seen (G1); `_opt` fails on a *variable* that cannot be named (G2).
They are not two instances of "the format is too small"; they are the two halves of what
`var_name`/`ind_const` were never designed to carry, and closing one leaves this entry exactly
as empty as before.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.**

Three reasons, inherited and not re-derived:

1. **Nothing on this side** — 0 generated rules, so no premise to place in an implication
   order.
2. **The published §6 explanations are indexed by run-time objects** — a compulsory-part set, a
   profile sequence, a chosen list of time points (`catalog/_literature/cumulative.md`,
   "Schema or per-propagation?", `QUOTED`). No index set here corresponds; reaching them is
   **E4**.
3. **The sourced paper covers neither suffix.** The `QUOTED` TimeD display has one Boolean per
   (task, time), no existence variable, and no zero-duration clause. So even the TimeD route —
   [`catalog/disjunctive.md`](disjunctive.md#calibration-w3-t5-d-0013)'s one piece of good news
   — has nothing to compare against here.

**Not compared on minimality.** The sourced paper proves nothing minimal (`QUOTED`, preprint
p.13, two open questions).

## Gaps

| gap | what it blocks here |
|---|---|
| `G2` | **binding.** `var_name` is a closed enum (`explenation generator.ml:3`) with no constructor for an optionality flag; `Ex_i` is user-visible, so D-0004 requires it to print. See [`disjunctive_opt`](disjunctive_opt.md) |
| `G1` | **equally binding.** No integer constant reaches a rule or a guard, so `d_i = 0` cannot be tested — *and*, separately, the sum's bound `1` reaches no atom. See [`disjunctive_strict`](disjunctive_strict.md) |
| `G15` | inherited from S9 — `t' = t − d_i` is the validator's measured `UNPARSED`, so even with G1 and G2 closed the entry would be `not validatable`, like `cumulative` |
| `G3` | **variable-duration form only** (`CHRISTMAS_LIST.md:169`) |
| — | **not a gap:** the four-summand `rule3`. Checked against the source; recorded so nobody re-derives it as a blocker |

Extensions: **E2** per `CHRISTMAS_LIST.md:169` ("same route" as the rest of the family).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none of this name. `ls decomps/` → 54 files, **no
  `disjunctive_strict_opt.md`**; the basis for the "no spec" statements above.
- `python3 tools/mzn_coverage.py --rank --json` → tier `D literature + solver-native`, ecodes
  `["E2"]`, `CHRISTMAS_LIST.md` line 169, section `6. Scheduling`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:3` (`var_name`), `:7`/`:466` (`ind_const` and
  its printer), `:313-317` (`rule3`'s any-length summand branch), `:810-812` and `:811`
  (`cumul`, and its existing multi-summand step).
- `CHRISTMAS_LIST.md:169`, `:167`, `:106-109` read → the W3-C amendment quoted above, the
  literature and solver cells, the legend.
- `catalog/_literature/cumulative.md` read, **not fetched** → that TimeD has no existence
  variable and no zero-duration clause; C2's tags carried across.
- `decomps/disjunctive.md`, `disjunctive_strict.md`, `disjunctive_opt.md`,
  `decomps/_shapes-ext.md:238-271,310-317`, `decomps/_shapes.md:226-238` read → the three
  parts, S9's instance list, the modifier definitions.
- The composed signature is **this entry's composition of two specs' prose**, flagged in place.
