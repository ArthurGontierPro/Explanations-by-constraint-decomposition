# `disjunctive_opt`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `disjunctive_opt`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` (shared row with `disjunctive`, `_strict`, `disjunctive_strict_opt`) |
| **Status** | `nothing generated — blocked on G2` |
| **Generated** | **0** rules. There is no `cata/disjunctive_opt.tex` |
| **Validator** | out of scope: nothing of this name to validate |
| **Calibration** | **out of reach** — the published §6 explanations are indexed by a run-time compulsory-part set, and there is no generated rule on this side either |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Read this first: the schema is not the blocker — the *name* is

`disjunctive_opt` is `disjunctive` plus an array of Booleans saying which tasks actually occur.
In shape terms that is **S9 + modifier M-opt**, and a modifier is explicitly "not a shape of
its own" (`decomps/_shapes.md:44-47`, `decomps/_shapes-ext.md:310-317`). The modifier adds one
conjunct:

```
B2_{i,t}  ⇔  Ex_i  ∧  B1_{i,t−d_i+1}  ∧  ¬B1_{i,t+1}
```

— a three-summand `rule3` instead of a two-summand one.

**The three-summand `rule3` is not hypothetical and this session checked it rather than
assuming it.** `rule3`'s multi-element branch (`explenation generator.ml:313-317`,
`| _ -> EXAND (e, fel del e de c dec ch)`) takes a summand list of any length, and the shipped
`cumul` value already exercises it: its step 2 carries **two** `Decomp_devent`s plus the
reified one (`explenation generator.ml:811`), so the `dee::[]` single-summand fast path is not
the one that runs. Adding `Ex_i` makes it three. **The schema is E0 and would run.**

What stops the entry is that `Ex_i` **cannot be named**. `var_name` is the closed variant
`X | B of int | T | I | V | N | O` (`explenation generator.ml:3`) and none of its constructors
means "this constraint's own optionality flag". The nearest free letter, `O`, already prints as
`global_cardinality`'s occurrence variable in the LaTeX printer (`printvartex`,
`explenation generator.ml:522`, `| O -> "O"^printglobal_eventtex v`). Reusing it would put
`gcc`'s printed letter into a scheduling rule. That is **G2**.

**And a defect found while checking that, which appears to be unrecorded.** The *plain-text*
printer disagrees with the LaTeX one about `O`: `printevent_var`
(`explenation generator.ml:493`) is `| O -> "   X"^printglobal_event v` — it renders the
occurrence variable as the letter **`X`**, i.e. as one of the user's decision variables. The
LaTeX printer at `:522` renders it as `O`. **No shipped `cata/*.tex` is affected**, because
every entry is written through the LaTeX path (`printfraqtex`, `:529-531`); the plain-text path is
reached by `explain` (`:877`) and prints to stdout. This is the same class as `CLAUDE.md`'s
`printind_name_list` trap — a plain-text-path-only rendering bug — and this session found no
record of it in `docs/`, `decomps/` or `CLAUDE.md`. Recorded here because it is exactly the
letter this entry would have to borrow.

And `Ex_i` cannot be routed round as an ordinary auxiliary either, because it is **not** an
auxiliary: the user writes it in the MiniZinc signature, so under D-0004 it *must* appear in
the explanation. `decomps/disjunctive_opt.md:8-11` puts it exactly right — it "leaks
legitimately".

## Constraint

`disjunctive_opt(array[int] of var int: s, array[int] of var int: d, array[int] of var bool: occ)`

As `disjunctive`, with a Boolean per task saying whether that task occurs at all; absent tasks
constrain nothing.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:56` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/disjunctive_opt.md:3`
describes the signature in prose ("as `disjunctive`, with an array of Booleans saying which
tasks actually occur") without giving the MiniZinc argument list; **the third argument's name
and type above are this entry's rendering of that prose, not a transcription of a spec, and
should be treated as the weakest line in this file.**

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:169`, literature cell, verbatim:

> implied by the cumulative papers (unary is the special case)

pointing at Schutt, Feydy, Stuckey, Wallace 2011 and Schutt, Feydy, Stuckey CPAIOR 2013
(`CHRISTMAS_LIST.md:167`).

**Rule shape:** the Constraints 2011 paper is sourced in
[`catalog/_literature/cumulative.md`](_literature/cumulative.md) and rendered, with C2's tags,
in [`catalog/disjunctive.md`](disjunctive.md#published-explanation). **Nothing in that file
covers optional tasks**, and this entry states nothing about optional-task explanations from
any paper. No paper was fetched by this session.

## Solver support

| | |
|---|---|
| Chuffed | native (`disjunctive.cpp`) |
| Geas | **`[G]`** present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:169`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers all four `disjunctive*` names, so this table is the family's.

## Decomposition used here

**Generator value:** none. The nearest is `cumul`, `explenation generator.ml:810-812`, which
has no existence family.
**Emitted by:** nothing under this name.
**Spec:** `decomps/disjunctive_opt.md`; shape **SCH-1 + M-opt**
(`decomps/_shapes-ext.md:238-271` and `:310-317`), renumbered **S9 + M-opt** in
`decomps/_shapes.md:40` and `:44-47`, which lists `disjunctive_opt` as one of S9's three
instances.

The chain, if it could be written:

- **step 1, `rule1`** (BC) — `B1_{i,t} ⇔ X_i ≥ t`, unchanged from `disjunctive`.
- **step 2, `rule3`**, three summands — `B2_{i,t} ⇔ Ex_i ∧ (overlap)`. Runs today as a schema;
  cannot be *named* today (G2).
- **step 3, `rule5`** — `Σ_i B2_{i,t} ≤ 1`, unchanged, and unweighted for the same reason as
  `disjunctive`: a unary resource has no weights.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_i ≥ t` / `X_i < t` (would be, from `xbc`) | — | **0** | not run: the existence family has no name (G2) |
| `Ex_i` (would be a third event) | — | **0** | not run: same reason — and note this event does not exist today either, since asking for it means writing a `Global_event` over a `var_name` that has no constructor |

The second row is worth keeping rather than tidying away. **`disjunctive_opt` is the first
constraint in this tier whose interesting event is about something other than `X`**: "why must
this task occur / not occur" is what an optional-task propagator explains, and G2 blocks both
the premise side and the conclusion side of it.

## Generated rules

**None.** There is no `cata/disjunctive_opt.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). The two rules in `cata/cumulative.tex` belong to the non-optional sibling and are
rendered in [`catalog/disjunctive.md`](disjunctive.md#generated-rules); they are deliberately
not reproduced here.

## Status

**`nothing generated — blocked on G2`**

The gap number is chosen against the alternative and the alternative is recorded: it is **not**
G1 (the schema needs no new constant), **not** a missing shape (S9 runs), and **not** G3 (the
atoms stay variable-vs-value while durations are constants). It is G2 —
`docs/DECOMP_FORMAT_NOTES.md:23-32`, "`var_name` has no slot for *this constraint's own
parameter*, only borrowed letters".

G2 was recorded by the counting pilot for `count`'s count variable `c`, and flagged there as
"mechanically harmless (each catalog file is generated in isolation)". **This entry is the case
where it is not harmless**: `Ex_i` is a user-visible variable, D-0004 requires it to print, and
printing it as `O` would print `global_cardinality`'s letter. So the gap stops being cosmetic
the moment a constraint has two kinds of user variable.

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.**

Three reasons, the first two shared with [`disjunctive`](disjunctive.md), the third specific:

1. **Nothing on this side** — 0 generated rules, so no premise to order.
2. **The published §6 explanations are indexed by run-time objects** (a compulsory-part set, a
   profile sequence, a chosen list of time points — `catalog/_literature/cumulative.md`,
   `QUOTED`), which have no index set here. Reaching them is **E4**.
3. **The sourced paper covers no optional-task case**, so even the TimeD route — which is
   `catalog/disjunctive.md`'s one piece of good news — has nothing to say about `Ex_i`. The
   `QUOTED` TimeD display has one Boolean per (task, time) and no existence variable.

**Not compared on minimality.** The sourced paper proves nothing minimal (`QUOTED`, preprint
p.13, two open questions).

## Gaps

| gap | what it blocks here |
|---|---|
| `G2` | **the binding one.** `var_name` is a closed enum (`explenation generator.ml:3`) with no constructor for a constraint's own optionality flag; the only free letter, `O`, is `global_cardinality`'s. `Ex_i` is user-visible, so D-0004 requires it to print |
| `G15` | inherited from S9 — `t' = t − d_i` is the validator's measured `UNPARSED`, so even if G2 closed, the entry would be `not validatable` like `cumulative` |
| `G1` | inherited from S9 — the sum's bound `1` reaches no atom |
| `G3` | **variable-duration form only** (`CHRISTMAS_LIST.md:169`) |
| — | **not a gap:** the three-summand `rule3`. Checked against the source, it runs today; recorded here so nobody re-derives it as a blocker |

Extensions: **E2** per `CHRISTMAS_LIST.md:169`. `decomps/disjunctive_opt.md:8` prices it
"**E0** for the schema, **E1** for the family name" — that split is the same finding as this
entry's, in the E-code vocabulary, and the E1 half is G2.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `disjunctive_opt.tex`.
- `python3 tools/mzn_coverage.py --rank --json` → tier `D literature + solver-native`, ecodes
  `["E2"]`, `CHRISTMAS_LIST.md` line 169. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:3` (`var_name`'s closed enum), `:313-317`
  (`rule3`'s any-length summand branch — the basis for "the schema is not the blocker"),
  `:811` (`cumul` already uses two summands plus a reified event), `:522` (`O` prints as `O` in
  the LaTeX printer) and `:493` (`O` prints as `X` in the plain-text one — the unrecorded
  defect above), `:529-531` (`printfraqtex`, the path every `cata/*.tex` goes through), `:877`
  (`explain`, the plain-text path), `:810-812` (the whole `cumul` chain).
- `decomps/disjunctive_opt.md`, `decomps/_shapes-ext.md:310-317`, `decomps/_shapes.md:40,44-47`
  read → the M-opt modifier, its E0/E1 split, S9's instance list.
- `CHRISTMAS_LIST.md:169`, `:167`, `:106-109` read → literature, solver and route cells.
- `catalog/_literature/cumulative.md` read, **not fetched** → that TimeD carries no existence
  variable, and the per-propagation finding; C2's tags carried across.
- The signature line's third argument is **this entry's rendering of prose**, flagged in place
  as the file's weakest line. Everything else above traces to a file and a line number.
