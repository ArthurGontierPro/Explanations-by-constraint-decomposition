# `all_different_except_0`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `all_different_except_0`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

**This entry shares a row, a spec, a shape and a gap with
[`all_different_except`](all_different_except.md).** Everything below that is not specific to
the excepted value being fixed at `0` is stated there and not duplicated here; the difference
is one sentence and it is in "Decomposition used here".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G8` |
| **Generated** | no generator entry — there is no `cata/all_different_except_0.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `all_different_except_0` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:117` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `explenation generator.ml` read |

## Constraint

`all_different_except_0(array[int] of var int: x)` — the values in `x` are pairwise distinct,
except that any number of them may be `0`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:19` carries the *name* only; the line above is the
reading `decomps/all_different.md` works from ("fixed at `0` for the `_0` variant"), recorded
there without a citation. **Treat the arity as recall.** `CHRISTMAS_LIST.md:117` files it under
section `1. AllDifferent family`.

**There is a third name for the same object.** `CHRISTMAS_LIST.md:120` carries a row
`alldifferent_except_0` (alias) | — | — | as above`. It is the older MiniZinc spelling and the
list marks it an alias with empty literature and solver cells. `docs/COVERAGE.md:137-139` names
that row as one of three in the file with no E-code, and `catalog/count_fn.md` records
(measured 2026-09-21) that the line it gives for it, 118, is stale and the row is at **120**.
Nothing in this entry rests on that row.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:117`'s literature column reads, verbatim:

> none

**Rule shape:** nothing to state — no `catalog/_literature/all_different_except_0.md` exists,
no paper was fetched and no web access was used. See
[`all_different_except.md`](all_different_except.md), "Published explanation", for why the
`all_different` citation on the neighbouring row (`CHRISTMAS_LIST.md:116`, Downing, Feydy and
Stuckey 2012) is **not** transferred here.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:117`, solver cell `decomp **[G]**`; legend at
`CHRISTMAS_LIST.md:106-109`. Verified 2026-09-21. The machine-filled stub read this correctly.
The row covers both `_except` and `_except_0`, so the cells are shared; the `[G]` is Geas'
native propagator.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/all_different.md`](../decomps/all_different.md), which covers
`all_different`, both `_except` variants and `symmetric_all_different` in one file; shape
**S2** in `decomps/_shapes.md`.

**The difference from [`all_different_except`](all_different_except.md), in one sentence:** the
excluded value is the constant `0` rather than a parameter, so the summed value family is
`[1,m] \ {0}` — a *fixed* hole instead of an instance-dependent one.

**And that difference buys nothing here.** `ind_set` is `D of int | D2 of ind_name list`
(`explenation generator.ml:6`); `ind_set_defined` (`:459`) admits `D 1`, `D 2`, `D 3` and
`printind_set_int` (`:460`) prints them as `[1,m]`, `[1,n]`, `[1,n]`. There is no fourth
constructor and no fourth defined set, so a *constant* exclusion is as unnameable as a
parameter one — **G8 is indifferent to whether the hole is known at authoring time**, because
the blocker is the absence of a set-former, not the absence of a value. This is worth stating
because `_except_0` is the variant one would expect to be the easy special case, and it is not.

A second reason it is not easier: with the value domain written `[1,m]`, `0` is not even in the
range the printer names — so the "hole" would have to be punched in a range that does not
contain it, or the range respelled. Neither is expressible. **This paragraph is read off
`:460`, not measured.**

## Scope of this entry

**Events the generator was asked to explain:** none. There is no
`cata/all_different_except_0.tex` and so no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

See [`all_different_except.md`](all_different_except.md), "Scope of this entry", for why
dropping the guard does not give a usable partial entry: it gives `all_different`, whose rule
is unsound for this constraint at the excepted value.

## Generated rules

**None.** `cata/all_different_except_0.tex` does not exist.

## Status

**`nothing generated — blocked on G8`** — the same gap, for the same reason, as
[`all_different_except`](all_different_except.md), whose Status section states it in full with
its three source lines. The `_0` variant adds no gap of its own and removes none: see
"Decomposition used here" for why fixing the excepted value to a constant does not help.

`docs/DECOMP_FORMAT_NOTES.md:76` names `all_different_except*` — the star covering both — as
the constraint that hit G8.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:117` names no paper, and with 0 rules there is no premise to place in an
implication order. Not `pending sourcing`, and **not** a transfer of `catalog/alldifferent.md`'s
verdict against Downing et al. §4 — see [`all_different_except.md`](all_different_except.md),
"Calibration", where the non-transfer is argued once.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one and the only one.** No subrange, no exclusion — and no relief from the hole being the constant `0` rather than a parameter |
| `E4` | not a gap — the missing `X_i = t` direction, inherited from `all_different` and unchanged by G8 |
| `G1` | not binding: the threshold is `all_different`'s invisible 1 and this variant does not vary it |

Extensions: **E0** — `CHRISTMAS_LIST.md:117`, verbatim: "**E0**, same shape with a guard on the
excepted value". Closing G8 belongs to **E2**/W2-T1.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 117,
  section `1. AllDifferent family` — the same row as `all_different_except`.
- `make validate` (2026-09-21, redirected then grepped) → `== 34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged ==`; no line names an `all_different_except_0` entry.
- `CHRISTMAS_LIST.md:117`, `:120`, `:116`, `:106-109` read → this row, the alias row, the
  `all_different` citation and the solver legend.
- `tools/data/minizinc-2.10.1-globals.txt:19` read → the name.
- `explenation generator.ml` read, not run: `:6` (`ind_set`), `:459-460` (`ind_set_defined` and
  the three printed ranges), `:464` (`printind_set`'s `D2` raise), `:808-809` (`alldiff`).
- `docs/DECOMP_FORMAT_NOTES.md:76` read → G8 and the `all_different_except*` attribution.
- `decomps/all_different.md` read → the family spec and its "`0` for the `_0` variant" reading.
- `catalog/all_different_except.md` (this session's sibling entry) read → everything this entry
  defers to rather than restating.
- **No scratch run.** As for the sibling: the substitution that matters has no `ind_set` value
  to write, so there is nothing to hand the generator.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.

**Discrepancies noted, not fixed.** The three recorded in
[`all_different_except.md`](all_different_except.md) apply here unchanged — `decomps/all_different.md`'s
pre-consolidation "G6" for what is now **G8**, its `printind_set` line number (375, measured
**462-464**), and its `"setfils"` symptom, which W1-T2 replaced with a raise.
