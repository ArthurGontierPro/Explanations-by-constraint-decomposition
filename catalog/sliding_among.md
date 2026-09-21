# `sliding_among`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `sliding_among`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G8` — **twice over**, and on `G1`. See Status |
| **Generated** | no generator entry — there is no `cata/sliding_among.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `sliding_among` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:133` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `explenation generator.ml` read |

## Constraint

**No signature is written here.** `sliding_among` is not vendored:
`tools/data/minizinc-2.10.1-globals.txt:111` carries the *name* only, there is no
`decomps/sliding_among.md`, and `CHRISTMAS_LIST.md:133` gives literature, solver and route and
no signature.

What the name and the list's filing give, and it is enough for the gap analysis below, is the
**construction**: `sliding_among` is [`among`](among.md) applied to every window of consecutive
positions rather than to the array as a whole. `CHRISTMAS_LIST.md` files it in
`2. Counting and cardinality`, immediately after `among` (`:129`) and `nvalue` (`:130`);
`docs/ROADMAP.md:90` files the same constraint in the **sequencing** family, W3-T2. Both are
right, and the split is the point: it is a counting constraint with a sliding index set.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:111`.
`CHRISTMAS_LIST.md:133` files it under section `2. Counting and cardinality`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:133` reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/sliding_among.md`, no paper
was fetched and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:133`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21: no `[G]`, no `[C]`, no `[C✗]`. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** **none** — there is no `decomps/sliding_among.md`. `decomps/_shapes.md` names no shape
for it either; the constraint is in the corpus's list of names and in nobody's spec wave.

**It is `among`'s shape with the summed index set slid.** `among` ships at
`explenation generator.ml:851-853`:

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule4, [Decomp_devent (true, (B 1), id, ontin (D 4)); Reified_devent (true, (B 2), id, t_out)]);
Decomp (3, rule7, [Decomp_devent (true, (B 2), id, oni)])
```

— a `rule1` grid, an S4 existential restricting the value to the parameter set `D 4`, and a
Boolean sum over **all** of `i`. `sliding_among` needs the last step's `oni`
(`OpOn (FI, D 1)`, `explenation generator.ml:763`; `:460` prints `D 1` as the whole `[1,n]`)
replaced by a sum over a window `[j, j+seq-1]` — a *subrange* of `[1,n]`, one per window
position.

**And the operator for that already exists.** `oniin set` (`:767`) is `oni` with the index set
as an argument, and `among` itself uses the value-family twin `ontin (D 4)` at `:852`. So the
missing thing is not an operator: it is a *set*, and `ind_set` cannot name one.

**That single substitution is the whole entry**, and it is refused twice: once for the value
set, once for the window. Both are **G8**, "`ind_set` names only whole predefined ranges — no
subrange, no exclusion" (`docs/DECOMP_FORMAT_NOTES.md:76`).

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/sliding_among.tex` and
so no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**What is measured, on the constraint one substitution away.** [`among`](among.md) ships a
decomposition and generates **0** rules: both of its events are refused because `D_4` — the
value set — is an index set the printer never defines (W1-T2). [`count`](count.md) was authored
into a scratch generator with the same `ontin (D 4)` step and produced **0** rules across four
events, every candidate `REFUSED … (D4)`. `sliding_among` carries that same step *plus* a second
undefined set for the window, so the expected result is 0 rules for the same reason twice.
**That is an inference from two measurements on neighbouring constraints, not a measurement of
`sliding_among`** — no decomposition for it exists to run.

## Generated rules

**None.** `cata/sliding_among.tex` does not exist.

## Status

**`nothing generated — blocked on G8`, twice over, and on `G1`.**

- **G8, the value set.** `among`'s `v` is already an undefined `D_4`; `sliding_among` inherits
  it unchanged, and `catalog/among.md` records it as that entry's binding gap.
- **G8, the window.** `∑_{i ∈ [j, j+seq-1]}` is a subrange of the position range, sliding with
  `j`. `ind_set` is `D of int | D2 of ind_name list` (`explenation generator.ml:6`);
  `ind_set_defined` (`:459`) admits `D 1`, `D 2`, `D 3` and nothing else, and `D2` — the hook
  that could name a computed set — has no printer and **raises** (`:464`, and
  `docs/DECOMP_FORMAT_NOTES.md:96-107`, where W2-A's "checked negative" on `D2` was withdrawn).
  Note that the *shift* operators exist (`iplus`, `imoin`, `:792-793`) and are what `increasing`
  and `regular` use, and `oniin`/`ontin` (`:767-768`) already take a set as an argument. What is
  missing is not arithmetic on an index, nor an operator to consume the set: it is the **set**.
- **G1, the bounds.** `sliding_among(lo, up, …)` compares each window's count against two bare
  integers, and no bare integer reaches the printed rule — the defect
  `at_least`/`at_most`/`exactly` share (`decomps/_shapes.md`, S2; see [`at_most.md`](at_most.md)).

**The E0 route cell is right about the schemas and silent about the index sets**, exactly as it
is for the rest of §2. Every schema this constraint needs exists; not one of the index sets it
needs can be named.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:133` names no paper — the condition `catalog/TEMPLATE.md` attaches to this
verdict — and with 0 rules there is nothing to place in an implication order. Not
`pending sourcing`: the row cites nothing to be pending on.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one, and it applies twice**: to `among`'s value set (already `D_4`, already refused) and to the sliding window subrange. `D2 of ind_name list` is the hook, is used by nothing and raises (`explenation generator.ml:464`) |
| `G1` | the window bounds `lo`/`up` never reach the printed rule |
| `G3` | only if the counted set's elements may be variables; not binding under D-0003's parameter reading, as for `among` |
| `G5` | **not this entry's** — the shipped `among`'s missing count channel is an authoring defect in `among`, and `sliding_among` has no shipped decomposition to inherit it |

Extensions: **E0** — `CHRISTMAS_LIST.md:133`, whose route cell is the single token `**E0**`.
Closing G8 belongs to **E2**/W2-T1, as `catalog/among.md` records.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 133,
  section `2. Counting and cardinality`.
- `make validate` (2026-09-21, redirected then grepped) → `== 34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged ==`; no line names a `sliding_among` entry.
- `CHRISTMAS_LIST.md:133`, `:129`, `:130`, `:106-109` read → the row, its neighbours and the
  solver legend.
- `tools/data/minizinc-2.10.1-globals.txt:111` read → the name.
- `docs/ROADMAP.md:90` read → W3-T2 files `sliding_among` in the sequencing family.
- `explenation generator.ml` read, not run: `:6` (`ind_set`), `:459-460` (`ind_set_defined` and the three defined ranges), `:464`
  (`printind_set`'s `D2` raise), `:777-779` (`sumi`/`oni`'s family), `:793-794` (the index
  shifts), `:851-853` (`among`, quoted above).
- `docs/DECOMP_FORMAT_NOTES.md:76` and `:96-107` read → G8's wording and the withdrawal of the
  `D2` checked negative.
- `catalog/among.md` and `catalog/count.md` read, not run → the two measured 0-rule results the
  inference in "Scope of this entry" rests on. **That inference is labelled as an inference in
  place**; no run was made for `sliding_among`, because no decomposition for it exists.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.
