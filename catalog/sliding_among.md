# `sliding_among`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `sliding_among`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G8` — **once over now, not twice**, and on `G1`. The value set became sayable on 2026-09-22; the sliding window did not. Re-checked by U2, 2026-09-22. See Status |
| **Generated** | no generator entry — there is no `cata/sliding_among.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `sliding_among` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:133` records `none` |
| **Last measured** | 2026-09-21 for the tier and validator rows. **Status re-checked 2026-09-22 (U2)** against `explenation generator.ml` after commits `4547daf`/`1e747ee`; the status value is unchanged, one of its three justifications is withdrawn, and no new run was made |

## Constraint

**No signature is written here.** `sliding_among` is not vendored:
`tools/data/minizinc-2.10.1-globals.txt:111` carries the *name* only, there is no
`decomps/sliding_among.md`, and `CHRISTMAS_LIST.md:133` gives literature, solver and route and
no signature.

What the name and the list's filing give, and it is enough for the gap analysis below, is the
**construction**: `sliding_among` is [`among`](among.md) applied to every window of consecutive
positions rather than to the array as a whole. `CHRISTMAS_LIST.md` files it in
`2. Counting and cardinality`, immediately after `among` (`:129`) and `nvalue` (`:130`);
`docs/ROADMAP.md:91` files the same constraint in the **sequencing** family, W3-T2. Both are
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
subrange, no exclusion" (`docs/DECOMP_FORMAT_NOTES.md:80`).

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

**`nothing generated — blocked on G8`** — **once over now, and still on `G1`.**

**Re-checked 2026-09-22 (U2) after G-1 closed G1 and G8 in commits `4547daf` and `1e747ee`.
One of the three justifications below is withdrawn; the other two hold, and either alone is
enough to keep the status.** `catalog/among.md`'s own warning is the frame for this: G8's
closure gave `among` two rules and **both are measured UNSOUND** — the set became sayable and
the decomposition did not become right.

- **~~G8, the value set.~~ WITHDRAWN.** `among`'s `v` was an undefined `D_4`; it is not any
  more. `ind_set` gained `DPar (name, parent)`, which names a parameter subset and prints its
  own containment (`explenation generator.ml:51`, printed `:536`), and shipped `among` now uses
  `ontin (DPar ("s", D 2))` (`:943`). `cata/among.tex` carries the result — two rules where it
  had none.
- **G8, the window. STANDS, and it is now the sharper half.** `∑_{i ∈ [j, j+seq-1]}` is a
  subrange of the position range, **sliding with `j`**. The new `DSub` former is
  `DSub of ind_set*int*int` (`explenation generator.ml:49`), and `printind_set` renders it as
  `"\\llbracket"^string_of_int a^","^string_of_int b^"\\rrbracket"` (`:534`): **both endpoints
  are OCaml `int` literals.** `DSub (D 1, 1, 3)` is writable; `[j, j+seq-1]`, whose endpoints
  are an `ind_name` and an offset from it, is not — no former takes an index in an endpoint
  position. `D2 of ind_name list`, the hook that could name a computed set, is **unchanged and
  still raises** (`:532`), and `ind_set_defined` still rejects it (`:521`). The *shift*
  operators exist and are what `increasing` and `regular` use, and `oniin`/`ontin` already take
  a set argument; what is missing is still the **set**, and G8's closure did not supply this one.
- **G1, the bounds. STANDS, half of it.** `sliding_among(lo, up, …)` compares each window's
  count against two bare integers. `DCard` now carries a threshold into the printed rule —
  `at_most(c)` writes `DCard ("S", D 1, EQ, BPar ("c", 1))` (`:995`) and ships
  `cata/at_most.tex` — so the `≤ up` direction is expressible. The `≥ lo` direction is not: its
  witness set has size `n − lo` and `ind_bound` is `BInt of int | BPar of string*int` (`:46`),
  printed at `:161-164` as a name plus or minus a *literal integer*. Same wall as
  [`at_least`](at_least.md), and **G-1 named it when it left that case undone**
  (`WORKLOG.md:1615-1616`).

**The E0 route cell is right about the schemas and silent about the index sets**, exactly as it
is for the rest of §2. Every schema this constraint needs exists; of the three index-set and
threshold constructs it needs, one arrived on 2026-09-22 and two did not.

*Everything in this section is read off `explenation generator.ml`'s types and printers with
line numbers re-measured today (W1-T14); nothing was run and no decomposition was authored.*

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:133` names no paper — the condition `catalog/TEMPLATE.md` attaches to this
verdict — and with 0 rules there is nothing to place in an implication order. Not
`pending sourcing`: the row cites nothing to be pending on.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one, and it now applies once, not twice.** The value set is CLOSED (2026-09-22): `DPar` writes it and shipped `among` uses it (`explenation generator.ml:943`). The **sliding window** is not: `DSub of ind_set*int*int` (`:49`) takes two literal `int` endpoints, and `[j, j+seq-1]`'s endpoints depend on a running index. `D2 of ind_name list` is still the hook, is still used by nothing and still raises (`:532`) |
| `G1` | **half closed 2026-09-22.** `DCard` carries a threshold for the `≤` direction, so `up` reaches the printed rule; `lo` does not — its witness set is `n − lo`, which `ind_bound` cannot form (`explenation generator.ml:46`, `:161-164`) |
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
- `docs/ROADMAP.md:91` read → W3-T2 files `sliding_among` in the sequencing family.
- `explenation generator.ml` read, not run: `:6` (`ind_set`), `:459-460` (`ind_set_defined` and the three defined ranges), `:464`
  (`printind_set`'s `D2` raise), `:763` and `:767-768` (`oni`, `oniin`, `ontin`), `:792-793` (the index
  shifts), `:851-853` (`among`, quoted above).
- `docs/DECOMP_FORMAT_NOTES.md:80` and `:100-111` read → G8's wording and the withdrawal of the
  `D2` checked negative.
- `catalog/among.md` and `catalog/count.md` read, not run → the two measured 0-rule results the
  inference in "Scope of this entry" rests on. **That inference is labelled as an inference in
  place**; no run was made for `sliding_among`, because no decomposition for it exists.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.
