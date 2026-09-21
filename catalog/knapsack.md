# `knapsack`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `knapsack`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecodes `E1`, `E8`, `E9` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G11` — **and on `G4`, `G12`, `G13`.** The only constraint in the corpus that needs all three sum extensions at once |
| **Generated** | no generator entry — there is no `cata/knapsack.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `knapsack` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:170` records `none found` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, and a **scratch generator run** (below) |

## Constraint

`knapsack(array[int] of int: w, array[int] of int: p, array[int] of var int: x, var int: W,
var int: P)` — `∑_i w_i x_i ≤ W` and `∑_i p_i x_i = P`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:76` carries the *name* only; the line above is
transcribed from `decomps/knapsack.md` ("Signature"), which records it without a citation.
**Treat it as recall.** `CHRISTMAS_LIST.md:170` files it under section `6. Scheduling` — by the
list's own account a filing decision, not a claim about its structure:
`decomps/knapsack.md` notes it "shares nothing with SCH-1/SCH-2 except the word 'sum'".

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:170` reads, verbatim:

> none found

**Rule shape:** nothing to state — there is no `catalog/_literature/knapsack.md`, no paper was
fetched by this session and no web access was used.

`decomps/knapsack.md` calls this "the one constraint in either of wave two's sections with no
paper", and the cell's wording is `none found` rather than `none` — a record that someone
looked, not that nothing exists. `tools/mzn_coverage.py` normalises it to `none` in the ranking
output (measured 2026-09-21); the distinction is kept here and changes no verdict.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | **`[C]` present** |

Source: `CHRISTMAS_LIST.md:170`, solver cell `decomp **[C]**`; legend at
`CHRISTMAS_LIST.md:106-109`. Verified 2026-09-21. The machine-filled stub read this correctly.

**The `[C]` is the interesting cell in this entry.** Choco has a native LCG propagator for
`knapsack` while Chuffed decomposes it, so an explaining implementation exists in a solver even
though the index records no paper. That is a pointer for whoever sources `_literature/` next —
a propagator's explanation scheme may be documented in Choco's sources rather than in a venue —
and **nothing about its content is claimed here.**

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/knapsack.md`](../decomps/knapsack.md); shape **S12** in
`decomps/_shapes.md` ("flat sum over integer-valued variables"), which names `knapsack` as
"two such sums over the *same* array — the `failwith` site, so **E3** as well".

The obstacle is not the shape, it is that three different missing pieces stack:

1. **Integer summands.** `rule5`/`rule6`/`rule7` sum a Boolean family; `x_i` is an integer
   variable. Gaps **G12** (no schema adds values) and **G13** (`var_name` has no integer-valued
   auxiliary).
2. **Coefficients.** `w_i` and `p_i`. Gap **G11**, extension **E8** — the same requirement as
   `cumulative`'s `r_i`.
3. **Two sums over the same array.** Gap **G4**, extension **E3** — the
   `failwith "sommes multiples pas encore implémentés"` site.

D-0011 (`docs/DECISIONS.md:259`) is what separates these: E8 is weighted Boolean sums (G11), E9
is sums of integer-valued variables (G12, G13), and E3 keeps D-0006's multi-family-cardinality
meaning (G4). `CHRISTMAS_LIST.md:170`'s route cell — "**E1 + E8 + E9** (was E3; weighted *and*
integer-valued — D-0011)" — carries the relabelling, and the "was E3" is traceability, not a
live fourth route.

### The order encoding does **not** rescue this entry, and that is worth stating

[`sum_pred`](sum_pred.md) records this session's measured finding that an *unweighted* sum of
integer variables needs neither E8 nor E9: over a **BC** channel, `Σ_{t} [X_i ≥ t] = X_i` turns
the integer sum into a plain Boolean count, and `rule1` + `rule6` — both shipped — express it.
That route was run today and emits.

**It does not extend here.** Order-encode `x_i` and `∑_i w_i x_i` becomes
`∑_{i,t} w_i · [x_i ≥ t]` — still weighted. The coefficient is a property of the *item*, not of
the encoding of its value, so nothing about the channel removes it. **G11 / E8 survives the
order encoding, and G12 / G13 do not.** So `knapsack`'s pricing reduces from three sum
extensions to two (E8 for the weights, E3 for the two sums) *if* the order encoding is adopted,
and the entry stays empty either way. This paragraph is reasoning about the arithmetic, checked
against the measurement in [`sum_pred`](sum_pred.md), not a run of its own.

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/knapsack.tex` and so no
`%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**What was measured: that the two-sums wall is a wall.** A **scratch run** handed the generator
a single `rule7` carrying **two** counted `Decomp_devent`s — the G4 shape — and the run exited
**2** with `Failure "sommes multiples pas encore implémentés"`, writing no file. `rule5`,
`rule6` and `rule7` each match `dee::[]` on the summand list and `failwith` otherwise
(`explenation generator.ml:355`, `:369`, `:383`). Note what that measurement does and does not
cover: it shows the site is reachable and fatal. It does **not** show that `knapsack`'s two
sums must go through one schema instance — they are two constraints and could be two `Decomp`s,
as `roots` (`:856-858`) has two independent `rule7`s. `decomps/knapsack.md` argues they cannot
be separated because "the two sums share `x`, so no per-sum decomposition avoids it"; **that
argument is the spec's and this session did not re-derive it.**

## Generated rules

**None.** `cata/knapsack.tex` does not exist.

## Status

**`nothing generated — blocked on G11`** — and on **G4**, **G12** and **G13**.

G11 is named first because it is the one that survives every re-encoding this session tried.
`decomps/knapsack.md`'s summary stands and this entry adopts it: *"Nothing about `knapsack` is
close."* It is the only constraint in the corpus needing all three of the sum extensions D-0011
separated, plus **E1** for `W` and `P` — which, as [`arg_val`](arg_val.md) notes for a different
variable, may be partly there already, since `var_name` does carry user-variable letters
(`N`, `O`, `V`) that `nvalues` and `gccn` channel with `rule1`.

Nothing here is validated, flagged or refuted. The entry's content is the negative result, one
measurement, and the sharpening in "The order encoding does not rescue this entry".

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:170` records `none found` and names no paper — the condition
`catalog/TEMPLATE.md` attaches to this verdict. Independently, with 0 rules there is no premise
to place in an implication order.

**With one flag for the next session.** `none found` plus a Choco LCG native (`[C]`) is the
combination most likely to hide a published or documented explanation scheme — an implemented
explaining propagator usually has one written down somewhere. If it is found, this verdict
becomes `pending sourcing` and then a real comparison. **This is a pointer, not a finding**;
no paper and no solver source was read by this session.

## Gaps

| gap | what it blocks here |
|---|---|
| `G11` | **named first: it survives everything.** No weighted Boolean sum — `rule5/6/7` count occurrences, with no coefficients. Extension **E8** (D-0011). The order encoding that removes G12/G13 for an unweighted sum leaves this one standing |
| `G4` | one Boolean-sum family per rule; the `failwith` site, measured reachable and fatal (`explenation generator.ml:355`, `:369`, `:383`). Extension **E3** |
| `G12` | no schema sums integer *values*. Extension **E9** — **avoidable** via the BC order encoding, at the cost of the domain assumption [`sum_pred`](sum_pred.md) records |
| `G13` | `var_name` has no integer-valued auxiliary. Extension **E9**, same avoidance |
| `G2`/`E1` | no letter for this constraint's own `W` and `P`; the existing user letters would have to be borrowed |

Extensions: **E1 + E8 + E9** — `CHRISTMAS_LIST.md:170`, verbatim: "**E1 + E8 + E9** (was E3;
weighted *and* integer-valued — D-0011)", plus **E3** for the two sums, which
`decomps/knapsack.md` and `decomps/_shapes.md` (S12) both add and which D-0011's table confirms
is still E3's meaning. Roadmap rows: **W3-T4** (E3), **W2-T2** (E1).
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering); `docs/DECISIONS.md:259`
for the E-code table.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E1","E8","E9"]`, `CHRISTMAS_LIST.md` line
  170, section `6. Scheduling`, literature normalised to `none`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`; no line names a `knapsack` entry.
- `CHRISTMAS_LIST.md:170` and `:106-109` read → the literature, solver and route cells.
- `tools/data/minizinc-2.10.1-globals.txt:76` read → the name.
- `docs/DECISIONS.md:259` (D-0011) read → the E3/E8/E9 table.
- `decomps/knapsack.md` and `decomps/_shapes.md` (S12) read → the shape, the three walls and
  the "two sums share `x`" argument, which is cited to the spec rather than re-derived.
- `explenation generator.ml` read, not run: `:343-383` (`rule5`/`rule6`/`rule7`, the `dee::[]`
  match and the three `failwith`s at `:355`, `:369`, `:383`), `:856-858` (`roots`, two sums in
  two separate `Decomp`s), `:3` (`var_name`).
- **Scratch generator run, 2026-09-21** — `explenation generator.ml` copied into this session's
  scratch directory, one `Decomp (2, rule7, [Decomp_devent …; Decomp_devent …])` appended with
  an `explainall`, run under OCaml 5.1.1 with stderr redirected to a file and then read: exit
  **2**, `Failure "sommes multiples pas encore implémentés"`, no file written. The same run
  backs [`distribute`](distribute.md).
- **Nothing was added to the repository.** The generator is untouched, no `cata/` file changed,
  `make check`'s goldens are unaffected.
- **Not fetched, not read:** the MiniZinc library (not vendored), Choco's sources, and any
  paper. No web access was used.

**Discrepancies noted, not fixed** (`decomps/` is not this session's).

1. **`decomps/knapsack.md:29-30` cites the `failwith` at "source l.320, l.334, l.348".**
   Measured 2026-09-21: **355**, **369**, **383**. Already on the W1-T14 list for the
   `_shapes-ext.md` copy of the same numbers; recorded here as still true of this file.
2. **`decomps/knapsack.md` still labels the weights gap "X5"** alongside G11. X5 is the
   pre-consolidation `_gaps-ext.md` number; `docs/DECOMP_FORMAT_NOTES.md:79` reassigns it to
   **G11**. The file says both, so no reader is misled, but the old label is live text.
