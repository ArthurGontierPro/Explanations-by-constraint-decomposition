# `alternative`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `alternative`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G3`, **conditional on a signature nobody here has.** See Status |
| **Generated** | no generator entry — there is no `cata/alternative.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `alternative` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:152` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `explenation generator.ml` read |

## Constraint

**No signature is asserted here, and this entry is more hedged than its neighbours because its
spec is.** `alternative` is not vendored: `tools/data/minizinc-2.10.1-globals.txt:22` carries
the *name* only, and `CHRISTMAS_LIST.md:152` — the row it shares with [`span`](span.md) —
gives literature, solver and route and no signature.

`decomps/alternative.md` reads it tentatively as "a task is scheduled at exactly one of several
optional alternative slots/options, an exactly-one-of choice", and flags that reading
**"lower confidence than `span`" … "more strongly than `span.md`'s hedge, because 'which of
several options is active' has more than one standard encoding and this session cannot tell
which MiniZinc picked"**. Its closing recommendation is to "re-derive `alternative` against the
actual MiniZinc predicate signature before treating this file as more than a placeholder."

**This entry carries that forward rather than resolving it**, and the reason it cannot resolve
it is the same one: the MiniZinc library is not in this repo and this session had no web
access. Everything below is conditional on the reconstructed reading and says so.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:22`.
`CHRISTMAS_LIST.md:152` files it under section `4. Sequencing and sliding`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:152` reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/alternative.md`, no paper
was fetched by this session and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:152`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21. The row is shared with `span`, so both entries carry the same three cells.
The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/alternative.md`](../decomps/alternative.md) — explicitly a placeholder, see
above. Shape: **S2 for one half only.** `decomps/_shapes.md` lists `alternative` among S2's
instances as "`rule7` against 1 — hedged, see that file; **its second, `rule3` half is not part
of this shape**".

Under the reconstructed reading the decomposition is in two halves, and the split is the whole
of this entry:

1. **The choice.** `B_k ⇔` "option `k` is chosen", then `∑_k B_k = 1` — `rule1` + `rule7`,
   shape **S2**.
2. **The consequence.** `B_k → (the task's start/duration = option `k`'s start/duration)` —
   a `rule3`-style implication per option. `decomps/alternative.md` does not establish whether
   an option's parameters are variables or parameters.

**Half 1 is encodable today, and uninteresting on its own.** Its threshold is 1 — the same
implicit 1 `alldiff` carries at `explenation generator.ml:808-809` — so for once **G1 does not
bite**: the one constant the format can silently assume is the one this half needs. But a rule
derived from half 1 alone says only "exactly one option is chosen", which is the selector's own
totality and says nothing about the task. **It is half 2 that carries the constraint.**

**And half 2 is where the signature decides everything.** If an option's start and duration are
**parameters** (fixed slots), `start = start_k` is a variable-vs-value atom, which this format
expresses — and then the constraint is encodable and merely unencoded. If they are **decision
variables**, `start = start_k` is variable-vs-variable, which is **G3**
(`docs/DECOMP_FORMAT_NOTES.md:38-45`), the wall that also blocks `maximum`, `minimum`,
`arg_max`, `arg_min` and [`span`](span.md) — this entry's row-mate.

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/alternative.tex` and so
no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**No scratch experiment was run for this entry**, and the reason is the signature and not
effort. Running half 1 alone would emit something — the S2 `rule7` shape does emit, measured
for [`exactly`](exactly.md), two rules — but those rules would be about a selector variable in
a decomposition nobody has established is this constraint's. That would be measuring an
invention. The neighbouring measurement that *is* transferable is `exactly`'s, and it is cited
rather than re-run.

## Generated rules

**None.** `cata/alternative.tex` does not exist.

## Status

**`nothing generated — blocked on G3`, conditional on the reading in which an option's times
are decision variables.**

Two things are settled and one is not.

**Settled.** Nothing is generated: no value, no `explainall`, no artifact. And half 1 —
exactly-one-of — is expressible with shipped schemas and the one threshold the format handles,
so **G1 is not this entry's blocker**, unlike every other §2-style counting constraint in this
session's slice.

**Not settled: which constraint `alternative` is.** The two outcomes are far apart, and naming
them is more useful than picking one:

- **options with variable times → `nothing generated — blocked on G3`.** Half 2's atom is
  variable-vs-variable and the entry stays empty, alongside `span` on the same
  `CHRISTMAS_LIST.md` row.
- **options with parameter times → `encodable today, not encoded`** (the status value added to
  `catalog/README.md`'s legend at `:66` on 2026-09-21). Both halves would be authorable with
  `rule1`, `rule3` and `rule7` as they ship, and the entry would be empty only because nobody
  has written the value — the same position [`sum_pred`](sum_pred.md)'s reading (a) is in.

The header row names G3 because that is the reading `decomps/alternative.md` leans towards and
the one shared with this row's other constraint; **it is marked conditional in both places
rather than presented as established.** Settling it needs the MiniZinc predicate text, which is
one lookup for anyone with the library — and it is the single highest-value thing to do to this
entry.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:152`'s literature cell is `none` — the condition `catalog/TEMPLATE.md`
attaches to this verdict — and with 0 rules there is no premise to place in an implication
order. Not `pending sourcing`: the row cites nothing to be pending on.

Note that this verdict is **not** conditional on the signature question, unlike the status: the
row records no paper whichever constraint the name denotes.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **conditional and probably binding**: half 2's `start = start_k` is variable-vs-variable if an option's times are variables. Same wall as [`span`](span.md), `maximum`, `minimum`, `arg_max`, `arg_min` |
| `G2` | `var_name` (`explenation generator.ml:3`) has no letter for the task's own start/duration, nor for a selector; existing letters would be borrowed. Note R6's 2026-09-21 hardening of G2 (`docs/DECOMP_FORMAT_NOTES.md:23-27`): a **second user array** taken as `B 1` makes `printvartex` raise (generator l.517), so a two-array reading of this constraint would not print at all |
| `G1` | **not binding, and that is unusual in this family**: half 1's threshold is 1, the constant the format already assumes for `alldifferent` |
| — | **the signature itself.** Not a gap; the open item, and the one that decides between the two statuses above |

Extensions: **E0** — `CHRISTMAS_LIST.md:152`, whose route cell is the single token `**E0**`,
shared with `span`. For `span` that cell is **withdrawn** (see that entry); for `alternative` it
is right under the parameter-times reading and wrong under the variable-times one. **The shared
cell therefore needs splitting**, and that file is not this session's.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 152,
  section `4. Sequencing and sliding`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`; no line names an `alternative` entry.
- `CHRISTMAS_LIST.md:152` and `:106-109` read → the literature, solver and route cells.
- `tools/data/minizinc-2.10.1-globals.txt:22` read → the name.
- `decomps/alternative.md` read → the reconstructed reading, its two halves and its own
  low-confidence flag, quoted above.
- `decomps/_shapes.md` (S2's instance list) read → "`rule7` against 1 — hedged … its second,
  `rule3` half is not part of this shape".
- `explenation generator.ml` read, not run: `:3` (`var_name`), `:808-809` (`alldiff`, the
  implicit threshold of 1), `:371-383` (`rule7`).
- `docs/DECOMP_FORMAT_NOTES.md:23-27` (G2 as hardened by R6) and `:38-45` (G3) read.
- `catalog/README.md:66` read → the `encodable today, not encoded` status value and its
  definition.
- `catalog/exactly.md` (this session's) read → the measured S2 `rule7` emission that half 1
  would reproduce; **not re-run here**, for the reason in "Scope of this entry".
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.
  **The signature is the open item**, and this entry is explicitly conditional on it in the
  Status row, the Status section and the Gaps table.
