# `span`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `span`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | no generator entry — there is no `cata/span.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `span` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:152` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `explenation generator.ml` read |

## Constraint

**No signature is asserted here.** `span` is not vendored:
`tools/data/minizinc-2.10.1-globals.txt:115` carries the *name* only, and
`CHRISTMAS_LIST.md:152` — the row it shares with [`alternative`](alternative.md) — gives
literature, solver and route and no signature.

`decomps/span.md` works from a **reconstructed** reading, and flags it as reconstructed: a task
with start `S` and end `E` spans a set of subtask intervals, with `S = min_i(start_i)` and
`E = max_i(end_i)`. That file's own words: "**Flagging this as reconstructed, not confirmed** …
if the real signature differs this file should be redone, not patched." **This entry inherits
the hedge and does not upgrade it.** What follows holds *under that reading*; the blocking gap
would have to be re-established under any other.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:115`.
`CHRISTMAS_LIST.md:152` files it under section `4. Sequencing and sliding`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:152` reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/span.md`, no paper was
fetched by this session and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:152`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21: no `[G]`, no `[C]`, no `[C✗]`. The machine-filled stub read this
correctly. The row is shared with `alternative`, so both entries carry the same three cells.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/span.md`](../decomps/span.md) — **and its E0 claim is withdrawn by its own
header.** Shape: **none.** `decomps/_shapes.md` lists `span` with `maximum`, `minimum`,
`arg_max` and `arg_min` in its "Not covered by any shape" table, all four against **G3**.

**This entry is downstream of a contradiction between two sessions, which the shape
consolidation resolved.** `decomps/_shapes.md`'s "Contradictions between sessions" §1 states it
in one line — "`span` is claimed E0 by one session and impossible by another, and the second is
right" — and the argument has two steps:

1. `S = min_i(start_i)` compares two **decision variables**. `Global_event`/`ind_modifs`
   express `X_i = t` for `t` an index-derived domain *value*, never `X_i = Y_i`
   (`docs/DECOMP_FORMAT_NOTES.md:38-45`, **G3**). `decomps/maximum.md` calls this "not a
   derivation gap, it is a missing primitive", and `span`'s min over subtask starts is
   `minimum` under another name.
2. **The precedent the E0 claim rested on does not exist.** `decomps/span.md` reused
   "Shape D" — `range`/`roots` read as a ∀-bound plus an ∃-tight pair. Read off the source,
   `range` (`explenation generator.ml:859-861`) is `rule1` + `rule6` + `rule7` and `roots`
   (`:856-858`) is `rule1` + two `rule7`s, each a **Boolean sum** over a value-restricted
   family. `rule6` is `∑ ≥` and `rule7` is `∑ =`; ∀ and ∃ are `rule3`/`rule4`. Shape D was a
   misreading of two schemas and `decomps/_shapes.md` deletes it.

**This entry adopts that resolution rather than reopening it**, and re-checked step 2 against
the source today: `range` and `roots` are at the lines above and are Boolean sums.

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/span.tex` and so no
`%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**No scratch experiment was run**, and here that is not a matter of effort: G3 means the atom
`S ≤ start_i` has no representation in the `event` type at all, so there is nothing to hand the
generator. A blocked-at-the-first-atom constraint is the one case where a run cannot even be
attempted, which is what distinguishes G3 from the index-set gaps elsewhere in this session's
slice — those get as far as a refusal or a crash.

## Generated rules

**None.** `cata/span.tex` does not exist.

## Status

**`nothing generated — blocked on G3`.**

G3 — "only variable-vs-domain-value comparisons exist, never variable-vs-variable" — is the
most load-bearing gap in the consolidated list: `docs/DECOMP_FORMAT_NOTES.md:92-94` records
that three independent families hit it (the counting pilot, `maximum`/`minimum`/`arg_*`, and
`lex_less`), and it blocks `span` before a decomposition can be written, not after.

**The route cell is wrong and this entry says so plainly.** `CHRISTMAS_LIST.md:152` prices
`span` at **E0**. That is inherited from `decomps/span.md`'s withdrawn Shape D reading; the
correct route is whatever extension covers variable-vs-variable atoms, which the E-code table
does not currently name — `CHRISTMAS_LIST.md`'s **E2** ("inequalities against expressions") is
the nearest and `docs/DECOMP_FORMAT_NOTES.md:44-45` links G3 to it. **Recorded as a finding for
whoever owns `CHRISTMAS_LIST.md`; this session did not edit that file.**

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:152`'s literature cell is `none` — the condition `catalog/TEMPLATE.md`
attaches to this verdict — and with 0 rules there is no premise to place in an implication
order. Not `pending sourcing`: the row cites nothing.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one, and it blocks the first atom.** `S = min_i(start_i)` compares two decision variables; `Global_event`/`ind_modifs` have no such comparison. Same wall as `maximum`, `minimum`, `arg_max`, `arg_min` (`decomps/_shapes.md`, "Not covered by any shape") |
| `G2` | secondary: `var_name` (`explenation generator.ml:3`) has no letter for a task's own start or end, so `S` and `E` would borrow another constraint's. `decomps/span.md` notes this too |

Extensions: the route cell says **E0** and that is **withdrawn** — see Status. G3's nearest
E-code is **E2**; no extension in the current table is scoped to variable-vs-variable atoms.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering); `decomps/_shapes.md`
for the contradiction and its resolution.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 152,
  section `4. Sequencing and sliding`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`; no line names a `span` entry.
- `CHRISTMAS_LIST.md:152` and `:106-109` read → the literature, solver and route cells.
- `tools/data/minizinc-2.10.1-globals.txt:115` read → the name.
- `decomps/span.md` read → the reconstructed signature, the withdrawn Shape D / E0 claim, and
  the W3-D correction header, quoted above.
- `decomps/_shapes.md` read → "Not covered by any shape" (G3, five constraints) and
  "Contradictions between sessions" §1 and §2.
- `explenation generator.ml:856-858` and `:859-861` read, not run → `roots` and `range`, which
  are Boolean sums and not a ∀/∃ pair; `:3` (`var_name`).
- `docs/DECOMP_FORMAT_NOTES.md:38-45` and `:92-94` read → G3's wording, its link to E2, and the
  three families that hit it.
- **No scratch run**, for the reason in "Scope of this entry".
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.
  **The signature is the open item**, inherited from `decomps/span.md` and not resolved here.

**Discrepancy noted, not fixed.** `CHRISTMAS_LIST.md:152` still prices `span` at **E0**, from
the reading `decomps/_shapes.md` withdrew on 2026-09-18. The row also covers `alternative`,
whose E0 is a separate question ([`alternative.md`](alternative.md)), so the cell cannot simply
be changed — it needs splitting. That file is not this session's.
