# `bin_packing_capa`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `bin_packing_capa`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`no-literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, ecode `E8`, section `7. Packing and geometry`. Re-tiered 2026-09-21 per **D-0014**: was filed `- out of scope` by the tool's section filter before the fix; see "History" below. |
| **Status** | `nothing generated — blocked on G11` |
| **Generated** | no generator entry — there is no `cata/bin_packing_capa.tex` |
| **Validator** | not run — no `cata/bin_packing_capa.tex` exists yet |
| **Calibration** | `out of reach` — 0 rules generated; no published shape exists to compare against (`CHRISTMAS_LIST.md:176`: "none found") |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank` (post-fix), `CHRISTMAS_LIST.md:176` read, `docs/DECISIONS.md` D-0014 read |

## Constraint

`bin_packing_capa` — no MiniZinc signature is vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt` lists `bin_packing_capa` as a global of MiniZinc 2.10.1
(name only). `CHRISTMAS_LIST.md:176` files it under section `7. Packing and geometry`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:176`, literature cell, verbatim:

> none found

No paper is sourced in `catalog/_literature/` for `bin_packing_capa`.

## Solver support

`CHRISTMAS_LIST.md:176`, solver cell, verbatim:

> decomp

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None yet.** There is no `decomps/bin_packing_capa.md` and no `cata/bin_packing_capa.tex`. What it would take is
below.

## Scope of this entry

**In scope, pending G11.** `CHRISTMAS_LIST.md:176`'s route cell: `E8 (was E3; weighted
sums — D-0011); '_load' is the most tractable`. Per **D-0014** (`docs/DECISIONS.md`, 2026-09-21), scope is
decided by the mechanism a constraint needs, not by the section it is filed under, and
`bin_packing_capa`'s mechanism — weighted Boolean sums — is **the identical gap `knapsack` carries**
(`E1 + E8 + E9`, `CHRISTMAS_LIST.md:170`), and `knapsack` sits in tier A, not out of scope.
The concrete blocker in this generator is **G11** — "no weighted Boolean sum: `rule5/6/7`
count occurrences, with no coefficients" (`docs/DECOMP_FORMAT_NOTES.md:79`), the same row
that also names `cumulative`.

**What it would take to generate rules here.** G11 needs closing — `rule5/6/7` extended to
admit per-literal coefficients rather than plain occurrence counts — shared prerequisite work
with `knapsack` and `cumulative`. Then someone writes `decomps/bin_packing_capa.md` encoding bin
capacity as a weighted sum over item-to-bin assignment Booleans. Neither step is done; this
entry records the target, not a result.

**History.** This entry was first filed `- out of scope` by `tools/mzn_coverage.py --rank`'s
section filter, which caught every row under "7. Packing and geometry" regardless of its
E-code. A prior pass of this catalog (R3, 2026-09-21) flagged that as a probable
misclassification — `bin_packing_capa`'s own route cell says `E8`, the same gap as tier-A `knapsack`,
not E5/E6/E7. The orchestrator checked that finding, recorded **D-0014**, and fixed the tool
(tier A count 36→43, out-of-scope 35→28). `bin_packing_capa` is filed here under its corrected tier as
a result — the classification was checked, not assumed.

## Generated rules

None. No `cata/bin_packing_capa.tex` exists.

## Status

**`nothing generated — blocked on G11`**

No decomposition has been attempted or encoded. This is a generator gap (G11, weighted
Boolean sums), not a scope exclusion: nothing in `docs/ROADMAP.md`'s "Explicitly out of
scope" list (`docs/ROADMAP.md:103-107`) names E8 or weighted sums as excluded, and D-0014
confirms it.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — 0 rules generated, no decomposition encoded, and
`CHRISTMAS_LIST.md:176` records no published explanation to compare against even once one
is generated.

## Gaps

| gap | what it blocks here |
|---|---|
| `G11` | no weighted Boolean sum — `rule5/6/7` count occurrences, with no coefficients; `bin_packing_capa`'s bin-capacity constraint needs per-item weights (`docs/DECOMP_FORMAT_NOTES.md:79`) |

Extensions: **E8** (`CHRISTMAS_LIST.md:176`).
Source: `docs/DECOMP_FORMAT_NOTES.md:79` (G11); `docs/DECISIONS.md` D-0014, D-0011 (the E3→E8/E9 split).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (re-run 2026-09-21, post-fix) → `bin_packing_capa` under tier
  **A**, ecode `E8`, section `7. Packing and geometry`.
- `CHRISTMAS_LIST.md:176` read → literature, solver and route cells quoted above, verbatim.
- `CHRISTMAS_LIST.md:170` read → `knapsack`'s identical `E8` gap, cited as the tier-A precedent.
- `docs/DECISIONS.md` D-0014 read → the re-tiering decision, the tool fix, and the before/after
  tier counts (36→43 tier A, 35→28 out of scope).
- `docs/DECOMP_FORMAT_NOTES.md:79` read → G11's definition, shared with `cumulative`.
- `os.path.isfile("decomps/bin_packing_capa.md")` → False. `os.path.isfile("cata/bin_packing_capa.tex")` → False.
- Nothing was compiled, run or validated. No rules exist yet for `bin_packing_capa`; this entry states
  the target (G11) and the history of how the tier was corrected, not a generated result.
