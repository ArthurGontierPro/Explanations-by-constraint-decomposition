# `bin_packing_load`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `bin_packing_load`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` per `tools/mzn_coverage.py --rank` (section `7. Packing and geometry`), ecode `E8` — **this session flags the tier itself as questionable; see "Is that classification right?" below** |
| **Status** | `nothing generated — blocked on E8` |
| **Generated** | no generator entry — there is no `cata/bin_packing_load.tex` |
| **Validator** | out of scope — no `cata/bin_packing_load.tex` exists |
| **Calibration** | `out of reach` — 0 rules generated |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:176` read |

## Constraint

`bin_packing_load` — no MiniZinc signature is vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt` lists `bin_packing_load` as a global of MiniZinc 2.10.1
(name only). `CHRISTMAS_LIST.md:176` files it under section `7. Packing and geometry`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:176`, literature cell, verbatim:

> none found

No paper is sourced in `catalog/_literature/` for `bin_packing_load`.

## Solver support

`CHRISTMAS_LIST.md:176`, solver cell, verbatim:

> decomp

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/bin_packing_load.md` and no `cata/bin_packing_load.tex` — nobody has written this
constraint's decomposition in this project's format yet, regardless of the scope question
below.

## Scope of this entry

**Why it is currently filed out of scope.** `tools/mzn_coverage.py --rank` puts `bin_packing_load`
under `- out of scope`. `docs/ROADMAP.md:103-107` explains the ranking tool needed a
*section* filter (Packing/geometry, Graph/reachability, Sets, Maths-and-misc-floats) "because
geometry rows are coded E2/E8 rather than E5/E6/E7" (this task's own brief, corroborated by
the row below). `bin_packing_load` is in section `7. Packing and geometry`, so it is caught by that section filter.

**Is that classification right for `bin_packing_load`?** **Questionable, for a specific and checkable reason.** `CHRISTMAS_LIST.md:176`'s route cell reads `E8 (was E3; weighted sums — D-0011); '_load' is the most tractable`. E8 (weighted Boolean sums, consolidated gap G11, `docs/DECOMP_FORMAT_NOTES.md:79`) is not one of the three excluded categories in `docs/ROADMAP.md:106` (E5/E6/E7) — it is a rule-engine gap in `rule5/6/7`, the same gap `knapsack` carries (`E1 + E8 + E9`, `CHRISTMAS_LIST.md:170`). `knapsack` is **not** filed out of scope; it sits in tier A ("no-literature + solver-decomposes"), the tier this task's sibling ranking treats as the most promising unaddressed work. `bin_packing_load` carries the identical E8 gap and is filed out of scope purely because its section header is `7. Packing and geometry` — the same section-filter effect named in `diffn`'s entry (`catalog/diffn.md`) — not because weighted counting is architecturally excluded the way graphs or floats are.

**What would bring it in scope.** E8 (weighted Boolean sums), same as `knapsack`. `_load` is called out by `CHRISTMAS_LIST.md:176` itself as "the most tractable" of the three; recommend re-tiering `bin_packing_load` alongside `knapsack` rather than under 'out of scope'.

## Generated rules

None. No `cata/bin_packing_load.tex` exists.

## Status

**`nothing generated — blocked on E8`**

No decomposition has been attempted or encoded. Unlike the E5/E6/E7 entries in this batch,
this is **not** a scope decision recorded in `docs/ROADMAP.md`'s "Explicitly out of scope"
list (`docs/ROADMAP.md:103-107` names only sets/E5, graphs/E6, geometry-and-packing, and
floats/E7 — see the misclassification note above for why "geometry and packing" as a *section
label* overshoots the actual blocker here).

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — 0 rules generated, no decomposition encoded. This says nothing
about whether the constraint is inherently unexplainable; see Scope above.

## Gaps

| gap | what it blocks here |
|---|---|
| `E8` | weighted Boolean sums — `rule5/6/7` count occurrences with no coefficients (consolidated gap G11, `docs/DECOMP_FORMAT_NOTES.md:79`) |

Extensions: `E8` (`CHRISTMAS_LIST.md:176`).
Source: `docs/ROADMAP.md:103-107`; `CHRISTMAS_LIST.md:227-244` ("What to actually ask for").

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `bin_packing_load` under tier `- out of scope`,
  ecode(s) `E8`, section `7. Packing and geometry`.
- `CHRISTMAS_LIST.md:176` read → literature, solver and route cells quoted above, verbatim.
- `CHRISTMAS_LIST.md:227-244` read → the "What to actually ask for" priority list, which is
  where the misclassification argument above comes from (comparing `bin_packing_load`'s named extension
  against constraints the same list treats as near-term, in-scope work).
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement, which names
  categories, not E-codes, and does not name `E8` as excluded on its own.
- `os.path.isfile("decomps/bin_packing_load.md")` → False. `os.path.isfile("cata/bin_packing_load.tex")` → False.
- Nothing was compiled, run or validated. The misclassification argument is this session's own
  reading, not a machine output — it is reasoning from the route cell and the priority list,
  flagged for the orchestrator to weigh, not asserted as settled.
