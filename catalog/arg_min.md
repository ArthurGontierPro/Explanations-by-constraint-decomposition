# `arg_min`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `arg_min`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` per `tools/mzn_coverage.py --rank` (section `9. Ordering, sorting, channelling`), ecode `E2+E7` — **this session flags the tier itself as questionable; see "Is that classification right?" below** |
| **Status** | `nothing generated — blocked on E2 (int/bool variant) / E7 (float variant)` |
| **Generated** | no generator entry — there is no `cata/arg_min.tex` |
| **Validator** | out of scope — no `cata/arg_min.tex` exists |
| **Calibration** | `out of reach` — 0 rules generated |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:197` read |

## Constraint

`arg_min` — no MiniZinc signature is vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt` lists `arg_min` as a global of MiniZinc 2.10.1
(name only). `CHRISTMAS_LIST.md:197` files it under section `9. Ordering, sorting, channelling`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:197`, literature cell, verbatim:

> none

No paper is sourced in `catalog/_literature/` for `arg_min`.

## Solver support

`CHRISTMAS_LIST.md:197`, solver cell, verbatim:

> native for bool (`bool_arg_max.cpp`)

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/arg_min.md` and no `cata/arg_min.tex` — nobody has written this
constraint's decomposition in this project's format yet, regardless of the scope question
below.

## Scope of this entry

**Why it is currently filed out of scope.** `tools/mzn_coverage.py --rank` puts `arg_min`
under `- out of scope`. `docs/ROADMAP.md:103-107` explains the ranking tool needed a
*section* filter (Packing/geometry, Graph/reachability, Sets, Maths-and-misc-floats) "because
geometry rows are coded E2/E8 rather than E5/E6/E7" (this task's own brief, corroborated by
the row below). `arg_min` is in section `9. Ordering, sorting, channelling`, so it is caught by that section filter.

**Is that classification right for `arg_min`?** **Partly.** `CHRISTMAS_LIST.md:197`'s route cell reads `E2; float variants E7`, and the row's solver cell notes a **native Boolean propagator already exists** (`bool_arg_max.cpp`) — which is the E2 case, not E7. That puts this constraint in the same position as `maximum`/`minimum` on the line just above it (`CHRISTMAS_LIST.md:196`, native `minimum.cpp`, route `E2`), which is **tier B** ("no-literature + solver-native"), not out of scope. `arg_max`/`arg_min` are polymorphic in MiniZinc — int and float array variants share a name — and only the **float** variant is genuinely E7 (out of scope, `docs/ROADMAP.md:106`); the **int/Boolean** variant, for which a native explaining propagator already exists per this row, is E2-reachable now, same as `maximum`/`minimum`. Filing the whole name under 'out of scope' conflates the two variants.

**What would bring it in scope.** For the int/Boolean variant: E2 (var-var atoms), same as `maximum`/`minimum` — arguably should sit in tier B alongside them rather than out of scope. For the float variant: E7, genuinely out of scope per `docs/ROADMAP.md:106`. Recommend splitting this row's tier judgement by variant rather than filing the name as one entry.

## Generated rules

None. No `cata/arg_min.tex` exists.

## Status

**`nothing generated — blocked on E2 (int/bool variant) / E7 (float variant)`**

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
| `E2 (int/bool variant) / E7 (float variant)` | E2 (int/bool variant) / E7 (float variant) |

Extensions: `E2+E7` (`CHRISTMAS_LIST.md:197`).
Source: `docs/ROADMAP.md:103-107`; `CHRISTMAS_LIST.md:227-244` ("What to actually ask for").

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `arg_min` under tier `- out of scope`,
  ecode(s) `E2+E7`, section `9. Ordering, sorting, channelling`.
- `CHRISTMAS_LIST.md:197` read → literature, solver and route cells quoted above, verbatim.
- `CHRISTMAS_LIST.md:227-244` read → the "What to actually ask for" priority list, which is
  where the misclassification argument above comes from (comparing `arg_min`'s named extension
  against constraints the same list treats as near-term, in-scope work).
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement, which names
  categories, not E-codes, and does not name `E2+E7` as excluded on its own.
- `os.path.isfile("decomps/arg_min.md")` → False. `os.path.isfile("cata/arg_min.tex")` → False.
- Nothing was compiled, run or validated. The misclassification argument is this session's own
  reading, not a machine output — it is reasoning from the route cell and the priority list,
  flagged for the orchestrator to weigh, not asserted as settled.
