# `diffn`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `diffn`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` per `tools/mzn_coverage.py --rank` (section `7. Packing and geometry`), ecode `E2` — **this session flags the tier itself as questionable; see "Is that classification right?" below** |
| **Status** | `nothing generated — blocked on E2` |
| **Generated** | no generator entry — there is no `cata/diffn.tex` |
| **Validator** | out of scope — no `cata/diffn.tex` exists |
| **Calibration** | `out of reach` — 0 rules generated |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:177` read |

## Constraint

`diffn` — no MiniZinc signature is vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt` lists `diffn` as a global of MiniZinc 2.10.1
(name only). `CHRISTMAS_LIST.md:177` files it under section `7. Packing and geometry`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:177`, literature cell, verbatim:

> none found

No paper is sourced in `catalog/_literature/` for `diffn`.

## Solver support

`CHRISTMAS_LIST.md:177`, solver cell, verbatim:

> decomp **[C]**

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/diffn.md` and no `cata/diffn.tex` — nobody has written this
constraint's decomposition in this project's format yet, regardless of the scope question
below.

## Scope of this entry

**Why it is currently filed out of scope.** `tools/mzn_coverage.py --rank` puts `diffn`
under `- out of scope`. `docs/ROADMAP.md:103-107` explains the ranking tool needed a
*section* filter (Packing/geometry, Graph/reachability, Sets, Maths-and-misc-floats) "because
geometry rows are coded E2/E8 rather than E5/E6/E7" (this task's own brief, corroborated by
the row below). `diffn` is in section `7. Packing and geometry`, so it is caught by that section filter.

**Is that classification right for `diffn`?** **Probably not — this looks like a section-filter false positive, and it is the clearest one in the whole out-of-scope tier.** `CHRISTMAS_LIST.md:177`'s route cell reads `E2 — pairwise non-overlap is a 4-way disjunction of var-var linear atoms, so actually reachable once E2 lands`. E2 ("richer side conditions": inequalities against expressions, 2-D constant tables) is not one of the three categories `docs/ROADMAP.md:106` names as excluded (E5/E6/E7); it is item 2 on the roadmap's own priority list (`CHRISTMAS_LIST.md:236-238`), described as "Biggest single unlock" and — the decisive point — `diffn` is **named explicitly** in that same list, alongside `disjunctive`, `maximum`, `minimum`, `inverse`, `sort`, `regular` and `table`, none of which are filed out of scope (`disjunctive` is tier D, `maximum`/`minimum` tier B). `diffn`'s shape, per the route cell itself, is exactly `disjunctive`'s in one more dimension: `d_i=0 ∨ d_j=0 ∨ s_i+d_i<=s_j ∨ s_j+d_j<=s_i`-style disjunctions of ordinary integer var-var atoms, no set/graph/float representation required. It is filed out of scope only because its section header is `7. Packing and geometry`, which the ranking tool's section filter also catches E5/E6/E7-coded rows under — but `diffn`'s own row carries `E2`, not E5/E6/E7.

**What would bring it in scope.** E2 — the same extension that would finish `regular`, unblock `table`, `disjunctive`, `maximum`/`minimum`, `sort`, `write*` (`CHRISTMAS_LIST.md:236-238`). This is near-term rule-engine work, not an architectural exclusion; recommend re-tiering `diffn`/`diffn_k`/`diffn_nonstrict`/`diffn_nonstrict_k` once E2 is scoped, rather than leaving them under 'out of scope' alongside `circuit` and `piecewise_linear`.

## Generated rules

None. No `cata/diffn.tex` exists.

## Status

**`nothing generated — blocked on E2`**

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
| `E2` | richer side conditions — inequalities against expressions and 2-D constant tables, not yet in the printer |

Extensions: `E2` (`CHRISTMAS_LIST.md:177`).
Source: `docs/ROADMAP.md:103-107`; `CHRISTMAS_LIST.md:227-244` ("What to actually ask for").

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `diffn` under tier `- out of scope`,
  ecode(s) `E2`, section `7. Packing and geometry`.
- `CHRISTMAS_LIST.md:177` read → literature, solver and route cells quoted above, verbatim.
- `CHRISTMAS_LIST.md:227-244` read → the "What to actually ask for" priority list, which is
  where the misclassification argument above comes from (comparing `diffn`'s named extension
  against constraints the same list treats as near-term, in-scope work).
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement, which names
  categories, not E-codes, and does not name `E2` as excluded on its own.
- `os.path.isfile("decomps/diffn.md")` → False. `os.path.isfile("cata/diffn.tex")` → False.
- Nothing was compiled, run or validated. The misclassification argument is this session's own
  reading, not a machine output — it is reasoning from the route cell and the priority list,
  flagged for the orchestrator to weigh, not asserted as settled.
