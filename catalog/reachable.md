# `reachable`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `reachable`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E6`, section `8. Graph and reachability` |
| **Status** | `nothing generated — blocked on E6` |
| **Generated** | no generator entry — there is no `cata/reachable.tex` |
| **Validator** | out of scope — no `cata/reachable.tex` exists for `make validate` to check |
| **Calibration** | see Calibration section below |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:186` read |

## Constraint

`reachable` — no MiniZinc signature is vendored in this repo.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt` lists `reachable` as a
global of MiniZinc 2.10.1 (name only, no signature). `CHRISTMAS_LIST.md:186` files it
under section `8. Graph and reachability`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:186`, literature cell, verbatim:

> none found beyond the circuit line of work

No paper has been fetched or read for this entry; `catalog/_literature/` has no file for
`reachable`, and none is written here (`catalog/TEMPLATE.md`: never state a rule shape from
memory).

## Solver support

`CHRISTMAS_LIST.md:186`, solver cell, verbatim:

> **native** (`tree.cpp`, `dtree.cpp`, `dag.cpp`, `dconnected.cpp`, `bounded_path.cpp`, `well-founded.cpp`, `EdExplFinder.cpp`) **[C✗ for `tree`]**

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/reachable.md` and no `cata/reachable.tex`; no decomposition in
this project's format has been written for `reachable`.

## Scope of this entry

**Why out of scope.** `docs/ROADMAP.md:103-107` ("Explicitly out of scope") names
"graph and reachability (E6)" as one of the three categories out of scope. `CHRISTMAS_LIST.md:105`'s own definition of E6 is stronger than a missing feature: "reachability/connectivity arguments have no finite Boolean decomposition that preserves the propagation-relevant reasoning" at all, for any n — not a gap this generator's event type could close by adding a literal. `CHRISTMAS_LIST.md:186`'s decomposition-route cell gives the extension code(s)
`E6`:

> **E6** — Chuffed has a dedicated *edge explanation finder*, which tells you how far this is from clause unfolding

**Is that classification right for `reachable`?** Yes. Every constraint in this group has a **native** Chuffed propagator built on a dedicated graph algorithm (see Solver support), and the published explanations that exist (Francis & Stuckey for `circuit`/`subcircuit`) are reachability arguments over the run-time graph, not over a finite unrolled Boolean formula. This is not a section-filter artefact: the route cell itself says `E6`, and E6 is one of the three categories `docs/ROADMAP.md:106` names explicitly.

**What would bring it in scope.** `docs/ROADMAP.md`'s own priority list (`CHRISTMAS_LIST.md:244`, item 7) reads "E6 / E7 — graph and float. Declare out of scope" — this is not scheduled as a future extension the way E5 is ("mechanical once the membership matrix exists", item 6). Getting this constraint in scope would need a new kind of literal over graph reachability facts, which nothing in this project's roadmap proposes.

## Generated rules

None. No `cata/reachable.tex` exists, so there is nothing to render.

## Status

**`nothing generated — blocked on E6`**

No decomposition has been attempted, encoded or generated for `reachable`. This is a scope
decision recorded in `docs/ROADMAP.md`, not a claim that one was tried and failed.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — with **0** rules generated and no decomposition encoded,
no comparison against a published shape is statable, independent of whether a paper
exists. See the Published explanation section for what the literature cell actually says.

## Gaps

| gap | what it blocks here |
|---|---|
| `E6` | reachability/connectivity has no finite Boolean decomposition that preserves the propagation-relevant reasoning (`CHRISTMAS_LIST.md:101`); `docs/ROADMAP.md`'s own priority list says to "declare out of scope" rather than schedule this |

Extensions: `E6` (`CHRISTMAS_LIST.md:186`), legend at `CHRISTMAS_LIST.md:97-105`.
Source: `docs/ROADMAP.md:103-107`, `docs/DECOMP_FORMAT_NOTES.md` for the numbered
rule-engine gaps (none of which model set, graph or float variables — see gap table
there, G1-G18, all internal to the integer/Boolean event format).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `reachable` under tier `- out of scope`,
  ecode(s) `E6`, section `8. Graph and reachability`.
- `CHRISTMAS_LIST.md:186` read → literature, solver and route cells quoted above, verbatim.
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement.
- `os.path.isfile("decomps/reachable.md")` → False. `os.path.isfile("cata/reachable.tex")` → False.
- `CHRISTMAS_LIST.md:97-105` (Legend) read → the E-code definitions quoted/paraphrased above.
- Nothing was compiled, run or validated. The scope judgement above is this session's own
  reading of the route cell against `docs/ROADMAP.md`'s exclusion list, not a machine output.
