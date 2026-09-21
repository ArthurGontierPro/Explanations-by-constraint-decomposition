# `network_flow`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `network_flow`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E6+E3`, section `8. Graph and reachability` |
| **Status** | `nothing generated — blocked on E6` |
| **Generated** | no generator entry — there is no `cata/network_flow.tex` |
| **Validator** | out of scope — no `cata/network_flow.tex` exists for `make validate` to check |
| **Calibration** | see Calibration section below |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:187` read |

## Constraint

`network_flow` — no MiniZinc signature is vendored in this repo.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt` lists `network_flow` as a
global of MiniZinc 2.10.1 (name only, no signature). `CHRISTMAS_LIST.md:187` files it
under section `8. Graph and reachability`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:187`, literature cell, verbatim:

> flow: Downing et al. 2012 (above)

No paper has been fetched or read for this entry; `catalog/_literature/` has no file for
`network_flow`, and none is written here (`catalog/TEMPLATE.md`: never state a rule shape from
memory).

## Solver support

`CHRISTMAS_LIST.md:187`, solver cell, verbatim:

> **native** (`mst.cpp`, `minimum_weight_tree.cpp`)

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/network_flow.md` and no `cata/network_flow.tex`; no decomposition in
this project's format has been written for `network_flow`.

## Scope of this entry

**Why out of scope.** `docs/ROADMAP.md:103-107` ("Explicitly out of scope") names
"graph and reachability (E6)" as one of the three categories out of scope. `CHRISTMAS_LIST.md:105`'s own definition of E6 is stronger than a missing feature: "reachability/connectivity arguments have no finite Boolean decomposition that preserves the propagation-relevant reasoning" at all, for any n — not a gap this generator's event type could close by adding a literal. `CHRISTMAS_LIST.md:187`'s decomposition-route cell gives the extension code(s)
`E6+E3`:

> **E6 + E3**

**Is that classification right for `network_flow`?** Mostly, but the E3 half is worth separating out. `docs/DECISIONS.md` (D-0011) split the old catch-all E3 into E8 (weighted sums) and E9 (integer-valued sums); this row predates that split and still reads `E3`. Either way the *dominant* reason this constraint cannot be explained here is E6 — the minimum-spanning-tree/max-flow argument is a graph-cut argument over the run-time structure, which is exactly what E6 rules out. The cardinality-style half (E3/E8/E9) would not by itself unblock this constraint if E6 stayed closed.

**What would bring it in scope.** E6 primarily (`docs/ROADMAP.md:244`: "declare out of scope"). Even a full E8/E9 landing (weighted/integer sums) would not reach this constraint on its own, since the flow-cut argument is graph reasoning, not a counting one.

## Generated rules

None. No `cata/network_flow.tex` exists, so there is nothing to render.

## Status

**`nothing generated — blocked on E6`**

No decomposition has been attempted, encoded or generated for `network_flow`. This is a scope
decision recorded in `docs/ROADMAP.md`, not a claim that one was tried and failed.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — with **0** rules generated and no decomposition encoded,
no comparison against a published shape is statable, independent of whether a paper
exists. See the Published explanation section for what the literature cell actually says.

## Gaps

| gap | what it blocks here |
|---|---|
| `E6` | reachability/connectivity has no finite Boolean decomposition that preserves the propagation-relevant reasoning (`CHRISTMAS_LIST.md:101`); `docs/ROADMAP.md`'s own priority list says to "declare out of scope" rather than schedule this |

Extensions: `E6+E3` (`CHRISTMAS_LIST.md:187`), legend at `CHRISTMAS_LIST.md:97-105`.
Source: `docs/ROADMAP.md:103-107`, `docs/DECOMP_FORMAT_NOTES.md` for the numbered
rule-engine gaps (none of which model set, graph or float variables — see gap table
there, G1-G18, all internal to the integer/Boolean event format).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `network_flow` under tier `- out of scope`,
  ecode(s) `E6+E3`, section `8. Graph and reachability`.
- `CHRISTMAS_LIST.md:187` read → literature, solver and route cells quoted above, verbatim.
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement.
- `os.path.isfile("decomps/network_flow.md")` → False. `os.path.isfile("cata/network_flow.tex")` → False.
- `CHRISTMAS_LIST.md:97-105` (Legend) read → the E-code definitions quoted/paraphrased above.
- Nothing was compiled, run or validated. The scope judgement above is this session's own
  reading of the route cell against `docs/ROADMAP.md`'s exclusion list, not a machine output.
