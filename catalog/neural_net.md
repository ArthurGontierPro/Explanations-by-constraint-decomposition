# `neural_net`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `neural_net`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E7`, section `11. Maths and misc` |
| **Status** | `nothing generated — blocked on E7` |
| **Generated** | no generator entry — there is no `cata/neural_net.tex` |
| **Validator** | out of scope — no `cata/neural_net.tex` exists for `make validate` to check |
| **Calibration** | see Calibration section below |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:215` read |

## Constraint

`neural_net` — no MiniZinc signature is vendored in this repo.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt` lists `neural_net` as a
global of MiniZinc 2.10.1 (name only, no signature). `CHRISTMAS_LIST.md:215` files it
under section `11. Maths and misc`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:215`, literature cell, verbatim:

> none

No paper has been fetched or read for this entry; `catalog/_literature/` has no file for
`neural_net`, and none is written here (`catalog/TEMPLATE.md`: never state a rule shape from
memory).

## Solver support

`CHRISTMAS_LIST.md:215`, solver cell, verbatim:

> decomp

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/neural_net.md` and no `cata/neural_net.tex`; no decomposition in
this project's format has been written for `neural_net`.

## Scope of this entry

**Why out of scope.** `docs/ROADMAP.md:103-107` ("Explicitly out of scope") names
"floats (E7)" as one of the three categories out of scope. `CHRISTMAS_LIST.md:105` marks E7 "out of scope" outright, with no proposed mechanism, unlike E5's membership matrix or E6's graph reasoning — there is no float-valued literal in the generator's event type and none is planned. `CHRISTMAS_LIST.md:215`'s decomposition-route cell gives the extension code(s)
`E7`:

> **E7**

**Is that classification right for `neural_net`?** Yes. `piecewise_linear`/`piecewise_linear_non_continuous` are literally float-domain constraints and `neural_net` composes them; none has an integer/Boolean encoding to decompose in the first place.

**What would bring it in scope.** Same as the graph group: `CHRISTMAS_LIST.md:244` says "declare out of scope", not "schedule E7". Nothing in `docs/ROADMAP.md` proposes a route in.

## Generated rules

None. No `cata/neural_net.tex` exists, so there is nothing to render.

## Status

**`nothing generated — blocked on E7`**

No decomposition has been attempted, encoded or generated for `neural_net`. This is a scope
decision recorded in `docs/ROADMAP.md`, not a claim that one was tried and failed.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — with **0** rules generated and no decomposition encoded,
no comparison against a published shape is statable, independent of whether a paper
exists. See the Published explanation section for what the literature cell actually says.

## Gaps

| gap | what it blocks here |
|---|---|
| `E7` | float/non-linear arithmetic; declared out of scope, not on the extension roadmap (`CHRISTMAS_LIST.md:102`, `docs/ROADMAP.md:106`) |

Extensions: `E7` (`CHRISTMAS_LIST.md:215`), legend at `CHRISTMAS_LIST.md:97-105`.
Source: `docs/ROADMAP.md:103-107`, `docs/DECOMP_FORMAT_NOTES.md` for the numbered
rule-engine gaps (none of which model set, graph or float variables — see gap table
there, G1-G18, all internal to the integer/Boolean event format).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `neural_net` under tier `- out of scope`,
  ecode(s) `E7`, section `11. Maths and misc`.
- `CHRISTMAS_LIST.md:215` read → literature, solver and route cells quoted above, verbatim.
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement.
- `os.path.isfile("decomps/neural_net.md")` → False. `os.path.isfile("cata/neural_net.tex")` → False.
- `CHRISTMAS_LIST.md:97-105` (Legend) read → the E-code definitions quoted/paraphrased above.
- Nothing was compiled, run or validated. The scope judgement above is this session's own
  reading of the route cell against `docs/ROADMAP.md`'s exclusion list, not a machine output.
