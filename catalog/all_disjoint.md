# `all_disjoint`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `all_disjoint`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E5`, section `1. AllDifferent family` |
| **Status** | `nothing generated — blocked on E5` |
| **Generated** | no generator entry — there is no `cata/all_disjoint.tex` |
| **Validator** | out of scope — no `cata/all_disjoint.tex` exists for `make validate` to check |
| **Calibration** | see Calibration section below |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:119` read |

## Constraint

`all_disjoint` — no MiniZinc signature is vendored in this repo.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt` lists `all_disjoint` as a
global of MiniZinc 2.10.1 (name only, no signature). `CHRISTMAS_LIST.md:119` files it
under section `1. AllDifferent family`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:119`, literature cell, verbatim:

> none

No paper has been fetched or read for this entry; `catalog/_literature/` has no file for
`all_disjoint`, and none is written here (`catalog/TEMPLATE.md`: never state a rule shape from
memory).

## Solver support

`CHRISTMAS_LIST.md:119`, solver cell, verbatim:

> decomp

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/all_disjoint.md` and no `cata/all_disjoint.tex`; no decomposition in
this project's format has been written for `all_disjoint`.

## Scope of this entry

**Why out of scope.** `docs/ROADMAP.md:103-107` ("Explicitly out of scope") names
"set variables unless channelled to Booleans first (E5)" as one of the three categories out of scope. The generator's event type is `(sign, variable, index list, AC|BC)` over integer/Boolean literals like `X_i = t` (`CLAUDE.md`, "the generator's design, in one paragraph"); there is no literal for set membership `v in S_i`, so nothing in `S_i` can appear in a premise or conclusion at all. `CHRISTMAS_LIST.md:119`'s decomposition-route cell gives the extension code(s)
`E5`:

> **E5** (set variables)

**Is that classification right for `all_disjoint`?** Yes, correctly filed. `all_disjoint` generalises `all_different` to disjointness of sets of variables/values rather than single values, and the route cell says outright it is `E5` "(set variables)" — the same membership-matrix gap as the rest of this group, not a section artefact.

**What would bring it in scope.** E5, same as the rest of this group; once the membership matrix exists this becomes an `all_different`-style disjointness rule over `b[i,v]` literals instead of `X_i=t` ones.

## Generated rules

None. No `cata/all_disjoint.tex` exists, so there is nothing to render.

## Status

**`nothing generated — blocked on E5`**

No decomposition has been attempted, encoded or generated for `all_disjoint`. This is a scope
decision recorded in `docs/ROADMAP.md`, not a claim that one was tried and failed.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — with **0** rules generated and no decomposition encoded,
no comparison against a published shape is statable, independent of whether a paper
exists. See the Published explanation section for what the literature cell actually says.

## Gaps

| gap | what it blocks here |
|---|---|
| `E5` | set variables have no channel to Boolean literals in the generator's event type; needs the membership matrix `b[i,v] <-> v in S_i` (`CHRISTMAS_LIST.md:99`) |

Extensions: `E5` (`CHRISTMAS_LIST.md:119`), legend at `CHRISTMAS_LIST.md:97-105`.
Source: `docs/ROADMAP.md:103-107`, `docs/DECOMP_FORMAT_NOTES.md` for the numbered
rule-engine gaps (none of which model set, graph or float variables — see gap table
there, G1-G18, all internal to the integer/Boolean event format).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `all_disjoint` under tier `- out of scope`,
  ecode(s) `E5`, section `1. AllDifferent family`.
- `CHRISTMAS_LIST.md:119` read → literature, solver and route cells quoted above, verbatim.
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement.
- `os.path.isfile("decomps/all_disjoint.md")` → False. `os.path.isfile("cata/all_disjoint.tex")` → False.
- `CHRISTMAS_LIST.md:97-105` (Legend) read → the E-code definitions quoted/paraphrased above.
- Nothing was compiled, run or validated. The scope judgement above is this session's own
  reading of the route cell against `docs/ROADMAP.md`'s exclusion list, not a machine output.
