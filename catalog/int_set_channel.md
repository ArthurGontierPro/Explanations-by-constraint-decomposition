# `int_set_channel`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `int_set_channel`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, ecode `E5`, section `9. Ordering, sorting, channelling` |
| **Status** | `nothing generated — blocked on E5` |
| **Generated** | no generator entry — there is no `cata/int_set_channel.tex` |
| **Validator** | out of scope — no `cata/int_set_channel.tex` exists for `make validate` to check |
| **Calibration** | see Calibration section below |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:200` read |

## Constraint

`int_set_channel` — no MiniZinc signature is vendored in this repo.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt` lists `int_set_channel` as a
global of MiniZinc 2.10.1 (name only, no signature). `CHRISTMAS_LIST.md:200` files it
under section `9. Ordering, sorting, channelling`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:200`, literature cell, verbatim:

> none

No paper has been fetched or read for this entry; `catalog/_literature/` has no file for
`int_set_channel`, and none is written here (`catalog/TEMPLATE.md`: never state a rule shape from
memory).

## Solver support

`CHRISTMAS_LIST.md:200`, solver cell, verbatim:

> decomp

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/int_set_channel.md` and no `cata/int_set_channel.tex`; no decomposition in
this project's format has been written for `int_set_channel`.

## Scope of this entry

**Why out of scope.** `docs/ROADMAP.md:103-107` ("Explicitly out of scope") names
"set variables unless channelled to Booleans first (E5)" as one of the three categories out of scope. The generator's event type is `(sign, variable, index list, AC|BC)` over integer/Boolean literals like `X_i = t` (`CLAUDE.md`, "the generator's design, in one paragraph"); there is no literal for set membership `v in S_i`, so nothing in `S_i` can appear in a premise or conclusion at all. `CHRISTMAS_LIST.md:200`'s decomposition-route cell gives the extension code(s)
`E5`:

> **E5** — and `link_set_to_booleans` *is* the E5 mechanism

**Is that classification right for `int_set_channel`?** Yes, and it is worth noting explicitly: `int_set_channel` is filed under "Ordering, sorting, channelling" by section, but the route cell is unambiguous `E5`. It is not geometry or graph out-of-scope by association; it is the channelling constraint itself, which is definitionally what E5 is for.

**What would bring it in scope.** E5. `CHRISTMAS_LIST.md:200` says the sibling `link_set_to_booleans` *is* the E5 mechanism, so `int_set_channel` (channelling an int-set pair rather than a set-to-Boolean array) is essentially the same construction once that lands.

## Generated rules

None. No `cata/int_set_channel.tex` exists, so there is nothing to render.

## Status

**`nothing generated — blocked on E5`**

No decomposition has been attempted, encoded or generated for `int_set_channel`. This is a scope
decision recorded in `docs/ROADMAP.md`, not a claim that one was tried and failed.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — with **0** rules generated and no decomposition encoded,
no comparison against a published shape is statable, independent of whether a paper
exists. See the Published explanation section for what the literature cell actually says.

## Gaps

| gap | what it blocks here |
|---|---|
| `E5` | set variables have no channel to Boolean literals in the generator's event type; needs the membership matrix `b[i,v] <-> v in S_i` (`CHRISTMAS_LIST.md:99`) |

Extensions: `E5` (`CHRISTMAS_LIST.md:200`), legend at `CHRISTMAS_LIST.md:97-105`.
Source: `docs/ROADMAP.md:103-107`, `docs/DECOMP_FORMAT_NOTES.md` for the numbered
rule-engine gaps (none of which model set, graph or float variables — see gap table
there, G1-G18, all internal to the integer/Boolean event format).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `int_set_channel` under tier `- out of scope`,
  ecode(s) `E5`, section `9. Ordering, sorting, channelling`.
- `CHRISTMAS_LIST.md:200` read → literature, solver and route cells quoted above, verbatim.
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement.
- `os.path.isfile("decomps/int_set_channel.md")` → False. `os.path.isfile("cata/int_set_channel.tex")` → False.
- `CHRISTMAS_LIST.md:97-105` (Legend) read → the E-code definitions quoted/paraphrased above.
- Nothing was compiled, run or validated. The scope judgement above is this session's own
  reading of the route cell against `docs/ROADMAP.md`'s exclusion list, not a machine output.
