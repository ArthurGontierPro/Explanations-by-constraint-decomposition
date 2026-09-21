# `diffn_nonstrict`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `diffn_nonstrict`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`no-literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, ecode `E2`, section `7. Packing and geometry`. Re-tiered 2026-09-21 per **D-0014**: was filed `- out of scope` by the tool's section filter before the fix; see "History" below. |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | no generator entry — there is no `cata/diffn_nonstrict.tex` |
| **Validator** | not run — no `cata/diffn_nonstrict.tex` exists yet |
| **Calibration** | `out of reach` — 0 rules generated; no published shape exists to compare against (`CHRISTMAS_LIST.md:177`: "none found") |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank` (post-fix), `CHRISTMAS_LIST.md:177` and `:51` read, `docs/DECISIONS.md` D-0014 read |

## Constraint

`diffn_nonstrict` — no MiniZinc signature is vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt` lists `diffn_nonstrict` as a global of MiniZinc 2.10.1
(name only). `CHRISTMAS_LIST.md:177` files it under section `7. Packing and geometry`:
non-overlap of k-dimensional boxes.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:177`, literature cell, verbatim:

> none found

No paper is sourced in `catalog/_literature/` for `diffn_nonstrict`. `CHRISTMAS_LIST.md:51` is the
closer-in-spirit citation: the Huub paper reports the solver it studies losing "precisely on
`diffn`, `cumulative`" — evidence this is a real gap worth closing, not a claim of a
published explanation for `diffn_nonstrict` itself.

## Solver support

`CHRISTMAS_LIST.md:177`, solver cell, verbatim:

> decomp **[C]**

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None yet.** There is no `decomps/diffn_nonstrict.md` and no `cata/diffn_nonstrict.tex`. What it would take is
below.

## Scope of this entry

**In scope, pending G3.** `CHRISTMAS_LIST.md:177`'s route cell: `E2 — pairwise non-overlap
is a 4-way disjunction of var-var linear atoms, so actually reachable once E2 lands`. Per
**D-0014** (`docs/DECISIONS.md`, 2026-09-21), scope is decided by the mechanism a constraint
needs, not by the section it is filed under, and `diffn_nonstrict`'s mechanism — variable-vs-variable
linear atoms, `d_i=0 ∨ d_j=0 ∨ s_i+d_i<=s_j ∨ s_j+d_j<=s_i`-style disjunctions — is the same
one `disjunctive` (tier D), `maximum`/`minimum` (tier B) and `table`/`regular` need, none of
which are out of scope. The concrete blocker in this generator is **G3** — "only
variable-vs-domain-value comparisons exist, never variable-vs-variable"
(`docs/DECOMP_FORMAT_NOTES.md:34-41`): `Global_event`/`ind_modifs` express `X_i = t` for `t` an
index-derived domain value, never `X_i = Y_i` (or here, `s_i + d_i \le s_j`) for two decision
variables. `diffn_nonstrict`'s non-overlap disjunction is exactly this wall.

**What it would take to generate rules here.** First, G3 needs closing — a var-var comparison
event, not just a var-value one — which is the same prerequisite `disjunctive`, `maximum`/
`minimum`, `sort` and `table` are waiting on (`CHRISTMAS_LIST.md:227-238`, "What to actually
ask for", item 2, "biggest single unlock"). Second, someone writes `decomps/diffn_nonstrict.md`
encoding the 4-way disjunction per pair of boxes/tasks as a `rule4` (∨) over the new var-var
atoms. Neither step is done; this entry records the target, not a result.

**History.** This entry was first filed `- out of scope` by `tools/mzn_coverage.py --rank`'s
section filter, which caught every row under "7. Packing and geometry" regardless of its
E-code. A prior pass of this catalog (R3, 2026-09-21) flagged that as a probable
misclassification — `diffn_nonstrict`'s own route cell says `E2`, not E5/E6/E7, and `diffn_nonstrict` is named
alongside in-scope constraints in the roadmap's own priority list. The orchestrator checked
that finding, recorded **D-0014**, and fixed the tool (tier A count 36→43, out-of-scope
35→28). `diffn_nonstrict` is filed here under its corrected tier as a result — the classification was
checked, not assumed.

## Generated rules

None. No `cata/diffn_nonstrict.tex` exists.

## Status

**`nothing generated — blocked on G3`**

No decomposition has been attempted or encoded. This is a generator gap (G3, variable-vs-
variable comparison), not a scope exclusion: nothing in `docs/ROADMAP.md`'s "Explicitly out of
scope" list (`docs/ROADMAP.md:103-107`) names E2 or var-var comparison as excluded, and D-0014
confirms it.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — 0 rules generated, no decomposition encoded, and
`CHRISTMAS_LIST.md:177` records no published explanation to compare against even once one
is generated.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | only variable-vs-domain-value comparisons exist in the event type, never variable-vs-variable; `diffn_nonstrict`'s non-overlap disjunction needs `s_i+d_i \le s_j`-style atoms (`docs/DECOMP_FORMAT_NOTES.md:34-41`) |

Extensions: **E2** (`CHRISTMAS_LIST.md:177`, `:227-238`).
Source: `docs/DECOMP_FORMAT_NOTES.md:34-41` (G3); `docs/DECISIONS.md` D-0014.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (re-run 2026-09-21, post-fix) → `diffn_nonstrict` under tier
  **A**, ecode `E2`, section `7. Packing and geometry`.
- `CHRISTMAS_LIST.md:177` read → literature, solver and route cells quoted above, verbatim.
- `CHRISTMAS_LIST.md:51` read → the Huub-solver citation used as evidence this is a live gap.
- `CHRISTMAS_LIST.md:227-238` read → the "What to actually ask for" priority list naming
  `diffn_nonstrict` beside `disjunctive`/`maximum`/`minimum`/`table`/`regular`.
- `docs/DECISIONS.md` D-0014 read → the re-tiering decision, the tool fix, and the before/after
  tier counts (36→43 tier A, 35→28 out of scope).
- `docs/DECOMP_FORMAT_NOTES.md:34-41` read → G3's definition and its explicit E2 cross-reference.
- `os.path.isfile("decomps/diffn_nonstrict.md")` → False. `os.path.isfile("cata/diffn_nonstrict.tex")` → False.
- Nothing was compiled, run or validated. No rules exist yet for `diffn_nonstrict`; this entry states
  the target (G3) and the history of how the tier was corrected, not a generated result.
