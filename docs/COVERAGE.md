# Coverage classification — `CHRISTMAS_LIST.md` against a MiniZinc release

`CHRISTMAS_LIST.md` was compiled by hand on 2026-09-18 and will rot the moment MiniZinc
ships a release. This document describes the tool that detects that rot, what it can and
cannot check, and the numbers it produced the first time it was run.

Task: **W0-T4** (`docs/ROADMAP.md`). Owner of `tools/` and this file: session **W0-B**.

---

## How to run it

```sh
# against a real MiniZinc installation — the intended mode
python3 tools/mzn_coverage.py --share /path/to/share/minizinc

# against the vendored snapshot — the fallback, used when no MiniZinc is installed
python3 tools/mzn_coverage.py

# machine-readable, and a gate that fails on drift
python3 tools/mzn_coverage.py --json coverage.json
python3 tools/mzn_coverage.py --check          # exit 1 if drift or a defect is found
```

Python 3.8+, standard library only, **no network at runtime**. There is no `make` target:
session W0-A owns the `Makefile` this wave, so the entry point is the plain command above.

Other flags: `--globals-file FILE` (point straight at a `globals.mzn`), `--snapshot FILE`
(pick a specific vendored snapshot), `--list FILE` (a different copy of the list),
`--emit-snapshot` (print the parsed global names one per line — this is how a new snapshot
is made).

## What it measures

The **canonical global set of a release** is the set of `include "<name>.mzn";` lines in
`<share>/std/globals.mzn`. That is the same definition `CHRISTMAS_LIST.md`'s own header
uses ("MiniZinc's `globals.mzn` (118 canonical entries)"), so the two are comparable.
Note this set is *not* every `.mzn` in `std/`: deprecated aliases such as
`alldifferent_except_0.mzn` exist as files but are not included by `globals.mzn`.

From `CHRISTMAS_LIST.md` the tool reads only the family tables under the `## <n>. <family>`
headings, and only their four columns. It resolves the list's two notational shorthands:

* a backticked token starting with `_` is a suffix on the **base** name of the same cell,
  so `` `global_cardinality`, `_closed`, `_low_up` `` means `global_cardinality_closed`
  and `global_cardinality_low_up` — not `global_cardinality_closed_low_up`;
* a token containing `*` (`lex_chain_*`, `*_orbitope`, `strictly_*`, `*_fn`) is matched as a
  glob against the release's names.

It then reports:

1. **drift, in both directions** — release globals with no row, and names the list mentions
   that are not globals of that release;
2. **distributions** of the machine-readable columns — E-code (per row and per covered
   global), solver class (`native` / `decomp` / unspecified), and whether the literature
   cell is a `none` variant or carries a citation;
3. **structural defects in the list** — a name claimed by two different rows, a row with no
   E-code. It reports them with line numbers and **never edits `CHRISTMAS_LIST.md`.**

## What it deliberately does not automate

**The literature column is not re-derivable by a script, and the tool does not try.** It
counts how many rows say "none" versus how many carry a citation; it cannot tell whether a
cited paper is the right one, whether it actually explains the constraint, or whether a
"none" is still true after a new CP/CPAIOR proceedings. That column cost a full session of
web research and only research can refresh it.

Two further things are out of scope by the same argument: the **solver** column (it came
from source inspection of Chuffed/Geas/Choco on 2026-09-18, and a coarse `native`/`decomp`
class is all a Markdown parser can recover), and the **decomposition-route prose** — the tool
extracts the `E0`–`E7` codes from it but does not judge whether the stated route is right.

**The point of the automation is catching drift between a MiniZinc release and the list, not
regenerating the research.**

## Which release this was measured against

`minizinc` is not on `PATH` in this environment, and `/usr/local/share/minizinc` holds only
Gecode redefinition files — there is no `std/` there, so it cannot be used as a share dir.

So `tools/data/minizinc-2.10.1-globals.txt` is a **vendored snapshot, not a live parse**, and
the file says so in its own header along with the source path and a `sha256` of the
`globals.mzn` it came from. The release is **MiniZinc 2.10.1**, released 31 August 2026;
the version is known from `project(libminizinc ... VERSION 2.10.1)` in the `CMakeLists.txt`
of the libminizinc source tree the snapshot was taken from, corroborated by the `2.10.1`
section of its `changes.rst`. The snapshot and a live `--share` parse of that same tree
produce byte-identical reports (verified by `diff`).

When MiniZinc is installed, run with `--share` and ignore the snapshot; the tool prints
`Live parse: yes` or `NO -- vendored snapshot` on every run so the two are never confused.
Version detection from a share dir tries, in order: `minizinc --version`, `project(...
VERSION ...)` in a `CMakeLists.txt` above `share/minizinc`, and finally the newest
`redefinitions-X.Y.Z.mzn` in `std/`, which it labels as a **lower bound only**.

---

## Results, run 2026-09-18 against the 2.10.1 snapshot

Every number below is **measured** by `tools/mzn_coverage.py`, not read off prose.

| | |
|---|---|
| globals in the release | **118** |
| rows in the family tables | 51 |
| distinct names the list mentions | 115 |
| release globals covered by a row | **113** (95.8%) |
| release globals with no row | 5 |
| names mentioned that are not globals of this release | 2 |

The list's own claim of "118 canonical entries" is **confirmed** for 2.10.1: the count comes
out at 118 `include` lines. That is a coincidence worth noting rather than a check of the
list's contents — it covers 113 of those 118.

### Drift found (reported, not fixed — W0-B does not own `CHRISTMAS_LIST.md`)

In the release, no row in the list:

| global | note |
|---|---|
| `all_equal` | **the sharp one** — `cata/allequal.tex` is a shipped catalog entry and the list has no row for the constraint at all (`grep -c 'all_equal' CHRISTMAS_LIST.md` → 0) |
| `lex_greater`, `lex_greatereq` | section 3 covers `lex_less`/`lex_lesseq` only; the `_greater` duals are separate `globals.mzn` entries |
| `cumulatives_opt` | section 6 names `cumulatives` and `cumulative_opt`, so this looks like a transcription slip rather than an omission |
| `disjunctive_strict_opt` | the `disjunctive`, `_strict`, `_opt` shorthand does not reach the four-way combination |

Named by the list, not a global of 2.10.1:

| name | note |
|---|---|
| `alldifferent_except_0` | the list already marks it `(alias)`, and it is correct to: `alldifferent_except_0.mzn` exists in `std/` as a deprecated alias but `globals.mzn` does not include it |
| `edit_distance` | does not exist in 2.10.1 `std/` at all, under any spelling |

### Structural defects in the list

* `cost_mdd` is named by **two** rows with **conflicting routes** — line 157 (section 5,
  `cost_regular, cost_mdd`, route `E1 + E2 + E3`) and line 214 (section 11,
  `cost_mdd, edit_distance`, route `E1 + E2`). Only one can be authoritative.
* Three rows carry no E-code: line 118 (`alldifferent_except_0`, the alias row — defensible),
  line 174 (`geost`, whose route cell says "out" rather than an E-code — also defensible, but
  a machine cannot tell "out of scope" from "not yet classified"), and line 213 (the `*_fn`
  functional-variants row, which covers 11 release globals with no route at all).

A follow-up worth considering: give "out of scope" its own code (`E8`, or reuse `E7`) so the
three cases above are distinguishable mechanically.

### Distributions

E-code per row (a row may carry several codes, so these do not sum to 51):

| code | rows |
|---|---|
| E0 | 19 |
| E1 | 6 |
| E2 | 16 |
| E3 | 7 |
| E4 | 4 |
| E5 | 5 |
| E6 | 4 |
| E7 | 3 |
| (none given) | 3 |

E-code combination per **covered release global** (these sum to 113):

| combination | globals |
|---|---|
| E0 | 32 |
| E2 | 18 |
| E5 | 10 |
| E6 | 10 |
| E0+E2 | 4 |
| E0+E3+E4 | 4 |
| E1+E2 | 4 |
| E3 | 4 |
| E2+E4 | 3 |
| E7 | 3 |
| E0+E3 | 1 |
| E0+E4 | 1 |
| E1 | 1 |
| E1+E2+E3 | 1 |
| E1+E3 | 1 |
| E2+E7 | 2 |
| E3+E6 | 2 |
| (none given) | 12 |

**32 of 118 release globals are claimed to need nothing beyond what the generator has
today (E0 alone).** That is the size of the reachable-now target — but the claim is the
list's, and it is unvalidated: per `CLAUDE.md`, until W0-T1 lands no catalog entry may be
reported as correct, and this tool checks coverage bookkeeping, never a rule.

Solver column, per row: `decomp` 32, `native` 17, unspecified 2.
Literature column, per row: a `none` variant 34, a citation 15, unspecified 2 — **presence
only**, see "What it deliberately does not automate" above.

## Rerunning on a new MiniZinc release

1. `python3 tools/mzn_coverage.py --share <new share/minizinc> --check`.
2. Every `+` line is a global the release added (or one the list always missed): it needs a
   row, and its literature cell needs a human.
3. Every `-` line is a name the release dropped or renamed: the row needs a note, not
   deletion — an explanation method for a removed constraint is still an explanation method.
4. If the release is worth pinning, regenerate the snapshot:
   `python3 tools/mzn_coverage.py --share <dir> --emit-snapshot > tools/data/minizinc-<ver>-globals.txt`
   and **write the provenance header by hand** (source path, sha256, date, and the words
   "NOT a live parse"). The tool picks the lexicographically newest snapshot by default.

---

## Priority ranking (added 2026-09-21)

`python3 tools/mzn_coverage.py` now ends with a ranking, and `--rank` prints every tier
instead of tier A alone. It is also in `--json`, under `result.ranking` and
`result.ranking_counts`.

**What it ranks, and what it does not.** It crosses two columns the list already carries —
literature present/absent, and solver native/decomposes — to estimate **the size of the gap a
derived schema would fill**. It says nothing about difficulty, elegance or scientific interest,
and it cannot: those are not in the list.

| tier | meaning | count, 2026-09-21 |
|---|---|---|
| **A** | no literature **and** solvers only decompose it | **36** |
| B | no literature, but a solver explains it natively | 8 |
| C | literature exists, and solvers decompose it anyway | 9 |
| D | literature **and** a native explaining propagator | 19 |
| – | unclassified: the list leaves a column blank | 11 |
| – | out of scope: sets, graph, geometry, floats | 35 |

**Tier A is the argument for this project in one number.** For those 36 constraints there is no
published explanation *and* no solver that explains them natively — so a generated schema would
be the only schema in existence. Tier D is the opposite: `table`, `regular`, `alldifferent`,
`cumulative` sit there, and for them the method is a **calibration target**, not a contribution.
That is worth keeping in view, because D is where the interesting constraints live and A is
where the value is.

Two scope rules, so the tiers agree with `docs/ROADMAP.md`: a row is out of scope if its route
carries E5/E6/E7, **or** if it is in the Packing-and-geometry, Graph-and-reachability or
Set-constraints section — geometry rows are coded E2/E8 and would otherwise rank as tier A.

Also fixed here: the E-code regex stopped at `E7` and so could not see **E8**/**E9** (D-0011),
and it parsed the `(was E3; …)` traceability notes as live routes. Both corrected; the notes are
stripped before the route is read.
