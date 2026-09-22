# `minimum`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `minimum`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecodes `['E2']` (shared row with `maximum`) |
| **Status** | `encodable today, not encoded` — **there is no gap to name**. The decomposition is `maximum`'s with one constructor changed; it was written and run in a scratch copy of the generator, and it works (below). It is not in `explenation generator.ml` and there is no `cata/minimum.tex` |
| **Generated** | **0** rules shipped. **4** rules in the scratch run, all sound and minimal — not committed, because `cata/minimum.tex` was outside session X-max's ownership |
| **Validator** | out of scope: nothing in `cata/` to validate. It would be out of reach anyway — `validator.ml`'s entry lists are hardcoded and it never scans `cata/` (**W1-T18**) |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:196` records the literature column as `none found` |
| **Last measured** | 2026-09-22, scratch run of a modified generator copy plus an exhaustive assignment sweep. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Constraint

`minimum(var int: m, array[int] of var int: x)`

`m = min_i(x_i)`: `m` is the smallest element of `x`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:94` carries the *name* only. The MiniZinc type
signature and argument order above are recall.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:196`'s literature column reads, verbatim,
`none found`.

**That phrasing is not the same as the bare `none` used on most rows**, and the difference
is recorded rather than smoothed over: `catalog/element.md` reads `none found` as "a
searched-and-empty finding", i.e. somebody looked. Either way the verdict below is the
same, because `catalog/README.md` and `catalog/TEMPLATE.md` give one verdict for an empty
literature cell.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. No web access was used and no search was made by this
session.

## Solver support

| | |
|---|---|
| Chuffed | native (`minimum.cpp`) |
| Geas | absent |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:196`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: **native** (`minimum.cpp`) **[C]**. Unlike its row-mate
[`maximum`](maximum.md), *this* name is the one the parenthetical actually supports.

## Decomposition used here

**Generator value:** none, and that is now a matter of nobody having typed it rather than
nobody having been able to.
**Emitted by:** nothing. There is no `explainall … "cata/minimum.tex"` call.
**Spec:** `decomps/maximum.md`, which covers this name and, since 2026-09-22, states the
decomposition rather than declaring it impossible.
**Shape:** [`maximum`](maximum.md)'s three-step channel with `rule3` (∧) in place of `rule4`
(∨):

| ctr | schema | meaning |
|---|---|---|
| 1 | `rule1` | `X_i ≥ t ⇔ B1_{i,t}` (BC) |
| 2 | `rule3` | `B2_t ⇔ ⋀_{i ∈ [[1,n]]} B1_{i,t}` |
| 3 | `rule1` | `O ≥ t ⇔ B2_t` (BC) |

**The dual is `m ≥ t ⇔ ⋀_i (x_i ≥ t)`, and this was checked rather than assumed** — the
natural-looking `m ≤ t ⇔ ⋀_i x_i ≤ t` is **false**, since `min_i x_i ≤ t` holds iff *some*
`x_i ≤ t`. The generator's positive `BC` atom is `≥`, not `≤`, so the conjunctive form is the
one that fits the language, and `rule3` is the constructor that expresses it. One line, one
word changed from `maxi`.

## Scope of this entry

**Events the generator was asked to explain:** **none in the shipped generator.** In the
scratch run, four — `X_i ≥ t`, `X_i < t`, `O ≥ t`, `O < t` — the same seeds `maximum` uses.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 1 | **1** (scratch only) | none |
| `X_{i}<t` | 1 | **1** (scratch only) | none |
| `O_{} \geq t` | 1 | **1** (scratch only) | none |
| `O_{}<t` | 1 | **1** (scratch only) | none |

### The claim this entry overturns

The previous version of this file said, quoting `decomps/maximum.md`:

> "No decomposition can be authored in the current encoding — this is not a derivation gap,
> it is a missing primitive."

**That is false**, for `minimum` exactly as for `maximum`, and for the same reason: it
reasoned from the direct decomposition (`∀i: m ≤ x_i`, `∃i: m = x_i`) and concluded about the
constraint. The generator's `BC` literals already are the order encoding, under which the
comparison between `m` and `x_i` **factors through a shared threshold** and every atom becomes
variable-against-value. The full argument is in [`maximum`](maximum.md), "The claim this entry
overturns, and why it was wrong"; it is not repeated here.

## Generated rules

**None shipped.** There is no `cata/minimum.tex`.

**In the scratch run** (session X-max, 2026-09-22: a copy of `explenation generator.ml` with
the value above added and one `explainall` call; run to completion, output read, copy
discarded). Four rules, the exact duals of `maximum`'s:

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `O ≥ t`  ⊢  `X_i ≥ t` | **SOUND**, **MINIMAL** |
| 2 | `∀i'≠i ∈ [[1,n]]: X_{i'} ≥ t`, `O < t`  ⊢  `X_i < t` | **SOUND**, **MINIMAL** |
| 3 | `∀i ∈ [[1,n]]: X_i ≥ t`  ⊢  `O ≥ t` | **SOUND**, **MINIMAL** |
| 4 | `∃i ∈ [[1,n]]: X_i < t`  ⊢  `O < t` | **SOUND**, **MINIMAL** |

Measured by exhaustive enumeration of every assignment satisfying `O = min_i X_i` with
`X_i ∈ [1,m]`, for every `n, m ∈ {1,2,3,4,5}` — **`n = 1` included**, which is where the
shipped `alldifferent` rule was found to fail (`catalog/README.md`, W1-T19). **0
counterexamples** on all four; firing counts **37329 / 4158 / 7995 / 18204**; every premise
needed, so none is droppable and all four are minimal. Same instrument as
[`maximum`](maximum.md), whose entry describes it in full.

**These verdicts describe a rule set that is not in the repository.** They are here so that
whoever lands `minimum` knows what to expect and can tell a regression from a surprise — not
as a claim about a shipped artifact. Nothing here is "validated" and nothing here is
"correct".

## Status

**`encodable today, not encoded`**

`catalog/README.md` added this status on 2026-09-21 for exactly this situation: "the current
format can already express the decomposition, but nothing in the generator does it, so **there
is no gap to name**. Use this rather than inventing a G-number to satisfy the row above."
`minimum` is now its second case, after `strictly_increasing`/`strictly_decreasing`, and it is
a stronger case than those: the decomposition has been written and run, not merely judged
expressible.

**It is not `nothing generated — blocked on G3`**, which is what this file said before
2026-09-22. Nor is it `generated, unvalidated` — nothing is generated in the repository.

**What it takes to land:** one `let minim = …` in the decomposition table, one
`let _ = explainall [xbc;mbc] minim "cata/minimum.tex"`, one regenerated golden, and the
`%% CAVEAT` numbers above. `mbc`, the scalar-bound seed event, already exists
(`explenation generator.ml:1079`) — it was added for `maximum` and is not `maximum`-specific.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:196`'s literature column reads `none found`. Per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing`: no paper is cited.
Not `out of reach`: that verdict needs a published premise to be out of reach of.

**Worth recording beside it:** `minimum` has a native explaining propagator in Chuffed —
here the citation is direct, `minimum.cpp` — and a `[C]` in Choco LCG. So explaining
implementations exist without a paper describing them. Calibrating against an implementation
is not possible from this repo: no solver source is vendored, and `CLAUDE.md` forbids
web-searching ahead of the index.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **nothing. Refuted for this constraint** by the scratch run, on the same evidence as [`maximum`](maximum.md). `m ≤ x_i` factors through a shared threshold; the order encoding performs the factoring; no variable-vs-variable atom survives |
| `G2` | the **legibility cost**, unchanged and inherited: `m` would print as `O` (`var_name`, `explenation generator.ml:3`, has no constructor for a constraint's own scalar bound) and as `O_{} ≥ t` with empty subscript braces. Both LaTeX no-ops, neither a blocker |
| — | **not a gap: nobody has written the two lines.** That is what `encodable today, not encoded` means |

Extensions: `CHRISTMAS_LIST.md:196` routes this constraint through **E2** ("var-var atoms").
On this evidence **`minimum` needs no extension** — it is E0, and the E2 routing is a
consequence of the retracted claim. `CHRISTMAS_LIST.md` is not this session's file to edit;
the discrepancy is reported.

## How this entry was produced

- A copy of `explenation generator.ml` in a scratch directory, with `minim` added and one
  `explainall` call; run under OCaml 5.1.1 in the `baguette` switch; exit 0, empty stderr;
  `cata/minimum.tex` produced and read. **The copy was discarded and nothing in the
  repository was changed by it** — `cata/minimum.tex` was outside session X-max's ownership.
- An exhaustive assignment sweep over `O = min_i X_i` for every `n,m ∈ {1,2,3,4,5}`,
  including `n = 1`, with per-premise droppability; counts quoted from the run.
- `make check` and `make validate` were run for this session's shipped change
  ([`maximum`](maximum.md)) and are recorded there. Neither is affected by this entry, which
  ships nothing.
- `CHRISTMAS_LIST.md:196`, `:106-109` read → the literature cell, the solver cell and its
  `minimum.cpp` parenthetical, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:94` read → the name.
- `explenation generator.ml` read → `var_name` at line **3**, `mbc` at **1079**, `maxi` at
  **1059**. Line numbers verified by `grep -n` after this session's final edit, per W1-T14.
- **The Tier row was not re-measured**; it is carried from the 2026-09-21
  `python3 tools/mzn_coverage.py --rank --json` run recorded in the previous version of this
  file.

**Discrepancies noted.**

1. **This file's own previous claim, retracted above.** Stated rather than overwritten.
2. **`CHRISTMAS_LIST.md:196` routes `minimum` through E2.** On this evidence it is E0. Not
   edited; reported.
3. **`decomps/_shapes.md`'s "Not covered by any shape" table** still lists `minimum` among
   five G3-blocked constraints. Not edited; reported.
4. **Inherited and kept from the previous version:** the stub's `Spec: none` field was wrong —
   this constraint is covered by `decomps/maximum.md`, whose title line names it.
   `tools/catalog_stub.py` matches filenames only.
