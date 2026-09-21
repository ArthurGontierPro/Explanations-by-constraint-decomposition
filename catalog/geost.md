# `geost`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `geost`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`,
> "What the catalog claims".

| | |
|---|---|
| **Tier** | `- out of scope` — `python3 tools/mzn_coverage.py --rank`, section `7. Packing and geometry` (`CHRISTMAS_LIST.md` gives this row no E-code at all) |
| **Status** | `nothing generated — blocked on E6/E7/E2 (unresolved, see below)` |
| **Generated** | no generator entry — there is no `cata/geost.tex` |
| **Validator** | out of scope — no `cata/geost.tex` exists |
| **Calibration** | `out of reach` — 0 rules, no decomposition |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank`, `CHRISTMAS_LIST.md:178` read |

## Constraint

`geost` — no MiniZinc signature is vendored in this repo. `geost` is MiniZinc's general
geometric placement constraint (k-dimensional non-overlap of arbitrary shapes), per
`CHRISTMAS_LIST.md:178`'s section heading, `7. Packing and geometry`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:178`, literature cell, verbatim:

> none found

No paper is sourced in `catalog/_literature/` for `geost`.

## Solver support

`CHRISTMAS_LIST.md:178`, solver cell, verbatim:

> decomp

Legend: `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**None.** There is no `decomps/geost.md` and no `cata/geost.tex`.

## Scope of this entry

**Why out of scope.** `tools/mzn_coverage.py --rank` files this row `- out of scope` by
section (`7. Packing and geometry`, one of the tool's filtered sections per this task's own
brief). But `geost`'s route cell carries **no E-code at all** — unlike `diffn`/`bin_packing`
in the same section, `CHRISTMAS_LIST.md:178` states the route in prose instead: `**out** — no schema-expressible decomposition`.

**Is that classification right?** Yes, and it is the *strongest* form of out-of-scope in this
whole section — stronger than `diffn` (E2) or `bin_packing` (E8), both of which name a
specific extension that would close the gap. `geost` names none: the claim is that its
shape vocabulary (arbitrary polytopes, k dimensions, rotations in some variants) has no
schema-expressible decomposition in *any* of the seven rule schemas this generator has or is
scoped to add (E0-E9), not merely that the current printer lacks one literal. This reads as a
correct, deliberate call, not a section-filter accident — but it is also the row where
"out of scope" is least like `diffn`'s or `bin_packing`'s, and lumping all three under one
tier label obscures that difference.

**What would bring it in scope.** Nothing named in `docs/ROADMAP.md` or `CHRISTMAS_LIST.md`'s
extension list (E0-E9) is claimed to reach `geost`; the row's own text says there is no
schema-expressible decomposition, so no single E-code closes it the way E5 would for
`disjoint` or E2 would for `diffn`.

## Generated rules

None. No `cata/geost.tex` exists.

## Status

**`nothing generated — blocked on E6/E7/E2 (unresolved, see below)`**

No numbered gap or E-code is attributed by the source row itself; `docs/ROADMAP.md`'s
"Explicitly out of scope" bucket (`docs/ROADMAP.md:103-107`) covers geometry and packing by
name, which is consistent with filing this here even without a specific E-code.

## Calibration (W3-T5, D-0013)

**Verdict:** `out of reach` — 0 rules generated, no decomposition encoded, and (unusually for
this catalog) no candidate extension is even named as a route in.

## Gaps

| gap | what it blocks here |
|---|---|
| — | `CHRISTMAS_LIST.md:178` names no extension; the row's own text is "no schema-expressible decomposition", which is a stronger claim than any single E-code gap |

Source: `docs/ROADMAP.md:103-107` ("Explicitly out of scope" names geometry and packing by
name); `CHRISTMAS_LIST.md:178`.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank` (run 2026-09-21) → `geost` under tier `- out of scope`,
  no ecode, section `7. Packing and geometry`.
- `CHRISTMAS_LIST.md:178` read → literature, solver and route cells quoted above, verbatim.
- `docs/ROADMAP.md:103-107` read → the "Explicitly out of scope" statement covering geometry.
- `os.path.isfile("decomps/geost.md")` → False. `os.path.isfile("cata/geost.tex")` → False.
- Nothing was compiled, run or validated.
