# `distribute`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `distribute`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecodes `E0`, `E3` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G4` — **and on `G8` for the counted values.** See Status |
| **Generated** | no generator entry — there is no `cata/distribute.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `distribute` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:132` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, and a **scratch generator run** (below) |

## Constraint

**No signature is written here.** `distribute` is not vendored in this repo:
`tools/data/minizinc-2.10.1-globals.txt:59` carries the *name* only, there is no
`decomps/distribute.md`, and `CHRISTMAS_LIST.md:132` gives literature, solver and route and no
signature. `catalog/TEMPLATE.md` is explicit that recall must not be presented as a citation,
and for this constraint the arity matters — see Status — so nothing is asserted.

What **is** quotable in-repo about its content is one line, `decomps/_shapes.md:389`:

> `global_cardinality` and `distribute` are in scope in principle (S3 + **E3**) and have no
> spec file

and one decision record, **D-0011** (`docs/DECISIONS.md:259`), whose table row for E3 reads:

> | **E3** | multi-family cardinality (unchanged) | G4 | `distribute`, the multi-family half of `global_cardinality` |

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:59`.
`CHRISTMAS_LIST.md:132` files it under section `2. Counting and cardinality`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:132` reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/distribute.md`, no paper was
fetched by this session and no web access was used.

The nearest cited paper in the same section is Downing, Feydy and Stuckey 2012, *Explaining
flow-based propagation* (`CHRISTMAS_LIST.md:127`), for `global_cardinality`. It is sourced in
`catalog/_literature/gcc.md` and **its content is not transferred here**: `distribute` has its
own row and that row cites nothing.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:132`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21: no `[G]`, no `[C]`, no `[C✗]`. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** **none** — `distribute` is one of the constraints `decomps/_shapes.md:389` lists as
in scope with no spec file. Shape, per that line: **S3** ("reify-and-count with a channelled
count variable") plus **E3**.

So the chain below is *not* read off a spec; it is the shape's, instantiated:

1. `B_{i,t} ⇔ X_i = t` — `rule1`, AC. The shared reification grid.
2. per counted value, `∑_i B_{i,t} = C_t` — `rule7` against a channelled count variable, which
   is what `gccn` already does (`explenation generator.ml:827-829`).
3. the part that is **not** step 2 repeated: `distribute` fixes *which* values are counted, by a
   second array, and relates the several counts.

**Step 2 alone is not the gap.** One sum per value already works: `gccn` leaves the value index
`t` free and gets one sum for every `t` without ever meeting the multi-family site, and `roots`
(`:856-858`) shows two independent `rule7` sums living in two separate `Decomp`s quite happily.
What D-0011 books as E3 is a *single* schema instance over more than one counted family.

**The E3 attribution is inherited, and this entry does not re-derive it.** D-0011 and
`decomps/_shapes.md` both name `distribute` for E3; neither says which conjunct of the
constraint reaches the site, and without a signature this session cannot say either. What it
can do is check that the site is real, which it did — below.

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/distribute.tex` and so no
`%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**What was measured instead: that the E3 wall is a wall.** A **scratch run** (bounded in "How
this entry was produced") handed the generator a single `rule7` with **two** counted
`Decomp_devent`s — the multi-family shape D-0011 prices at E3 — and the run exited **2** with

```
Exception: Failure "sommes multiples pas encore implémentés".
```

`rule5`, `rule6` and `rule7` each match `dee::[]` on the summand list and `failwith` on anything
longer (`explenation generator.ml:355`, `:369`, `:383`, re-measured today). So the site named by
G4 is reachable, aborts the whole run, and writes no file — it does not degrade to a partial
entry. That is the difference between this entry and the `at_most` family: there the shape emits
something and the something is wrong; here nothing is emitted at all.

## Generated rules

**None.** `cata/distribute.tex` does not exist.

## Status

**`nothing generated — blocked on G4`** — and on **G8** for the counted values.

- **G4 / E3 — the named blocker.** One Boolean-sum family per rule; anything else is a hard
  `failwith`, measured above. D-0011 (`docs/DECISIONS.md:259`) books `distribute` under E3 for
  exactly this, and roadmap **W3-T4** is the row scoped to removing it.
- **G8 — and it bites first in practice.** Whatever the arity, `distribute` counts a *given set
  of values*, not the whole value range. `ind_set` names only whole predefined ranges
  (`explenation generator.ml:6`, `ind_set_defined` at `:459` admits `D 1`, `D 2`, `D 3` and
  nothing else), so that set is a `D k` the printer refuses under W1-T2. This is measured for
  the identical construct on [`count`](count.md) and [`among`](among.md): four events,
  0 rules, `REFUSED … (D4)`.
- **An arity-dependent third**, stated as conditional because the signature is not pinned: if
  `distribute`'s counted values are **decision variables** rather than parameters, the
  reification grid is being indexed by a variable, which is **G10** (`no variable in index
  position`) and not a small thing. If they are parameters, G8 covers it. **This entry does not
  choose**, and the next owner should pin the signature from the MiniZinc library before
  treating either as settled.

Nothing here is validated, flagged or refuted. The entry's content is the negative result, one
measurement, and a recorded open question about the arity.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:132`'s literature cell is `none` — the condition `catalog/TEMPLATE.md`
attaches to this verdict. Independently, with 0 rules there is no premise to place in an
implication order.

**One thing this verdict must not be read as.** `distribute` is a cardinality constraint and the
flow-based explanation of `global_cardinality` (Downing et al. 2012) plainly bears on it. That
paper is sourced in `catalog/_literature/gcc.md`, and `catalog/gcc.md`'s verdict against it is
**out of reach** — the published premise is indexed by a cut of a residual graph, which this
printer has no index set for. If `distribute`'s row is ever given that citation, the expected
verdict here is `out of reach` for the same reason. **That is a prediction about a row that
does not cite the paper, not a finding**, and it is written down so it can be falsified cheaply.

## Gaps

| gap | what it blocks here |
|---|---|
| `G4` | **the named one.** One Boolean-sum family per rule; `rule5/6/7` `failwith "sommes multiples pas encore implémentés"` (`explenation generator.ml:355`, `:369`, `:383`) — measured reachable, aborts the run |
| `G8` | `ind_set` names only whole predefined ranges, so the counted value *set* has no expression. Same refusal as `among` and `count` |
| `G10` | **conditional on the arity**: if the counted values are variables, the grid is indexed by a variable |
| `G2` | `var_name` (`explenation generator.ml:3`) has no letter for "the count of value `j`"; the counts must borrow `N` or `O` |
| `G1` | not binding — `distribute`'s counts are variables, carried by the channel, not bare constants |

Extensions: **E0 + E3** — `CHRISTMAS_LIST.md:132`, verbatim: "**E0** + **E3**". E3's meaning is
D-0006's and D-0011's: multi-family cardinality, gap G4. Roadmap **W3-T4** is the row.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering); `docs/DECISIONS.md:259`
for the E-code table.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0","E3"]`, `CHRISTMAS_LIST.md` line 132,
  section `2. Counting and cardinality`.
- `make validate` (2026-09-21, redirected then grepped) → `== 34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged ==`; no line names a `distribute` entry.
- `CHRISTMAS_LIST.md:132`, `:127`, `:106-109` read → the cells quoted above.
- `tools/data/minizinc-2.10.1-globals.txt:59` read → the name.
- `docs/DECISIONS.md:259` (D-0011) read → the E3 row quoted verbatim.
- `decomps/_shapes.md:389` read → "in scope in principle (S3 + E3) and have no spec file".
- `explenation generator.ml` read, not run: `:3` (`var_name`), `:6` (`ind_set`), `:355`, `:369`,
  `:383` (the three `failwith` sites), `:459` (`ind_set_defined`), `:827-829` (`gccn`, the
  working per-value count), `:856-858` (`roots`, two sums in two `Decomp`s).
- **Scratch generator run, 2026-09-21** — `explenation generator.ml` copied into this session's
  scratch directory, one `Decomp (2, rule7, [Decomp_devent …; Decomp_devent …])` appended with an
  `explainall`, run under OCaml 5.1.1, stderr redirected to a file and then read: exit **2**,
  `Failure "sommes multiples pas encore implémentés"`. **Nothing was added to the repository** —
  the generator is untouched, no `cata/` file changed, `make check`'s goldens are unaffected.
- **Not fetched, not read:** the MiniZinc library (not vendored here) and any paper. No web
  access was used. The arity question in Status is left open for that reason.

**Discrepancy noted, not fixed.** [`catalog/distribute_fn.md`](distribute_fn.md) quotes this
entry's Status as `not reviewed`, read off the stub on 2026-09-21; it is now
`nothing generated — blocked on G4`. That file is not this session's to edit.
