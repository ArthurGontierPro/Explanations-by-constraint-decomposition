# `mdd_nondet`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `mdd_nondet`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecodes `E1`, `E2` (shared row with `mdd`) |
| **Status** | `nothing generated — blocked on G7` |
| **Generated** | **0** rules — there is no `cata/mdd_nondet.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — Gange, Stuckey & Szymanek 2011 is cited and unsourced |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: non-determinism costs nothing here, which is itself the finding

`mdd_nondet` is `mdd` without the determinism restriction on outgoing edge labels — a node may
have several outgoing edges whose label sets overlap. **Shape `EXT-3`, purely**
(`decomps/mdd_nondet.md:5-7`), renumbered **S8** in `decomps/_shapes.md:206-225`, which lists
`mdd` and `mdd_nondet` side by side among its five instances.

**Why the suffix is free.** The edge-flow encoding never assumed determinism. Its two working
clauses are

```
Ed_{i,e}   ⇔ N_{i,tail(e)} ∧ B1_{i,lab(e)}                   rule3
N_{i+1,v}  ⇔ ⋁_{e : head(e)=v} Ed_{i,e}                      rule4
```

and non-determinism only makes the `rule4` disjunction wider — more edges `e` with
`head(e) = v`. **Disjunction width is not a format question**: `rule4`'s multi-element branch
(`explenation generator.ml:331-333`) takes a summand list of any length, and the shipped
`cumul` value already exercises the multi-element path in `rule3` at `:811`. So the schema
does not notice.

`decomps/_shapes-ext.md:127-128` makes the same observation for the automaton case: "For a DFA
the `⋁` is over a single `(q,t)` per `q'` per symbol; the NFA case is the same schema without
that restriction, which is why `regular_nfa` is a pure instance here."

**So `mdd_nondet` is blocked by exactly what blocks [`mdd`](mdd.md), no more and no less** —
G7, G16 and G17, each binding independently — and everything about those is established in
that entry. This file states the suffix and cites the rest, rather than duplicating a
derivation that would then have to be kept in step.

**One consequence worth stating rather than leaving implicit.** In this corpus a suffix is
free when it widens a clause and costly when it needs a new *kind* of thing:
`mdd_nondet` and [`strict_lex2`](strict_lex2.md) are free; [`disjunctive_strict`](disjunctive_strict.md)
is **G1** because its suffix is a predicate on a constant, and
[`disjunctive_opt`](disjunctive_opt.md) is **G2** because its suffix is a new variable. That
three-way split is a small piece of evidence for D-0010's claim that shapes, not constraint
names, are the unit of work.

## Constraint

`mdd_nondet(array[int] of var int: x, int: N, array[int] of int: level, int: E, array[int] of int: from, array[int] of set of int: label, array[int] of int: to)`

As `mdd` — `x` spells out a root-to-sink path of the given multi-valued decision diagram —
without the determinism restriction on outgoing edge labels.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:92` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/mdd_nondet.md:3` gives the
constraint in prose ("as `mdd`, without the determinism restriction") and no argument list, so
the signature above is [`mdd`](mdd.md)'s, itself transcribed from `decomps/mdd.md:3-5` without
a citation of its own. Treat it as recall, and note that **whether the two constraints really
share an argument list is not established here.**

**Which fragment this entry covers** (D-0012, mandatory for this family): **none.** There is no
shipped decomposition and no generated rule, so no fragment claim of any kind is made.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:160`, literature cell, verbatim:

> **Gange, Stuckey, Szymanek 2011**

— *MDD propagators with explanation*, Constraints 16:407–429.

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry**, and no web
access was used. The second-hand characterisation of that paper's explanation as a
*reachability* argument is discussed — and marked **UNSOURCED** — in
[`catalog/mdd.md`](mdd.md#published-explanation); it is not restated here as if it were
independent evidence.

**One thing specific to this name and worth flagging.** `CHRISTMAS_LIST.md:160` gives `mdd` and
`mdd_nondet` one row and one citation. **Whether the cited paper treats non-deterministic
diagrams at all is not established by anything in this repo** — the row is a previous
session's routing note, not a reading of the paper.

## Solver support

| | |
|---|---|
| Chuffed | native (`mddglobals.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C✗]`** — a Choco LCG *failure*: it throws in LCG mode |

Source: `CHRISTMAS_LIST.md:160`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers both names on the row, so this table is `mdd`'s and is not evidence of a
propagator specific to the non-deterministic case.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `mdd_nondet`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/mdd_nondet.md` → `decomps/mdd.md`; shape **EXT-3**
(`decomps/_shapes-ext.md:189-220`), renumbered **S8** (`decomps/_shapes.md:206-225`).

The chain is [`mdd`](mdd.md#decomposition-used-here)'s, unchanged:

```
B1_{i,t}   ⇔ X_i = t                                        rule1, AC
Ed_{i,e}   ⇔ N_{i,tail(e)} ∧ B1_{i,lab(e)}                   rule3
N_{i+1,v}  ⇔ ⋁_{e : head(e)=v} Ed_{i,e}                      rule4   — wider here, same schema
```

`N_{i,v}` and `Ed_{i,e}` are genuine auxiliaries that do not wash out, and **D-0004 licenses
them by name** for `mdd`: "Some constraints (`sliding_sum`, `mdd`) have no known auxiliary-free
decomposition. Those entries record their auxiliaries' definitions alongside the rule."
`mdd_nondet` is not named in that clause. This entry reads it as covering the shape rather than
the spelling — **a reading, flagged here rather than assumed silently**, since D-0004 is not
this session's record to extend.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `X_{i} ≠ t` (would be, from `xac`) | — | **0** | not run: `lab`/`head`/`tail` are index-dependent relations (G7), and the four index families exhaust `ind_fam` (G16) |

What would still be wrong if all three gaps closed is [`mdd`](mdd.md#scope-of-this-entry)'s
point unchanged: S8 emits rules pivoting on nodes and edges, and reaching a reachability
argument in `X` literals needs a resolution pass the pipeline does not have (G17).

## Generated rules

**None.** There is no `cata/mdd_nondet.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G7`**

Identical to [`mdd`](mdd.md#status) in every respect, including that G16 and G17 bind
independently and that closing G7 alone would not produce an entry. The legend takes one gap
number; the other two are in the Gaps table.

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions fail independently: no published shape is in the repo (`catalog/_literature/`
has no file for Gange et al. 2011), and there are **0** generated rules, so there is no premise
to place in an implication order.

The prior — that a decision-diagram propagator's premises are indexed by nodes, edges or
layers, which would make the eventual verdict `out of reach` — is recorded once, with its two
qualifications, in [`catalog/mdd.md`](mdd.md#calibration-w3-t5-d-0013). It applies here
unchanged and is **not** counted twice.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G7` | **the headline one.** `lab`/`head`/`tail` are relations read as functions of an index. `D2 of ind_name list` is the hook, is used by nothing, and now **raises** rather than printing `"setfils"` (`explenation generator.ml:463-464`) |
| `G16` | **binds independently.** `ind_fam` is a closed four-element enum (`:38`); S8 needs position, value, node and edge |
| `G17` | **binds independently.** No pivot-elimination pass, so `N_{i,v}` and `Ed_{i,e}` survive into premises |
| — | **not a gap: non-determinism.** It widens a `rule4` disjunction, and `rule4`'s multi-element branch (`:331-333`) takes any length. Recorded so nobody schedules it as work |

Extensions: **E1 + E2** (`CHRISTMAS_LIST.md:160`; `decomps/mdd_nondet.md:8-9` agrees, "identical
to `mdd`, including gap X8 … and gap X7"). [`catalog/mdd.md`](mdd.md#gaps)'s disagreement with
that pricing — E1 + E2 buys expressibility, not the published explanation — applies here too.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `mdd_nondet.tex`. `find . -name '*.mzn'` → empty.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E1", "E2"]`, `CHRISTMAS_LIST.md` line 160. Confirms
  the stub's tier row; D-0014 left it untouched.
- `explenation generator.ml` read, not run → `:331-333` (`rule4`'s any-length branch — the
  basis for "non-determinism costs nothing"), `:811` (the shipped multi-element use), `:38`
  (`ind_fam`), `:463-464` (`printind_set` raises on `D2`), `:879-893` (the fifteen `explainall`
  calls — none is `mdd_nondet`).
- `CHRISTMAS_LIST.md:160`, `:106-109` read → the citation, the shared row, the solver legend.
- `decomps/mdd_nondet.md`, `decomps/mdd.md`, `decomps/_shapes-ext.md:117-220`,
  `decomps/_shapes.md:206-225` read → the purity claim, EXT-3's maths, the DFA/NFA remark, S8.
- `docs/DECOMP_FORMAT_NOTES.md:75, 84, 85` read → G7, G16, G17.
- `catalog/mdd.md` read → the derivation this entry cites rather than repeats.
- **Not fetched, not written:** no paper. Two things are flagged as unestablished in place:
  whether the two `mdd*` constraints share an argument list, and whether the cited paper
  treats non-deterministic diagrams at all.
