# `mdd`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `mdd`, and no claim of that kind is
> made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecodes `E1`, `E2` (shared row with `mdd_nondet`) |
| **Status** | `nothing generated — blocked on G7` |
| **Generated** | **0** rules — there is no `cata/mdd.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — Gange, Stuckey & Szymanek 2011 is cited and unsourced. A prior of `out of reach` is recorded below, as a prior |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: three gaps, and closing the headline one is not enough

`mdd` is shape **EXT-3** (`decomps/_shapes-ext.md:189-220`), renumbered **S8** in
`decomps/_shapes.md:206-225`, which merges EXT-2b and EXT-3 because "an MDD is EXT-2b with the
state set allowed to differ per layer". Its sibling [`catalog/regular.md`](regular.md) is the
model for this entry in almost every respect — and in one respect it is not, which is the
point of this section.

**`regular` has two shapes and chose the cheap one. `mdd` has one.** `regular` ships a
decomposition (EXT-2a / S1) that introduces no state variable at all, which is why its entry
can name **G7** as *the* binding gap: close G7 and `cata/regular.tex` starts emitting rules
over the 2-local fragment. There is no EXT-2a analogue for a decision diagram — a node's
"state predicate" is the set of prefixes reaching it, a DNF rather than a clause
(`decomps/_shapes-ext.md:153-187`, the sharpened inlining criterion; `decomps/mdd.md:27-30`) —
so `mdd` must use S8, and S8 carries two further blockers of its own:

| gap | why it binds here |
|---|---|
| **G7** | `lab`, `head`/`from` and `tail`/`to` are constant relations read *as a function of another index*. This is `decomps/_gaps-ext.md`'s **X2**, consolidated to G7 (`docs/DECOMP_FORMAT_NOTES.md:75`) |
| **G16** | `ind_fam` is the closed enum `FI` / `FT` / `FP` / `FR` (`explenation generator.ml:38`) with hardcoded printers `i`/`t`/`p`/`r`. S8 needs position, value, node and edge — **four**, leaving nothing over, and printing a node as `p` or `r` (`decomps/_gaps-ext.md`'s X7) |
| **G17** | no pivot-elimination pass. `N_{i,v}` appears on both sides of the chain, and the pipeline is AND/OR traversal plus DNF flattening with cycle detection — no resolution step (`decomps/_gaps-ext.md`'s X8) |

**So the honest headline is: `nothing generated — blocked on G7`, and unlike `regular`, G7
alone would not produce an entry.** The status legend takes one gap number; this section is
where the other two are stated so the number is not read as the whole answer.

## Constraint

`mdd(array[int] of var int: x, int: N, array[int] of int: level, int: E, array[int] of int: from, array[int] of set of int: label, array[int] of int: to)`

`x` spells out a root-to-sink path of the given multi-valued decision diagram: `N` nodes with
their layer in `level`, `E` edges with tail in `from`, label set in `label` and head in `to`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:91` carries the *name* only, and this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). The signature above is transcribed
from `decomps/mdd.md:3-5`, "Signature", which records it without a citation of its own; treat
it as recall. It is the most detailed of this session's fifteen signatures and it is no better
sourced than the others.

**Which fragment this entry covers** (D-0012, mandatory for this family): **none.** There is no
shipped decomposition, no generated rule, and therefore no fragment claim of any kind — not
even the narrow, honest kind [`catalog/regular.md`](regular.md) makes for the strictly 2-local
languages. That entry can state a fragment because it has an artifact whose reach can be
bounded; this one has nothing to bound.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:160`, literature cell, verbatim:

> **Gange, Stuckey, Szymanek 2011**

— i.e. *MDD propagators with explanation*, Constraints 16:407–429, which
`CHRISTMAS_LIST.md:158` describes as subsuming table, regular and set/multiset constraints.

**Rule shape:** **pending sourcing — see `catalog/_literature/`.** That directory holds
`alldifferent`, `cumulative` and `gcc` only; there is no `mdd.md` in it.
`catalog/_literature/README.md`'s provenance convention and `catalog/README.md` step 2 both
forbid writing a published rule shape from memory. **No published rule shape is stated in this
entry**, and no web access was used.

**What *is* in-repo and quotable about the paper's shape — and it is second-hand, so it is
marked.** `decomps/mdd.md:32-40` characterises the published explanation as a **reachability**
argument over the diagram, reported as a set of `X` literals. That is a previous session's
reading of `CHRISTMAS_LIST.md`'s summary, not a reading of the paper: `decomps/_shapes-ext.md`
declares at its head that "nothing here is measured by this session; this session ran no code",
and neither spec cites a page. **Treat the characterisation as UNSOURCED** until
`catalog/_literature/mdd.md` exists. It is repeated here because the Gaps table below turns on
it, and a reader should be able to see exactly how weak its provenance is.

## Solver support

| | |
|---|---|
| Chuffed | native (`mddglobals.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C✗]`** — a Choco LCG *failure*: `mdd` throws in LCG mode |

Source: `CHRISTMAS_LIST.md:160`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.

**The `[C✗]` is the same marker `regular` carries**, and `CHRISTMAS_LIST.md:72-85` lists the
Choco-LCG-unsupported constraints as the place where a derived explanation would be worth most.
`regular` is called "the standout" there because the repo already has a decomposition for it.
**`mdd` does not**, so the same argument gives it a much weaker claim on attention — which is
a reason to read this entry beside [`regular.md`](regular.md) rather than as its equal.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `mdd`, and none of
the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/mdd.md`; shape **EXT-3** in `decomps/_shapes-ext.md:189-220`, renumbered
**S8** in `decomps/_shapes.md:206-225`.

The decomposition this project would use (`decomps/_shapes-ext.md:194-199`):

```
B1_{i,t}   ⇔ X_i = t                                        rule1, AC
Ed_{i,e}   ⇔ N_{i,tail(e)} ∧ B1_{i,lab(e)}                   rule3   "edge e is still usable"
N_{i+1,v}  ⇔ ⋁_{e : head(e)=v} Ed_{i,e}                      rule4   "node v survives at layer i+1"
```

with the root asserted and a disjunction over the sinks asserted.

- **The schema set is `rule1`, `rule3`, `rule4` and no sums.** Mechanically those schemas are
  E0; nothing here needs `rule5/6/7`. What is missing is not a schema.
- **`tail`, `head` and `lab` are three constant relations**, and each is used as a function of
  an index — G7.
- **`N_{i,v}` and `Ed_{i,e}` are genuine auxiliaries and do not wash out.** They are the pivots
  of every derived rule, and nothing eliminates a pivot (G17). A premise would read `N_{i,v}` —
  "node `v` at layer `i` is still on a surviving prefix".

**D-0004 licenses that leak, by name.** The decision record's own exception clause reads: "Some
constraints (`sliding_sum`, `mdd`) have no known auxiliary-free decomposition. Those entries
record their auxiliaries' definitions alongside the rule." So `mdd` is the rare entry where
printing an auxiliary is *permitted* — and `decomps/mdd.md:24-25` makes the nicest distinction
in this family: a node is "a variable they did not write, though one they did draw", which is
the honest difference from `regular`'s invented automaton state.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `X_{i} ≠ t` (would be, from `xac`) | — | **0** | not run: `lab`/`head`/`tail` are index-dependent relations (G7), and the four index families exhaust `ind_fam` (G16) |

**What would still be wrong if all three gaps closed, and it is this entry's real content.**
S8 would emit rules whose premises are about nodes and edges. On the (UNSOURCED, see above)
characterisation of the published explanation as a reachability argument reported in `X`
literals, those rules would be a *different object*, not a weaker version of the same one:
getting from one to the other means resolving away every `N`/`Ed` pivot along all surviving
paths. `decomps/mdd.md:38-40` puts it exactly right and this entry adopts it — `mdd` would be
*expressible* at E1 + E2 while its good explanation stays *underivable*, "closer in character
to E4/E6 than to E1/E2". **Nothing in `CHRISTMAS_LIST.md:160`'s `E1 + E2` pricing reflects
that**, and that mismatch is the most useful thing this review found about `mdd`.

## Generated rules

**None.** There is no `cata/mdd.tex` (`ls cata/` → 16 files, none of this name; 2026-09-21).
Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G7`**

Three gaps bind independently — G7, G16, G17 — and the legend takes one number; "Read this
first" states all three, and states that closing G7 alone would not produce an entry, which is
the difference from [`regular`](regular.md).

Nothing here is validated, flagged or refuted. `docs/ROADMAP.md:89` (W3-T3, the extensional
family) is still `TODO`, and its own note says the row hides two plans: G6 + G7 delivers the
2-local fragment of `regular`, while `regular` entire "additionally needs E1 and G17, at which
point `mdd` comes nearly free and it is no longer a small contribution". **`mdd` is on the far
side of that fork**, and D-0012 chose the near side.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions fail independently: no published shape is in the repo (`catalog/_literature/`
has no `mdd.md`, and writing one from memory is forbidden), and there are **0** generated rules,
so there is no premise to place in an implication order.

**A prior, recorded as a prior and not as a verdict.** [`catalog/regular.md`](regular.md)
already records one for this same paper: both cited works explain a **decision-diagram**
propagator, whose premises are indexed by nodes, edges or layers of a diagram built for the
instance — the same kind of run-time object as `alldifferent`'s Hall sets and `gcc`'s flow cut,
which made both **out of reach**. `mdd` is the constraint where that prior is *most* likely to
hold, because here the diagram is the constraint itself rather than an artefact of the
propagator.

Two qualifications, both pushing the other way and both worth keeping:

1. **The diagram is user-supplied.** `mdd`'s nodes and edges are arguments, not objects the
   propagator invents, so unlike a Hall set they *do* have a stable name the format could in
   principle index. Whether that makes the published premise expressible here is exactly what
   G16 and G17 decide, so the prior is conditional on engine work rather than on structure.
2. **If the published explanation really is reported in `X` literals** (UNSOURCED, from
   `decomps/mdd.md:32-40`), then the comparison target is a set of user-vocabulary literals
   after all, and `out of reach` would be the wrong verdict — `incomparable` or `weaker` would
   be reachable once G17 gave a pivot-elimination pass.

**These are predictions about an unread paper and are worth exactly that much.** They are
written down so the next session can falsify them quickly rather than re-derive them.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G7` | **the headline one.** A value set indexed by another index: `lab`/`head`/`tail` read as functions. `D2 of ind_name list` is the right hook, is used by nothing, and now **raises** rather than printing `"setfils"` (`explenation generator.ml:463-464`). Shared with `regular` (`docs/DECOMP_FORMAT_NOTES.md:75`) |
| `G16` | **binds independently.** `ind_fam` is a closed four-element enum (`:38`); S8 needs position, value, node and edge, exhausting it, and an MDD node would print as `p` or `r` |
| `G17` | **binds independently, and is the one that matters for quality.** No pivot-elimination pass, so `N_{i,v}` and `Ed_{i,e}` survive into premises. D-0004 licenses that for `mdd` specifically — but see "Scope of this entry": it is also what separates an S8 rule from the published reachability argument |
| `G6` | **not this entry's.** A 2-D constant table read as a function is `table`'s gap; `mdd`'s three relations are the index-dependent *set* form, which is G7 (`decomps/_gaps-ext.md`, X1 vs X2 — "the single most consequential thing in this file for W2-T1") |

Extensions: **E1 + E2** (`CHRISTMAS_LIST.md:160`; `decomps/mdd.md:12-14` agrees, E1 for the
node and edge families, E2 for the three relations). **This entry's one disagreement with that
pricing is recorded in "Scope of this entry"**: E1 + E2 buys expressibility, not the published
explanation.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `mdd.tex`. `find . -name '*.mzn'` → empty.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E1", "E2"]`, `CHRISTMAS_LIST.md` line 160, section
  `5. Extensional — table, regular, MDD`. Confirms the stub's tier row; D-0014 left it
  untouched.
- `explenation generator.ml` read, not run → `:38` (`ind_fam`'s closed enum), `:39-49`
  (`ind_op`), `:463-464` (`printind_set` raises on `D2`), `:879-893` (the fifteen `explainall`
  calls — none is `mdd`).
- `CHRISTMAS_LIST.md:160`, `:158`, `:72-85`, `:106-109` read → the citation, the subsumption
  remark, the Choco-LCG failure table, the solver legend.
- `decomps/mdd.md`, `decomps/_shapes-ext.md:153-220`, `decomps/_shapes.md:206-225`,
  `decomps/_gaps-ext.md` (X1, X2, X7, X8) read → EXT-3's maths, the sharpened inlining
  criterion, S8, and the three gaps.
- `docs/DECOMP_FORMAT_NOTES.md:75, 84, 85` read → G7, G16, G17 and their `X`-number origins.
- `docs/ROADMAP.md:89` read → W3-T3 still `TODO`, and the two-plan note that puts `mdd` on the
  far side of the fork.
- `catalog/regular.md` read → the sibling entry's structure, its G7 headline, and the
  `out of reach` prior this entry inherits and qualifies.
- **Not fetched, not written:** no paper. The characterisation of the published explanation as
  a reachability argument is marked **UNSOURCED** in place, because its only in-repo provenance
  is a spec that cites no page.
