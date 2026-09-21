# `regular_nfa`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `regular_nfa`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` (shared row with `regular`, `regular_regexp`) |
| **Status** | `nothing generated — blocked on G7` |
| **Generated** | **0** rules — there is no `cata/regular_nfa.tex`. The shared artifact `cata/regular.tex` also holds **0** rules, and is the *deterministic* 2-local fragment in any case |
| **Validator** | out of scope: nothing of this name to validate. `cata/regular.tex` is itself out of scope: "index sets D_8, D_9 — the transition relation — are never defined by the printer (W1-T2)" |
| **Calibration** | **pending sourcing (C2)** — two papers cited at `CHRISTMAS_LIST.md:159`, neither sourced |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/regular.tex \| wc -l`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: the one member of the `regular` row that cannot use the shipped shape

Read [`catalog/regular.md`](regular.md) first; this entry is its sibling and does not repeat
it. The thing to carry across is that `regular` has **two** possible shapes and the repo ships
the cheap one:

| shape | what it introduces | covers |
|---|---|---|
| **EXT-2a / S1** — the shipped `regular` decomposition (`explenation generator.ml:854-855`) | nothing; transitions directly on consecutive `X` via value sets | the **strictly 2-local** languages only |
| **EXT-2b / S8** | a layered Boolean state matrix `S_{i,q}` — a variable the user never wrote | regular languages in general |

**`regular_nfa` cannot use EXT-2a.** `decomps/regular_nfa.md:10-13` states why and this entry
adopts it: an NFA's state is not a function of the last symbol except in degenerate cases, so
there is no auxiliary-free route, "EXT-2b is the only option, and D-0004's exception clause
(the one that licenses `mdd`) is what licenses it."

**So this entry's gap set is `mdd`'s, not `regular`'s.** G7 for the transition relation, and
then **G16** and **G17** as independent blockers of the only available shape:

| gap | why it binds here |
|---|---|
| **G7** | `δ ⊆ Q × Σ × Q` is a relation read as a function of `(q,t)` — `decomps/_gaps-ext.md`'s **X2**, consolidated at `docs/DECOMP_FORMAT_NOTES.md:75`. Shared with `regular` |
| **G16** | `ind_fam` is the closed enum `FI` / `FT` / `FP` / `FR` (`explenation generator.ml:38`) with hardcoded printers `i`/`t`/`p`/`r`. EXT-2b needs **position, symbol, source state, target state** — four, exactly exhausting it, so a state prints as `p` or `r` and nothing is left for anything else (`decomps/_gaps-ext.md`'s X7, which names `regular_nfa` first) |
| **G17** | no pivot-elimination pass. `S_{i,q}` is the pivot of every derived rule and the pipeline is AND/OR traversal plus DNF flattening with cycle detection — no resolution step (X8) |

**The consequence for planning, stated plainly.** `docs/ROADMAP.md:89` (W3-T3) says the
extensional row hides two plans: "(a) G6+G7 delivers a *complete method for the 2-local
fragment*, genuinely small; (b) `regular` entire additionally needs E1 and G17, at which point
`mdd` comes nearly free". D-0012 bought plan (a). **`regular_nfa` is on plan (b)** — it is not
reached by the wave that reaches `regular`, and an index that files all three names on line
159 together hides that.

## Constraint

`regular_nfa(array[int] of var int: x, int: Q, int: S, array[int,int] of set of int: d, int: q0, set of int: F)`

The word `x[1..n]` is accepted by the NFA `(Q, S, d, q0, F)`; `d` is a transition **relation**
— `d[q,t]` is a *set* of successor states — rather than a function.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:106` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/regular_nfa.md:3-4` gives
only the differing argument ("`d` a transition *relation* (`array[int,int] of set of int`)
instead of a function"), so the signature above is [`catalog/regular.md`](regular.md)'s with
that one type changed — and that one is itself transcribed from `decomps/regular.md` without a
citation. Treat it as recall.

**Which fragment this entry covers** (D-0012, mandatory): **none, and the reason is not the
same as `mdd`'s.** `catalog/regular.md` can state a fragment — the strictly 2-local languages,
minus the boundary conditions — because it has an artifact whose reach can be bounded. Here
there is no artifact *and* the shipped shape is not applicable: EXT-2a decomposes 2-local
languages, and a 2-local language has a deterministic automaton by construction, so the
shipped decomposition does not cover a sub-fragment of `regular_nfa` either. **No fragment
claim of any kind is made.**

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:159` cites two —

- **Gange, Stuckey, Szymanek 2011**, *MDD propagators with explanation*, Constraints
  16:407–429 (the row notes MDDs subsume table, regular, set/multiset);
- **McIlree & McCreesh, CP 2023**, *Proof logging for smart extensional constraints*, which the
  row says covers Regular Language Membership.

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session.

**Nothing in this repo says whether either paper distinguishes the NFA case.** The row is one
row for three names; that is a routing decision by a previous session, not a reading.

## Solver support

| | |
|---|---|
| Chuffed | native (`regular.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C✗]`** — a Choco LCG *failure*: it throws in LCG mode |

Source: `CHRISTMAS_LIST.md:159`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.
`CHRISTMAS_LIST.md:72` lists `regular` first among the Choco LCG failures and `:85` calls it
"the standout", **on the ground that a decomposition already exists in `cata/regular.tex`**.
That argument does not extend to this name: no decomposition exists for it, and the one that
exists is not applicable.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `regular_nfa`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it. The `regular` value at
`:854-855` is EXT-2a and is *not* this constraint's.
**Emitted by:** nothing.
**Spec:** `decomps/regular_nfa.md`; shape **EXT-2b** (`decomps/_shapes-ext.md:117-151`),
renumbered **S8** (`decomps/_shapes.md:206-225`), which names `regular_nfa` among its five
instances.

The decomposition this project would use (`decomps/_shapes-ext.md:121-126`):

```
B1_{i,t}   ⇔ X_i = t                                        rule1, AC
S_{i,q}                                                      "state q is reachable at layer i"
E_{i,q,t}  ⇔ S_{i,q} ∧ B1_{i,t}                              rule3   "transition taken"
S_{i+1,q'} ⇔ ⋁_{(q,t) : q' ∈ δ(q,t)} E_{i,q,t}               rule4
```

with `S_{1,q₀}` asserted and `⋁_{q ∈ F} S_{n+1,q}` asserted.

**Non-determinism costs nothing in the schema** — it only widens the `rule4` disjunction, and
`rule4`'s multi-element branch (`explenation generator.ml:331-333`) takes a summand list of any
length. `decomps/_shapes-ext.md:127-128` says the same: "the NFA case is the same schema
without that restriction, which is why `regular_nfa` is a pure instance here." **What costs is
that the only shape available is the one with the state variable.**

**D-0004 cost, and it is the whole question.** `S_{i,q}` does not wash out; it is the pivot of
every derived rule, and a printed premise would read "the automaton is in state `q` before
position `i`" — a variable nobody wrote. D-0003 and D-0004 both argue against exactly that,
and `decomps/_shapes-ext.md:147-149` states the trade in one line: **"EXT-2b is therefore the
shape that is cheap for the engine and expensive for the catalog", and EXT-2a is the reverse.**
`regular` gets to pick; `regular_nfa` does not.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `X_{i} ≠ t` (would be, from `xac`) | — | **0** | not run: `δ` is an index-dependent relation (G7), four index families exhaust `ind_fam` (G16), and the state pivot cannot be eliminated (G17) |

**For contrast, the sibling that *was* run.** `cata/regular.tex` exists, was asked two events,
produced **two candidate branches each and zero rules**: one legitimate `F` discard and one
W1-T2 refusal naming `D_8`/`D_9` per event (`catalog/regular.md`, "Scope of this entry";
`grep -o '\frac' cata/regular.tex | wc -l` → **0**, measured 2026-09-21). That is what a
blocked-but-encoded constraint looks like in this catalog. `regular_nfa` is not even that.

## Generated rules

**None.** There is no `cata/regular_nfa.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21), and the shared `cata/regular.tex` holds 0 rules (measured, same date). Nothing is
rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G7`**

The number matches the family's headline and [`catalog/regular.md`](regular.md)'s, so that the
three names on `CHRISTMAS_LIST.md:159` read consistently — **but the content differs and the
"Read this first" section is where that is stated.** For `regular`, G7 is *sufficient*: close
it and the shipped EXT-2a decomposition starts emitting rules over the 2-local fragment. For
`regular_nfa`, G7 is *necessary and not sufficient*: EXT-2a is unavailable, so G16 and G17 bind
too, and this constraint arrives with `mdd` on W3-T3's plan (b) rather than with `regular` on
plan (a).

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions fail independently: no published shape is in the repo — `catalog/_literature/`
has no file for either cited paper, and `catalog/README.md` step 2 forbids writing one from
memory — and there are **0** generated rules, so there is no premise to place in an implication
order.

**A prior, recorded as a prior.** [`catalog/regular.md`](regular.md#calibration-w3-t5-d-0013)
records it for this same row: both cited papers explain a **decision-diagram** propagator,
whose premises are indexed by nodes, edges or layers built for the instance — the same kind of
run-time object that made `alldifferent` and `gcc` **out of reach** — so the likely eventual
verdict is `out of reach`, with any `agrees`/`weaker` comparison available only against
whatever the papers say about a restricted case.

**One qualification specific to this name, pushing the same way.** `regular`'s prior leaves
open a comparison "against whatever the papers say about the 2-local case specifically". That
escape is not available here: `regular_nfa` has no 2-local route at all (see "Which fragment
this entry covers"). So if the prior is wrong for `regular` it may still be right for this
name.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G7` | **the headline one, and shared with `regular`.** A value set indexed by another index: `δ(q,t)` is a set-valued relation. `D2 of ind_name list` is the hook, is used by nothing, and now **raises** rather than printing `"setfils"` (`explenation generator.ml:463-464`) |
| `G16` | **binds independently, and is what separates this entry from `regular`'s.** `ind_fam` is closed at four (`:38`); EXT-2b needs position, symbol, source state and target state. `decomps/_gaps-ext.md`'s X7 names `regular_nfa` first among the constraints that hit it |
| `G17` | **binds independently.** No pivot-elimination pass, so `S_{i,q}` survives into the premises — the leak D-0004 forbids by default, licensed here only by its `mdd` exception clause, read across |
| — (`ext X3`, unconsolidated) | `OpPrim` introduces a sibling index it does not bind (`explenation generator.ml:46`, whose own comment says "as `OpSum` but the sibling is not bound here"), so a premise can print with no quantifier. This is **D-0009** at a named site, not a gap with a number. It bites EXT-2a and would bite any transition premise here too |
| `G6` | **not this entry's.** A 2-D constant table read as a *function* is `table`'s gap; `δ` is the index-dependent *set* form, which is G7. `decomps/_gaps-ext.md` calls the X1-vs-X2 distinction "the single most consequential thing in this file for W2-T1" |

Extensions: **E2** per `CHRISTMAS_LIST.md:159`; `decomps/regular_nfa.md:15-16` prices it
**E1 + E2**, and that is the more accurate of the two, because E1 is what the `S`/`E` families
cost. Beyond both, **G17** is what would make a derived rule resemble a published one.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name;
  `cata/regular.tex` in the out-of-scope block with the `D_8`/`D_9` reason quoted in the header
  table. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2
  rules in 5 entries out of scope.**
- `grep -o '\frac' cata/regular.tex | wc -l` → **0**.
- `ls cata/` → 16 `.tex` files, none named `regular_nfa.tex`. `find . -name '*.mzn'` → empty.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E2"]`, `CHRISTMAS_LIST.md` line 159, section
  `5. Extensional — table, regular, MDD`. Confirms the stub's tier row; D-0014 left it
  untouched.
- `explenation generator.ml` read, not run → `:854-855` (the `regular` value, EXT-2a, *not*
  this constraint's), `:38` (`ind_fam`), `:46` (`OpPrim`'s non-binding comment), `:331-333`
  (`rule4`'s any-length branch), `:463-464` (`printind_set` raises on `D2`), `:879-893` (the
  fifteen `explainall` calls — none is `regular_nfa`).
- `CHRISTMAS_LIST.md:159`, `:72`, `:85`, `:106-109` read → the two citations, the Choco LCG
  failure table and the "standout" assessment, the solver legend.
- `decomps/regular_nfa.md`, `decomps/regular.md`, `decomps/_shapes-ext.md:69-151`,
  `decomps/_shapes.md:206-225`, `decomps/_gaps-ext.md` (X2, X3, X7, X8) read → the EXT-2b-only
  argument, the two shapes, the DFA/NFA remark, S8, and the gaps.
- `docs/DECOMP_FORMAT_NOTES.md:75, 84, 85` read → G7, G16, G17.
- `docs/ROADMAP.md:89` read → W3-T3 `TODO` and the two-plan note that puts this name on plan (b).
- `catalog/regular.md` read → the sibling entry's structure, its fragment statement, its
  diagnostics and its prior.
- **Not fetched, not written:** no paper. Two things are flagged unestablished in place:
  whether either cited paper distinguishes the NFA case, and the signature, which is recall.
