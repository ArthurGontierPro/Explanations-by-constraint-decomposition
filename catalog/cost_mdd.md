# `cost_mdd`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `cost_mdd`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, re-run 2026-09-21 after **D-0014**; unmoved. Ecodes `E1`, `E2`, `E9`; `CHRISTMAS_LIST.md:161`, section `5. Extensional — table, regular, MDD`. The row is shared with [`cost_regular`](cost_regular.md) |
| **Status** | `nothing generated — blocked on G15` — **and on everything that already blocks `mdd`**: `G7`, and `G17` for the reachability explanation. See Status |
| **Generated** | **0** — there is no `cata/cost_mdd.tex`. `ls cata/` (2026-09-21) lists 16 files and none is this one |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex`; this name appears in no line of the 2026-09-21 run |
| **Calibration** | **pending sourcing (C2)** — `catalog/_literature/` holds `alldifferent`, `cumulative` and `gcc` only, and no rule shape may be written from memory. A *prior* is recorded, labelled as a prior |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json`, and reads of `explenation generator.ml`, `CHRISTMAS_LIST.md:161`, `decomps/cost_mdd.md` and `decomps/_shapes-ext.md` |

## Read this before the rest of the entry

**This constraint is two layers away from anything this repo has generated, and both layers are
real.**

1. **The base layer.** `cost_mdd` is `mdd` plus a cost. `mdd` has **no entry in `cata/` and no reviewed catalog entry**: `catalog/mdd.md` is still a
   machine-filled stub as of 2026-09-21, carrying `tools/catalog_stub.py`'s banner (it is tier **D** and belongs
   to another session's list). `docs/DECOMP_FORMAT_NOTES.md` routes `mdd` at **G7** — value set
   indexed by another index — alongside `regular`.
2. **The cost layer.** The accumulator `C_{i+1} = C_i + c[q,t]` is, in
   `decomps/cost_regular.md`'s words, "the first construct in §5 or §6 that needs **arithmetic
   on variable values** rather than on indices". Every arithmetic construct in the format —
   `Addint`, `Addcst`, `OpShift`, `OpShiftC` — rewrites an `ind_name` inside an index list.
   There is **no encoding for it at all**.

`decomps/cost_mdd.md` puts the ordering plainly, and this entry adopts it: "**Nothing here is
reachable before `mdd` is.**" The same holds of `cost_regular` and `regular`. So what follows is
a statement of distance, not a partial result.

## Constraint

`cost_mdd(...)` — **not vendored in this repo.** `tools/data/minizinc-2.10.1-globals.txt:40`
carries the name only. **No MiniZinc signature is written here**, from recall or otherwise.

What *is* in-repo and quotable is `decomps/cost_mdd.md`'s signature note, verbatim:

> **Signature.** As `mdd`, with a cost per edge and a total-cost variable.

So: a word accepted by a layered decision diagram, where each **edge** carries a cost and the
accumulated cost is bounded.

## Published explanation

**Citation:** **Gange, Stuckey, Van Hentenryck, CP 2013**, *Explaining propagators for
edge-valued decision diagrams* — `CHRISTMAS_LIST.md:161`, which cites it for `cost_regular` and
`cost_mdd` together. The name of the paper is the reason the two share a row: an EVDD is a
decision diagram with values on its edges, which is what a cost automaton compiles to.

**Rule shape:** **pending sourcing — see `catalog/_literature/`.** That directory holds
`alldifferent`, `cumulative` and `gcc` only; there is no `cost_regular.md` or `cost_mdd.md` in
it, and `catalog/_literature/README.md`'s provenance convention
(`QUOTED` / `DERIVED` / `SECONDARY` / `NOT SOURCED`) means **nothing about the paper's content
may be written here until someone fetches it**. No published rule shape is stated in this entry.
No paper was fetched by this session and no web access was used.

What is in-repo and quotable is this repo's own **pricing**, and only that. `CHRISTMAS_LIST.md:161`
routes the pair at **E1 + E2 + E9**, with its own correction attached:

> **E1 + E2 + E9** (was E3; costs accumulate — D-0011)

`decomps/cost_mdd.md` gives the reason for the relabelling in full: the accumulator **adds
values**, so it is **E9** (gaps G12 + G13); it is *not* E3, which keeps D-0006's
multi-family-cardinality meaning, and *not* E8, which is coefficients on a Boolean count.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | **`[C✗]`** — a Choco LCG *failure* |

Source: `CHRISTMAS_LIST.md:161`, whose solver cell reads `decomp **[C✗]**`; legend at
`CHRISTMAS_LIST.md:106-109`. **Published literature and no native explaining propagator
anywhere** is exactly the tier-C signature. The `[C✗]` is shared with `regular`, `mdd` and
`mdd_nondet` — the whole extensional section throws under Choco LCG or is decomposed.

## Decomposition used here

**Generator value:** **none.** `grep -n 'explainall' 'explenation generator.ml'` (2026-09-21)
prints 15 emitting calls at lines 879–893; none is a `cost_*` value, and no `let cost_...`
binding exists in the file.
**Emitted by:** nothing.
**Spec:** [`decomps/cost_mdd.md`](../decomps/cost_mdd.md) — **read by this session**, 13 lines.

**Shape: `EXT-4`** (`decomps/_shapes-ext.md`, "EXT-4 — EXT-2b/EXT-3 plus an integer
accumulator", whose "Instantiated by" line names `cost_regular` and `cost_mdd` and nothing
else). `decomps/cost_mdd.md`: "`EXT-4` over `EXT-3` instead of `EXT-2b`. Differs from
`cost_regular` only in where the cost is attached (edge rather than `(state, symbol)` pair),
which is the same 2-D constant lookup."

**`EXT-3` is the layered-DAG shape** (`decomps/_shapes-ext.md`, "Instantiated by: `mdd`,
`mdd_nondet`"): `B1_{i,t} ⇔ X_i = t`; `Ed_{i,e} ⇔ N_{i,tail(e)} ∧ B1_{i,lab(e)}` by `rule3`;
`N_{i+1,v} ⇔ ⋁_{e : head(e)=v} Ed_{i,e}` by `rule4`. The shapes file notes that EXT-3
"collapses into EXT-2b mechanically" — an MDD is EXT-2b with a per-layer state set — and is
kept separate only because `lab`/`head`/`tail` are three constant tables rather than one.
**Three constant tables is three instances of G6, not one.** *That last sentence is this
session's arithmetic over the shapes file, labelled as reasoning.*

**The auxiliaries here are licensed, and that is on the record.** `decomps/_shapes-ext.md`
quotes D-0004 in as many words: "Some constraints (`sliding_sum`, `mdd`) have no known
auxiliary-free decomposition. Those entries record their auxiliaries' definitions alongside the
rule." So `N_{i,v}` and `Ed_{i,e}` may leak, provided the entry prints their definitions — and
`C_i` joins them.

**The accumulator is a genuine leaking auxiliary and the spec says so.** `decomps/cost_regular.md`:
`C_i` "cannot be inlined: a counter's value is not a disjunction of user literals under any
reading of M-1's criterion" — the one part of that criterion the session found needed no
repair. D-0004's exception clause covers it by the same argument as `mdd`, "and the entry must
print `C_i`'s definition beside its rules". **This entry has no rules, so there is nothing to
print `C_i` beside; the obligation is recorded here for whoever writes the first one.**

## Scope of this entry

**Events the generator was asked to explain:** **none under this name.** The generator was never
invoked for it, so there is no `%% generator diagnostics (W1-T3)` footer to quote.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**The events that *would* be asked.** `X_i = t` and `X_i ≠ t` from `xac`, as for
[`regular`](regular.md) (`explenation generator.ml:869`, and line 890 passes `[xac]` for the
`regular` value). The cost layer adds **two more that the format cannot currently express as
events at all**: a bound on the total cost, `C ≤ K`, and a bound on an intermediate accumulator
`C_i`. `var_name` is the closed variant `X | B of int | T | I | V | N | O` and
`docs/DECOMP_FORMAT_NOTES.md`'s **G13** states that "every constructor but `X` is read as
Boolean or index-like" — so there is no constructor that could carry an integer-valued
accumulator, and therefore no literal over it to ask about. *That is reasoning off G13 and the
`var_name` enum, not a measurement.*

## Generated rules

**None.** There is no `cata/cost_mdd.tex`, so `grep -o '\\frac'` has no input. This is a third
kind of zero, and the distinctions matter when reading the catalog's counts:
[`regular`](regular.md) ran and had every branch refused over an undefined index set;
[`cumulatives`](cumulatives.md) and this entry were never asked — but `cumulatives` has a
decomposition someone could write today modulo four gaps, and `cost_mdd` has one whose central
construct has no encoding in the format at any price short of E9.

## Status

**`nothing generated — blocked on G15`**

**G15 is named because it is the gap the `cost_` prefix itself introduces**, and
`decomps/_gaps-ext.md` (X9, consolidated to G15) names this constraint first among the four that
hit it: "arithmetic exists on indices, never on variable values. `cost_regular`, `cost_mdd`,
`knapsack`, and `cumulative` with variable durations". The mechanism, quoted from that file:
`Addint`, `Addcst`, `OpShift` and `OpShiftC` "all rewrite `ind_name`s inside an index list", and
"a cost accumulator `C_{i+1} = C_i + c[q,t]` has no encoding at all". It is *wider* than G3
(variable-vs-variable comparison): "G3 asks for `X_i = Y_j` as an atom, X9 asks for expressions
over variable values inside one".

**Three more gaps sit under G15 and none of them is optional.**

- **`G12` + `G13`** — the pair that *is* **E9** under D-0011. G12: no schema sums integer
  *values* rather than counting Booleans, and it "is a fourth kind of schema, not a
  generalisation of the three". G13: `var_name` has no integer-valued auxiliary. Together they
  are why `C_i` can be neither summed nor named.
- **`G6`** — 2-D constant table read as a function; `Addcst` is 1-D. `decomps/cost_mdd.md` calls the edge-cost and `(state, symbol)`-cost forms "the same 2-D constant lookup". The uncosted `mdd` already needs three constant tables of its own — `lab`, `head`, `tail` — so the cost table is the fourth.
- **`G17`** — no pivot-elimination pass, so an auxiliary cannot be removed from a finished rule.
  `decomps/_gaps-ext.md` (X8) records that this "is why D-0004 currently costs coverage rather
  than merely costing rule length", and lists `regular` (EXT-2b), `mdd` and `mdd_nondet` — i.e. this constraint's own base among the shapes it hits.

**And the base layer is blocked first.** `mdd` is not reachable yet either: `docs/DECOMP_FORMAT_NOTES.md` routes it at
**G7** with `regular`, and `catalog/mdd.md` is still an unreviewed stub, so this entry cannot
lean on a measured statement about the base the way [`cost_regular`](cost_regular.md) can lean on
[`regular.md`](regular.md). `decomps/cost_mdd.md` states the dependency flatly: **"Nothing here
is reachable before `mdd` is."**

**So the honest summary is an ordering, not a list.** **G7** comes first, because there is no cost diagram without a diagram; **G6**
next, and three or four times over, because `lab`, `head`, `tail` and the edge-cost table are all
2-D constant lookups; **G17**, because `decomps/_shapes-ext.md` argues that even an *uncosted*
`mdd`'s published explanation — the reachability argument — needs a resolution pass the
pipeline does not have; then **G12 + G13** for an integer-valued accumulator, and **G15** for the
arithmetic that advances it. Six numbered gaps, of which E9's pair and G15 are specific to the
`cost_` prefix and the rest are `mdd`'s. *This ordering is reasoning
over the two spec files and the consolidated gap table, labelled as such; nothing was run,
because there is nothing to run.*

Nothing here is validated, flagged or refuted. The 2026-09-21 `make validate` run
(**34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of
scope**) contains no line for this name.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions for a calibration fail, independently:

1. **No published shape is in the repo.** `CHRISTMAS_LIST.md:161` cites Gange, Stuckey & Van
   Hentenryck, CP 2013, and `catalog/_literature/` has no file for it.
   `catalog/README.md` step 2 and `catalog/_literature/README.md` both forbid writing a
   published rule shape from memory, and no paper was fetched here.
2. **No generated rule exists on this side.** With **0** rules there is nothing to place in an
   implication order even if the shape were sourced.

**A prior, recorded as a prior and not as a verdict.** [`catalog/regular.md`](regular.md) wrote
one for its two cited papers and the same argument applies a fortiori here: the cited work
explains a **decision-diagram** propagator, whose premises are indexed by nodes, edges or layers
of a diagram built for the instance — the same kind of run-time object as the Hall sets and
flow cuts that made `alldifferent` and [`gcc`](gcc.md) **out of reach**, and which the printer
has no index set for. `decomps/_shapes-ext.md` says the same thing about the *uncosted* MDD
without needing the paper: the published explanation "is *not* the clausal unfolding" but "a
**reachability** argument over the diagram — no path through that edge survives", and deriving
that "needs a pass that resolves away every `N`/`Ed` pivot along all paths", which the pipeline
(AND/OR traversal plus DNF flattening with cycle detection) does not have. **The likely outcome
is therefore `out of reach`, and the edge values make it no closer.** This is a prediction about
an unread paper and is worth exactly that much; it is written down so the next session can
falsify it quickly rather than re-derive it.

**What calibration cannot be substituted with.** Not the validator (no artifact), and not
minimality: `catalog/README.md` records that none of the three papers sourced so far proves any
explanation minimal, so the axis when it opens is implication strength.

## Gaps

| gap | what it blocks here |
|---|---|
| **`G15`** | **the gap the `cost_` prefix introduces.** No arithmetic relating variable *values*: `C_{i+1} = C_i + c[e]` has no encoding at all. `X9`, which names `cost_mdd` second after `cost_regular` |
| **`G12` + `G13`** | **= E9** (D-0011). No schema sums integer values (G12); `var_name` has no integer-valued auxiliary (G13). `C_i` can be neither summed nor named |
| **`G6`** | 2-D constant table read as a function; `Addcst` is 1-D. Paid **several times** here: `lab`, `head` and `tail` are constant tables before the cost table is added |
| **`G7`** | inherited from `mdd`: value set indexed by another index, `t' ∈ D(t)`. `ind_set`'s `D2 of ind_name list` is the right hook, no decomposition uses it, and W2-B/W2-C found it prints the literal string `"setfils"` |
| **`G17`** | no pivot-elimination pass. Sharper here than anywhere: `decomps/_shapes-ext.md` argues the published MDD explanation is a **reachability** argument, and deriving it from EXT-3 "needs a pass that resolves away every `N`/`Ed` pivot along all paths" |
| — | and the *published* explanation is blocked by no gap on this list: see Calibration's prior. `decomps/_shapes-ext.md` reaches the same conclusion for the uncosted `mdd` without needing the paper, calling EXT-3 "closer in character to E4/E6 than to E1/E2" |

Extensions: **E1 + E2 + E9** (`CHRISTMAS_LIST.md:161`, with the E3→E9 relabelling at **D-0011**,
which `decomps/cost_mdd.md` restates and justifies). E1 opens `var_name`; E2 is the base
extensional layer; E9 is the accumulator, consolidated gaps **G12 + G13**.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (re-run 2026-09-21, after **D-0014**) → `cost_mdd`
  in `C literature + solver-decomposes`, ecodes `E1`, `E2`, `E9`, `CHRISTMAS_LIST.md` line 161,
  section `5. Extensional — table, regular, MDD`. D-0014 moved seven constraints between tiers
  and this was not one of them.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`,
  `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions this
  name.**
- `ls cata/` → 16 `.tex` files; `cost_mdd.tex` is not among them.
- `grep -n 'explainall' 'explenation generator.ml'` → 15 calls, lines 879–893, none for a
  `cost_*` value; line **890** is `explainall [xac] regular "cata/regular.tex"`.
- `grep -n '^let regular' 'explenation generator.ml'` → **854** (re-measured; four documents in
  this repo cite the old 712–713, per [`regular.md`](regular.md)'s discrepancy note).
- `grep -n 'ind_set_defined' 'explenation generator.ml'` → line **459**, admitting `D 1`, `D 2`,
  `D 3` only.
- `CHRISTMAS_LIST.md:161` read → the citation, the solver cell `decomp **[C✗]**`, the
  `E1 + E2 + E9` route and its "(was E3; costs accumulate — D-0011)" note, all quoted above.
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `decomps/cost_mdd.md` read → the signature note, the `EXT-4` shape, the E9 relabelling argument,
  and the gap attributions quoted above.
- `decomps/_shapes-ext.md` read → `EXT-3`, `EXT-4` and the "Instantiated by" lines; the
  reachability-argument paragraph quoted in Calibration.
- `decomps/_gaps-ext.md` read → `X8` and `X9` in full, including the sentences quoted in Status.
- `docs/DECOMP_FORMAT_NOTES.md` read → G6, G7, G12, G13, G15, G16, G17 and the consolidated
  wave-two mapping from `decomps/`'s `X`-labels.
- `catalog/regular.md` read, not run → the base entry's `nothing generated — blocked on G7`
  status, its fragment statement, and the shape of the prior reproduced in Calibration.
- `tools/data/minizinc-2.10.1-globals.txt:40` read → the name and the release it ships in.
- **Not fetched, not read:** the Gange et al. 2013 paper, or any other. No web access was used.
  Every sentence in "Published explanation" is about this repo's *pricing*, never the paper's
  content.
- **The event analysis in "Scope", the three-kinds-of-zero distinction and the gap ordering in
  Status are reasoning, labelled as such in place.** No code was run.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`docs/COVERAGE.md`'s "Structural defects in the list" still reports `cost_mdd` as named by
   two rows with conflicting routes** (its lines 157 and 214, `E1 + E2 + E3` against `E1 + E2`,
   the second pairing `cost_mdd` with `edit_distance`). **That was fixed on 2026-09-18 by W3-C**:
   the §11 row was removed, an HTML comment at `CHRISTMAS_LIST.md:219` records the removal and
   its reasoning, and `python3 tools/mzn_coverage.py --rank` now prints `no duplicate names` and
   lists `cost_mdd` once. Per `CLAUDE.md` ("a finding taken from a document that predates the
   fix"), this is recorded as **stale, not as a defect** — and it is this entry's constraint the
   stale passage is about, which is why it is named here first.
2. **`decomps/edit_distance.md` still exists** under `decomps/`, although
   `CHRISTMAS_LIST.md:219`'s removal note confirms `edit_distance` "is not a MiniZinc 2.10.1
   constraint under any spelling" and `tools/mzn_coverage.py` lists no such global. Not read by
   this session beyond its name in `ls decomps/`; recorded because a reader hunting `cost_mdd`'s
   history will meet it.
3. **`docs/COVERAGE.md`'s line numbers have drifted.** It cites the three E-code-less rows at
   118, 174, 213; measured today, **120**, **178**, **217**.
4. **`catalog/mdd.md` is an unreviewed stub**, so this entry's base layer rests on
   `docs/DECOMP_FORMAT_NOTES.md` and `decomps/_shapes-ext.md` rather than on a reviewed sibling.
   `mdd` is tier **D** and not this session's to review.
