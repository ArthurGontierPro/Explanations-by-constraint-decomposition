# `regular_regexp`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `regular_regexp`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` (shared row with `regular`, `regular_nfa`) |
| **Status** | `nothing generated — blocked on G7` |
| **Generated** | **0** rules — there is no `cata/regular_regexp.tex`. The shared artifact `cata/regular.tex` also holds **0** rules |
| **Validator** | out of scope: nothing of this name to validate. `cata/regular.tex` is itself out of scope: "index sets D_8, D_9 — the transition relation — are never defined by the printer (W1-T2)" |
| **Calibration** | **pending sourcing (C2)** — two papers cited at `CHRISTMAS_LIST.md:159`, neither sourced |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/regular.tex \| wc -l`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: the shape depends on the expression, so the fragment statement has two halves

Read [`catalog/regular.md`](regular.md) first; this entry is its sibling and does not repeat
it. `regular_regexp` is `regular` with the language given by a **regular expression** instead
of an automaton, and `decomps/regular_regexp.md:5-7` gives the consequence: the shape is
"whichever of `EXT-2a` / `EXT-2b` the compiled automaton falls into".

**D-0012 requires this entry to say which fragment it covers, and the answer has two halves**
because the shape is chosen per instance:

| the expression denotes… | shape | gap picture |
|---|---|---|
| a **strictly 2-local** language (the state is a function of the last symbol) | **EXT-2a / S1** — the shipped `regular` decomposition, `explenation generator.ml:854-855` | **G7 alone**, exactly as [`regular`](regular.md) |
| anything else | **EXT-2b / S8** — a layered Boolean state matrix | **G7 + G16 + G17**, exactly as [`regular_nfa`](regular_nfa.md) |

**So the fragment this entry could cover, if G7 landed, is the first row and nothing else** —
and it is narrower even than that, for the reason [`catalog/regular.md`](regular.md) states
about its own artifact: the shipped value is two `Decomp`s, a `rule1` channel and one uniform
`rule4` pair clause, **with no clause for position 1, none for position `n`, and nothing
corresponding to `q0` or `F`**. A strictly 2-local language is fixed by its permitted adjacent
pairs *plus* its permitted first and last symbols, so the shipped artifact reaches the
pair-constraint part and not the boundary. An expression like `a(b|c)*d` pins both endpoints
and is exactly what the shipped shape cannot say.

**Two things follow, and both are this entry's rather than `regular`'s.**

1. **The status has to be one thing while the constraint is two.** `nothing generated —
   blocked on G7` is chosen because G7 is necessary on both rows and sufficient on the first.
   A reader who takes it to mean "close G7 and `regular_regexp` works" would be wrong for
   every expression outside the 2-local fragment; that is what this section is for.
2. **The compilation step itself costs nothing.** `decomps/regular_regexp.md:9-10`: "The
   compilation step is a modelling act outside the format and adds no requirement of its own."
   This entry agrees — the expression is *par* data, compiled before any decomposition is
   written, so no `ind_op`, `ind_set` or `var_name` is involved. **What it does do is make the
   shape choice invisible in the constraint's name**, which is precisely the situation D-0012
   exists to stop from being papered over.

## Constraint

`regular_regexp(array[int] of var int: x, string: r)`

The word `x[1..n]` is in the language of the regular expression `r`.

**Provenance of the signature:** not vendored in this repo, and **weaker than this family's
other two.** `tools/data/minizinc-2.10.1-globals.txt:107` carries the *name* only; this
checkout holds no `.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21).
`decomps/regular_regexp.md:3-4` says only "as `regular`, with the language given by a regular
expression" and gives no argument list at all. **The second argument's name and type above are
this entry's guess at how an expression would be passed and are not sourced from anything;**
treat this line as the weakest in the file, and weaker than
[`regular_nfa`](regular_nfa.md)'s, which at least had the differing argument's type stated.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:159` cites two —

- **Gange, Stuckey, Szymanek 2011**, *MDD propagators with explanation*, Constraints
  16:407–429;
- **McIlree & McCreesh, CP 2023**, *Proof logging for smart extensional constraints*, which the
  row says covers Regular Language Membership.

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session. Nothing in this
repo says whether either paper treats a regular *expression* as distinct from an automaton.

## Solver support

| | |
|---|---|
| Chuffed | native (`regular.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C✗]`** — a Choco LCG *failure*: it throws in LCG mode |

Source: `CHRISTMAS_LIST.md:159`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers all three names on the row.

## Decomposition used here

**Generator value:** none of this name. The `regular` value at `explenation generator.ml:854-855`
is EXT-2a and would serve this constraint **only** for a 2-local expression; none of the
fifteen `explainall` calls (lines 879-893) mentions `regular_regexp`.
**Emitted by:** nothing under this name.
**Spec:** `decomps/regular_regexp.md` → `decomps/regular.md` and `decomps/regular_nfa.md`;
shapes **EXT-2a** (`decomps/_shapes-ext.md:69-100`, renumbered **S1** in
`decomps/_shapes.md:71-91`) or **EXT-2b** (`:117-151`, renumbered **S8** in `:206-225`, which
names `regular_regexp` among its five instances).

**On the 2-local row**, the chain is the shipped one
([`catalog/regular.md`](regular.md#decomposition-used-here)): `rule1` channelling
`B1_{i,t} ⇔ X_i = t`, then one `rule4` pair clause with `t'` drawn from the value set `D_8`
(descending) or `D_9` (ascending). No state variables — which is the design, per D-0003 and
D-0004, and the reason the entry's explanations stay in the user's vocabulary.

**On the other row**, it is [`regular_nfa`](regular_nfa.md#decomposition-used-here)'s layered
state matrix, whose `S_{i,q}` pivot does not wash out.

**Which row an instance lands on is decided by the compiler, not by the model**, and nothing
in a `.tex` artifact would record the choice. That is worth stating because
`decomps/_gaps-ext.md`'s **X11** already names the underlying problem — "an entry cannot state
the fragment it is complete for" — for `regular`. `regular_regexp` is the sharper case: two
different shapes, same constraint name, no field anywhere that says which one produced a rule.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `X_{i} ≠ t` (would be, from `xac`) | — | **0** | not run: the transition relation is an index-dependent value set (G7) on both rows, plus G16 and G17 on the non-2-local row |

**For contrast, the sibling that *was* run.** `cata/regular.tex` was asked two events and
produced two candidate branches each and **zero rules** — one legitimate `F` discard and one
W1-T2 refusal naming `D_8`/`D_9` per event (`catalog/regular.md`, "Scope of this entry";
`grep -o '\frac' cata/regular.tex | wc -l` → **0**, measured 2026-09-21).

## Generated rules

**None.** There is no `cata/regular_regexp.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21), and the shared `cata/regular.tex` holds 0 rules. Nothing is rendered here and
nothing is claimed.

## Status

**`nothing generated — blocked on G7`**

G7 is necessary on both shape rows and sufficient on the 2-local one; "Read this first" states
the split, and states that for a non-2-local expression G16 and G17 bind as well, putting
those instances with [`regular_nfa`](regular_nfa.md) and [`mdd`](mdd.md) on `docs/ROADMAP.md:89`
(W3-T3)'s plan (b) rather than with `regular` on plan (a).

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions fail independently: no published shape is in the repo (`catalog/_literature/`
has no file for either cited paper, and `catalog/README.md` step 2 forbids writing one from
memory), and there are **0** generated rules, so there is no premise to place in an
implication order.

**A prior, recorded as a prior**, and it is [`catalog/regular.md`](regular.md#calibration-w3-t5-d-0013)'s
unchanged: both cited papers explain a decision-diagram propagator whose premises are indexed
by nodes, edges or layers built for the instance, which is the kind of run-time object that
made `alldifferent` and `gcc` **out of reach**; so `out of reach` is the likely eventual
verdict, with any `agrees`/`weaker` comparison available only against whatever the papers say
about a restricted case. Unlike [`regular_nfa`](regular_nfa.md), this name **does** keep that
escape open on its 2-local row.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G7` | **the binding one, on both rows.** A value set indexed by another index — `D_8`/`D_9` on the 2-local row, `δ(q,t)` on the other. `D2 of ind_name list` is the hook, is used by nothing, and now **raises** rather than printing `"setfils"` (`explenation generator.ml:463-464`) |
| `G16` | **non-2-local expressions only.** `ind_fam` is closed at four (`:38`) and EXT-2b needs position, symbol, source state, target state |
| `G17` | **non-2-local expressions only.** No pivot-elimination pass, so `S_{i,q}` survives into the premises |
| — (`ext X3`, unconsolidated) | `OpPrim` introduces a sibling index it does not bind (`:46`, whose own comment says so), so even on the 2-local row a premise would print `t' ∈ D_9, t' ≠ t` with no quantifier. **D-0009** at a named site, not a gap with a number |
| — (`ext X11`, unconsolidated) | an entry cannot state the fragment it is complete for. Sharper here than for `regular`: two shapes, one constraint name, and the choice made by a compiler |
| `G6` | **not this entry's.** The 2-D constant *table* read as a function is `table`'s gap; this is the index-dependent *set* form, G7 |

Extensions: **E2** for the 2-local row and **E1 + E2** for the other, exactly as
`decomps/regular_regexp.md:9` prices it. `CHRISTMAS_LIST.md:159` gives the row a flat **E2**,
which is right for the fragment the repo's shipped decomposition addresses and understates the
general case — the same understatement [`catalog/mdd.md`](mdd.md#gaps) records for its own row.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name;
  `cata/regular.tex` in the out-of-scope block with the reason quoted in the header table. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `grep -o '\frac' cata/regular.tex | wc -l` → **0**.
- `ls cata/` → 16 `.tex` files, none named `regular_regexp.tex`. `find . -name '*.mzn'` → empty.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E2"]`, `CHRISTMAS_LIST.md` line 159. Confirms the
  stub's tier row; D-0014 left it untouched.
- `explenation generator.ml` read, not run → `:854-855` (the `regular` value, EXT-2a), `:38`
  (`ind_fam`), `:46` (`OpPrim`'s non-binding comment), `:463-464` (`printind_set` raises on
  `D2`), `:879-893` (the fifteen `explainall` calls — none is `regular_regexp`).
- `CHRISTMAS_LIST.md:159`, `:106-109` read → the two citations, the solver cells and legend.
- `decomps/regular_regexp.md`, `decomps/regular.md`, `decomps/regular_nfa.md`,
  `decomps/_shapes-ext.md:69-151`, `decomps/_shapes.md:71-91,206-225`, `decomps/_gaps-ext.md`
  (X2, X3, X7, X8, X11) read → the two-shape reading, S1/S8, the boundary-condition limit, the
  fragment-statement gap.
- `docs/DECOMP_FORMAT_NOTES.md:75, 84, 85` read → G7, G16, G17.
- `docs/ROADMAP.md:89` read → W3-T3 `TODO` and its two plans.
- `catalog/regular.md`, `catalog/regular_nfa.md`, `catalog/mdd.md` read → the sibling entries
  this one cites instead of repeating.
- **Not fetched, not written:** no paper. The signature's second argument is flagged in place
  as a guess, not a transcription.
