# `regular`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `regular`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` (same tier row for `regular_nfa`, `regular_regexp`) |
| **Status** | `nothing generated — blocked on G7` |
| **Generated** | **0** rules in `cata/regular.tex` |
| **Validator** | out of scope. Machine-printed reason: "index sets D_8, D_9 — the transition relation — are never defined by the printer (W1-T2); gccat has no `regular` entry at all (docs/GCCAT.md s5.1)" |
| **Calibration** | **pending sourcing (C2)** — see `catalog/_literature/`; two papers are cited in the index and neither has been sourced |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/regular.tex \| wc -l`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`regular(array[int] of var int: x, int: Q, int: S, array[int,int] of int: d, int: q0, set of int: F)`

The word `x[1..n]` is accepted by the DFA `(Q, S, d, q0, F)`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:105` carries the *name* only. The signature above is
transcribed from `decomps/regular.md` ("Signature"), which records it without a citation of its
own; treat it as recall.

**Which fragment this entry covers, and it is not all of `regular`** (D-0012, mandatory).

**The decomposition in this repo is a complete, auxiliary-free decomposition of the strictly
2-local languages — those whose automaton state is a function of the last symbol read — and
not of the regular languages.** A conjunction of binary constraints on consecutive positions
cannot express "an even number of `a`s". W2-B established this; D-0012 decided it must appear
in the entry, in those terms, because "an entry labelled `regular` that decomposes only 2-local
languages is the kind of claim this project exists to stop making".

Three qualifications, because the sentence should be checkable and not merely repeated:

1. **It is derived, not measured.** `decomps/regular.md` says so: obtained by reading the
   generator's `rule4` step and asking what a consecutive-pair chain can define. Nothing
   measures it — the validator puts this entry out of scope, so no run bears on it either way.
2. **W2-B's sharpened criterion is the statement of the fragment**, and it is the part that
   does work: *a state may be inlined only when its state predicate is a **clause** — a
   disjunction in which every disjunct is a single literal.* That passes exactly
   `X_{i-1} ∈ V_q` (2-local) and fails general `regular`, whose state predicate is the DNF of
   all prefixes reaching `q`. `docs/GCCAT.md`'s weaker criterion ("a finite disjunction over
   user literals") passes general `regular` too and therefore draws no line.
3. **The shipped decomposition is narrower than the full 2-local fragment, and this entry says
   so rather than rounding up.** A strictly 2-local language is fixed by its permitted adjacent
   pairs *plus its permitted first and last symbols* (`decomps/_shapes-ext.md`, EXT-2a, is
   explicit about the "plus"). The shipped value is **two** `Decomp`s — the `rule1` channel and
   one `rule4` pair clause applied uniformly over `i` — with no clause for position 1, none for
   position `n`, and nothing corresponding to `q0` or `F`. Nor is the `±1` index shift guarded:
   a shipped sibling, `cata/increasing.tex`, prints `X_{i'} \geq t,~i'=i-1` with no `i' ∈ [1,n]`
   side condition at all. So the honest scope of the shipped artifact is *the pair-constraint
   part* of the 2-local fragment; the boundary conditions have nowhere to go today. **This
   paragraph is reasoning read off `explenation generator.ml:854-855` and `cata/increasing.tex`,
   not a measurement**, and it sharpens W2-B rather than contradicting it.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:159` cites two —

- **Gange, Stuckey, Szymanek 2011**, *MDD propagators with explanation*, Constraints 16:407–429
  (the row notes MDDs subsume table, regular, set/multiset);
- **McIlree & McCreesh, CP 2023**, *Proof logging for smart extensional constraints*, which the
  row says covers Regular Language Membership.

**Rule shape:** **pending sourcing — see `catalog/_literature/`.** That directory holds
`alldifferent`, `cumulative` and `gcc` only; there is no `regular.md` in it, and its README's
provenance convention (`QUOTED` / `DERIVED` / `SECONDARY` / `NOT SOURCED`) means nothing about
either paper's content may be written here until someone fetches them. **No published rule
shape is stated in this entry, from memory or otherwise.** No web access was used.

What is in-repo and quotable is this repo's own pricing, and only that: `CHRISTMAS_LIST.md:159`
routes `regular` at **E2** and adds that the repo "already has a *different and legitimate*
decomposition — transitions directly on consecutive `X` via value sets, no state variables, so
explanations stay in the user's vocabulary", needing "`D_8`/`D_9` defined in the printer and 2-D
table side conditions". `decomps/regular.md` corrects the second half: 2-D constant tables are
`table`'s gap (**G6**); what this decomposition wants is an index-dependent *value set*
(**G7**). Measured against the artifact, that correction is right — the refused sets come from
`tprimin (D 8)` / `tprimin (D 9)`, which are value sets, not tables.

## Solver support

| | |
|---|---|
| Chuffed | native (`regular.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C✗]`** — a Choco LCG *failure*: `regular` throws in LCG mode |

Source: `CHRISTMAS_LIST.md:159`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
`[C✗]` is not incidental: `CHRISTMAS_LIST.md:72` lists `regular` first in the table of Choco
constraints that throw under LCG, annotating it "**a decomposition already exists in
`cata/regular.tex`** — needs `D_8`/`D_9` defined and **E2**", and `CHRISTMAS_LIST.md:85` calls
it "the standout". Read that alongside the **Generated** row above: the decomposition exists,
the output does not.

## Decomposition used here

**Generator value:** `regular`, `explenation generator.ml:854-855`
**Emitted by:** `explainall [xac] regular "cata/regular.tex"`, line 890
**Spec:** `decomps/regular.md`; shape **EXT-2a** in `decomps/_shapes-ext.md:69-100`, which
`decomps/_shapes.md` renumbers to **S1**

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule4, [Decomp_devent (true,  (B 1), id, id);
                   Decomp_devent (false, (B 1), imap [imoin 1; tprimin (D 8)],
                                                imap [iplus 1; tprimin (D 9)])])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency.
- **step 2, `rule4`** — one disjunction, `B1_{i,t} ∨ ¬B1_{i∓1,t'}` with `t'` drawn from the
  value set `D_8` (descending) or `D_9` (ascending): the binary clause "if the neighbouring
  position holds `t'` then this one holds `t`", one per admitted transition. `D_8` means
  `pred(t)` and `D_9` means `succ⁻¹(t)` — a *value set indexed by another index*.

**No state variables, and that is the design.** D-0003 uses exactly this against importing
MiniZinc's `a[i+1] = d[a[i], xs[i]]`: MiniZinc's encoding is chosen for flattening, and its
explanations would be about invented automaton states nobody wrote, where this one's mention
only `X` literals. D-0004 agrees for the same reason. This entry does not reopen either; it
records what that choice costs, which is the fragment statement above.

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i = t` and `X_i ≠ t`, from the `xac`
global event (arc consistency, `explenation generator.ml:869`). Nothing else: the decomposition
has no auxiliary the user named, so there is no third literal to ask about.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 2 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 1` (`D9`) |
| `X_{i} \neq t` | 2 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 1` (`D8`) |

Verbatim from the artifact:

```
%%   ** REFUSED for X_{i}=t: 1 branch(es) reference undefined index set(s) D9; emitting them
%%      would state a rule over a set the artifact never defines (W1-T2) **
%%   ** NO RULE EMITTED for X_{i}=t: 2 candidate(s), all blocked **
```

**Each event has two candidates and loses them to two different causes.** One is an `F` drop —
a branch reaching a constraint that is not reified, which `CLAUDE.md` and W1-T3 both record as
legitimate, and which W1-S measured to be the *only* kind of drop that ever occurred across all
16 entries. The other is the W1-T2 refusal. So the count is not "one thing went wrong twice";
it is one legitimate discard and one refusal, per event, and only the refusal is a gap.

**What would change it: G7, and nothing smaller.** `ind_set_defined`
(`explenation generator.ml:459`) admits `D 1`, `D 2`, `D 3`. `D 8` and `D 9` are the transition
relation, and G7 is precisely "**value set indexed by another index**, `t' ∈ D(t)`. `ind_set`'s
`D2 of ind_name list` is the right hook and no decomposition uses it"
(`docs/DECOMP_FORMAT_NOTES.md:75`). The hook exists in the type and is unusable: W2-B and W2-C
independently found that `D2` prints the literal string `"setfils"`, which is why
`docs/DECOMP_FORMAT_NOTES.md:96-104` **withdraws** W2-A's "variable-length chains are a checked
negative" and routes them to the same missing printer. Defining `D_8` in the printer is
explicitly *not* the fix — the `D_k` counter is per-decomposition, so one definition would name
two entries' different sets alike (`explenation generator.ml:440-446`). It belongs to W2-T1 / E2.

**A second defect that G7 would expose rather than fix.** `OpPrim` introduces `t'` and does not
bind it: `prim_node` builds `Set` + `Rel` where `sum_node` also builds `EXFORALL`
(`explenation generator.ml:46`, whose own comment says "as `OpSum` but the sibling is not bound
here"). So the premise would print `t' ∈ D_9, t' ≠ t` with **no quantifier**, and "for some
`t'`" and "for every `t'`" are different rules with different soundness. This is
`decomps/_gaps-ext.md`'s **X3**; it received no number in the consolidated wave-two list, and
the thing it is an instance of is **D-0009** (open: "the `.tex` does not determine the rule").
Anyone who lands G7 and reads two rules out of this file has not finished.

**Not "nothing is explainable about `regular`".** Two candidate branches per event exist and are
structurally sound-looking; the generator declined to print them over an undefined set.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/regular.tex`.

## Generated rules

**None.** `grep -o '\\frac' cata/regular.tex | wc -l` → `0`. The file is the diagnostics footer
and nothing else.

## Status

**`nothing generated — blocked on G7`**

Four candidate branches (two per event) reduce to zero rules: two legitimate `F` discards and
two W1-T2 refusals naming `D_8` and `D_9`. `docs/ROADMAP.md:48` books `regular 2→0 rules` as the
intended cost of W1-T2 and `docs/ROADMAP.md:88` (W3-T3) is still `TODO`. Nothing here is
validated, flagged or refuted; the entry's content is the negative result and the fragment
statement above.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two conditions for a calibration both fail, and they fail independently:

1. **No published shape is in the repo.** `CHRISTMAS_LIST.md:159` cites Gange et al. 2011 and
   McIlree & McCreesh 2023, and `catalog/_literature/` has no file for either. The convention
   is not negotiable here: `catalog/README.md` step 2 and `catalog/_literature/README.md` both
   forbid writing a published rule shape from memory, and no paper was fetched by this session.
2. **No generated rule exists on this side.** With **0** rules there is no premise to place in
   an implication order even if the shape were sourced.

**A prior, recorded as a prior and not as a verdict.** When the shape is sourced, the comparison
is likely to be *awkward rather than clean*, for a reason already visible in the artifact: both
cited papers explain a **decision-diagram** propagator, whose premises are indexed by nodes,
edges or layers of an MDD built for the instance. That is the same kind of object as the Hall
sets and flow cuts that made `alldifferent` §5/§6 and `gcc` **out of reach** — a run-time
structure the printer has no index set for. The likely outcome is therefore `out of reach`
against the MDD rule even after G7 lands, with any `agrees`/`weaker` comparison available only
against whatever the papers say about the 2-local case specifically, if anything. **This is a
prediction about two unread papers and is worth exactly that much**; it is written down so the
next session can falsify it quickly rather than re-derive it.

**What calibration cannot be substituted with.** Not the validator (out of scope here), and not
minimality: `catalog/README.md` records that none of the three papers sourced so far proves any
explanation minimal, so the axis when it opens is implication strength.

## Gaps

| gap | what it blocks here |
|---|---|
| `G7` | **the binding one.** No value set indexed by another index, `t' ∈ D(t)`. `D_8`/`D_9` are the transition relation; `D2 of ind_name list` is the right hook, is used by nothing, and prints `"setfils"` |
| — (`ext X3`, unconsolidated) | `OpPrim` introduces `t'` without binding it, so even after G7 the printed rule would not say whether `t'` is existential or universal. This is **D-0009**'s ambiguity at a named site, not a gap with a number |
| `G16` | **general `regular` only.** `ind_fam` is a closed 4-element enum (`FI`/`FT`/`FP`/`FR`) and the state-matrix shape EXT-2b alone needs `i, t, q, q'` |
| `G17` | **general `regular` only.** No pivot-elimination pass, so a state auxiliary cannot be removed from a finished rule — which is *why* D-0004 costs coverage here rather than only rule length |
| `G6` | **not this entry's.** `CHRISTMAS_LIST.md:159`'s "2-D table side conditions" names `table`'s gap; D-0012 bundles G6 with G7 in one wave because they land together, not because `regular` needs G6 |

Extensions: **E2** for the shipped fragment (`CHRISTMAS_LIST.md:159`, `:72`); **E1 + G17** on
top for `regular` entire (D-0012, which chose *not* to buy that and said to revisit when E1
lands for another reason, e.g. the `cost_*` family). `regular_nfa` and `regular_regexp` share
the row and the tier; `regular_regexp`'s expression compiles into this same shape
(`decomps/_shapes-ext.md:71-72`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, output redirected then grepped) → `cata/regular.tex
  (0 rules, parses)` in the out-of-scope block, reason string quoted verbatim in the header
  table. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules
  in 5 entries out of scope.**
- `grep -o '\\frac' cata/regular.tex | wc -l` → `0`.
- `python3 tools/mzn_coverage.py --rank --json` → `regular`, `regular_nfa`, `regular_regexp` all
  in tier `D literature + solver-native`, ecodes `["E2"]`, `CHRISTMAS_LIST.md` line 159,
  section `5. Extensional — table, regular, MDD`.
- `cata/regular.tex` read, not run → the diagnostics footer, quoted above.
- `cata/increasing.tex` read, not run → the unguarded `i'=i-1` side condition cited in the
  fragment section.
- `explenation generator.ml:854-855, 869, 890` read, not run → the decomposition, the global
  event, the emitting call; `:46` for `OpPrim`'s non-binding comment, `:459` for
  `ind_set_defined`, `:440-446` for why `D_8` must not simply be defined.
- `CHRISTMAS_LIST.md:159, 72, 85, 106-109` read → citations, the Choco-LCG exception table, the
  "standout" assessment, the solver legend.
- `docs/DECISIONS.md` D-0012 (`:278-300`) and D-0003 (`:52-77`) read → the fragment requirement
  and the no-state-variables rationale, both quoted in substance.
- `decomps/regular.md` and `decomps/_shapes-ext.md:69-100`, `decomps/_gaps-ext.md:45-52` read →
  EXT-2a's maths, the coverage limit, the X3 defect.
- `docs/DECOMP_FORMAT_NOTES.md:75, 84, 85, 96-104` read → G7, G16, G17, and the withdrawal of
  W2-A's checked negative over `D2`'s missing printer.
- `docs/ROADMAP.md:48, 88` read → W1-T2 `DONE` with `regular 2→0` booked; W3-T3 still `TODO`.
- **Not fetched, not written:** no paper. The "Published explanation" and "Calibration" sections
  state no rule shape, per `catalog/_literature/README.md`'s convention.
- The paragraph on boundary conditions, and the `out of reach` prior in Calibration, are
  **reasoning, explicitly labelled as such in place**, not measurements.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **Stale line numbers, four documents.** `decomps/regular.md` cites the shipped decomposition
   at "l.712–713", `decomps/_shapes-ext.md:71,82` at "l.712–713"/"l.713", and `docs/GCCAT.md:78`
   at "generator l.421–422". Measured today: **854-855**.
2. **`decomps/_gaps-ext.md:45-52` (X3) quotes a premise "read off `cata/regular.tex`":**
   `X_{i'} = t', i' = i+1, t' ∈ D_9, t' ≠ t`. That string is no longer in the file — W1-T2 left
   the entry with 0 rules. The defect is still real and still readable off
   `explenation generator.ml:46` and `:854-855`; only its stated provenance has rotted.
3. **`docs/VALIDATOR.md`'s reason string for this entry leads with the undefined `D_8`/`D_9`**,
   which describes why the *branches* were refused rather than why the *file* cannot be
   validated (it holds no rules). `docs/ROADMAP.md:55` (W1-T11 (a)) already has this open for
   `among`/`range`/`regular`/`roots`; recorded here only as still true on 2026-09-21.
