# The cross-family shape list

**This file supersedes the four per-family shape lists as the single statement of what the
corpus decomposes into.** `_shapes-seq.md` (A–E), `_shapes-perm.md` (P1–P4), `_shapes-ext.md`
(EXT-1…4, SCH-1…3) and the counting pilot's shapes, which live inside `count.md`,
`at_least.md`, `at_most.md`, `exactly.md`, `among.md` and `nvalue.md`, were written by four
sessions without sight of each other. They overlap. Their prose stays where it is — the
derivations, the line numbers and the defect reports are still the record — and this file states
each shape **once**, says which constraints instantiate it and what each one varies.

Written by W3-D, 2026-09-18. Nothing here was measured; it is read off the four shape files, the
per-constraint specs, and `explenation generator.ml` where a line number is given. Where a
shipped entry is measured, the measurement is cited to `docs/VALIDATOR.md` via the file that
made it, not re-derived.

---

## The number

> **Twelve shapes, plus three modifiers, cover fifty-five in-scope constraints.**

Five further in-scope constraints have **no** shape: `maximum`, `minimum`, `arg_max`, `arg_min`
and `span` are blocked by gap **G3** before a decomposition can be written at all. They are not
"unshaped work"; they are a missing primitive.

This is the coverage claim for D-0010. "118 globals" is a list; **12 shapes** is the claim, and
it is the one that says what building the engine actually buys — fixing one shape fixes every
constraint under it. The per-shape counts below are what makes the number auditable.

| shape | what it is | # | merged from |
|---|---|---|---|
| **S1** | adjacent-position binary clause (2-local chain) | 4 | seq A, perm P2, ext EXT-2a |
| **S2** | reify-and-count: Boolean sum against a bare threshold | 8 | perm P1, seq C, counting pilot |
| **S3** | reify-and-count with a **channelled** count variable | 3 | counting pilot (in no shape file) |
| **S4** | quantified indicator over one index family | 2 | perm P4, counting pilot's ∃ step |
| **S5** | accumulated-state chain (genuine auxiliary) | 12 | seq B |
| **S6** | cross-variable channel by paired OR-clauses | 8 | perm P3 |
| **S7** | candidate-set selector over a constant relation | 1 | ext EXT-1 |
| **S8** | layered state/node chain (recursive rule3/rule4) | 5 | ext EXT-2b + EXT-3 |
| **S9** | overlap indicator plus a Boolean sum per time point | 3 | ext SCH-1 |
| **S10** | weighted Boolean sum against a capacity | 3 | ext SCH-2 |
| **S11** | recursive integer accumulator | 4 | seq E + ext EXT-4 |
| **S12** | flat sum over integer-valued variables | 2 | ext SCH-3 |
| | **total** | **55** | |

Modifiers — they apply *on top of* a shape and are not shapes: **M-opt** (optional tasks,
`disjunctive_opt`, `cumulative_opt`), **M-mach** (variable-determined index set, `cumulatives`),
**M-row** (replicate over the `R` index family, `lex2`, `lex_chain`, `orbitope`, `var_sqr_sym`).

---

## Two conventions, declared up front, because every merge below turns on them

These are judgement calls. They are stated here rather than applied silently so the next session
can reject them and recount.

1. **`{rule3, rule4}` is one schema family.** `Decomp_devent` carries a free sign bit on every
   summand and on the reified side, so `⋀_i B_i = ¬⋁_i ¬B_i` is expressible either way: `rule3`
   with flipped signs *is* `rule4`. Two decompositions that differ only by De Morgan are one
   shape. (The generator says so itself: `decr` is `incr` with the two `Decomp_devent` signs
   swapped, l.688–691, and nobody calls those two shapes.)
2. **`{rule5, rule6, rule7}` is one schema family**, parameterised by the comparator `≤ / ≥ / =`.
   `at_most`/`at_least`/`exactly` differ in nothing else.

**What these conventions do NOT license.** A *different arrangement* — an extra step, a
recursion where there was none, a pivot that appears on both sides — is a different shape even
when every schema is shared. That is what separates S7 from S8, and S2 from S9.

---

## S1 — adjacent-position binary clause (2-local chain)

`rule1` reification, then **one** `rule4` clause between the same reified family at positions
`i` and `i±1`. Generator l.689 and l.713 are the same construct with different `imap`s.

**Instances.** `increasing`, `decreasing` (shipped l.688–691, validated 2/2 each),
`strictly_increasing`, `strictly_decreasing`.

**What varies.** Consistency level (BC for the ordering four, AC for the transition chain);
signs on the two `Decomp_devent`s (`decreasing` is `increasing` with them swapped); whether the
*value* index is primed through an index-dependent set `D(t)` (`OpPrim` + `tprimin`).

**E-code.** E0 for the ordering four. The primed-value-set instances need **E2**, gap **G7** —
and that single index operator is the whole difference between an entry that runs today and one
that cannot be printed.

**Also an instance, counted under S8 instead:** `regular` restricted to the strictly 2-local
languages (the shipped `regular`, l.712–713) and `regular_regexp` when its expression compiles
into that class. They are counted once, at S8, where their general form lives; D-0012 requires
the catalog entry to state the fragment.

## S2 — reify-and-count: Boolean sum against a bare threshold

`rule1` reification, then **one** `rule5`/`rule6`/`rule7` over one Boolean family, with a single
`Decomp_devent` and **no** `Reified_devent`. The threshold lives only as an OCaml literal in the
choice of schema — gap **G1**, which is why no instance of this shape can print its own number.

**Instances.** `all_different` (`∑_i B_{i,t} ≤ 1` per value `t`, shipped l.678–679, validated
1/1 sound and minimal), `all_different_except`, `all_different_except_0` (guarded index set,
G8), `symmetric_all_different`'s `alldifferent` half, `at_least` (`rule6`), `at_most` (`rule5`),
`exactly` (`rule7`), `alternative` (`rule7` against 1 — hedged, see that file; its second,
`rule3` half is not part of this shape).

Also shipped and unspecified: `range` (l.717–719) and `roots` (l.714–716) are two more instances
— `rule1` + `rule6`/`rule7` over a Boolean family restricted to a value set `D 5`/`D 6`, single
`Decomp_devent`, no `Reified_devent`. Read off the source. They are not counted in the 55
because `CHRISTMAS_LIST.md` §8 was in no wave's scope and they have no spec file.

**What varies.** The comparator (`rule5`/`6`/`7`); the threshold constant (1 for
`all_different`, `n` for the counting three); whether the counted value is a **parameter** (`v`
in `at_most`) or a **second index family** (`t` in `all_different`); whether the summed index
set is the whole range or a restriction (G8 for the `_except` variants, a value set for
`range`/`roots`).

**E-code.** E0 throughout. Everything this shape cannot do is G1.

## S3 — reify-and-count with a channelled count variable

S2's sum, plus a second `rule1` channel `B'_p ⇔ C = p` over a count-value family `p`, with the
sum matched against it as the `Reified_devent` (`rule7`). This second channel is the only thing
in the corpus that lets a derived rule **conclude something about a count variable** rather than
only about the `X` literals.

**Instances.** `count` (direct), `nvalue` (shipped as `nvalues`, l.406–409, with an S4 indicator
step interposed), `among` (**should** be this and is not: shipped l.418–420 with S2's
single-`Decomp_devent` `rule7`, so none of its four generated rules concludes anything about
`n` — gap **G5**). `global_cardinality`'s per-value half is a further instance and needs **E3**
for the multi-family part; it has no spec file and is not counted.

**What varies.** Whether an S4 indicator feeds the sum (`nvalue`, `among`) or the `rule1` grid
feeds it directly (`count`).

**E-code.** E0. `nvalue` additionally has the double-binder printing defect recorded in its own
file.

## S4 — quantified indicator over one index family

`rule1` reification, then **one** `rule3`/`rule4` clause ranging over a whole index family: an
indicator for "some / every position satisfies the literal".

**Instances.** `member` (∃, `rule4`, target a parameter); `all_equal` (shipped l.674–677 — this
shape **composed twice with dual signs**, `B2 ⇔ ⋀_i B1_i` and `B3 ⇔ ⋀_i ¬B1_i`, closed by an
unquantified two-literal `rule4`). Also used *inside* other shapes, where it is not a separate
constraint: `nvalue`'s `B2_t ⇔ ∃i: B1_{i,t}`, `among`'s `B2_i ⇔ ∃t ∈ s: B1_{i,t}`, and EXT-1's
row conjunction is the same step over `i`.

**What varies.** ∀ vs ∃ (convention 1 — one shape); whether the target is a parameter
(`member`) or an index family (`nvalue`); whether the index set is a whole range or a subset
(`among`'s `t ∈ s`).

**E-code.** E0. `all_equal` ships with two of four rules measured UNSOUND (inverted quantifier
in the printed premise, not in the decomposition); repair is in `explenation generator.ml`, not
here.

## S5 — accumulated-state chain (genuine auxiliary)

`rule1`, then a **recursive** clause `b_i ⇔ b_{i±1} ∘ L_i` (`rule4` for ∨, `rule3` for ∧ — one
shape by convention 1), then a per-position guard clause linking `b_i` back to a literal.

The auxiliary is what separates this from S1: `b_i` is an accumulated fact ("`s` has occurred
in the prefix", "the prefix is still tied") with **no `Global_devent` standing for it**, so
nothing substitutes it back. It meets the `"ERROR B "` printer bug (generator l.399, l.428,
roadmap W1-T10) immediately.

**Instances (12).** `value_precede`, `value_precede_chain`, `seq_precede_chain` (∨ form,
guarded literal `X_i = t`, E0); `lex_less`, `lex_lesseq` (∧ form, guarded literal `X_i = Y_i`,
blocked by **G3**); `lex2`, `strict_lex2`, `lex2_strict`, `lex_chain`, `orbitope`,
`var_perm_sym`, `var_sqr_sym` (the lex chain replicated over the `R` index family — modifier
M-row, and W2-A's checked negative that `R` already exists for this stands).

**What varies.** ∧ vs ∨; whether the guarded literal is variable-vs-value (E0) or
variable-vs-variable (G3); replication over `R`; how many chained copies (instance-dependent for
`lex_chain`/`value_precede_chain`, which is **blocked on the same missing `D2` printer as G7**,
not a free escape hatch — W2-A's earlier checked negative on this was withdrawn).

## S6 — cross-variable channel by paired OR-clauses

One `rule1` per participating global, then **two** `rule4` clauses forming a biconditional (the
De Morgan expansion). The shape exists in this form only because `rule1` links one
`Global_devent` to one `Reified_devent`: there is no `Global ⇔ Global` schema, gap **G9**, so
every channel re-derives `element`'s detour by hand.

**Instances (8).** `element` (3 reifications, shipped l.692–696, validated 2/6 — the 4 lost
rules are a scalar-quantifier authoring bug, see that file); `inverse`, `inverse_in_range` (2
reifications, no third scalar, so no quantifier trap); `sort`, `arg_sort` (composed, and also
needing S2 over the permutation plus **G10**; sketched, not derived); `write`, `writes`,
`writes_seq` (§11 — `element` for the written cell, plus a guarded channel for every other cell,
gap **G18**).

**What varies.** Two reified globals or three; whether the index set of the channel is the whole
range (`inverse`), a subrange (`inverse_in_range`, G8), or excludes a **variable** position
(`write`, G18).

## S7 — candidate-set selector over a constant relation

`rule1`, then `rule3` conjoining **all** positions of one candidate, then **one** top-level
`rule4` selecting a candidate. Two levels, flat, no recursion.

**Instances (1).** `table` (and gccat's `in_relation`, out of scope). The shipped entry does not
implement this shape: it carries the row index `r` on the `X` literal and omits the
`t = T[r,i]` side condition entirely; `docs/VALIDATOR.md` measures its 3 rules as 3 UNSOUND.

**E-code.** **E2**, gap **G6** — a 2-D constant table read as a *function* of two indices. G6 is
a hard prerequisite, and D-0012 buys it for this reason.

## S8 — layered state/node chain (recursive rule3/rule4 alternation)

`rule1`, then `rule3` defining a transition/edge indicator from *the previous layer's state* and
a literal, then `rule4` defining the next layer's state as a disjunction over those indicators —
**recursive in the position index**, with the state auxiliary appearing on both sides.

**Instances (5).** `regular` (general), `regular_nfa`, `regular_regexp` (general), `mdd`,
`mdd_nondet`.

**What varies.** Whether the state set is fixed across layers (automaton) or differs per layer
(MDD); one 2-D constant table (`δ`) or three (`lab`/`head`/`tail`); determinism, which changes
only the width of the `rule4` disjunction.

**E-code.** **E1 + E2**, plus gap **G16** (four index families — position, symbol, source state,
target state — exhaust the closed `ind_fam` enum) and gap **G17** (the state is a pivot and
nothing eliminates it, so it leaks into premises, which D-0004 forbids by default). This is the
shape that is cheap for the engine and expensive for the catalog; S1 is the reverse. D-0012
settles the trade for `regular` in favour of the S1 fragment, with the fragment stated in the
entry.

## S9 — overlap indicator plus a Boolean sum per time point

`rule1` (**BC**), then `rule3` defining `B2_{i,t} ⇔ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1}` ("task `i` is
running at `t`"), then `rule5` over `B2` at each `t`.

**Instances (3).** `disjunctive`, `disjunctive_strict`, `disjunctive_opt` (+M-opt). The shipped
`cumulative` entry (l.680–682) is this shape, not S10 — its bound is an implicit 1, i.e. a unary
resource.

**E-code.** E0 for the schemas, and it is the only scheduling shape that runs today. Everything
it cannot say is G1 (the capacity never reaches the page, which is why `cata/cumulative.tex`
and a `disjunctive` entry would be indistinguishable) and G15 (`t' = t − d_i` is the measured
`UNPARSED`).

## S10 — weighted Boolean sum against a capacity

S9's first two steps, then `∑_i r_i · B2_{i,t} ≤ C`.

**Instances (3).** `cumulative`, `cumulatives` (+M-mach, gap G14), `cumulative_opt` (+M-opt).

**E-code.** **E8** (D-0011), gap **G11** — not E3: there is one sum per time point, so the
`failwith "sommes multiples"` site is never reached. Plus G1 for the capacity, now load-bearing,
and **E4** for the window/capacity argument the literature considers correct, which no single
sum can reach.

## S11 — recursive integer accumulator

An integer-valued auxiliary `A_i = A_{i−1} + (contribution)`, advanced along the position index
and compared against bounds. **No schema exists**: `rule5`/`6`/`7` count Booleans.

**Instances (4).** `sliding_sum` — standalone; contribution `X_i`, test on a windowed difference
`S_{i+w} − S_i ∈ [lo,hi]`. `cost_regular`, `cost_mdd`, `edit_distance` — **composed on top of
S8**; contribution is a cost read from a constant table and gated by S8's transition indicator.

**E-code.** **E9** (D-0011), gaps **G12 + G13**. D-0004 names `sliding_sum` and `mdd` as the
constraints with no known auxiliary-free decomposition, so the accumulator leaks by licence and
the entry must print its definition beside the rules.

## S12 — flat sum over integer-valued variables

`∑_i w_i X_i` compared against a bound or a variable total. No recursion.

**Instances (2).** `knapsack` (two such sums over the *same* array — the `failwith` site, so
**E3** as well), `sum_pred` (§11; one sum, so no E3 — and under one reading of its unsettled
signature, a variable chooses the summed index set, which is G14).

**E-code.** **E9** for the integer summands (G12 + G13), **E8** where coefficients are present
(G11), **E3** only where there are several sums (G4). `knapsack` is the only entry in the corpus
that needs all three at once.

---

## Merges accepted, with the reason

1. **seq A = perm P2 = ext EXT-2a → S1.** Three sessions wrote the same construct. A and P2 are
   the same generator lines (l.688–691) described twice. EXT-2a is l.713, *the same*
   `Decomp (id, rule4, [Decomp_devent(_, B1, imoin 1, …); Decomp_devent(_, B1, iplus 1, …)])`
   with different index modifiers — differing only in index-family operations and AC/BC, which
   is exactly "parameters or index families". `increasing` is itself a strictly 2-local
   constraint, and EXT-2a's own inlining table already lists `increasing` and 2-local `regular`
   in adjacent rows.
2. **perm P1 = seq C = the counting pilot's `at_least`/`at_most`/`exactly` → S2.** `rule1` +
   one `rule5/6/7` with a single `Decomp_devent` and no `Reified_devent`, in both. They differ
   in the threshold (1 vs `n`) and in whether the counted value is a parameter or a second index
   family. `_shapes-perm.md` already noticed the coincidence in prose ("the same 'implicit
   constant, never printed' shape `at_least.md` flags as G1") and stopped short of merging.
   **This is the largest merge: `all_different` and the counting family are one shape**, and G1
   is one defect, not two.
3. **perm P4 = the counting pilot's ∃ step → S4**, which `_shapes-perm.md` states outright
   ("the same shape `nvalue.md` step 2 uses ... with the target fixed").
4. **ext EXT-3 → EXT-2b → S8.** Self-declared in `_shapes-ext.md`: "an MDD is EXT-2b with the
   state set allowed to differ per layer, so EXT-3 collapses into EXT-2b mechanically". The only
   residue is three constant tables instead of one, which is a parameter of the same E2.
5. **seq E + ext EXT-4 → S11.** EXT-4 was defined as "EXT-2b/EXT-3 **plus** an integer
   accumulator"; seq E is that accumulator standing alone. Making the accumulator the shape and
   the automaton the carrier removes a shape and explains why `cost_regular` and `sliding_sum`
   hit the same gaps (G12+G13) from opposite directions. **EXT-4 stops being a shape and becomes
   the composition S8 + S11.**
6. **seq Shape D's actual basis → S2.** Shape D was described as "min/max over an index set:
   `rule6` (a bound holding for every index) plus `rule7` (achieved for at least one)", citing
   `range`/`roots`. Read off the source (l.714–719), `range` is `rule1` + `rule6` + `rule7` and
   `roots` is `rule1` + `rule7` + `rule7`, each a **single `Decomp_devent` over a value-restricted
   Boolean family** — i.e. two S2 sums, not a ∀/∃ pair. `rule6`/`rule7` are Boolean-**sum**
   schemas; ∀ and ∃ are `rule3`/`rule4` (S4). **Shape D is deleted**, its instances move to S2,
   and its description was a misreading — see the contradiction below.
7. **`all_equal` → S4, composed twice**, rather than a thirteenth shape. Its two `rule3` steps
   are each S4's single step with dual signs; its closing `rule4` is the same clause schema with
   no index family, a degenerate case. The alternative reading (a distinct "dichotomy at every
   threshold" shape) is recorded in `all_equal.md` so the choice is visible.

## Merges rejected, with the reason

Each of these is two shapes with the same *intent*.

- **S7 (`table`) vs S8 (`mdd`).** Both are `rule1` + `rule3` + `rule4`; both mean "select a
  surviving candidate". **Rejected because the arrangement differs where it matters:** S7's
  `rule3` spans all `n` positions at once and its `rule4` is a single top-level selection, with
  no recursion and no auxiliary on both sides of a step. S8 alternates `rule3`/`rule4` per layer
  with the state as a pivot. The consequence is exactly G17: S8's auxiliary cannot be eliminated
  and S7's washes out. Same schemas, different shape, different D-0004 verdict.
- **S2 vs S9.** S9 is S2's sum with a `rule3` overlap indicator interposed. **Rejected because
  the interposed step is load-bearing**: it is where `d_i` enters through `OpShiftC` and it is
  the site of the measured `UNPARSED: t'=t-d_i` (G15). Calling `disjunctive` "`all_different`
  over time points" would hide the only part of it that is broken.
- **S9 vs S10.** Same first two steps; the last step differs only by coefficients. **Rejected
  because a weighted sum is a schema that does not exist** (G11/E8), not a parameter of one that
  does. This is the distinction D-0011 was decided to protect.
- **S11 vs S12.** Both need E9 and neither has a schema. **Rejected because one is a recursion
  along the position index and the other is a flat sum over the whole array**, and because S12
  additionally hits the `failwith` (two sums, E3) which S11 never does. "Both are blocked" is
  not evidence that two things are the same shape.
- **S1 vs S5.** `_shapes-seq.md` calls them "the same mechanical skeleton". **Rejected**: S1's
  `rule4` relates two copies of a family that *is* a reification of `X_i op t`, so the printer
  substitutes it away; S5's recursion defines its Boolean in terms of **itself** plus a literal,
  giving an auxiliary with no `Global_devent` behind it. That difference is the whole of
  W1-T10's `"ERROR B "` and the whole of D-0004's cost here.
- **S3 vs S2.** One extra `rule1` channel. **Rejected because the extra channel is the only
  thing in the corpus that lets a rule conclude about a count variable** — it is the difference
  between `nvalues` and the broken shipped `among` (G5), so collapsing it would erase a real
  defect.
- **S4 vs S3.** S4 is S3's first two steps. **Rejected**: a prefix of a shape is not that shape.
- **`span` into seq Shape D.** See below — the merge was rejected because Shape D itself does
  not exist as described.

---

## Contradictions between sessions, found by consolidating

1. **`span` is claimed E0 by one session and impossible by another, and the second is right.**
   `decomps/span.md` (seq) gives `span` "Shape D", E0, reusing `range`/`roots`, on the reading
   `S = min_i(start_i)`, `E = max_i(end_i)`. `decomps/maximum.md` (perm) states that
   `maximum`/`minimum` "cannot be authored in the current encoding — this is not a derivation
   gap, it is a missing primitive", because `m ≥ x_i` compares two decision variables (**G3**).
   Both cannot hold: `span`'s min/max over subtask starts is `minimum` under another name.
   Reading the source settles it — `range`/`roots` (l.714–719) are Boolean **sums** over a
   value-restricted family, not a ∀-bound-plus-∃-tight pair, so they are no precedent for
   min/max at all. **`span` has no shape and is blocked by G3**, exactly as `maximum` is. It is
   excluded from the 55 and listed with the blocked four. `decomps/span.md`'s own hedge ("if the
   real signature differs this file should be redone, not patched") anticipated this; its E0
   claim should be read as withdrawn, and the file is left in place for its next owner rather
   than rewritten from outside.
2. **seq Shape D describes `rule6`/`rule7` as quantifiers.** "`rule6` (a bound holding for every
   index) plus `rule7` (achieved with equality for at least one index)" reads the two
   Boolean-sum schemas as ∀ and ∃. They are `∑ ≥` and `∑ =`. This is what produced (1), and it is
   worth stating separately because a reader of `_shapes-seq.md` alone would carry the misreading
   into any new min/max-flavoured constraint.
3. **`D2` as an escape hatch.** Already caught by the orchestrator and recorded in
   `docs/DECOMP_FORMAT_NOTES.md`'s checked negatives; `decomps/lex_chain.md` still says `D2`
   "already allows an index set given as an explicit list ... already within the format's
   reach". It is not: `D2` is used by nothing and prints the literal string `"setfils"`. Noted
   here because `lex_chain.md` was not corrected when the negative was withdrawn, and S5's
   "what varies" row above states the corrected position.

## Not covered by any shape

| constraint | why | code |
|---|---|---|
| `maximum`, `minimum` | `m ≥ x_i` is variable-vs-variable; no primitive | **G3** |
| `arg_max`, `arg_min` | as above, twice | **G3** |
| `span` | `S = min_i(start_i)`; see contradiction 1 | **G3** |

Out of scope by declaration, with one line each in the per-family index files: set variables
(**E5**), graph (**E6**), floats and geometry (**E7**), and the `*_fn` functional variants,
which are not separate constraints. `global_cardinality` and `distribute` are in scope in
principle (S3 + **E3**) and have no spec file; `bin_packing*` likewise (S10 + **E8**).
