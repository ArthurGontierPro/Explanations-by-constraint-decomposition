# cumulative

**Signature.** `cumulative(array[int] of var int: s, array[int] of var int: d,
array[int] of var int: r, var int: b)` — at every time point the resource used by the running
tasks is at most `b`.

**Shape: `SCH-2`** (`_shapes-ext.md`) = `SCH-1` with weights and an explicit capacity:
`∑_{i∈[1,n]} r_i · B2_{i,t} ≤ C`. Everything above that last line is `disjunctive.md`.

**What `cata/cumulative.tex` actually contains is SCH-1, not SCH-2.** Read off
`explenation generator.ml` l.682, the final step is `rule5` over a single unweighted Boolean
family with an implicit bound of 1. That is a unary resource. `CHRISTMAS_LIST.md` §6 records the
same. The shipped entry is `disjunctive` under `cumulative`'s file name; see `disjunctive.md`
for its measured status (`docs/VALIDATOR.md` l.330: not checkable).

**Three requirements separate SCH-1 from SCH-2, and they are distinct extensions.**

1. **Weights on the summands — extension E8, gap G11.** `rule5`/`rule6`/`rule7` sum one Boolean
   family with unit coefficients (source l.308–350). `r_i · B2_{i,t}` has no encoding. This is
   *not* the `failwith "sommes multiples"` wall — that is several sums, which is **E3**; this is
   one sum with coefficients, which **D-0011 names E8**. The contradiction this file reported in
   wave two (D-0006 calling E3 multi-family cardinality while `CHRISTMAS_LIST.md` §6 called
   `knapsack`'s weighted sums E3) is **resolved**, not outstanding: E3 keeps D-0006's meaning and
   the weighted sum becomes E8. `cumulative` needs **E8 and not E3** — there is one sum per time
   point, so the `failwith` site is never reached.
2. **The capacity must reach the page (gap X4 = G1).** `docs/VALIDATOR.md` l.330 states it
   mechanically: the capacity "appears in no atom". In the counting family G1 loses a threshold;
   here it loses the distinction between `cumulative` and `disjunctive`, which is why this entry
   and that one are indistinguishable in `cata/`.
3. **Variable durations and resources (gap X9 / G3).** `d_i` is currently an `ind_const` inside
   `OpShiftC`, i.e. a symbol carried through index arithmetic that stands in for value
   arithmetic; the validator reports `UNPARSED: index equation offset: t'=t-d_{i}` (**measured**,
   `docs/VALIDATOR.md` l.330). Making `d_i` or `r_i` a variable needs atoms over expressions in
   variable values. `CHRISTMAS_LIST.md` §6 prices this **E2**.

**And a fourth thing, which is the research (gap X10).** Even with 1–3, the derived rule would
still explain by all `n` tasks, because `rule5` reasons within a single sum. Schutt, Feydy,
Stuckey & Wallace 2011 (*Explaining the cumulative propagator*, Constraints 16(3):250–282) and
Schutt, Feydy & Stuckey CPAIOR 2013 explain with a **time window plus a capacity/counting
argument** over a task subset. That is D-0006's **E4** verbatim — "counting / pigeonhole
reasoning across several cardinality constraints" — and D-0006 says E4 is the only route to
explanations matching the published hand-written ones, naming Schutt on `cumulative` as one of
the two examples. `cumulative` is therefore not a near-term entry: 1–3 make it *expressible*,
E4 makes it *good*.

**Auxiliaries.** `B1`, `B2` as in SCH-1, both washing out under D-0004. Weights and capacity are
constants, not auxiliaries; the D-0004 question does not arise for them, only the X4 printing
question does.
