# Format gaps — extensional (§5) and scheduling (§6)

Payload for W2-T1, from the W2-T5 specs in `decomps/_shapes-ext.md` and the fifteen
`decomps/<name>.md` files of `CHRISTMAS_LIST.md` §5 and §6. One bullet per gap, each naming the
constraint that hit it. Numbered `X1…` to stay disjoint from `docs/DECOMP_FORMAT_NOTES.md`'s
`G1…G5`, which the orchestrator consolidates; where a gap here is the same wall as a `G`, it
says so instead of renaming it.

Everything below is **read off `explenation generator.ml` and `cata/*.tex`**, with measurements
cited to `docs/VALIDATOR.md`. This session ran no code and measured nothing itself.

---

## The two that W2-T3 (E2) must satisfy, and they are not the same requirement

- **X1 — a constant table indexed by two indices, read as a *function*.** `table` (EXT-1). The
  atom is `X_i = T[r,i]`: the *value* index `t` is determined by the *row* index `r` and the
  *position* index `i`. The nearest existing construct is
  `Addcst of ind_name*ind_name*ind_symbols*ind_const*ind_name` — `i₃ = i₂ ± c·i`, a 1-D constant
  array used as a coefficient (source l.10), plus `OpShiftC` which shifts one family by a
  constant named per index of another. Neither *determines* one index from two others, and no
  construct at all lets a side condition say "these two index values are related by a stored
  relation". Without X1 there is no correct `table`: `docs/VALIDATOR.md` l.287 **measures**
  `cata/table.tex`'s three rules as three UNSOUND, and the reason, read off l.720–722, is that
  the shipped entry carries `r` as a free index on the `X` literal *instead of* this side
  condition.

- **X2 — a value set that depends on another index: `t' ∈ D(t)`.** `regular` (EXT-2a), and
  `mdd` for `lab`/`head`/`tail`. The shipped `regular` writes `t' ∈ D_8` and `t' ∈ D_9`
  where the intended meaning is `t' ∈ pred(t)` and `t' ∈ succ(t)`. `ind_set` is
  `D of int | D2 of ind_name list` (source l.6) — **`D2` is exactly the right constructor and is
  used by nothing**: it is matched in two places only, printing `"D(list)"` in the debug printer
  (l.111) and the literal string `"setfils"` in the LaTeX printer (l.375), which is not LaTeX.
  So the hook exists, unimplemented and unprintable.

  **X1 and X2 are separate requirements.** A 2-D constant table (X1) gives a *value* from two
  indices; an index-dependent set (X2) gives a *set* from one index. D-0006's E2 line reads
  "inequalities against expressions, 2-D constant tables", which names X1 and not X2. `regular`
  — the constraint D-0006 cites as E2's motivating case, and which W3-T3 calls the smallest
  complete contribution available — needs X2, and X1 only if the state layer is imported.
  **This is the single most consequential thing in this file for W2-T1.**

## What the printed rules cannot say

- **X3 — `OpPrim` introduces an index it does not bind, and the printer emits it unbound.**
  `regular`. `prim_node` (source l.94) builds `Set`+`Rel` modifications; `sum_node` (l.93) builds
  the same plus `EXFORALL`. The source comment on `OpPrim` (l.45) says so outright: "as `OpSum`
  but the sibling is not bound here". Read off `cata/regular.tex`, the premise
  `X_{i'} = t', i' = i+1, t' ∈ D_9, t' ≠ t` therefore has no quantifier on `t'`, and "for some
  `t'`" and "for every `t'`" are different rules with different soundness. A reader cannot
  recover which was meant. `docs/VALIDATOR.md` l.332 lists `regular` as **not checkable** for a
  different reason (`D_8`/`D_9` undefined), so no measurement settles this either.

- **X4 — the numeric parameter of a constraint never reaches the page.** `cumulative`
  (capacity `C`), `knapsack` (`W`, `P`), `disjunctive` (the implicit `1`). This is **G1**, and
  §6 raises its stakes: in the counting family G1 loses a threshold, here it loses *the
  distinction between two different constraints*. `cata/cumulative.tex` is generated from a
  `rule5` whose bound is `1`, i.e. it is the **unary** resource; nothing in the file says so, and
  a reader has no way to tell `cumulative` from `disjunctive`. `docs/VALIDATOR.md` l.330 records
  this mechanically: the capacity "appears in no atom".

## What the rule schemas cannot compute

- **X5 — weighted Boolean sums.** `cumulative`, `cumulatives`, `bin_packing`-shaped entries.
  `∑_i r_i · B2_{i,t} ≤ C` — `rule5`/`rule6`/`rule7` sum one Boolean family with unit
  coefficients. This is *not* the `failwith "sommes multiples"` wall: one family, one sum,
  coefficients. **Contradiction to report, not to fix:** D-0006's table defines **E3** as
  "multi-family cardinality (removes `failwith \"sommes multiples\"`)", i.e. several sums, while
  `CHRISTMAS_LIST.md` §6 assigns `knapsack` "E1 + E3 (**weighted** sums over integer vars)". The
  two readings of E3 are different extensions and W2-T1 should not assume one covers the other.

- **X6 — summing over an index set that a decision variable determines.** `cumulatives`. The
  sum at machine `k` runs over `{ i : M_i = k }`. `ind_set` and every `ind_op` are static; there
  is no construct whose extent depends on a variable. The auxiliary-free workaround —
  `B3_{i,k,t} ⇔ (M_i = k) ∧ B2_{i,t}`, then sum `B3` over `i` at fixed `(k,t)` — is expressible
  in the *schemas* and is the right decomposition, but see X7: it needs a fourth index family.

- **X7 — `ind_fam` is a closed four-element enum and §5/§6 exhaust it.** `regular_nfa`, `mdd`,
  `cumulatives`, `cost_regular`. `type ind_fam = FI | FT | FP | FR` with hardcoded printers
  `i`/`t`/`p`/`r` (source l.38, l.373). EXT-2b needs position, symbol, source state and target
  state — four, leaving nothing for anything else; EXT-4 wants a fifth for cost; `cumulatives`
  needs position, time, machine and (via X6) the assignment. `table` already spends three
  (`i`,`t`,`r`). This is the same *kind* of closed-enum problem as **G2** on `var_name`, on the
  index side rather than the variable side, and W2-T1 should fix both or neither.

- **X8 — no way to eliminate a pivot auxiliary from a derived rule.** `regular` (EXT-2b),
  `mdd`, `mdd_nondet`. The pipeline is AND/OR traversal with cycle detection (`find`) then DNF
  flattening (`an`). Nothing resolves an auxiliary that appears on both sides of a chain, so any
  state or node family survives into the printed premise. **This is why D-0004 currently costs
  coverage rather than merely costing rule length**: the only way to keep `regular`'s
  explanation in the user's vocabulary is to pick a decomposition that never introduces the
  state (EXT-2a), and EXT-2a covers only the strictly 2-local fragment of `regular`. A
  resolution pass would let EXT-2b satisfy D-0004 too. It is a pipeline requirement, not a
  format one, and it belongs in W2-T1's payload because the format's answer to "may I introduce
  an auxiliary?" depends on it.

- **X9 — arithmetic exists on indices, never on variable values.** `cost_regular`, `cost_mdd`,
  `knapsack`, and `cumulative` with variable durations. `Addint`, `Addcst`, `OpShift`,
  `OpShiftC` all rewrite `ind_name`s inside an index list. `cumulative` already *uses* index
  arithmetic to stand in for value arithmetic — `t' = t − d_i` — and `docs/VALIDATOR.md` l.330
  **measures** the consequence: `UNPARSED: index equation offset: t'=t-d_{i}`, i.e. `d_i` is an
  uninterpreted symbol the validator cannot read. A cost accumulator `C_{i+1} = C_i + c[q,t]`
  has no encoding at all. Related to but wider than **G3** (variable-vs-variable comparison):
  G3 asks for `X_i = Y_j` as an atom, X9 asks for expressions over variable values inside one.

- **X10 — the window/capacity argument is not reachable from a single sum.** `cumulative`,
  `disjunctive`. Both rules in `cata/cumulative.tex` explain with `∀i', i' ≠ i, i' ∈ [1,n]`:
  every other task. Schutt, Feydy, Stuckey & Wallace 2011 explain with a time window and a task
  subset justified by a capacity count. `rule5` reasons within one sum; the window argument
  reasons across time points. This is **E4** exactly as D-0006 defines it, D-0006 calls E4 the
  research and says it buys few constraints — `cumulative` is one of the few, and it is the
  named benchmark. Recorded here so W2-T1 does not mistake §6's shortfall for a missing E2.

## A gap in what a `.tex` entry can claim, not in the format

- **X11 — an entry cannot state the fragment it is complete for.** `regular`. EXT-2a is a
  complete, sound, auxiliary-free decomposition of the **strictly 2-local** languages — those
  whose automaton state is a function of the last symbol — and is not a decomposition of
  `regular` in general, because a conjunction of binary constraints on consecutive positions
  cannot express e.g. "an even number of `a`s". Derived by reading generator l.713 and asking
  what a consecutive-pair chain can define; not measured, and `docs/VALIDATOR.md` l.332 puts
  `regular` out of scope, so nothing measured bears on it. The catalog entry has no field in
  which to say this, and `docs/GCCAT.md`'s own D-0008 proposal (an entry is complete only
  relative to a stated Purpose and a `complete`/`partial` label) is the right home for it.
