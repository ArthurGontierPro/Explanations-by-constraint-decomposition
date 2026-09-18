# edit_distance

`CHRISTMAS_LIST.md` §11: Gange, Stuckey & Van Hentenryck 2013, native (`edit_distance.cpp`),
route **E1 + E2**. Shape reference: `decomps/_shapes.md` **S8 + S11** — a layered state chain
carrying an integer accumulator, i.e. the same composition `cost_regular` and `cost_mdd` are
(what `_shapes-ext.md` called `EXT-4`). Not in the generator — authored here.

**Signature.** Two sequences and a bound: the number of insert/delete/substitute operations
turning one into the other is at most (or equal to) a cost variable.

**Decomposition (maths).** The standard DP table, read as a layered graph:

- `B1_{i,t} ⇔ X_i = t` and `B2_{j,t} ⇔ Y_j = t` — `rule1`, AC, one grid per sequence.
- `Eq_{i,j} ⇔ ⋁_t (B1_{i,t} ∧ B2_{j,t})` — "the two positions agree"; `rule3` inside `rule4`.
- `C_{i,j} = min(C_{i-1,j}+1, C_{i,j-1}+1, C_{i-1,j-1} + [¬Eq_{i,j}])` — the accumulator,
  recursive in **two** position indices.
- `C_{n,m} ≤ K`.

**Why this is S8 + S11 and not a new shape.** The `Eq`/`C` pair is exactly EXT-2b's
`E_{i,q,t}`/`C_i` pair with the automaton layer index replaced by a second *position* index:
`rule3` to define the transition indicator, `rule4` over the incoming alternatives, and an
integer accumulator advanced along the chain. Nothing in the schema set is new; the arrangement
is the same recursion.

**E-code: E1 + E2 + E9.** E1 for the `Eq`/`C` families (`var_name` is closed), E2 for `Eq`'s
two-index comparison, **E9** for the accumulator — sums of integer-valued variables, D-0011,
the same code `cost_regular.md` and `cost_mdd.md` now carry. `CHRISTMAS_LIST.md` §11 gives
E1 + E2 and does not price the accumulator; this file adds E9 for it, by the same argument the
`cost_*` entries make.

**Gaps hit, all already numbered.**
- **G16** — `ind_fam` is the closed four-element enum `FI | FT | FP | FR`. This constraint needs
  *two position families* (`i` in `X`, `j` in `Y`) plus a value family, and the accumulator
  wants a fourth. `regular_nfa` exhausts the enum with position/symbol/two states; this
  exhausts it a different way, which is independent evidence for G16.
- **G12 + G13** — the integer accumulator, as `sliding_sum` and `cost_regular`.
- **G3** — `Eq_{i,j}` is a variable-vs-variable comparison. Routing it through the two grids
  (`⋁_t B1_{i,t} ∧ B2_{j,t}`) is the standard dodge and it works here because both sequences
  are over the same finite value domain, so G3 is *avoidable* for this constraint — worth
  recording, since `maximum`/`lex_less` have no such dodge. The cost is `|domain|` clauses per
  cell.
- **G17** — `C_{i,j}` is a pivot on every path and nothing eliminates it, so the printed rule
  would name DP cells. D-0004's exception clause (the one that licenses `mdd`) is what would
  license it; the entry must print `C`'s definition beside its rules.

**Also: `min` of three expressions has no encoding at all.** The accumulator's recurrence is a
minimum, not a sum, and the format has no arithmetic over variable values in any form (G15).
Under E9 the natural route is the three inequalities `C_{i,j} ≤ …` plus a disjunction asserting
one is tight — the same `∀`-bound-plus-`∃`-tight pattern `maximum` needs and cannot have.

**Not a near-term entry**; strictly harder than `cost_regular`, which is itself behind E1 + E9.
