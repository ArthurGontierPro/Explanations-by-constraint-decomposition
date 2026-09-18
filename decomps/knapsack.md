# knapsack

**Signature.** `knapsack(array[int] of int: w, array[int] of int: p, array[int] of var int: x,
var int: W, var int: P)` — `∑ w_i x_i ≤ W` and `∑ p_i x_i = P`.

**Shape: `SCH-3`** (`_shapes-ext.md`) — weighted sums over integer variables. It shares nothing
with SCH-1/SCH-2 except the word "sum"; it is grouped into §6 by `CHRISTMAS_LIST.md`'s section
layout, not by decomposition.

**E-code: E1 + E3 + E8 + E9** — relabelled per **D-0011**, which splits the E3 this file
carried in wave two. `knapsack` is the one constraint that genuinely needs all three sum codes
at once: **E9** for integer-valued summands (`x_i` is an int variable, gaps G12 + G13), **E8**
for the coefficients `w_i`/`p_i` (gap G11), and **E3** proper for the two sums over the same
array (the `failwith` site, gap G4). E1 is unchanged (`var_name` must open for `W` and `P`).
`CHRISTMAS_LIST.md` §6 gave "E1 + E3" before the split and notes "none found" for the
explanation literature — this is the one constraint in either of wave two's sections with no
paper.

**Three walls at once, all named elsewhere.**

- **Integer summands.** `rule5`/`rule6`/`rule7` sum a Boolean family. `x_i` is an integer
  variable. The standard route — reify `B_{i,t} ⇔ x_i = t` and sum `t · B_{i,t}` — turns this
  into gap **X5** (weights) immediately.
- **Weights (gap X5 = G11, extension E8).** `w_i`, `p_i`. Same requirement as `cumulative`'s
  `r_i`. The E3-means-two-things contradiction this file reported in wave two is resolved by
  **D-0011**: weighted Boolean sums are **E8**, integer-valued sums are **E9**, and E3 keeps
  D-0006's multi-family-cardinality meaning.
- **Two sums over the same variables.** This *is* the `failwith "sommes multiples pas encore
  implémentés"` site (source l.320, l.334, l.348) and is gap **G4** of
  `docs/DECOMP_FORMAT_NOTES.md` — the wall the counting pilot stayed on the near side of. The two
  sums share `x`, so no per-sum decomposition avoids it.

**Auxiliaries.** The `B_{i,t}` reification washes out as everywhere else; the bounds variables
`W` and `P` are the user's own and must print, which is gap **G2** again (`var_name` has no
letter for a constraint's own bound variable).

**Not a near-term entry.** Nothing about `knapsack` is close: it needs E1, E8 (X5's weights),
E9 (integer summands) **and** E3 proper (two sums). It is the only entry in the corpus that
needs all three of the sum extensions D-0011 separated.
