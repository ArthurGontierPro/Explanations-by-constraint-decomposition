# knapsack

**Signature.** `knapsack(array[int] of int: w, array[int] of int: p, array[int] of var int: x,
var int: W, var int: P)` — `∑ w_i x_i ≤ W` and `∑ p_i x_i = P`.

**Shape: `SCH-3`** (`_shapes-ext.md`) — weighted sums over integer variables. It shares nothing
with SCH-1/SCH-2 except the word "sum"; it is grouped into §6 by `CHRISTMAS_LIST.md`'s section
layout, not by decomposition.

**E-code: E1 + E3** (`CHRISTMAS_LIST.md` §6, which notes "none found" for the explanation
literature — this is the one constraint in either of this session's sections with no paper).

**Three walls at once, all named elsewhere.**

- **Integer summands.** `rule5`/`rule6`/`rule7` sum a Boolean family. `x_i` is an integer
  variable. The standard route — reify `B_{i,t} ⇔ x_i = t` and sum `t · B_{i,t}` — turns this
  into gap **X5** (weights) immediately.
- **Weights (gap X5).** `w_i`, `p_i`. Same requirement as `cumulative`'s `r_i`, and the same
  E3-means-two-things contradiction recorded in `cumulative.md` and `_gaps-ext.md`.
- **Two sums over the same variables.** This *is* the `failwith "sommes multiples pas encore
  implémentés"` site (source l.320, l.334, l.348) and is gap **G4** of
  `docs/DECOMP_FORMAT_NOTES.md` — the wall the counting pilot stayed on the near side of. The two
  sums share `x`, so no per-sum decomposition avoids it.

**Auxiliaries.** The `B_{i,t}` reification washes out as everywhere else; the bounds variables
`W` and `P` are the user's own and must print, which is gap **G2** again (`var_name` has no
letter for a constraint's own bound variable).

**Not a near-term entry.** Nothing about `knapsack` is close: it needs E1, the weighted form of
whichever extension X5 ends up being, and E3 proper.
