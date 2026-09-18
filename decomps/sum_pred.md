# sum_pred

`CHRISTMAS_LIST.md` §11. Route: **E9** (the row says "was E3 — D-0011"). Not in the generator —
authored here. Shape reference: `decomps/_shapes.md` **S12** (flat sum over integer-valued
variables), with a hedge on the second half.

**Signature — hedge, flagged not asserted.** `CHRISTMAS_LIST.md` §11 gives only
"none / decomp / E9" and no predicate signature, and this session's scoped reading (§11 only,
no web) does not pin MiniZinc's arity down. Two readings are current in the literature-free
state this file is written in:

- **(a) plain reading** — `sum_pred` is the generic "sum of an array of integer variables,
  compared against a bound or a variable total": `∑_{i∈[1,n]} X_i = S`.
- **(b) selected-index-set reading** — a decision variable `I` selects which of several index
  sets the sum ranges over: `∑_{j ∈ s[I]} c_j = S`.

Both are recorded because the E-code is the same under either and the *gaps* are not. Whoever
revisits this file should settle the signature against the MiniZinc predicate text first.

**Decomposition (maths), reading (a).**

- `B_{i,t} ⇔ X_i = t`, `i ∈ [1,n]`, `t ∈ [1,m]` — `rule1`, AC, the shared channelling grid.
- `∑_{i∈[1,n]} ∑_{t∈[1,m]} t · B_{i,t} = S` — one sum, integer-valued summands, obtained from
  the grid by weighting each reified literal by the value it stands for.

**Rule schemas.** `rule1` exists. The second line has **no schema**: `rule5`/`rule6`/`rule7`
count occurrences of one Boolean family with unit coefficients (source l.308–350). Weighting by
`t` is gap **G11** and adding *values* rather than counting is gaps **G12 + G13**.

**E-code: E9**, and E8 if the summands carry their own coefficients (`∑ w_i X_i`), which is then
`knapsack`'s single-sum half — see `decomps/knapsack.md`. Not E3: there is one sum here, not
several, so the `failwith "sommes multiples"` site is not reached under reading (a). Under
reading (b) it is still one sum, but its *extent* is chosen by a variable, which is gap **G14**
(`cumulatives` hit the same wall from the scheduling side).

**Auxiliaries.** `B_{i,t}` is reification scaffolding and washes out as everywhere else. `S` is
the user's own variable and must print — gap **G2** again (`var_name` has no letter for a
constraint's own total).

**Not a near-term entry.** E9 is unbuilt, and reading (b) additionally needs G14.
