# at_most

> Shape reference: **`decomps/_shapes.md`** (W3-D, 2026-09-18) is the single cross-family
> shape list. The shape derived in this file is **S2** there, shared with constraints from
> other families.

**Signature.** `at_most(int: n, array[int] of var int: x, int: v)` — `v` occurs at most `n`
times in `x`. `n`, `v` par, same shape as `at_least` with the inequality flipped.

**Decomposition (maths).**

- `B_i ⇔ X_i = v`, for `i ∈ [1,n_x]`.
- `∑_{i∈[1,n_x]} B_i ≤ n`.

**Rule schemas.**
1. `B_i ⇔ X_i = v` → `rule1`, `i ∈ [1,n_x]`, AC.
2. `∑ B_i ≤ n` → `rule5` (Bool sum `≤`), single `Decomp_devent`, no `Reified_devent` — exactly
   `alldifferent`'s own pattern (generator line 388), with `alldifferent`'s implicit threshold
   of 1 replaced by `at_most`'s general `n`.

**Index sets and relations.** `i ∈ [1,n_x]` only, as `at_least`.

**E-code: E0.** `rule1` + `rule5`, both pre-existing, both already exercised with a
single-element decomp-event list (`alldifferent`).

**Auxiliaries.** `B_i` only, non-leaking per D-0004, identical justification to `at_least`.
Same format-gap as `at_least`: `n` is invisible in the printed rule (G1) — and since
`at_least(n,x,v)` and `at_most(n,x,v)` differ from each other, from `alldifferent`, and from
each other's negation *only* in that invisible threshold and in `rule5` vs `rule6`, the printed
LaTeX for two different `at_most` entries with different `n` would be byte-identical. This is
the same failure mode `CLAUDE.md` already documents for `atleastnvalues.tex`/
`atmostnvalues.tex` (byte-identical despite different decompositions) — here it would recur
*within* one constraint family across different `n`.
