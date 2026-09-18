# exactly

**Signature.** `exactly(int: n, array[int] of var int: x, int: v)` — `v` occurs exactly `n`
times in `x`. `n`, `v` par. This is `count(x,v,c)` with `c` fixed to the constant `n` instead of
left as a decision variable — so it needs no count-channel step at all, unlike `count`.

**Decomposition (maths).**

- `B_i ⇔ X_i = v`, for `i ∈ [1,n_x]`.
- `∑_{i∈[1,n_x]} B_i = n`.

**Rule schemas.**
1. `B_i ⇔ X_i = v` → `rule1`, `i ∈ [1,n_x]`, AC.
2. `∑ B_i = n` → `rule7` (Bool sum `=`), single `Decomp_devent`, no `Reified_devent` — same
   "implicit constant" shape as `at_least`/`at_most`, using the schema `count` needs the
   two-step channelled form of (generator lines 406-409 for `nvalues`' analogous `B4` step).

**Index sets and relations.** `i ∈ [1,n_x]` only.

**E-code: E0.** `rule1` + `rule7`, pre-existing schemas, single-element decomp-event list
already precedented by `alldifferent`'s `rule5` use.

**Auxiliaries.** `B_i` only, non-leaking (D-0004), same reasoning as `at_least`/`at_most`.
Inherits format-gap G1 exactly (the constant `n` is invisible in the printed rule) — for
`exactly` this is arguably the sharpest case of the three, since `exactly`'s defining feature
*is* the precise count `n`, and the generated LaTeX would say only "occurs" / "does not occur"
with no number attached.
