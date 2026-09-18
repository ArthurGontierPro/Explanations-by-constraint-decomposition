# at_least

> Shape reference: **`decomps/_shapes.md`** (W3-D, 2026-09-18) is the single cross-family
> shape list. The shape derived in this file is **S2** there, shared with constraints from
> other families.

**Signature.** `at_least(int: n, array[int] of var int: x, int: v)` — `v` occurs at least `n`
times in `x`. `n` and `v` are both parameters (par) in the standard MiniZinc global, so this
constraint has no auxiliary decision variable to channel at all — it is strictly simpler than
`count`.

**Decomposition (maths).**

- `B_i ⇔ X_i = v`, for `i ∈ [1,n_x]` (using `n_x` for the array length to avoid clashing with
  the parameter `n`).
- `∑_{i∈[1,n_x]} B_i ≥ n`.

**Rule schemas.**
1. `B_i ⇔ X_i = v` → `rule1`, index set `i ∈ [1,n_x]`, AC.
2. `∑ B_i ≥ n` → `rule6` (Bool sum `≥`), a single `Decomp_devent` with **no** `Reified_devent`
   — the same shape `alldifferent` uses for its implicit "≤1" (generator line 388:
   `Decomp (2, rule5, [Decomp_devent (true, (B 1), id, oni)])`). `reified_devent` on an empty
   remainder defaults to the placeholder `Reified_devent (true, T, id, id)` (generator line
   111), which never matches any real variable name, so the rule always takes the "explain the
   individual `B_i`" branch rather than ever concluding something about `n`.

**Index sets and relations.** `i ∈ [1,n_x]` only. No second index — `v` and `n` are baked in as
constants, not events.

**E-code: E0.** `rule1` + `rule6`, both already built and already used elsewhere with a
single-element decomp-event list.

**Auxiliaries.** `B_i` only, washing out per D-0004 exactly as in `count`. **But** see
format-gap G1: because the threshold `n` is carried as a bare OCaml `int` inside the
`Decomp_ctr`/schema call rather than as any kind of `event` or `index`, it never appears
anywhere in the printed LaTeX — confirmed empirically against `cata/alldifferent.tex`, whose
generated rule never prints its own implicit "1". `at_least`'s entire point is the number `n`,
so this is not cosmetic: the generated explanation for `at_least` will read "occurs" with no
threshold, indistinguishable from `at_most`'s or `exactly`'s equally silent threshold.
