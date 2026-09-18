# member

`CHRISTMAS_LIST.md` §9: `member(x, y)` — `exists(i)(x[i]=y)`, **E0**. Shape reference:
`decomps/_shapes-perm.md` Shape P4 (existential disjunction over one array against a fixed
target). Not in the generator — authored here.

**Decomposition (maths).**

- `B_i ⇔ X_i = y`, `i ∈ [1,n]`, `rule1`, AC (`y` a parameter, matching this project's D-0003
  choice to keep the target a constant rather than a variable, same move `at_least.md` makes
  for its `v`).
- `∃i: B_i`, a single `rule4` existential clause — the same shape `nvalue.md` uses for its
  `B2_t ⇔ ∃i: B1_{i,t}` step, minus the outer `t` index (here the target is fixed, not ranged
  over a value domain).

**E-code: E0.** Both schemas (`rule1`, `rule4`) already exist and are already used for exactly
this pattern elsewhere (`nvalue`'s step 2). Three-line instance, no new derivation needed.

## Auxiliaries (D-0004)

`B_i` only; washes out the same way `at_least`'s and `nvalue`'s reification booleans do — a
printed rule should mention only `X` and the parameter `y`.

## What's known-broken

Nothing — not shipped, no defect to inherit.
