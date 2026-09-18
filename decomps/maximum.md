# maximum, minimum, arg_max, arg_min, sort, arg_sort

`CHRISTMAS_LIST.md` §9. These five (six, counting `arg_max`/`arg_min` as a pair) do not get a
Shape-P instance because each is blocked by a real format gap rather than being a
straightforward substitution. Recorded together since the blocker is shared.

## maximum, minimum

`maximum(m, x)`: `m = max_i(x_i)`, i.e. `∀i: m ≥ x_i` and `∃i: m = x_i`. Both conjuncts compare
**two decision variables** (`m` and `x_i`), never a variable against a domain-derived value.
`Global_event`/`ind_modifs` (generator lines 6-19) only ever produce `X_i {=,≥,<} t` for `t` an
index-derived constant; there is no constructor anywhere in `decomp_event`/`ind_op` that takes
a second `var_name` as the comparison target. **No decomposition can be authored in the current
encoding — this is not a derivation gap, it is a missing primitive.** `CHRISTMAS_LIST.md`
already marks this **E2** and native-solver-only (`minimum.cpp`); this file adds no new claim,
just confirms the blocker by reading the type definition rather than inferring it from the
literature note.

## arg_max, arg_min

Needs everything `maximum`/`minimum` needs (var-var comparison, same block) **plus** a second
channel from the winning index back to a reported position variable — i.e. `maximum`'s blocked
comparison composed with something like Shape P4's existential-position pattern. Since the
first half is already blocked, this doesn't reach the second half. Float variants are **E7** on
top, out of scope per task instructions (one line, no spec).

## sort, arg_sort

`CHRISTMAS_LIST.md`: **E2**, "composes `element`". Concretely: the output array `y` is a
permutation of `x` (an all-different-style channel, Shape P1 territory) **and** sorted
(`increasing` on `y`, Shape P2, already fine) **and** each `y_j` must equal some `x_i` (Shape
P3, the `element`/`inverse` channel, hitting gap **G7** once per position pair). The
permutation-channel half additionally needs to say "`y` is `x` reordered by permutation `p`",
which is `y_j = x_{p_j}` — variable-valued index into `X`, the **same gap G8**
`all_different.md` records for `symmetric_all_different`. So `sort` hits G7 and G8 both, on top
of composing three already-distinct shapes. Sketched, not derived line-by-line, because the
G8 half has no representable starting point (same reasoning as `symmetric_all_different`).

## Auxiliaries (D-0004)

Not reached — none of the six constraints here has a completable decomposition to attach
auxiliaries to.

## What's known-broken

None shipped in the generator for any of these six; nothing to inherit.
