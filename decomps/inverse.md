# inverse, inverse_in_range

`CHRISTMAS_LIST.md` §9. Shape reference: `decomps/_shapes-perm.md` Shape P3, two-array variant
(no third constant-valued variable, unlike `element`). Not in the generator — authored here.

`inverse(x, y)`: `x_i = j ⇔ y_j = i`, for `i, j ∈ [1,n]`.

**Decomposition (maths).**

- `B1_{i,j} ⇔ X_i = j`, `rule1`, AC, index `(i,j) ∈ [1,n]×[1,n]`.
- `B2_{j,i} ⇔ Y_j = i`, `rule1`, AC, same index set read the other way round.
- `¬B1_{i,j} ∨ B2_{j,i}` and `¬B2_{j,i} ∨ B1_{i,j}` — two `rule4` clauses, together the
  biconditional, exactly `element`'s two-clause pattern but without `element`'s third variable
  (there is no constant-valued `I`/`V` slot here; both sides are already array-indexed, so no
  scalar-quantifier trap of the kind `element.md` documents).

**E-code: E0 in spirit** (two `rule1`s + two `rule4`s, all schemas that already exist), but
**mechanically this reinvents `element`'s 5-`Decomp` structure by hand** because `rule1` only
links one `Global_devent` to one `Reified_devent` — there is no schema for
`Global_devent ⇔ Global_devent` directly. That is gap **G7**: every channelling constraint
between two arrays has to go through this same two-booleans-plus-two-OR-clauses detour, which
is boilerplate that a direct "channel" rule schema would remove. Not proposing the fix (engine
code, out of scope this wave) — just naming where it recurs.

`inverse_in_range(x, y, lo_x, hi_x, lo_y, hi_y)`: same shape, index sets restricted to
sub-ranges of `[1,n]` rather than the full array — hits the **same G6 subrange gap**
`all_different_except` hits (`ind_set` has no constructor for an arbitrary contiguous
sub-range either, only the three hardcoded full ranges `D 1`/`D 2`/`D 3`).

## Auxiliaries (D-0004)

`B1_{i,j}`, `B2_{j,i}` are pure reification scaffolding; a printed rule should show only `X`
and `Y` literals, same wash-out as `element`'s `B1`. Not verified by running anything — this
decomposition has not been added to the generator, so there is no `.tex` to check it against.

## Skipped

`int_set_channel`, `link_set_to_booleans` — set variables, **E5**, one line in the family index
(`decomps/_shapes-perm.md`), no spec.
