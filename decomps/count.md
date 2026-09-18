# count

> Shape reference: **`decomps/_shapes.md`** (W3-D, 2026-09-18) is the single cross-family
> shape list. The shape derived in this file is **S3** there, shared with constraints from
> other families.

**Signature.** `count(array[int] of var int: x, int: v, var int: c)` — `c` = the number of
`i` such that `x_i = v`. Per D-0003 we take `v` as a parameter (constant), matching
`CHRISTMAS_LIST.md:125` ("E0 — this is rule5/6/7 exactly as built"); a variable `v` needs G3
below.

**Decomposition (maths).**

- `B_i ⇔ X_i = v`, for `i ∈ [1,n]` — channel.
- `B'_p ⇔ C = p`, for `p ∈ [0,n]` — channel the count variable.
- `∑_{i∈[1,n]} B_i = p ⇔ B'_p` — the sum, closing the loop with the channel above.

**Rule schemas.**
1. `B_i ⇔ X_i = v` → `rule1` (reified equivalence), index set `i ∈ [1,n]`, AC.
2. `C ⇔` (channelled the same way `N` is in `nvalues`, generator lines 406-407) → `rule1`,
   index set `p ∈ [0,n]`, AC.
3. `∑ B_i = p ⇔ B'_p` → `rule7` (Bool sum `=`), summing over `i ∈ [1,n]`, matched against the
   `p`-indexed channel from step 2 — same shape as `nvalues`' `B4` step (generator line 409),
   minus the intermediate per-value existential that `nvalue`/`among` need and `count` does not
   (there is exactly one target value `v`, not a set).

**Index sets and relations.** `i ∈ [1,n]` (array positions), `p ∈ [0,n]` (possible count
values). No relation between them beyond the sum ranging over all of `i`'s domain for each
fixed `p` — identical in shape to `nvalues`' `p`/`t`/`i` grid, one dimension narrower.

**E-code: E0.** Two `rule1` channels plus one `rule7`, all schemas already exist and are
already exercised by `nvalues`/`gcc`. No engine change needed.

**Auxiliaries.** `B_i` (per `i`) and `B'_p` (per `p`) are pure reification scaffolding for
`rule1`/`rule7`; per D-0004 they must not leak, and by the same mechanism visible in
`cata/nvalues.tex` (which prints only `X` and `N` literals, never a `B`), they wash out of the
final printed explanation. The one real vocabulary note: `count`'s own count variable has no
dedicated `var_name` constructor (the type is `X | B of int | T | I | V | N | O`); reusing `N`
(already `nvalue`'s letter) or `O` is the only option today. Mechanically harmless within one
catalog file, but it means the printed letter for "count of `v`" is borrowed from another
constraint rather than being `count`'s own — see format-gap G2.
