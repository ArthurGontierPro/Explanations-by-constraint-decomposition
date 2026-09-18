# write, writes, writes_seq

`CHRISTMAS_LIST.md` §11: "**E2** (array update = `element` family)". Shape reference:
`decomps/_shapes.md` **S6** (cross-variable channel by paired OR-clauses) — the same shape
`element` and `inverse` instantiate. Not in the generator — authored here.

**Signature.** `write(array[int] of var int: a, var int: i, var int: v,
array[int] of var int: b)` — `b` is `a` with position `i` overwritten by `v`. `writes` does
several positions at once; `writes_seq` applies them in sequence, so it is `writes` with the
later updates taking precedence.

**Decomposition (maths).** Two halves, and only the first is `element`.

- **The written cell** — exactly `element`: `B_i ⇔ I = i`, `B_t ⇔ V = t`,
  `B1_{i,t} ⇔ B_i = t`, then the two `rule4` clauses `¬B_i ∨ ¬B_t ∨ B1_{i,t}` and
  `¬B_i ∨ B_t ∨ ¬B1_{i,t}`. This is S6 verbatim, with `B` (the output array) in the slot
  `element` gives to its input array.
- **Every other cell** — `∀j ≠ I: B_j = A_j`, an array-to-array channel *guarded by a
  disequality against a decision variable*.

**Rule schemas.** The first half needs only `rule1` and `rule4`, as `element` does.
The second half needs `rule1` on both arrays plus two `rule4` clauses per position — gap **G9**
again (no `Global ⇔ Global` schema, so every channel re-derives `element`'s detour) — and it
needs its index set to exclude a position named by a *variable*.

**E-code: E2**, as `CHRISTMAS_LIST.md` gives it, plus **gap G18** (new, see
`docs/DECOMP_FORMAT_NOTES.md`): the quantifier `∀j ≠ I` ranges over an index set whose excluded
point is a decision variable. **G8** covers a range minus a *constant* (`all_different_except`)
and **G14** covers a *summation* whose extent a variable determines (`cumulatives`); neither
covers a universally quantified channel with a variable-determined hole. The auxiliary-free
workaround that works for `cumulatives` — reify `M_i = k` and conjoin it — applies here too
(`B_j = A_j ∨ I = j`, a `rule4` clause per `j`), and it is probably the right decomposition;
recorded as the intended one, with G18 noted because the *quantifier* form is what the format
cannot write.

**What differs per variant.**
- `write` — one update. Pure S6 plus the guarded channel above.
- `writes` — `k` updates. The guard becomes `∀j ∉ {I_1..I_k}`, i.e. a conjunction of `k`
  disequalities; same G18, `k` times. The updates must also be pairwise distinct or the
  constraint is unsatisfiable unless the values agree — an `all_different`-flavoured side
  condition (**S2**) on the index array.
- `writes_seq` — same as `writes` with a priority order among colliding indices, i.e. the
  later write wins. Expressing "later wins" needs, per position, a disjunction over *which*
  update was last to touch it, which is a second guarded channel of the same kind. No new
  shape, no new gap beyond G18.

**Auxiliaries.** `B_i`, `B_t`, `B1_{i,t}` are reification scaffolding. `A`, `B`, `I`, `V` are
all the user's own variables and must print; G2 applies to none of them in `element`'s case
(`X`, `I`, `V` already have letters) but the *second* array has no letter — the `var_name` enum
is `X | B of int | T | I | V | N | O` and `B of int` is the Boolean-auxiliary family, so a
second user array would print as a Boolean auxiliary. That is **G2** on a new constraint, and
it is sharper here than in the cases already recorded, because the collision is with the
auxiliary family rather than with another constraint's letter.

**Status: authored, not generated, not validated.**
