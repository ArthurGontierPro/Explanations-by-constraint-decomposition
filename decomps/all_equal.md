# all_equal

`CHRISTMAS_LIST.md` §1, and **shipped**: `alleq`, `explenation generator.ml` l.674–677,
generated as `cata/allequal.tex` (4 rules; **measured** 2 SOUND and MINIMAL / 2 UNSOUND per the
task brief, not re-measured here). Wave two's §1 session wrote `all_different.md` and missed
this one; added by W3-D.

Shape reference: `decomps/_shapes.md` **S4** (quantified indicator over one index family),
instantiated **twice with dual signs** and closed by one unquantified clause. Short instance
file, not a full derivation — no new schema and no new gap.

**Signature.** `all_equal(array[int] of var int: x)` — every `x_i` takes the same value.

**Decomposition (maths), read off the source.** A **bounds** decomposition: for each threshold
`t`, the array is entirely above it or entirely below it.

- `B1_i ⇔ X_i ≥ t` — `rule1`, **BC** (l.674). Note BC, not AC: `all_different` and the counting
  family reify `X_i = t`; this one reifies a bound, like `increasing` and `disjunctive` do.
- `B2 ⇔ ⋀_{i∈[1,n]} B1_i` — `rule3` over the whole `i` family (l.675).
- `B3 ⇔ ⋀_{i∈[1,n]} ¬B1_i` — `rule3`, the same step with the summand sign flipped (l.676).
- `B2 ∨ B3` — `rule4`, two literals, **no index family attached** (l.677).

Soundness of the decomposition itself: if all `x_i` equal `v` then for `t ≤ v` all are `≥ t`
and for `t > v` all are `< t`; conversely, if the dichotomy holds at every threshold, no two
variables can be separated by a threshold, so all are equal. The decomposition is right; see
below for what the generated rules do with it.

**Why this is S4 and not a shape of its own.** Steps 2 and 3 are each S4's single step — one
clause ranging over one whole index family — under the `{rule3, rule4}`-are-dual convention
stated at the top of `_shapes.md` (`⋀_i B_i = ¬⋁_i ¬B_i`, and both sign bits are free in
`Decomp_devent`). Step 4 is the same clause schema with **no** quantifier, a degenerate case
rather than a new arrangement. So `all_equal` adds no schema, no index family and no gap; it is
S4 composed with itself. Recorded as a composition, not as a thirteenth shape — the alternative
reading (a distinct "dichotomy at every threshold" shape) is stated here so the choice is
visible rather than silent.

**E-code: E0.** Every schema exists and is already running.

**Auxiliaries (D-0004).** `B1_i` washes out the way `increasing`'s does — it is nothing more
than `X_i ≥ t` and the printer substitutes it back; `cata/allequal.tex` prints only `X_i ≥ t` /
`X_i < t` literals, confirming it (read off the file). `B2`/`B3` are unquantified indicators
that also wash out through the `rule4`. No leak.

## What the entry should conclude, and what it ships

**Should**, from the dichotomy: if any other variable is above the threshold, every variable is.

- `X_i ≥ t  ←  ∃i' ≠ i: X_{i'} ≥ t`
- `X_i < t  ←  ∃i' ≠ i: X_{i'} < t`

**Ships** (read off `cata/allequal.tex`) four rules, of which the two non-trivial ones invert
the quantifier *and* the sign:

- `X_i ≥ t  ←  ∀i' ≠ i: X_{i'} < t` — from "all the others are below" it concludes the opposite
  of what follows.
- `X_i < t  ←  ∀i' ≠ i: X_{i'} ≥ t` — likewise.

These are the two the validator measures UNSOUND. The other two are
`X_i ≥ t ← X_i ≥ t, ∃i` and its dual — sound, and vacuous. **`explenation generator.ml` is
W3-S's file and is being repaired right now; nothing here proposes the fix**, and this file
records the intended conclusions so the repair has something to be checked against. The
inversion is in how the two `rule3` steps' quantifiers reach the printed premise, not in the
decomposition above, which is correct as written.

**Status: shipped, measured 2/4 sound, decomposition sound, rules under repair.**
