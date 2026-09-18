# value_precede

**Signature.** `value_precede(int: s, int: t, array[int] of var int: x)` — if `t` occurs in
`x`, some earlier position holds `s` first. `s`, `t` par (per D-0003).

**Decomposition (maths).** Shape B (`decomps/_shapes-seq.md`):

- `b_1 = false` (base case: nothing precedes position 1).
- `b_{i+1} ⇔ b_i ∨ (X_i = s)`, for `i ∈ [1,n_x-1]` — "`s` has appeared by position `i`".
- `X_i = t → b_i`, for `i ∈ [1,n_x]` — `t` may not appear before `s` has.

**Rule schemas.**
1. `X_i = s` channel is already the shared `B1_{i,t}`-style grid (`rule1`, AC) used by
   `among`/`count`/`gcc`; no new channel needed for the `X_i=s` half.
2. `b_{i+1} ⇔ b_i ∨ (X_i=s)` → `rule4` (disjunction), fixed shift `i→i+1`/`i→i-1` — mechanically
   identical to `incr`'s `rule4` (generator line 689), except the disjunct is `b_{i-1}` itself,
   not a re-indexed copy of the *same* reified predicate.
3. `X_i = t → b_i` → `rule3`-style implication (or its contrapositive as a `rule4`), AC.

**E-code: E0** per `CHRISTMAS_LIST.md` §3 (native propagator, `value-precede.cpp`), and
`rule3`/`rule4` both pre-exist. Mechanically nothing new is required to *encode* this
decomposition.

**Auxiliaries.** `b_i` is not optional the way `count`'s `c` or `among`'s `B2_i` are — it is
the only device that expresses "somewhere earlier". Per D-0004 it must be justified and its
printed appearance stated. **It does not wash out the way Shape A's `B` does**: `b_i` has no
backing `Global_devent`, so `var_name`'s catch-all `B i -> "ERROR B "` (generator lines 399,
427) is live for it — see `decomps/_shapes-seq.md` Shape B and `_gaps-seq.md`. Whether the
generated `cata/value_precede.tex` would show a real premise or the literal text `"ERROR B "`
depends on whether `find`'s AND/OR walk fully unfolds the recursion to a base case before it
gives up; **not run, so not known** — flagged, not measured.

**Checking the roadmap's claim.** `docs/ROADMAP.md`/`CHRISTMAS_LIST.md` both call this
"structurally identical to `increasing`". True at the level of "`rule4` plus a fixed shift by
1" — the recursion mechanics match. **False** at the level that matters for this catalog:
`increasing`'s chained `B_1` *is* the explained literal (`X_i≥t`), so it needs zero genuine
auxiliaries; `value_precede`'s `b_i` is an accumulated fact with no single-literal equivalent,
so it is a real auxiliary of exactly the kind D-0004 says must be justified and may leak. Report
this as a correction to the "good early win" framing, not a rejection of E0 — the schemas
exist, but the auxiliary-leak risk that `increasing` sidesteps is real here.
