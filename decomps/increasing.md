# increasing, decreasing, strictly_increasing, strictly_decreasing

`CHRISTMAS_LIST.md` §9. Shape reference: `decomps/_shapes-perm.md` Shape P2 (monotone adjacent
chain).

`increasing` and `decreasing` are pure Shape P2, already in the generator (`incr`/`decr`,
lines 688-691) and validated **2/2 each** (task brief). `CHRISTMAS_LIST.md` calls this pair
"already correct in the repo" and "cleanly dual" — confirmed by reading the two decomposition
values directly: `decr` is `incr` with the two `Decomp_devent` signs in the `rule4` clause
swapped, nothing else differs.

`strictly_increasing`/`strictly_decreasing`: same shape, same two rule schemas (rule1 + rule4),
threshold shifted by one — either an `Addint` step onto the existing index-shift operators
(`imoin 1`/`iplus 1` become `imoin 1`/`iplus 0`-with-strict-BC, depending on which side absorbs
the strictness) or a switch from `≥`/`<` (BC) framing to `>`/`≤`. **E0**, no new schema, not
derived line-by-line here because it is a pure parameter change on an already-validated shape.

## Auxiliaries (D-0004)

`B_i`, reification of `X_i ≥ t`, washes out identically to `increasing`/`decreasing` today —
only `X` literals print in `cata/increasing.tex`/`cata/decreasing.tex` (read off the files, not
re-verified here since the task brief already reports 2/2 validated).

## What's known-broken

Nothing in this file — this is the one pair in §9 the task brief and `CHRISTMAS_LIST.md` agree
is already correct.
