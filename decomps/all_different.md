# all_different, all_different_except, all_different_except_0, symmetric_all_different

`CHRISTMAS_LIST.md` §1. Shape reference: `decomps/_shapes-perm.md` Shape P1 (pairwise-sum
guard) and, for `symmetric_all_different`, also gap G8 below.

## all_different

Pure Shape P1, already in the generator (`alldiff`, l.808–809 — was 678-679, stale since W1-T3/T7 grew the file) and validated **1/1 sound
and minimal** (task brief, not re-measured here). One rule, `X_i ≠ t ← ∃i'≠i: X_i'=t`; the
second rule ("X_i = t") some earlier note wanted does not exist because it needs Hall-set
counting across sums (E4), not a ≤-direction sum. Nothing to add.

## all_different_except, all_different_except_0 (and the `alldifferent_except_0` alias)

Shape P1, guarded: the sum in step 2 must range over `t ∈ [1,m] \ {v_0}` instead of the full
value domain, where `v_0` is the excepted value (fixed at `0` for the `_0` variant, a parameter
for the general one). **E0** in spirit — same two rule schemas, no new schema — but **blocked
by gap G6**: `ind_set` (generator line 6: `type ind_set = D of int | D2 of ind_name list`) has
no constructor for "a named range minus one point". `D2` looks promising (a list of index
names) but is unused by any shipped decomposition and the printer (`printind_set`, line 375)
doesn't handle it beyond `"setfils"` — a placeholder string, not real output. So this
constraint's decomposition can be written on paper but not encoded as-is today.

## symmetric_all_different

`alldifferent(x)` (Shape P1, as above) **conjoined with** `∀i: x[x_i] = i` — the self-inverse
channelling half. That second conjunct is **not expressible at all** in the current format:
`Global_event`'s index positions are `ind_name` values (`I`/`T`/`P`/`R`), and there is no way
to write "the index is itself the *value* of another occurrence of `X`". This is gap **G8**,
distinct from G7 (which is about linking two Global variables' *values*, not one variable's
value used as the *other's index*). Recorded here rather than derived, because there is no
partial decomposition to write down — the blocking point is the very first index position.

## Auxiliaries (D-0004)

Shape P1's `B_{i,t}` washes out exactly as `alldifferent.tex` demonstrates (only `X` literals
print). `symmetric_all_different`'s blocked half would, if the format supported it, likely
still print only `X` literals (no aux needed for a direct index-into-array equality) — but this
is speculative since it cannot be authored to check.

## What's known-broken elsewhere in this file's namespace

None — `all_different` is the one family-1 entry the task brief lists as already sound. The
guarded and self-inverse variants are un-encodable rather than broken.
