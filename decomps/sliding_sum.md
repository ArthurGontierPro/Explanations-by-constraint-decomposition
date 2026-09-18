# sliding_sum

**Signature.** `sliding_sum(int: low, int: up, int: seq, array[int] of var int: x)` — every
window of `seq` consecutive elements of `x` sums to within `[low,up]`.

**Decomposition (maths), per `CHRISTMAS_LIST.md` §4.** MiniZinc's own decomposition (prefix
sums):

- `S_0 = 0`; `S_i = X_i + S_{i-1}`, for `i ∈ [1,n]` — integer running total, **not** Boolean.
- `low ≤ S_{i+seq} - S_i ≤ up`, for every valid `i`.

**D-0004 exception, explicitly.** `CLAUDE.md`/D-0004 name `sliding_sum` as one of the
constraints with "no known auxiliary-free decomposition" — its auxiliary (`S_i`) must be
recorded and justified rather than eliminated. Recorded here: `S_i` means "sum of `x_1..x_i`",
and if it appears in a printed explanation the reader needs that told to them; the catalog
entry should print it as a named quantity, not leave it unexplained.

**Why this does not fit any of Shapes A–D (`decomps/_shapes-seq.md`).** Every existing rule
schema (`rule1`, `rule3`–`rule7`) is built over `event`s, and every summing schema
(`rule5`/`rule6`/`rule7`) sums **occurrences of a Boolean `Decomp_devent`** — i.e. cardinality,
"how many indices satisfy this Boolean condition" — never a sum of the variables' own integer
values. `S_i = X_i + S_{i-1}` is arithmetic on `X_i` itself, and `var_name`'s closed variant
(`X | B of int | T | I | V | N | O`) has no constructor for an integer-valued auxiliary either
(`DECOMP_FORMAT_NOTES.md`'s G2, about `var_name` lacking slots, generalises to this case too).

**E-code: E1 + E2**, matching `CHRISTMAS_LIST.md` exactly — confirmed by reading the generator
rather than only trusting the list entry. Two genuinely separate needs:
- **E1** — an integer-sum rule schema (`S_i` itself, and the window difference
  `S_{i+seq}-S_i`), which is new engine work, not a variant of `rule5`–`rule7`.
- **E2** — threshold arithmetic `u-t` (the window test is against a *difference* of two sums
  against two constants `low`/`up`, not a single comparison against one constant the way
  `at_least(n,x,v)`'s `n` is).

**Rule schemas: none apply as-is.** This constraint cannot be given a `decomps/<name>.md` rule
derivation under the current encoding — it can only be specified at the maths level, as done
above, pending E1/E2. Recording that explicitly rather than forcing it through `rule1`/`rule3`
and producing a decomposition that looks encoded but silently drops the arithmetic (the
`DECOMP_FORMAT_NOTES.md` G1 pattern: plausible-looking output that omits the constant that
matters).
