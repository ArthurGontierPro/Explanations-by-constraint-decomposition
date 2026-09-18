# cost_mdd

**Signature.** As `mdd`, with a cost per edge and a total-cost variable.

**Shape: `EXT-4`** over `EXT-3` instead of `EXT-2b`. Differs from `cost_regular` only in where
the cost is attached (edge rather than `(state, symbol)` pair), which is the same 2-D constant
lookup.

**E-code: E1 + E2 + E3**, plus gaps **X9** (arithmetic on variable values) and **X8** (`mdd`'s
reachability explanation is not derivable from the clausal unfolding). Nothing here is reachable
before `mdd` is.
