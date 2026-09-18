# cost_mdd

**Signature.** As `mdd`, with a cost per edge and a total-cost variable.

**Shape: `EXT-4`** over `EXT-3` instead of `EXT-2b`. Differs from `cost_regular` only in where
the cost is attached (edge rather than `(state, symbol)` pair), which is the same 2-D constant
lookup.

**E-code: E1 + E2 + E9** — relabelled per **D-0011**, identically to `cost_regular.md` and for
the same reason: the cost accumulator adds values (E9, gaps G12 + G13), it is not multi-family
cardinality (E3) and it is not a coefficient on a Boolean count (E8). Plus gaps **X9 = G15**
(arithmetic on variable values) and **X8 = G17** (`mdd`'s reachability explanation is not
derivable from the clausal unfolding). Nothing here is reachable before `mdd` is.
