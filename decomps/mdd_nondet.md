# mdd_nondet

**Signature.** As `mdd`, without the determinism restriction on outgoing edge labels.

**Shape: `EXT-3`, purely.** The edge-flow encoding never assumed determinism — a node may have
several outgoing edges with overlapping labels and the `rule4` disjunction is unchanged.

**E-code: E1 + E2**, identical to `mdd`, including gap **X8** (the reachability explanation is
expressible but not derivable) and gap **X7** (index families).
