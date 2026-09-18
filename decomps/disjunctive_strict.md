# disjunctive_strict

**Signature.** As `disjunctive`, but zero-duration tasks may not overlap other tasks either.

**Shape: `SCH-1`, purely.** The strictness changes only which time points a zero-duration task
occupies — `B2_{i,t}` becomes true at `t = s_i` when `d_i = 0`, a boundary condition on the same
`rule3` conjunction, not a new schema.

**E-code: E0** for constant durations, **E2** for variable ones, exactly as `disjunctive`.
