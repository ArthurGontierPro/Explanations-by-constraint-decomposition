# disjunctive_opt

**Signature.** As `disjunctive`, with an array of Booleans saying which tasks actually occur.

**Shape: `SCH-1` + modifier `M-opt`** (`_shapes-ext.md`): `B2_{i,t} ⇔ Ex_i ∧ (overlap)`, a
three-element `rule3` conjunction, which the schema already accepts.

**E-code: E0 for the schema, E1 for the family name.** `Ex_i` is a variable the *user wrote*, so
it leaks legitimately under D-0004 and should print. It cannot be named: `var_name` is the closed
enum `X | B of int | T | I | V | N | O` and the nearest letter, `O`, already prints as
`global_cardinality`'s occurrence variable — gap **G2** of `docs/DECOMP_FORMAT_NOTES.md`.
