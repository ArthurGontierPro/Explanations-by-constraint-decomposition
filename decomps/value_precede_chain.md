# value_precede_chain

Instance of `decomps/value_precede.md` (Shape B): `value_precede_chain(c, x)` for a value
sequence `c = [c_1,...,c_k]` is `value_precede(c_j, c_{j+1}, x)` for every consecutive pair
`j ∈ [1,k-1]`. Same auxiliary `b_i` per pair (or one two-state chain per pair — either way,
`k-1` independent copies of `value_precede`'s decomposition, not a new shape). Same E-code
(E0) and same auxiliary-leak caveat. No new file needed beyond this pointer.
