# seq_precede_chain

`CHRISTMAS_LIST.md` §3 lists this separately from `value_precede_chain` with route E0 and no
solver column filled in (unlike `value_precede*`, which says **native**); read as: decomposed
only, no dedicated propagator noted. Same instance-of relationship as
`decomps/value_precede_chain.md` — `seq_precede_chain(x)` is `value_precede(v, v+1, x)` for
every consecutive pair of values `v` in the array's domain (the "chain" is over the *value*
domain, not an externally given sequence `c`). Same Shape B, same auxiliary-leak caveat as
`decomps/value_precede.md`. No new file.
