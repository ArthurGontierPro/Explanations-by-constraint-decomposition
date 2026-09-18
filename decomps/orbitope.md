# orbitope (covers `*_orbitope`)

Instance of `lex_chain` (`decomps/lex_chain.md`): row-wise and column-wise lex ordering
combined (the standard orbitope symmetry-breaking shape is `lex2` applied to rows **and**
`lex2` applied to columns of the same matrix). Column ordering reuses the same Shape B chain
with the roles of `I` (column index) and `R` (row index) swapped. No new schema, no new index
family — same G3 blocker as `lex_less`. E0.
