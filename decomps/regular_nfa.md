# regular_nfa

**Signature.** As `regular`, with `d` a transition *relation* (`array[int,int] of set of int`)
instead of a function.

**Shape: `EXT-2b`, purely.** The layered Boolean state matrix already tolerates several
successors per `(q,t)` — `S_{i+1,q'} ⇔ ⋁_{(q,t): q' ∈ δ(q,t)} E_{i,q,t}` is the same `rule4` with
a larger disjunction. Nothing in the schema set changes.

**What differs from `regular`.** EXT-2a is unavailable: the NFA state is not a function of the
last symbol except in degenerate cases, so there is no auxiliary-free route. `regular`'s choice
between two shapes does not arise here — EXT-2b is the only option, and D-0004's exception
clause (the one that licenses `mdd`) is what licenses it.

**E-code: E1 + E2.** Plus gap **X7** — four index families (position, symbol, source state,
target state) exhaust `ind_fam`.
