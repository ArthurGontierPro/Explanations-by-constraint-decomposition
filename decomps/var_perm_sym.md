# var_perm_sym

**Signature (as read off `CHRISTMAS_LIST.md` §3 alone — not independently checked against a
spec text).** Breaks symmetry under a permutation group acting on a variable array, native
propagator `sym-break.cpp`, literature Chu & Stuckey 2011 (the same static-symmetry-breaking
citation as `lex_less`, not a dedicated paper).

**Decomposition.** Canonical-ordering symmetry breaking of this kind is standardly expressed as
a `lex_lesseq` between the array and each of its images under the permutation group's
generators — i.e. an instance of `decomps/lex_less.md` (Shape B), one `lex_lesseq` pair per
generator, not one for the whole group. Same G3 blocker.

**E-code: E0/E2** per `CHRISTMAS_LIST.md` — the `/E2` likely covers per-instance generator sets
being data rather than a fixed arity, the same instance-count point as `lex_chain.md`, not a
new shape. Not independently re-derived beyond that; low confidence, flagged rather than
asserted.
