# lex_chain (covers `lex_chain_*`)

Instance of `lex2` (`decomps/lex2.md`): the same row-pairwise `lex_less`/`lex_lesseq`
replication, but `CHRISTMAS_LIST.md` §3 notes MiniZinc's own decomposition "branches on
instance data" — i.e. which pairs get chained, and how many, is instance-dependent rather than
fixed by the constraint's arity. That is an **instance-count** question, not a shape question:
the generator's `ind_set = D of int | D2 of ind_name list` already allows an index set given as
an explicit list rather than a fixed range, so a variable number of chained row-pairs is
already within the format's reach. No new file, no new gap — flagging only because
`CHRISTMAS_LIST.md`'s phrasing ("one entry per variant") could be misread as an engine
limitation; it is not, it is a per-instance modelling choice.
