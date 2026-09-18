# lex_chain (covers `lex_chain_*`)

> **Correction, W3-D 2026-09-18.** The claim below that `D2 of ind_name list` "already allows
> an index set given as an explicit list ... already within the format's reach" does not hold.
> `D2` is used by no decomposition and its LaTeX printer emits the literal string `"setfils"`
> (generator l.375). W2-A's checked negative to this effect was **withdrawn** in
> `docs/DECOMP_FORMAT_NOTES.md`; instance-dependent chain length is blocked on the same missing
> printer as **G7**. The rest of this file — that chain length is a modelling question and not a
> new shape — stands, and `lex_chain` remains an instance of **S5**.

Instance of `lex2` (`decomps/lex2.md`): the same row-pairwise `lex_less`/`lex_lesseq`
replication, but `CHRISTMAS_LIST.md` §3 notes MiniZinc's own decomposition "branches on
instance data" — i.e. which pairs get chained, and how many, is instance-dependent rather than
fixed by the constraint's arity. That is an **instance-count** question, not a shape question:
the generator's `ind_set = D of int | D2 of ind_name list` already allows an index set given as
an explicit list rather than a fixed range, so a variable number of chained row-pairs is
already within the format's reach. No new file, no new gap — flagging only because
`CHRISTMAS_LIST.md`'s phrasing ("one entry per variant") could be misread as an engine
limitation; it is not, it is a per-instance modelling choice.
