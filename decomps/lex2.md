# lex2 (covers `lex2`, `strict_lex2`, `lex2_strict`)

**Signature.** `lex2` orders the rows of a matrix pairwise under `lex_lesseq` (`strict_lex2`/
`lex2_strict` under `lex_less`). `CHRISTMAS_LIST.md` §3 lists all three together with one
literature/route entry, which reads as MiniZinc treating them as near-duplicates; **not
independently confirmed** — flagging rather than asserting `strict_lex2 = lex2_strict`.

**Decomposition.** `lex_less`/`lex_lesseq` (`decomps/lex_less.md`, Shape B) applied to every
pair of adjacent rows. The only addition versus a single `lex_less` call is the second,
row-indexing dimension.

**A positive finding, not a gap.** The generator already has a third index family, `R of int`
(`ind_name = I of int | T of int | P of int | R of int`), used by `table`'s decomposition to
address a table's row (`generator.ml`'s `table` decomp uses `onr`/`D 4`-style row sets, and
`x3ac` at line ~727 is a three-index `Global_event` `[I 1; T 1; R 1]`). So a matrix's row index
for `lex2` does **not** need a new index family — `R` already exists for exactly this
"address a second, row-like dimension" purpose. This is worth recording because it would be
easy to assume matrix constraints need new engine machinery; here they can reuse `R`.

**E-code: E0.** `rule3`/`rule4` per `lex_less`, `R`-indexed replication already available.
Still blocked by G3 (var-vs-var `X_i=Y_i`), same as `lex_less` itself — replication across rows
does not add or remove that blocker.
