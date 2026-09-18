# table

**Signature.** `table(array[int] of var int: x, array[int,int] of int: t)` — the tuple
`x[1..n]` is one of the rows of the constant matrix `t[1..m_r, 1..n]`.

**Shape.** `EXT-1` (`_shapes-ext.md`), the only instance of it in scope. `in_relation` in gccat
is the same shape and is out of this wave's file scope.

**What differs from the shape: nothing. `table` *is* EXT-1.** The full maths, literals, rule
schemas (`rule1` / `rule3` / `rule4`), index families (`i`,`t`,`r`) and the auxiliary `R_r` with
its D-0004 wash-out argument are in `_shapes-ext.md` and are not repeated here.

**E-code: E2**, for gap **X1** — the side condition `t = T[r,i]`, a constant table read as a
function of two indices. This is the one thing standing between the format and a correct
`table`.

**Status of the shipped entry — this is the part worth writing down.**

`cata/table.tex` ships three rules and `docs/VALIDATOR.md` l.287 **measures** all three as
UNSOUND; the first has an empty premise and carries the generator's own W1-T4 defect comment in
the file. Read off `explenation generator.ml` l.720–722 and l.734 (`x3ac`), the cause is
structural rather than a printer accident:

- the global event is `x3ac = Global_event (true, X, [Ind (I 1,[]); Ind (T 1,[]); Ind (R 1,[])], AC)`
  — the row index `r` is attached to the **`X` literal itself**;
- the `rule1` step uses `id`/`id` on the `Global_devent`, so `r` is neither introduced on the
  way down nor removed on the way up;
- nothing anywhere states `t = T[r,i]`.

So the decomposition says "`B1_{i,t,r} ⇔ X_i = t`", which is `r`-independent on the right and
`r`-indexed on the left, and the `rule3`/`rule4` steps then quantify over an `r` that constrains
nothing. An empty premise concluding `X_i = t` is the visible symptom of a free index, not of a
missing rule. `docs/VALIDATOR.md` l.123–125 also notes it has to *guess* `D_4` as the row set
because the printer never defines it, and l.340 that `D_4` means a different thing in
`cata/among.tex` — two independent signs that the row dimension is carried by convention rather
than by the encoding.

**Fixing it needs X1 and nothing else.** With a 2-D side condition the `X` event drops back to
two indices, `R_r` becomes a genuine `rule3` conjunction over `i` at fixed `r`, and the derived
rules are the smart-table justifications of McIlree & McCreesh, CP 2023 (`CHRISTMAS_LIST.md`
§5). Until then this entry is **generated, unvalidated, and measured unsound**.
