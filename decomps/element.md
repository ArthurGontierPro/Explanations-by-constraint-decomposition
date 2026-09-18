# element

`CHRISTMAS_LIST.md` §9. Shape reference: `decomps/_shapes-perm.md` Shape P3 (three-way channel
via cross-variable OR-clauses). Already in the generator (`elem`, lines 692-696), generated as
`cata/element.tex` with 6 rules, validated **2/6** (task brief).

`element(x, i, v)`: `v = x_i`. Decomposition reifies each of the three global variables (`X`,
`I`, `V`) to its own Boolean via `rule1`, then encodes the biconditional `(I=i ∧ V=t) ⇔ X_i=t`
as two `rule4` OR-clauses (De Morgan expansion, generator lines 695-696). Full derivation is in
the shape file; nothing about `element` itself differs from the shape.

## The known defect, and what the decomposition should have been

Task brief: 4 of 6 rules are lost to unsatisfiable premises reading `∀t: V=t` / `∀i: I=i`.
Reading Shape P3's clauses: `I` and `V` are scalar globals (one instance, no array index), so
`B2 ⇔ I=i` and `B3 ⇔ V=t` are point facts, not array-indexed families — they should need **no**
quantifier when substituted into a query at a fixed `(i,t)`. The shipped clauses instead
compose `foralli`/`forallt` (`EXFORALL`) onto those `Decomp_devent`s (lines 695-696):
`Decomp_devent (false, B3, foralli, i_out)` and `Decomp_devent (false, B2, forallt, t_out)` —
note `B3` (which should quantify over nothing, since `V` has no array index at all) is composed
with `foralli`, and `B2` with `forallt`, each the *wrong* variable's quantifier grafted onto the
*other* scalar. What it should have been: point substitution with no quantifier at all —
`Decomp_devent (false, B2, id, i_out)` and `Decomp_devent (false, B3, id, t_out)`, mirroring
how `B1` in the same clause is left unquantified (`id, id`). This reads as an index-operator
authoring slip (composing a stray `EXFORALL` where a plain substitution was meant), the same
class of bug `nvalue.md` documents for `nvalues`' repeated binders — not a limitation of Shape
P3 itself, since the shape's two-clause biconditional is otherwise sound (that's exactly how
`inverse` below is derived without hitting this problem, because it never introduces a
scalar-with-spurious-quantifier in the first place).

## Auxiliaries (D-0004)

`B1_{i,t}`, `B2_i`, `B3_t` — three reification booleans, washing out per D-0004 if the printer
reaches them; task brief does not report whether `cata/element.tex`'s surviving 2 rules print
clean `X`/`I`/`V` literals only, so this is not claimed as verified here.
