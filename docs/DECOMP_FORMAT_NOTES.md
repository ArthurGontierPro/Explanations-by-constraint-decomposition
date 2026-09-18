# Decomposition format notes — payload for W2-T1

Written while specifying the counting family (`decomps/count.md`, `at_least.md`, `at_most.md`,
`exactly.md`, `among.md`, `nvalue.md`, W2-T5 pilot). Each bullet is a concrete gap in the
current `event`/`ind_modifs`/rule-schema encoding, named against the constraint that hit it,
read off `explenation generator.ml` and the generated `cata/*.tex` — not from web research or
from `CHRISTMAS_LIST.md`'s own extension table (E0-E5), which this list refines rather than
repeats.

- **G1 — no way to carry a bare integer threshold into the printed rule.**
  `at_least(n,x,v)`, `at_most(n,x,v)`, `exactly(n,x,v)` are each `rule1` + one of
  `rule5`/`rule6`/`rule7` with a single `Decomp_devent` and no `Reified_devent` — the same
  shape `alldifferent` already uses for its implicit "at most 1" (generator line 388). On an
  empty remainder, `reified_devent` defaults to a placeholder (`Reified_devent (true, T, id,
  id)`, generator line 111) that never matches a real variable, so the rule schema has no path
  that ever mentions the constant. Confirmed empirically: `cata/alldifferent.tex`'s one rule
  never prints its own implicit "1". The same will happen to `n` in all three counting
  constraints — the whole point of `exactly(n,...)` is `n`, and the generated LaTeX cannot say
  it. This is not an index-set problem or a printer omission that could be patched locally; the
  constant is never captured as an `event`, `index`, or anything else the printer walks — it
  lives only as an OCaml literal baked into which schema gets called.

- **G2 — `var_name` has no slot for "this constraint's own parameter", only borrowed letters.**
  `count`'s count variable `c` needs a `rule1` channel exactly like `nvalue`'s `N` or `gccn`'s
  `O`, but `var_name` is a closed variant (`X | B of int | T | I | V | N | O`) and none of its
  constructors mean "count of a single given value" — the nearest fits (`N`, `O`) already carry
  a different constraint's meaning. Mechanically harmless (each catalog file is generated in
  isolation), but it means the format cannot express "here is a variable that is native to this
  constraint's own signature" without reusing another constraint's printed letter. This
  sharpens `CHRISTMAS_LIST.md`'s E1 entry ("open `var_name`"): the gap isn't limited to
  *auxiliary* variables, it also blocks giving a constraint's own official variable its own
  name.

- **G3 — only variable-vs-domain-value comparisons exist, never variable-vs-variable.**
  `Global_event`/`ind_modifs` express `X_i = t` for `t` an index-derived domain value, never
  `X_i = Y_i` for two decision variables. This pilot sidesteps it by treating `count`'s `v` and
  `among`'s `s` as parameters (matching this project's own D-0003 choice to decompose for
  explanation quality), which the standard `at_least`/`at_most`/`exactly` MiniZinc globals also
  do — but `count`'s and `among`'s general MiniZinc signatures allow `v`/elements of the
  channel to be variables, and that would need this. Same wall as `CHRISTMAS_LIST.md`'s E2 line
  ("inequalities against expressions"), now with a concrete constraint pinned to it.

- **G4 — one Boolean-sum family per rule, hard failure otherwise.** `rule5`/`rule6`/`rule7`
  pattern-match `dee::[]` and `failwith "sommes multiples pas encore implémentés"` on anything
  else (generator lines 177-219). None of the six pilot specs need more than one summed family,
  but `among`/`count`'s shape is one step away from `global_cardinality`'s per-value sums, which
  do need this (`CHRISTMAS_LIST.md`'s E3) — worth flagging now because the pilot's simplicity
  is partly *because* it stays on this side of the wall, not because the wall isn't there.

- **G5 — found while re-deriving `among`, a decomposition bug rather than a format gap:** the
  shipped `among` (generator lines 418-420) uses the single-`Decomp_devent` `rule7` shape (G1's
  shape) for its own count variable `n`, instead of the two-step `N`-channel shape `nvalues`
  uses (generator lines 406-409). Effect, confirmed by reading `cata/among.tex` directly: all
  four generated rules conclude `X_i=t` or `X_i≠t`; none concludes anything about `N`. The
  format already has the machinery to do this correctly (`nvalues` proves it); this is a
  decomposition-authoring mistake in the shipped `among` entry, not a limitation of
  `ind_modifs`/the rule schemas. Recorded here so W2-T1 doesn't mistake it for a format
  requirement, and recorded in `decomps/among.md` so whoever revises `among`'s decomposition
  sees it.
