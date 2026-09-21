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
  **2026-09-21, corrected within the day — G2 is a legibility cost, NOT a hard stop.** The first
  reading was that a second *user array* must be taken as `B 1`, which makes `printvartex`
  **raise** (l.517, W1-T10), and that reading was published here for about twenty minutes. R6
  re-measured and retracted it: **`var_name`'s `O` is a perfectly good second array** — l.522
  renders it `"O" ^ printglobal_eventtex v`, the same indexed-global path `X` uses, and `gccn`
  already carries `O` as a real user global (l.829). So a two-array channel (`inverse`, `sort`,
  the `write` family) **is writable today**, with one array wearing `gcc`'s letter. The cost is
  exactly what G2 always said: the explanation names `O` where the reader wrote something else.
  **`decomps/write.md`'s G2 paragraph is wrong in both directions** — a second array as `B 1`
  does not "print as a Boolean auxiliary", it raises; and `O`, which that paragraph never
  mentions, prints fine.
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
  else (generator l.355, 369, 383 — re-measured 2026-09-21; this cited 177-219, from before W1-T3/T7 grew the file). None of the six pilot specs need more than one summed family,
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

---

# Consolidated gap list, wave two (2026-09-18)

G1–G5 above come from the counting-family pilot. Three sessions then specified six more
families into their own `decomps/_gaps-{seq,perm,ext}.md`, each numbering from G6 in its own
file. **This section is the reconciled numbering and supersedes those three files' numbers**
(their prose stays where it is; only the labels move). Every gap names the constraint that hit
it. Nothing here was measured by running code — all of it is read off `explenation
generator.ml`, with line numbers, or off `docs/VALIDATOR.md`'s measurements.

| # | gap | hit by | was |
|---|---|---|---|
| G6 | **2-D constant table read as a function**, `t = T[r,i]`. `Addcst` is 1-D | `table` | ext X1 |
| G7 | **value set indexed by another index**, `t' ∈ D(t)`. `ind_set`'s `D2 of ind_name list` is the right hook and no decomposition uses it | `regular`, `mdd` | ext X2 |
| G8 | **`ind_set` names only whole predefined ranges** — no subrange, no exclusion | `all_different_except*`, `inverse_in_range` | perm G6 |
| G9 | **no `Global ⇔ Global` channel schema**; `rule1` is fixed to `Global ⇔ Reified`, so every array-to-array channel re-derives `element`'s five-`Decomp` detour | `inverse`, `sort`, `arg_sort` | perm G7 |
| G10 | **no variable in index position**, `X_{X_i}` | `symmetric_all_different`, `sort` | perm G8 |
| G11 | **no weighted Boolean sum** — `rule5/6/7` count occurrences, with no coefficients | `cumulative`, `knapsack` | ext X5 |
| G12 | **no schema sums integer *values*** rather than counting Booleans. This is a fourth kind of schema, not a generalisation of the three | `sliding_sum` | seq G7 |
| G13 | **`var_name` has no integer-valued auxiliary** — every constructor but `X` is read as Boolean or index-like | `sliding_sum` | seq G8 |
| G14 | **no summation over a variable-determined index set** | `cumulatives` | ext X6 |
| G15 | **no arithmetic relating variable values to indices** — this is the measured `UNPARSED: t'=t-d_i` | `cumulative` (variable durations), `cost_regular` | ext X9 |
| G16 | **`ind_fam` is a closed 4-element enum** and §5/§6 exhaust it; `EXT-2b` alone needs `i, t, q, q'` | `regular` general form | ext X7 |
| G17 | **no pivot-elimination pass**, so an auxiliary cannot be removed from a finished rule. This is *why* D-0004 currently costs coverage rather than only rule length | every shape with a genuine auxiliary | ext X8 |
| G18 | **quantification over an index set with a variable-determined exclusion**, `∀j ≠ I` for `I` a decision variable. G8 covers a *constant* exclusion and G14 a variable-determined *summation* extent; neither covers a universally quantified channel with a variable-determined hole | `write`, `writes`, `writes_seq` | new, §11 (W3-D) |

**G3 (variable-vs-variable comparison) is reinforced, not duplicated.** Two families hit it
independently of the counting pilot: `maximum`/`minimum`/`arg_max`/`arg_min` (perm) and
`lex_less` (seq). Three independent families make it load-bearing.

## Checked negatives — recorded so nobody re-derives them as gaps

- **Row/matrix indexing is NOT a gap.** The `R of int` index family, already used by `table`,
  covers a second row-like dimension for `lex2`, the orbitopes and `var_sqr_sym`. (W2-A)
- **Instance-dependent chain length IS a gap after all — this one was reconciled, not accepted.**
  W2-A recorded `D2 of ind_name list` as a working escape hatch for variable-length chains
  (`lex_chain_*`, `value_precede_chain`, `seq_precede_chain`) and therefore as a checked
  negative. W2-C and W2-B, working separately, both found that **`D2`'s printer emits the
  literal string `"setfils"`** — `printind_set`, generator l.375, confirmed by the orchestrator.
  **Updated 2026-09-21: it no longer prints that string, it RAISES** (W1-T2 added the backstop,
  generator l.463–464). The gap is unchanged — `D2` still has no real printer — but a session
  quoting `"setfils"` today is quoting a state that no longer exists.
  So `D2` exists in the type, is used by nothing, and would print garbage into the `.tex` if
  used. It is the right hook for G7, and it is not usable until it has a printer. **W2-A's
  checked negative is withdrawn; treat variable-length chains as blocked on the same missing
  printer as G7.**

## Two things the freeze must settle that are not gaps

1. **The E-code taxonomy collides with itself.** D-0006 defines **E3** as *multi-family
   cardinality* (the `failwith "sommes multiples"` site); `CHRISTMAS_LIST.md` §6 uses **E3** for
   *weighted sums* (G11). These are different extensions and the code is load-bearing in both
   documents. The author should pick one meaning and the other gap should get a new code.
2. **`B` prints as the literal `"ERROR B "`** (generator l.399, l.428) — a bug, not a format
   gap, so it is roadmap **W1-T10** rather than a `G` number. It is listed here only because any
   shape with an accumulated-state auxiliary (`value_precede`, `lex_less`) meets it immediately.

## Wave three addendum — §11 (W3-D, 2026-09-18)

`CHRISTMAS_LIST.md` §11 ("maths and misc") was the last in-scope family. It added **one** gap,
**G18** above, from `write`/`writes`/`writes_seq`. Everything else in §11 landed on gaps the
first ten sections had already produced, which is itself the useful result — the gap list
converged before the corpus ran out:

- `sum_pred` — G11 (weights), G12 + G13 (integer-valued summands), and G14 under the reading in
  which a variable selects the summed index set. Nothing new.
- `edit_distance` — G16 (`ind_fam` exhausted, here by *two position families* rather than by two
  automaton-state families, which is independent evidence for G16), G12 + G13, G17, and G3
  *avoided* via the two reification grids. Nothing new.
- `piecewise_linear*`, `neural_net` — E7, declared out of scope; no gap recorded.
- the `*_fn` variants — not separate constraints; no gap recorded.

Nothing above was measured by this session; all of it is read off `explenation generator.ml`
and `CHRISTMAS_LIST.md` §11.
