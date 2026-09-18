# Format gaps — AllDifferent family (§1) and Ordering/sorting/channelling (§9)

Written for W2-T5 (session W2-C), payload for W2-T1 alongside the counting family's
`docs/DECOMP_FORMAT_NOTES.md` (G1-G5, not this session's file to edit). Each bullet read off
`explenation generator.ml`'s type definitions, not from the literature or `CHRISTMAS_LIST.md`'s
own E0-E5 table, which these refine.

- **G6 — `ind_set` can express only whole predefined ranges, never a subrange or an exclusion.**
  `type ind_set = D of int | D2 of ind_name list` (generator line 6). `D of int` denotes one of
  three hardcoded full ranges (`printind_set_int`, line 375: `1 -> [1,n]`, `2 -> [1,m]`,
  `3 -> [1,n]`, else an undefined `D_k`) — a whole named range or nothing. `D2 of ind_name list`
  exists but is unused by any shipped decomposition, and its printer branch
  (`printind_set`, line 376) emits the literal placeholder string `"setfils"`, not a rendered
  set — so it is not a working escape hatch today. **`all_different_except`/
  `all_different_except_0`** need "the value range minus one excepted value" for their Shape
  P1 sum; **`inverse_in_range`** needs an arbitrary contiguous sub-range of `[1,n]` for its
  Shape P3 channel. Both are un-encodable for the same underlying reason.

- **G7 — no schema links two `Global_devent`s directly; every array-to-array channel reinvents
  `element`'s pattern by hand.** `rule1` (generator line 263 area) is fixed to
  `Global_devent ⇔ Reified_devent` — one global variable to one Boolean auxiliary, never
  `Global_devent ⇔ Global_devent`. `element` (lines 692-696) works around this by reifying all
  three of its globals (`X`, `I`, `V`) to separate Booleans and hand-writing the biconditional
  as two `rule4` OR-clauses (the De Morgan expansion). `inverse`/`inverse_in_range`
  (`decomps/inverse.md`) need exactly this same five-`Decomp` detour to link `X` and `Y`, and
  `sort`/`arg_sort` (`decomps/maximum.md`) need it once per adjacent position pair. A direct
  "channel" rule schema (`Global_devent ⇔ Global_devent`, expanding to the same two clauses
  internally) would remove boilerplate that currently has to be re-derived per constraint.

- **G8 — no representation for a variable used as another variable's index.**
  `Global_event`'s index positions (`index = Ind of ind_name*ind_modifs list`, line 20) are
  always `ind_name` (`I`/`T`/`P`/`R` — plain index symbols), never a `var_name`. There is no
  way to write `X_{X_i}` (index into `X` by the *value* of another occurrence of `X`).
  `symmetric_all_different` (`decomps/all_different.md`) needs this for its self-inverse half
  `x[x_i] = i`; `sort` (`decomps/maximum.md`) needs it for its permutation channel
  `y_j = x_{p_j}`. This is distinct from **G3** (`docs/DECOMP_FORMAT_NOTES.md`, var-vs-var
  *comparison*) — G8 is about a variable appearing in *index position*, not as a comparison
  target, and blocks the decomposition before any comparison is even reached.

- **G3 reinforced (not new — already in `docs/DECOMP_FORMAT_NOTES.md`), with two more
  constraints pinned to it.** `maximum`, `minimum` need `X_i ≥ M` for two decision variables;
  `arg_max`, `arg_min` need the same thing before their second (index-reporting) half is even
  reachable. Recorded here only because this family hits the identical wall twice independently
  of the counting family's `count`/`among` — evidence this is a load-bearing gap for the
  project overall, not a one-off from one family's authoring choices.

## `CHRISTMAS_LIST.md` claims this session's reading complicates (report, not fix)

- §9's `element` row says "already in `cata/element.tex`, 6 rules" with no caveat. Per the task
  brief (measured, not by this session) only 2 of those 6 survive `removeimp`'s silent
  discard — the row is accurate about what was generated but silent about validated status,
  the same silence `CLAUDE.md`'s "Reality check" table warns every `cata/*.tex` entry carries
  until the validator says otherwise. Not a contradiction, but worth flagging since a reader
  skimming §9 alone (as this session was scoped to) would take "6 rules" as a size claim, not a
  soundness one.
