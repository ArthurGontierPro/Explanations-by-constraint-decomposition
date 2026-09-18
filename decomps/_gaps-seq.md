# Format gaps — payload for W2-T1, found specifying §3/§4 (value ordering/precedence/symmetry,
sequencing/sliding)

Each bullet read off `explenation generator.ml` (line numbers given) or `CHRISTMAS_LIST.md`
§3/§4, not from web research. These are new; `docs/DECOMP_FORMAT_NOTES.md`'s G1-G5
(counting-family pilot) are not repeated, only cross-referenced where the same wall is hit
again by a different constraint.

- **G6 — `var_name`'s `B` constructor prints as the literal string `"ERROR B "`, unconditionally,
  in both printers.** `printevent_var`/`printvartex` (generator lines 399 and 427) both have
  `| B i -> "ERROR B "` with no other case. This is silent in exactly the way `CLAUDE.md`
  warns about generically ("expect silence rather than an error") but it is worse than silence:
  it is a plausible-looking LaTeX fragment that reads as a typo, not a dropped branch. It is
  harmless for every existing catalog entry's auxiliaries (`count`, `nvalue`, `among`, `gcc`,
  `increasing`'s `B_1`) **only because those auxiliaries are always defined, in the same
  `Decomp` step, as a direct reification of a `Global_devent`** (`B ⇔ X_i op t`), so the
  printer substitutes them back to `X`/`N`/etc. before ever calling `printvartex` on a bare `B`.
  It is live risk for `value_precede`/`lex_less`'s Shape B chains (`decomps/value_precede.md`,
  `decomps/lex_less.md`): their chained Boolean (`b_i`/`tied_i`) is an **accumulated** fact with
  no single `Global_devent` standing for it, so whether it prints correctly or as `"ERROR B "`
  depends on whether `find`'s AND/OR walk fully unfolds the recursion to an `X`-only base case
  before terminating — not established, not run. This sharpens D-0004 ("auxiliaries leak into
  the explanation") with a concrete, checkable failure mode: for some auxiliaries the failure
  is not stylistic leakage but literally broken output text.

- **G7 — no rule schema sums integer-valued expressions, only Boolean occurrence counts.**
  `rule5`/`rule6`/`rule7` (generator lines ~177-219, per `CLAUDE.md`'s own description) sum
  occurrences of a `Decomp_devent` — cardinality. `sliding_sum`'s `S_i = X_i + S_{i-1}` sums the
  variables' own integer values. This is CHRISTMAS_LIST's E1 line, but sharpened: E1 as written
  ("new integer family") could be read as "extend the existing sum schemas"; it cannot be — the
  existing schemas are structurally about *counting how many Booleans hold*, not *adding up
  values*, so this is a fourth kind of rule schema, not a generalisation of the three that
  exist. See `decomps/sliding_sum.md`.

- **G8 — `var_name` has no constructor for an integer-valued auxiliary at all.** G2 (existing
  notes) already flags that `var_name` can't give a constraint its own named Boolean/count
  variable without borrowing another constructor. `sliding_sum`'s `S_i` sharpens this further:
  it isn't asking for a *named slot*, it's asking for an auxiliary that is **integer-valued**,
  and every existing constructor other than `X` (`B of int | T | I | V | N | O`) is understood,
  by the printers' own case analysis, as Boolean or index-like. There is currently no
  `var_name` case that could carry `S_i` even under a borrowed name.

- **No new gap found for row/matrix indexing (`lex2`, orbitopes, `var_sqr_sym`).** Recorded as
  a checked negative: the `R of int` index family (used by `table`'s decomposition to address
  rows) already covers "a second, row-like dimension" for lex-ordered matrices — see
  `decomps/lex2.md`. Not claiming this as a gap; recording it so nobody re-derives it as one.

- **No new gap found for instance-dependent chain length (`lex_chain_*`, `value_precede_chain`,
  `seq_precede_chain`).** `ind_set`'s `D2 of ind_name list` variant already allows an index set
  given as an explicit list rather than a fixed range, which is what a variable-length chain of
  pairs needs. See `decomps/lex_chain.md`. Recorded as a checked negative for the same reason.
