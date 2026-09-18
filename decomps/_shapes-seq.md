# Shapes — value ordering / precedence / symmetry (§3) and sequencing / sliding (§4)

One file per **distinct decomposition shape** used by the constraints in these two
`CHRISTMAS_LIST.md` sections. Per-constraint files say only which shape they instantiate and
what differs. Read off `explenation generator.ml` (line numbers given) and the two sections
of `CHRISTMAS_LIST.md`; nothing here was run.

## Shape A — Threshold chain (already built: `increasing`/`decreasing`)

`explenation generator.ml:688-691`:

```
let incr = [Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
            Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true, (B 1), imoin 1, iplus 1)])]
```

- `B_i ⇔ X_i ≥ t` (`rule1`, BC) — the reified literal **is** the thing being explained; it is
  not a separate invented fact about the array.
- `¬B_i ∨ B_{i-1}` shifted to conclude `B_i` at `i` from `B_i` at `i-1` (`rule4`), a **fixed
  local shift by 1** (`imoin 1`/`iplus 1`), no unbounded quantifier.

Key property: **zero genuine auxiliaries.** `B_1` washes out completely because it is defined,
in the same `Decomp`, as nothing more than `X_i ≥ t` — the printer substitutes it back to the
`Global_devent` before emitting anything, which is why `cata/increasing.tex` prints
`X_{i'} \geq t` and never `B_1`. E0, already generated (unvalidated).

## Shape B — Boolean state chain with a genuine auxiliary (`value_precede`, `lex_less`/`lex_lesseq`)

Same mechanical skeleton as Shape A — `rule1`/`rule3`/`rule4`, a fixed local shift by 1 — but
the chained Boolean is **not** itself a reification of any single `X_i op t`. It is an
accumulated fact ("has `s` occurred in the prefix", "is the prefix still tied") that only a
recursive definition captures:

- `value_precede`: `b_i ⇔ b_{i-1} ∨ (X_{i-1} = s)` (`rule4`, `id`/`imoin 1`).
- `lex_less`/`lex_lesseq`: `b_i ⇔ b_{i-1} ∧ (X_i = Y_i)` (`rule3`), plus a per-position
  disjunction `X_i < Y_i ∨ (b_i ∧ X_i ≤ Y_i)` for the final comparator.

Two things distinguish this from Shape A and matter for the conclusions drawn in
`decomps/value_precede.md` and `decomps/lex_less.md`:

1. **`X_i = Y_i` is a variable-vs-variable comparison** — `DECOMP_FORMAT_NOTES.md`'s **G3**
   (only `X_i = t` against a domain value exists today). Already recorded there; not repeated
   as new here.
2. **The chained Boolean is a real auxiliary, and `var_name`'s `B` constructor prints as the
   literal string `"ERROR B "` whenever it survives to the output** (`printevent_var`/
   `printvartex`, generator lines 399 and 427: `| B i -> "ERROR B "` in *both* the plain-text
   and the LaTeX printer, unconditionally). Shape A never hits this because its `B` always
   resolves back to a `Global_devent` in the same step. Shape B's `b_i` has no `Global_event`
   standing for it — there is nothing to resolve back to — so whether it prints as `"ERROR B "`
   or as a real premise depends on whether the AND/OR walk (`find`) manages to unfold the
   recursion down to `X`-events before it terminates, and per `CLAUDE.md`'s own traps section,
   cycle-cut branches (`R`) and dead ends (`IM`) are exactly the kind of thing this walk hits on
   recursive definitions. This is new: see `_gaps-seq.md`.

E0 per `CHRISTMAS_LIST.md` (both existing native propagators), but "same shape as `increasing`"
undersells the difference: `increasing` needs no auxiliary at all; Shape B always needs one,
and D-0004 says an auxiliary "leaks into the explanation" — here it may print as `"ERROR B "`
instead.

## Shape C — Boolean-sum cardinality (reused from the counting-family pilot)

`rule1` channel + `rule5`/`rule6`/`rule7` (Boolean sum vs. threshold), exactly as documented in
`decomps/at_least.md` and `decomps/among.md`. Tentatively reused for `alternative` (see that
file for the hedge on its semantics). E0, nothing new needed.

## Shape D — Min/max-over-index-set (reused from `range`/`roots`, already in the generator)

`explenation generator.ml`'s `range`/`roots` decompositions use `rule6` (a bound holding for
every index) plus `rule7` (achieved with equality for at least one index) over an index set
`D_k`. `span` reuses this shape: the spanning bound is a `rule6`-style "for all subtasks" bound
in each direction, tight (`rule7`-style) for at least one subtask. No new schema. Inherits the
already-known printer trap (`D_k` for `k>3` is unhandled by the printer — a `CLAUDE.md` trap,
not new).

## Shape E — Prefix-sum sliding window (`sliding_sum`) — does not reduce to A–D

Integer (not Boolean) running sum `S_i = X_i + S_{i-1}` and a window test
`S_{i+w} - S_i` against `[lo,hi]`. Needs a rule schema that sums **integer-valued** literals,
which does not exist (`rule5`/`rule6`/`rule7` are hard-coded to sum `Decomp_devent` occurrences
of a single Boolean family — see `DECOMP_FORMAT_NOTES.md`'s G4, which is about combining
*multiple* Boolean sums, a narrower problem than "no integer sum exists at all"). Full spec in
`decomps/sliding_sum.md`; this is CHRISTMAS_LIST's own E1+E2 line, confirmed by reading the
generator rather than only trusting the list entry.
