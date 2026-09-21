# disjunctive

**Signature.** `disjunctive(array[int] of var int: s, array[int] of var int: d)` — tasks with
starts `s_i` and durations `d_i` do not overlap. In the version this spec covers, `d_i` is a
constant.

**Shape: `SCH-1`** (`_shapes-ext.md`). **This is the shape the generator already runs**: the
entry named `cumul` at `explenation generator.ml` l.810–812, emitted to `cata/cumulative.tex`,
is `rule5` with an implicit bound of 1 over the per-time-point overlap Booleans — a **unary**
resource, i.e. `disjunctive`. `CHRISTMAS_LIST.md` §6 says the same ("the repo's entry is the
unary-resource special case"), and the file name is the only thing that says `cumulative`.

**What differs from the shape: nothing.** Full maths, literals (`X_i ≥ t`, **BC** — the one
bounds decomposition in either of this session's sections), the `rule1` / `rule3` / `rule5`
schema chain and the D-0004 wash-out argument are in `_shapes-ext.md`.

**E-code: E0 for constant durations.** The schemas exist and run. For `fzn_disjunctive`'s
general form with variable durations — `d_i = 0 ∨ d_j = 0 ∨ s_i + d_i ≤ s_j ∨ s_j + d_j ≤ s_i`,
which `CHRISTMAS_LIST.md` §6 prices **E2** — the atoms become variable-vs-variable and it is gap
**G3** / **X9**.

**Auxiliaries.** `B1_{i,t} ⇔ X_i ≥ t` and `B2_{i,t}` = "task `i` runs at `t`". Both wash out:
`cata/cumulative.tex` (read off the output) prints only `X_i ≥ t` and `X_i < t` literals plus
index equations. D-0004 satisfied without argument.

**Status: generated, unvalidated — and in fact not checkable.** `docs/VALIDATOR.md` l.330
**measures** the failure mechanically: the parser reports
`UNPARSED: index equation offset: t'=t-d_{i}`, because the durations are `ind_const` symbols the
validator cannot interpret, and the capacity appears in no atom. So the one §6 entry that ships
has no measurement at all, in either direction.

**Weakness of the derived rules, read off the output (gap X10).** Both rules explain by
`∀i', i' ≠ i, i' ∈ [1,n]` — every other task. The published explanation (Schutt, Feydy, Stuckey &
Wallace 2011; unary is the special case of the cumulative papers) names a small time window and a
task subset. `rule5` reasons within one sum; the window argument reasons across time points.
That is D-0006's **E4**, which D-0006 itself calls the research.
