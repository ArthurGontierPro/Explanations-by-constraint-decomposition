# Shapes — AllDifferent family (§1) and Ordering/sorting/channelling (§9)

Written for W2-T5 (session W2-C). Four distinct shapes cover every in-scope constraint in
these two `CHRISTMAS_LIST.md` sections. Per-constraint files in this directory say only which
shape applies and what differs; the derivation lives here once.

---

## Shape P1 — pairwise-sum guard

The `alldifferent` shape (generator lines 678-679, `cata/alldifferent.tex`).

- `B_{i,t} ⇔ X_i = t`, `i ∈ [1,n]`, `t ∈ [1,m]` (rule1, AC).
- `∑_{i∈[1,n]} B_{i,t} ≤ 1`, for each `t` (rule5, Boolean sum ≤, single `Decomp_devent`, no
  `Reified_devent` — the same "implicit constant, never printed" shape `at_least.md` flags as
  G1).

One rule: `X_i ≠ t ← ∃i'≠i: X_i' = t`. **This is correct and minimal as shipped** — the second
rule an earlier `CLAUDE.md` draft wanted (concluding `X_i = t`) is not derivable from a ≤
direction; it needs Hall-set reasoning across sums, which is E4, not this shape. Do not
re-report it as a bug (task fact, confirmed by task brief, not independently re-derived here).

**Instances:** `all_different` (pure). `all_different_except`, `all_different_except_0`
(guarded: the sum ranges over `t ∈ [1,m]\{v_0}` instead of `t ∈ [1,m]`) — blocked by **gap
G6** below, since `ind_set` cannot express a range minus one value. `symmetric_all_different`'s
`alldifferent(x)` half (pure).

---

## Shape P2 — monotone adjacent chain

The `increasing`/`decreasing` shape (generator lines 688-691, validated 2/2 each per task
brief).

- `B_i ⇔ X_i ≥ t`, `i ∈ [1,n]` (rule1, BC).
- `¬B_i ∨ B_{i-1}` reshaped as one `rule4` OR-clause: `Decomp_devent (false, B1, id, id)` paired
  with `Decomp_devent (true, B1, imoin 1, iplus 1)` — i.e. "`X_i < t` or `X_{i-1} ≥ t`",
  contrapositive of `X_{i-1} ≥ t → X_i ≥ t`.

`decreasing` is the same clause with the two `Decomp_devent` signs swapped (lines 690-691) —
literally dual, matching `CHRISTMAS_LIST.md`'s own note ("cleanly dual").

**Instances:** `increasing`, `decreasing` (pure, already in the generator). `strictly_increasing`,
`strictly_decreasing` (same shape, threshold shifted by one step — either an extra `Addint`
index shift or a BC→AC consistency change on the same events; no new schema needed, E0).

---

## Shape P3 — three-way channel via cross-variable OR-clauses

The `element` shape (generator lines 692-696). This is the shape every channelling constraint
in §9 actually needs, because `rule1` only links **one** `Global_devent` to **one**
`Reified_devent` (a Boolean aux) — there is no schema for `Global_devent ⇔ Global_devent`
directly (see gap **G7**). `element` works around this by reifying *each* global variable to
its own Boolean and then writing the biconditional as two `rule4` (OR) clauses, the De Morgan
expansion of `(B2∧B3) → B1` and its converse:

- `B1_{i,t} ⇔ X_i = t` (rule1, AC).
- `B2_i ⇔ I = i` (rule1, AC).
- `B3_t ⇔ V = t` (rule1, AC).
- `¬B3 ∨ ¬B2 ∨ B1` and `B3 ∨ ¬B2 ∨ ¬B1` (two `rule4` clauses, generator lines 695-696) —
  together, `(I=i ∧ V=t) ⇔ X_i=t`.

**Known defect (not this session's to fix):** per task brief, 4 of `element`'s 6 generated
rules are lost to unsatisfiable premises reading `∀t: V=t` / `∀i: I=i`. Reading the shape:
`I` and `V` are scalars (one instance each, no array index), so the `B2`/`B3` literals should
need **no** quantifier at all when explaining a fixed query pair `(i,t)` — the `foralli`/
`forallt` operators attached to their `Decomp_devent`s (lines 695-696) are quantifying a
single-valued fact as if it ranged over the whole domain. **What the decomposition should have
used**: `Decomp_devent (false, B2, id, i_out)` / `(false, B3, id, t_out)` with no
`EXFORALL`/`EXEXISTS` wrapper at all — the plain point-substitution `id`/`i_out`/`t_out` already
used for `B1` — rather than composing a universal quantifier onto a scalar. This is an
index-operator authoring bug in the shipped decomposition, matching the same family of bug
`nvalue.md` reports for `nvalues`' repeated binders, not a limitation of the shape itself.

**Instances:** `element` (shipped, defective as above). `inverse`, `inverse_in_range`: same
three-reification-plus-two-clause shape, with `Y` in place of the constant-valued `I`/`V` slots
— `B1_{i,j} ⇔ X_i=j`, `B2_{j,i} ⇔ Y_j=i`, then the two `rule4` clauses `¬B1∨B2` and `¬B2∨B1`
express the biconditional directly (no third variable needed, since both sides are already
array-indexed). `inverse_in_range` differs only in index set (a sub-range of `[1,n]` rather
than all of it — same G6-style exclusion/subrange gap as `all_different_except`, but on the
*domain* of the channel rather than the value set). `sort`, `arg_sort`: compose this shape
once per pair of adjacent output positions, chained through auxiliary permutation booleans —
sketched, not fully derived, because it additionally needs Shape P1-style all-different
reasoning over the permutation and hits gap G7 twice (once per `element`-style channel, once
for the permutation channel to the original array).

**Not this shape — blocked entirely by gap G3 (already recorded in
`docs/DECOMP_FORMAT_NOTES.md`):** `maximum`, `minimum`, `arg_max`, `arg_min`. All four need
`X_i` compared to `X_j` (`X_i ≥ X_j` for all `j`, or `X_i ≥ M` for variable `M`), i.e.
variable-vs-variable, not variable-vs-domain-value. `Global_event`/`ind_modifs` cannot express
this at all (confirmed by reading the type: `Global_event`'s comparison target is always an
`ind_name`-derived index, never a second `var_name`). No decomposition can be authored in the
current encoding; `CHRISTMAS_LIST.md` already marks this E2, and this family hits it twice
independently (`maximum`/`minimum` natively, `arg_max`/`arg_min` on top of it), which is
evidence the gap is not a one-off.

---

## Shape P4 — existential disjunction over one array against a fixed target

- `B_i ⇔ X_i = y` for `i ∈ [1,n]`, `y` a parameter (rule1, AC).
- `∃i: B_i` (rule4, single existential clause — the same shape `nvalue.md` step 2 uses for
  `B2_t ⇔ ∃i: B1_{i,t}`, but with the target fixed rather than ranging over `t`).

**Instances:** `member` (pure — `exists(i)(x[i]=y)`, per `CHRISTMAS_LIST.md`).

---

## Out of scope in these two families (one line each, no spec)

- `all_disjoint` — set variables, **E5**.
- `int_set_channel`, `link_set_to_booleans` — set variables, **E5**; `link_set_to_booleans` is
  itself the mechanism E5 would need.
- `arg_max`/`arg_min` float variants — **E7**, on top of already being blocked by G3 for the
  int case.
