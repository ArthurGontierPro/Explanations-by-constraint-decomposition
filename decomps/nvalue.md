# nvalue

> Shape reference: **`decomps/_shapes.md`** (W3-D, 2026-09-18) is the single cross-family
> shape list. The shape derived in this file is **S3** there, shared with constraints from
> other families.

**Signature.** `nvalue(var int: n, array[int] of var int: x)` — `n` = the number of distinct
values taken by `x`.

**Decomposition (maths) — already in the generator as `nvalues`, lines 406-409, generated
(unvalidated) as `cata/nvalues.tex`.** Recorded here per task scope, plus the known bug.

- `B1_{i,t} ⇔ X_i = t`, for `i ∈ [1,n_x]`, `t ∈ [1,m]` (`m` = domain size) — full grid.
- `B2_t ⇔ ∃i: B1_{i,t}` — "value `t` is used by some `x_i`".
- `N ⇔ B4_p` (channel, `p ∈ [1,n_x]`) — same shape as `count`'s count-channel and `gccn`'s `O`
  channel (generator line 396).
- `∑_{t∈[1,m]} B2_t = p ⇔ B4_p`.

**Rule schemas.**
1. `B1_{i,t} ⇔ X_i = t` → `rule1`, AC, index set `(i,t) ∈ [1,n_x]×[1,m]`.
2. `B2_t ⇔ ∃i: B1_{i,t}` → `rule4`, index `i ∈ [1,n_x]` (existential).
3. `N ⇔ B4_p` → `rule1`, AC, index `p ∈ [1,n_x]`.
4. `∑ B2_t = p ⇔ B4_p` → `rule7`, sum over `t ∈ [1,m]`, matched against the `p`-channel from
   step 3.

**Index sets and relations.** Three nested indices: `i` (positions), `t` (values), `p`
(possible counts, itself ranging over the same set as `i` since at most `n_x` distinct values
are possible). `count`'s spec above reuses exactly this `p`-channel shape but drops the
per-value existential (step 2), since `count` targets one fixed value, not "any value".

**E-code: E0** (`CHRISTMAS_LIST.md:127`: "already in `cata/nvalues.tex`, but the generated
rule repeats binders (`∀i` twice); fix is index hygiene, not an extension").

**Auxiliaries.** `B1_{i,t}`, `B2_t`, `B4_p` — all reification scaffolding, non-leaking under
D-0004: `cata/nvalues.tex` prints only `X` and `N` literals, confirming the wash-out (read off
the file directly, not inferred).

**Known defect (not this session's to fix, `explenation generator.ml` is W1-S's file).**
`cata/nvalues.tex`'s third and fourth `\frac{...}` rules each bind `∀i,~i ∈ [1,n]` **twice** in
the same premise (visible directly in the file: `...,~\forall i,~i \in [1,n]...,~\forall
t,~...,~\forall i,~i \in [1,n]`). Read off the generated text, not inferred from the source —
consistent with `CHRISTMAS_LIST.md`'s own note and with `CLAUDE.md`'s warning that
`printind_name_list`/`printiopl_list` silently truncate index lists (an index-composition bug,
not a soundness argument either way — the validator has not checked `nvalues`).
