# among

> Shape reference: **`decomps/_shapes.md`** (W3-D, 2026-09-18) is the single cross-family
> shape list. The shape derived in this file is **S3** there, shared with constraints from
> other families.

**Signature.** `among(var int: n, array[int] of var int: x, set of int: s)` — `n` = the number
of `i` such that `x_i ∈ s`. `s` a parameter set (per D-0003); `n` a decision variable.

**Decomposition (maths) — already in the generator, `among` at generator lines 418-420, and
already generated (unvalidated) as `cata/among.tex`.** Recorded here as the worked style
example the task brief points to, plus one finding.

- `B1_{i,t} ⇔ X_i = t`, for `i ∈ [1,n_x]`, `t` ranging over the value domain — the shared
  per-`(i,t)` channelling grid used by `nvalue`/`gcc` too.
- `B2_i ⇔ ∃t ∈ s: B1_{i,t}` — "`x_i` takes a value in `s`".
- `∑_{i∈[1,n_x]} B2_i` compared against `n`.

**Rule schemas.**
1. `B1_{i,t} ⇔ X_i = t` → `rule1`, AC.
2. `B2_i ⇔ ∃t ∈ s: B1_{i,t}` → `rule4` (disjunction), index set `t ∈ s` (`D 4` in the
   generator's index-set enumeration).
3. `∑ B2_i` vs `n` → `rule7`, but — see finding below — coded in the generator as a single
   `Decomp_devent` with no `Reified_devent` (generator line 420:
   `Decomp (3, rule7, [Decomp_devent (true, (B 2), id, oni)])`), the same "implicit constant"
   shape as `at_least`/`at_most`/`exactly`, **not** the two-step `N`-channel shape `nvalues`
   uses for its own count variable (generator lines 406-409).

**Index sets and relations.** `i ∈ [1,n_x]`; `t ∈ s` (a strict subset of the full value domain,
`D 4`); the `rule7` sum ranges again over `i ∈ [1,n_x]`.

**E-code: E0** (`CHRISTMAS_LIST.md:126`: "already in `cata/among.tex`"). All three schemas
pre-exist and are already wired up.

**Auxiliaries.** `B1_{i,t}`, `B2_i` are reification scaffolding, non-leaking under D-0004 by
the same washing-out mechanism as `count`/`nvalue`.

**Finding, not a format gap — a decomposition bug in the shipped entry.** Because step 3 uses
the single-`Decomp_devent` form, `reified_devent` defaults to the placeholder `T` (generator
line 111), so `rule7`'s branch that would conclude something about `n` never fires — the
`dname re = dname de` test is always false for the placeholder. Checked against the actual
output: `cata/among.tex` contains four `\frac{...}` rules and every one concludes `X_i=t` or
`X_i \neq t`; none concludes anything about `N`/`n`. So the shipped `among` explains its own
literals but never explains its own count variable — `among` cannot currently be asked "why is
n at least/at most k?" The fix is `nvalues`' pattern (an explicit `N`-channel `rule1` step
before the `rule7`), not an engine change; flagging per instructions rather than fixing (this
file is read-only to this session).
