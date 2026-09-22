# maximum, minimum, arg_max, arg_min, sort, arg_sort

> **RETRACTION, session X-max, 2026-09-22.** The previous version of this file said, of
> `maximum` and `minimum`: *"No decomposition can be authored in the current encoding — this
> is not a derivation gap, it is a missing primitive."* **That claim is wrong, and it was
> wrong when it was written.** `maximum` is authorable in the language exactly as it stands;
> it is now encoded, it generates four rules, and all four are sound and minimal under an
> exhaustive check. `cata/maximum.tex` is the artifact. The three constraints this file
> recorded as G3-blocked for the same reason — `minimum`, `arg_max`, `arg_min` — are all
> reachable too (measured, below). What remains blocked is `sort`/`arg_sort`, and for a
> different gap.
>
> The old claim's error is stated once, plainly, because it is the interesting part: it
> reasoned from **one** decomposition of `maximum` and concluded about **the constraint**.

## maximum — DONE, encoded, measured

### Why the old blocker was not a blocker

The direct decomposition of `maximum(m, x)` is

```
∀i: m ≥ x_i      and      ∃i: m = x_i
```

and both conjuncts do compare two decision variables, which the format cannot type. That much
of the old note was correct. What does not follow is that *no* decomposition can be written,
because that reading is not the only one.

The generator's `BC` literals **already are the order encoding**: a `Global_event (b,X,il,BC)`
means `X_i ≥ t` when `b`, and `X_i < t` when not. Under the order encoding `maximum` is stated
without a single variable-versus-variable atom:

```
m ≥ t   ⇔   ⋁_i (x_i ≥ t)                        (equivalently  m < t  ⇔  ⋀_i x_i < t)
```

Every atom here is *variable against threshold*, which is exactly what `BC` expresses. The
comparison between `m` and `x_i` has not disappeared — it has been **factored through a shared
threshold `t`**, and the order encoding is what performs the factoring. `t` is quantified at
the constraint level, so it is a free parameter of the rule schema, which the format carries
(`OpPoint`, W1-T9) and the printer prints.

### The decomposition

Three atomic constraints, the same three-step channel `gccn` uses to reach a second user
global, with `rule4` (∨) where `gccn` has `rule6` (Boolean sum ≥):

| ctr | schema | meaning |
|---|---|---|
| 1 | `rule1` | `X_i ≥ t ⇔ B1_{i,t}` (BC) |
| 2 | `rule4` | `B2_t ⇔ ⋁_{i ∈ [[1,n]]} B1_{i,t}` |
| 3 | `rule1` | `O ≥ t ⇔ B2_t` (BC) |

Generator value: `maxi`, `explenation generator.ml`; seeds `[xbc; mbc]`, artifact
`cata/maximum.tex`. Constraint 2 is `nvalues`' constraint 2 with a `BC` `B1` instead of an
`AC` one; constraint 3 is `gccn`'s constraint 3 with one value index instead of `(t,p)`.
**Nothing was added to the language**: no constructor, no rule schema, no printer case, no
index operator.

`m` is spelled `O`. `var_name` has no constructor meaning "this constraint's own scalar
bound", so `gcc`'s occurrence letter is borrowed. That is **G2**, a recorded legibility cost,
and it is the *only* gap this decomposition pays.

### Rules generated

Four events asked, four rules emitted, no branch dropped, no empty premise, no index bound
twice:

| # | rule |
|---|---|
| 1 | `∀i'≠i ∈ [[1,n]]: X_{i'} < t`, `O ≥ t`  ⊢  `X_i ≥ t` |
| 2 | `O < t`  ⊢  `X_i < t` |
| 3 | `∃i ∈ [[1,n]]: X_i ≥ t`  ⊢  `O ≥ t` |
| 4 | `∀i ∈ [[1,n]]: X_i < t`  ⊢  `O < t` |

Rule 1 is the useful one and it is the textbook `maximum` explanation: the bound is at least
`t` and every *other* variable is below `t`, so this one carries it.

**Measured** (X-max, 2026-09-22), by exhaustive enumeration of every assignment satisfying
`O = max_i X_i` for every `n, m ∈ {1,2,3,4,5}` — **`n = 1` included**, which is where the
shipped `alldifferent` rule was found to fail (W1-T19):

- **all four SOUND**: 0 counterexamples. Firing counts at `n,m ≤ 4`: 359 / 652 / 1592 / 192.
  At `n,m ≤ 5`: 4173 / 10488 / 23903 / 2296. At `n = 1` alone: 20 / 10 / 20 / 10 firings,
  0 failures.
- **all four MINIMAL**: dropping any premise produces a counterexample.
- cross-checked by a full domain-store sweep at `n,m ∈ {1,2,3}` (277 / 1908 / 4379 / 196
  firing stores, 0 counterexamples). The two instruments agree.

Not from `make validate`: its entry lists are hardcoded and it cannot see a new file (W1-T18).
The numbers above are carried into `cata/maximum.tex`'s `%% CAVEAT` footer.

## minimum — the dual, measured, not shipped

The dual is **not** `m ≤ t ⇔ ⋀_i x_i ≤ t`; that is false (`min_i x_i ≤ t` iff *some* `x_i ≤ t`).
Checked rather than assumed. In the generator's own literal vocabulary, whose positive `BC`
atom is `≥`, the dual is

```
m ≥ t   ⇔   ⋀_i (x_i ≥ t)
```

so `minimum` is `maxi` with **`rule4` replaced by `rule3`** and nothing else changed — one
constructor on one line.

Run in a scratch copy of the generator (X-max, 2026-09-22; **not committed**, because
`cata/minimum.tex` was outside this session's ownership). It emits four rules, the exact
duals:

| # | rule | verdict |
|---|---|---|
| 1 | `O ≥ t` ⊢ `X_i ≥ t` | SOUND, MINIMAL |
| 2 | `∀i'≠i: X_{i'} ≥ t`, `O < t` ⊢ `X_i < t` | SOUND, MINIMAL |
| 3 | `∀i ∈ [[1,n]]: X_i ≥ t` ⊢ `O ≥ t` | SOUND, MINIMAL |
| 4 | `∃i ∈ [[1,n]]: X_i < t` ⊢ `O < t` | SOUND, MINIMAL |

Same instrument as `maximum`: every assignment, every `n,m ∈ {1,2,3,4,5}`, `n = 1` included;
0 counterexamples, every premise needed. Firing counts 37329 / 4158 / 7995 / 18204.

**What `minimum` needs is therefore one line in the decomposition table and one `explainall`
call.** It is `encodable today, not encoded` in `catalog/README.md`'s vocabulary — no gap.

## arg_max, arg_min — also reachable; the remaining question is rule quality, not typing

The old note said `arg_max` "needs everything `maximum`/`minimum` needs (var-var comparison,
same block) plus a second channel from the winning index back to a reported position
variable". The first half is gone. The second half turns out to be **`element`'s existing
clause, verbatim in shape**: `element`'s constraint 4 is a bare three-literal clause
`¬B3_t ∨ ¬B2_i ∨ B1_{i,t}` with index operators `(foralli, i_out)` / `(forallt, t_out)` /
`(id, id)`, and `arg_max` needs the same clause with `B2` = the bound channel and `B4` = the
position channel:

| ctr | schema | meaning |
|---|---|---|
| 1–3 | | exactly `maxi` above |
| 4 | `rule1` | `I = i ⇔ B4_i` (AC) — `element`'s index channel |
| 5 | `rule4` | `¬B2_t ∨ ¬B4_i ∨ B1_{i,t}`, i.e. `(m ≥ t) ∧ (I = i) → x_i ≥ t` |

**Run in scratch** (X-max, 2026-09-22; not committed): it compiles, it runs, and it emits
**14 rules over 6 events**, including the one that matters —
`{I = i, O ≥ t} ⊢ X_i ≥ t`. So `arg_max` is **authorable today**, and `arg_min` is the same
substitution `minimum` is.

**It is not ready to ship, and the reasons are not G3.** From the scratch run's own
diagnostics: `I = i` gets **0 rules** (its single candidate is `F`-blocked — the same shape as
`element`'s `I = i`, which `CLAUDE.md` attributes to **E4**, counting across sums); **11
branches were cut by cycle detection**, each a lost candidate, because the five constraints
form a genuine cycle `B1 → B2 → B1`; and at least two emitted rules **bind `i` twice**
(`{I=i, ∃i: X_i ≥ t} ⊢ X_i ≥ t`), which is **D-0009**, the quantifier-ambiguity defect. None
of that is a typing wall. `arg_max` moves from *"blocked, no shape"* to *"a shape exists, its
output needs work"* — a different and much cheaper problem.

Float variants are **E7**, out of scope, unchanged.

## span — the G3 half is gone; what is left is a second array

`decomps/span.md` withdrew its own E0 claim on the grounds that `S = min_i(start_i)` "compares
two decision variables, which is gap G3". **That withdrawal rested on the claim retracted
above and does not stand.** Under its reconstructed signature, `span` is `S = min_i(start_i)`
and `E = max_i(end_i)` — one `minimum` and one `maximum`, both now demonstrated.

What `span` still needs is **two independent arrays in one decomposition**. `var_name` has one
array letter, `X`; `I`, `V`, `N`, `O` are scalars. If `end_i = start_i + d_i` with parameter
durations the second array is not needed at all — `tplusci`/`tmoinci` already shift a threshold
by a per-index constant and `cumulative` uses them — but if `start` and `end` are independent
variable arrays, that is a **naming gap in `var_name` (G2's stronger form)**, not G3. Not run;
this paragraph is reasoning, and `span`'s signature is still reconstructed rather than sourced.

## sort, arg_sort — unchanged, and now the only genuinely blocked pair here

Nothing above helps these. The permutation half needs `y_j = x_{p_j}`, a **variable-valued
index** into an array, and that does *not* factor through a shared threshold the way `m ≥ x_i`
does: there is no value `t` such that both sides can be stated against `t` independently. That
is the real, irreducible content of the old G3 note, and it is **G8**'s territory, plus **G7**
once per position pair. `CHRISTMAS_LIST.md` keeps these at **E2**. Sketched, not derived.

## Auxiliaries (D-0004)

`maximum` introduces `B1` and `B2`, both ordinary reification auxiliaries of the kind every
shipped decomposition uses, and both resolved back to solver literals by a `Global_devent`
before any printer sees them (no W1-T10 `B` reaches the output). `O` is `maximum`'s own
signature variable under a borrowed letter, not an invented auxiliary — no D-0004 concern.

## What's known-broken

- **`cata/maximum.tex` prints the bound as `O_{} ≥ t`**, with empty subscript braces, because
  `m` has no array position and `printglobal_eventtex` emits the subscript unconditionally.
  Empty braces are a no-op in LaTeX, so the artifact is well-formed; it is noise, it is the
  printer's, and it is G2.
- The borrowed letter itself: a reader of `cata/maximum.tex` sees `O` and has to be told it
  means `m`. Also G2.
- Nothing else. No branch was dropped, no rule has an empty premise, no index is bound twice,
  and no undefined index set is referenced.
