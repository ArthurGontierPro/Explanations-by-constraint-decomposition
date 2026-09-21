# `all_equal`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `all_equal`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — no literature + solver decomposes (`tools/mzn_coverage.py --rank`, ecodes `E0`) |
| **Status** | `validated: sound and minimal at n,m <= 4` |
| **Generated** | 2 rules in `cata/allequal.tex` |
| **Validator** | 2 `SOUND and MINIMAL`, 0 flagged |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:121` records "none" |
| **Last measured** | 2026-09-21, `make validate` (E2's own run) and `python3 tools/mzn_coverage.py --rank --json` |

**Read the "Generated rules" section before quoting the `2 SOUND and MINIMAL` above.** Both
rules have the conclusion as their premise. Under one of the two readings the `.tex` admits,
they are tautologies and infer nothing; under the other they are the intended dichotomy rule.
The validator passes them because *both* readings are sound, which is a different thing from
their being useful. This entry is the catalog's sharpest instance of "sound and minimal is a
floor, not strength" — sharper than `alldifferent`'s, because there the rule is dead and here
it is alive and empty.

## Constraint

`all_equal(array [$X] of var int: x)`

Every `x[i]` takes the same value.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:21` carries the *name* only. The signature is recall;
`decomps/all_equal.md` states the same one and is likewise not a vendored source.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:121` reads
`| all_equal | none | decomp | **E0** — added 2026-09-18, W3-C. …`

**Rule shape:** nothing to source; `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only.

**Two stale claims in that row, flagged not fixed** (the row is not this session's file):

1. It says "No `decomps/all_equal.md` exists to cite for the shape". **It exists** — added by
   W3-D, and it is what this entry's Decomposition section cites.
2. It describes the `.tex` as showing "a two-way existential/universal pattern over
   `X_i ≥ t`/`X_i < t`". That was true of the four-rule artifact; **the universal half is
   gone** (commit `790bfa7`, below), and what ships is existential only.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:121`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.

## Decomposition used here

**Generator value:** `alleq`, `explenation generator.ml:804-807`
**Emitted by:** `explainall [xbc] alleq "cata/allequal.tex"`, line 879
**Spec:** `decomps/all_equal.md` (shape **S4** in `decomps/_shapes.md`, instantiated twice
with dual signs and closed by one unquantified clause). **That file cites "l.674–677", which
no longer resolves** — the value is at 804-807. Its measured line ("4 rules; 2 SOUND and
MINIMAL / 2 UNSOUND") is also stale; see below.

```ocaml
let alleq = [Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
             Decomp (2, rule3, [Decomp_devent (true,  (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
             Decomp (2, rule3, [Decomp_devent (false, (B 1), id, oni); Reified_devent (true, (B 3), id, i_out)]);
             Decomp (4, rule4, [Decomp_devent (true,  (B 2), id, id); Decomp_devent (true, (B 3), id, id)])]
```

A **bounds dichotomy**: at every threshold `t`, the array is entirely above it or entirely
below it.

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i ≥ t`, **BC**. A bound is reified, not an equality —
  the same choice `increasing` and `disjunctive` make, and the opposite of `alldifferent`'s.
- **step 2, `rule3`** — `B2_t ⇔ ⋀_{i∈[1,n]} B1_{i,t}` (all above).
- **step 3, `rule3`** — `B3_t ⇔ ⋀_{i∈[1,n]} ¬B1_{i,t}` (all below), the same step with the
  summand sign flipped.
- **step 4, `rule4`** — `B2_t ∨ B3_t`, two literals, **no index family attached**.

`B1`, `B2`, `B3` all wash out; only `X` literals print (D-0004), confirmed by reading the
`.tex`.

### `all_equal` is the constraint that exposed the `EXOR`/`EXAND` defect

**Two of this entry's four rules were removed, and that is the most substantive thing the
entry records.** Commit `790bfa7` (2026-09-18, W1-T9 defect 1); the reasoning is preserved in
the generator itself at `explenation generator.ml:266-296`, which is the in-repo source for
everything in this subsection.

For a reified conjunction `R ⇔ ⋀_j L_j`, concluding that one conjunct `L_k` is **false** needs
**both** `¬R` and every other conjunct `L_{j≠k}`: from `¬R` alone nothing follows about `L_k`,
and from the siblings alone nothing follows either. `rule3` and `rule4` built that pair with
`EXOR` when `del` is a single indexed family, so **each half shipped as a rule in its own
right, without the other**. The half carrying only the sibling literals was `allequal`'s old
rule 2:

```
X_{i'} < t ,  ∀i' ≠ i
---------------------- ⊢   (REMOVED — UNSOUND)
X_{i} ≥ t
```

which is backwards: under `all_equal`, every other variable being below `t` puts `X_i` below
`t` too. **Counterexample, measured by the validator at W1-T8: `n = m = 2, X = (1,1), t = 2`.**

The multi-conjunct branch two lines down already used `EXAND`, and so do `rule5/6/7` in the
same situation, so the singleton case was disagreeing with every sibling rather than stating a
deliberate reading. With `EXAND`, a branch whose `¬R` half has no explanation now dies as a
whole and is *counted* by `filter_branches` (W1-T3) instead of shipping as half a rule — which
is exactly what happens here, because `¬B2`/`¬B3` are not derivable from `B2 ∨ B3`. The
generator's own comment puts the conclusion plainly at line 291: **"`allequal` honestly has no
non-trivial rule under this decomposition."**

Catalog-wide effect of that one repair, as recorded at `explenation generator.ml:283-288`:
42 rules → 35, every disappearing rule one the validator had flagged, no `SOUND and MINIMAL`
rule lost. `atleastnvalues`, `atmostnvalues` and `nvalues` each lost one `UNSOUND` rule;
`table` lost two of three.

**That figure is 35 and my own run reports 34** — the difference is not unexplained. Three
commits touch the generator or `cata/` after `790bfa7` (`git log 790bfa7..HEAD -- cata/
'explenation generator.ml'`), and `576c718` (W1-T2, refuse an undefined index set) took
`table` from its last remaining rule to none. 35 − 1 = 34. Quote the run, not the comment.

## Scope of this entry

**Events the generator was asked to explain:** two, both from `xbc`
(`Global_event (true, X, [Ind (I 1,[]); Ind (T 1,[])], BC)`, `explenation generator.ml:868`) —
`X_i ≥ t` and `X_i < t`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i}<t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |

**The `F` drop on each event is the removed rule.** Before `790bfa7` each event yielded 2
rules; now the second branch reaches a blocking `F` leaf (`¬B2`/`¬B3` have no explanation) and
is counted rather than shipped. No `IM`, no `FE`, no cycle cut, no undefined index set.

No equality event was asked and none is answerable: the decomposition reifies a bound, so
`X_i = t` has no reified counterpart to descend into. Getting an equality rule here would need
the `≥`/`<` pair to be combined across two thresholds, which is not something any of the seven
schemas does.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/allequal.tex`.

## Generated rules

Rendered from `cata/allequal.tex` (`grep -o '\\frac' cata/allequal.tex | wc -l` → 2).

### Rule 1 — `X_i ≥ t`

```
X_{i} ≥ t ,  ∃i ,  i ∈ [1,n]
----------------------------- ⊢
X_{i} ≥ t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `2 (2 sound, 0 unsound)` — `(no binder)` and `exists i`.
`cross-check: store sweep agrees with singleton reduction`

### Rule 2 — `X_i < t`

```
X_{i} < t ,  ∃i ,  i ∈ [1,n]
----------------------------- ⊢
X_{i} < t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `2 (2 sound, 0 unsound)` — `(no binder)` and `exists i`.
`cross-check: store sweep agrees with singleton reduction`

### What these rules actually say — the two readings, and why the verdict cannot separate them

**The premise literal is the conclusion literal.** Both use the index name `i`, and the
premise additionally binds it with `∃`. So the `.tex` admits two readings, and they are very
far apart:

| reading | rule | content |
|---|---|---|
| `(no binder)` — the premise's `i` is the conclusion's `i` | `X_i ≥ t ⊢ X_i ≥ t` | **a tautology.** Sound for any constraint whatsoever; infers nothing; a propagator built from it would never remove a value |
| `exists i` — the premise's `∃i` shadows the conclusion's `i` | `∃i': X_{i'} ≥ t ⊢ X_i ≥ t` | **the intended dichotomy rule**, and the useful one: one variable above the threshold puts them all above it. This is precisely the shape `decomps/all_equal.md` says the entry *should* conclude |

Both readings are sound, so the validator returns `SOUND and MINIMAL` rather than `AMBIGUOUS`
— `AMBIGUOUS` is reserved for "sound under some readings, unsound under others"
(`docs/VALIDATOR.md:225-226`). The verdict is therefore correct and uninformative about which
rule was meant. Minimality is equally uninformative: there is one premise, and dropping it
leaves an empty premise concluding `X_i ≥ t`, which is unsound — so *any* rule of this shape
is minimal, including the tautology.

**Root cause of the shadowing, read off the source.** `addprim`
(`explenation generator.ml:204`) renames the index it introduces — it builds `prim i` and adds
`Rel (prim i, NEQ, i)`, which is why `alldifferent`'s and `gcc`'s premises print as `X_{i'}`
with `i' ≠ i`. `addexists` (l.202) and `addforall` (l.203) **do not rename**: they reuse the
same `ind_name`. When the conclusion's own index is `i`, the premise's `∃i` lands on top of
it. The fix is not a printer patch — it is the binder-scope work in **W1-T1**, which
`docs/ROADMAP.md:47` states as "binders need rule-level scope, not per-literal scope".

**The generator's own ambiguity detector does not flag this, and it should be known that it
does not.** `branch_ambig` (`explenation generator.ml:613-617`) counts
`repeated (binders_indexes …)` *within a single premise literal's* index list — the D-0009
"binds an index name twice" check. Here `i` is bound once, in one literal; the collision is
with the *conclusion*, which `branch_ambig` never looks at. So `cata/allequal.tex` carries no
`** DEFECT … (D-0009) **` line while the validator reports two readings. **Two checks, two
answers, and the weaker one is the generator's.** Compare [`gcc.md`](gcc.md), where the
disagreement runs the other way (generator flags, validator finds one reading).

## Status

**`validated: sound and minimal at n,m <= 4`**

Established: at `n, m ∈ {2,3,4}` (all 9 pairs; store sweep `n, m ≤ 3`,
`docs/VALIDATOR.md:184`), neither shipped rule is unsound under any reading the `.tex` admits,
and neither has a droppable premise. The gccat cross-checks on the hand-encoded semantics also
hold for this constraint: `all_equal contractible wrt VARIABLES`, `all_equal => increasing`,
`all_equal => decreasing`, all `ok` in my run.

Not established, and not implied by that verdict: that either rule infers anything. One of the
two readings is a tautology, the `.tex` does not choose, and under the useful reading the rule
is the one `decomps/all_equal.md` was written to specify — so the honest summary is that
**this entry's artifact is consistent with both the right rule and an empty one.** The
generator's own comment (l.291) says `allequal` has no non-trivial rule under this
decomposition; the validator's `2 SOUND and MINIMAL` does not contradict that, it just cannot
see it.

`docs/VALIDATOR.md`'s per-entry table (l.279-288) is also **stale for this entry and several
others** — it predates `790bfa7` and the `gcc` repair. My own run, quoted above and in "How
this entry was produced", is the current measurement.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.** `CHRISTMAS_LIST.md:121` records the literature column as
`none`, and that row was itself added in wave three specifically because `all_equal` was the
sharpest hole in the index. Nothing is sourced into `catalog/_literature/`; this session has
no web access and did not search.

No implication comparison is therefore statable against a paper. Two internal comparisons are,
and both are worth recording because they are the calibration this entry *can* support:

- **Against its own spec.** `decomps/all_equal.md` states what the entry should conclude:
  `X_i ≥ t ← ∃i' ≠ i: X_{i'} ≥ t` and its dual. The shipped rules **agree with that shape
  under the `exists i` reading and are strictly weaker (indeed trivial) under the
  `(no binder)` reading.** Since the artifact does not determine which, the comparison against
  the spec is *undetermined*, not favourable. Closing it is W1-T1, not new literature.
- **Against `alldifferent`.** [`alldifferent.md`](alldifferent.md) is this catalog's standing
  proof that `SOUND and MINIMAL` is a floor: its one rule passes and can never fire for
  `n ≥ 3`. `all_equal` is the complementary proof, and arguably the stronger one: its rules
  *can* fire, on every store where the conclusion already holds, and under one admissible
  reading that is all they do. **Dead and empty are different failures, and the same verdict
  covers both.**

## Gaps

| gap | what it blocks here |
|---|---|
| — | **no `G`-number blocks this decomposition.** Every schema it needs (`rule1` BC channel, `rule3` conjunction, `rule4` clause) exists and runs; `decomps/all_equal.md` prices it E0 and adds no gap |
| `G8` | why the premise cannot print `i' ∈ [1,n] \ {i}` as a *set* restriction: `ind_set` names whole predefined ranges only. `addprim` works around it with an explicit `i' ≠ i` relation, and `addexists` does not use that workaround — which is this entry's defect |
| — | the open item here is **roadmap W1-T1** (binder scope), not a format gap. It is also what blocks [`element.md`](element.md), for a different symptom |

Extensions: **E0** (`CHRISTMAS_LIST.md:121`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/allequal.tex  (2 rules) ----`, two
  `VERDICT   : SOUND and MINIMAL`, each `readings  : 2 (2 sound, 0 unsound)` listing
  `[sound  ] (no binder)` and `[sound  ] exists i`, each with
  `cross-check: store sweep agrees with singleton reduction`. Run totals: **34 rules checked
  in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**;
  19/19 invariants hold, including `all_equal contractible wrt VARIABLES`,
  `all_equal => increasing` and `all_equal => decreasing`; all 11 controls behaved.
- `python3 tools/mzn_coverage.py --rank --json` → `all_equal` in
  `A no-literature + solver-decomposes`, `ecodes: ['E0']`, `line: 121`.
- `grep -o '\\frac' cata/allequal.tex | wc -l` → 2.
- `cata/allequal.tex` read, not run → the two rules and the diagnostics footer, including the
  `dropped F 1` on each event and the **absence** of any `(D-0009)` line.
- `explenation generator.ml:202-204` read, not run → `addexists`/`addforall` reuse the index
  name, `addprim` renames it. This is the root-cause claim, and it is read off the code.
- `explenation generator.ml:613-617` read, not run → `branch_ambig` inspects premise literals
  only, which is why the generator does not flag the premise/conclusion collision.
- `explenation generator.ml:266-296` read, not run → the whole `EXOR`→`EXAND` account,
  including the `n = m = 2, X = (1,1), t = 2` counterexample and the line-291 sentence. Quoted
  from the comment, not re-derived.
- `explenation generator.ml:804-807, 868, 879` read, not run → the `alleq` value, the `xbc`
  global event, the emitting call. Checked against the current file; `decomps/all_equal.md`'s
  "l.674–677" does not resolve.
- `git log -1 790bfa7` → `2026-09-18  W1-T9 defect 1: allequal's inverted inequality was an
  OR where an AND belongs`.
- `CHRISTMAS_LIST.md:121`, `:106-108` read → literature column, solver column, legend, and the
  two stale claims flagged above.
- `docs/VALIDATOR.md:184, 225-226, 279-288` read → sizes, the `AMBIGUOUS` definition, and the
  stale per-entry table.
- **The two-readings analysis is reasoning about the printed rule, not a measurement.** The
  measurement is the validator's `readings : 2`; naming one of them a tautology and the other
  the intended rule is this session's reading of the `.tex`.
