# `nvalue`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `nvalue`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — no literature + solver decomposes (`tools/mzn_coverage.py --rank`, ecodes `E0`) |
| **Status** | `flagged` |
| **Generated** | 5 rules in `cata/nvalues.tex` |
| **Validator** | 0 `SOUND and MINIMAL`; 4 `VACUOUS`, 1 `UNSOUND` (the firing-reading kind) |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:130` records "none" |
| **Last measured** | 2026-09-21, `make validate` (E2's own run) and `python3 tools/mzn_coverage.py --rank --json` |

**Not one rule in this entry can both fire and be sound.** Four are `VACUOUS` — no store
satisfies their premises — and the fifth is `UNSOUND` precisely under the one reading that
could ever fire. Three of the five also carry the generator's own D-0009 flag, so their LaTeX
does not determine what they mean. This is the weakest entry of the seven E2 wrote, and
nothing below should be read as a usable rule.

## Constraint

`nvalue(var int: n, array [int] of var int: x)`

`n` is the number of distinct values taken by the array `x`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:97` carries the *name* only (and `nvalue_fn` at 98,
which `CHRISTMAS_LIST.md:217` records as a functional wrapper, not a separate constraint).
The signature above matches the one in `decomps/nvalue.md`; neither is a vendored citation.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:130` reads
`| nvalue | none | decomp | **E0** — already in cata/nvalues.tex, but the generated rule
repeats binders (∀i twice); fix is index hygiene, not an extension |`.

**Rule shape:** nothing to source; `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only.

**That row understates the entry in one respect and this must be said plainly.** "Repeats
binders … fix is index hygiene, not an extension" is a rendering complaint. Measured, the
entry has no sound-and-firing rule at all, and one rule is outright unsound with a
counterexample at `n = m = 2`. Index hygiene may still be the whole fix — the roadmap thinks
so (W1-T1) — but the row's tone would let a reader take the rules as usable, and they are not.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:130`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.

## Decomposition used here

**Generator value:** `nvalues`, `explenation generator.ml:839-842`
**Emitted by:** `explainall [xac;nac] nvalues "cata/nvalues.tex"`, line 886
**Spec:** `decomps/nvalue.md` (shape **S3** in `decomps/_shapes.md`). **Its line citation
"lines 406-409" no longer resolves** — the value is at 839-842; it also cites "generator line
396" for the `N` channel, which is now line 840.

```ocaml
let nvalues = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
               Decomp (1, rule1, [Global_devent (true, N, id, id, AC); Reified_devent (true, (B 4), id, id)]);
               Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni); Reified_devent (true, (B 2), id, i_out)]);
               Decomp (3, rule7, [Decomp_devent (true, (B 2), id, ont); Reified_devent (true, (B 4), imap [foralli;p_out], imap [i_out;t_out;forallp])])]
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency, over the full `[1,n]×[1,m]`
  grid.
- **step 2, `rule1`** — `B4_p ⇔ N = p`, arc consistency: the count channel, the same mechanism
  `gccn` uses for `O` (`CHRISTMAS_LIST.md:96` calls this out as the thing E1 would open up).
- **step 3, `rule4`** — `B2_t ⇔ ⋁_{i} B1_{i,t}`: "value `t` is used by some `X_i`".
- **step 4, `rule7`** — a Boolean sum with `=`: `Σ_{t∈[1,m]} B2_t = p ⇔ B4_p`.

`B1`, `B2`, `B4` all wash out; only `X` and `N` literals print (D-0004), confirmed by reading
the `.tex`.

**`rule7` is the one schema in the generator its author marked as doubtful.** Lines 377-378
carry the comment `(*incohérent?*)` on both arms of `rule7`'s `dname de = dname re` branch —
one builds an `EXAND` of the positive and negative `forall` explanations, the other an `EXOR`
of the same pair. `nvalues` is one of only two shipped decompositions that use `rule7` (the
other is `among`, which emits nothing), and step 4 above is exactly that branch when the
explained event is `N`. That is not a diagnosis of the defects below, and it is not claimed
to be one; it is recorded because this entry is where an author-flagged uncertainty and four
unusable rules coincide.

**`gccn` is the near relative that works, and the difference is one operator.** `gccn`
(`explenation generator.ml:827-829`) has the same three-layer shape — reify, sum, channel to
a count variable — and all four of its rules are `SOUND and MINIMAL`. The repair that got it
there (W1-T9 defect 3, comment at l.815-826) replaced a `forallp` in the sum's *ascending*
operator with `pointp`, because `p` is a schema parameter and not something the premise
quantifies. **`nvalues` step 4 still carries `forallp`** in its ascending `imap`
(`imap [i_out;t_out;forallp]`), where `gccn` now carries `pointp`. Whether transplanting that
change fixes this entry is **not tested here** — this session owns no generator file, and the
two decompositions differ elsewhere (`rule7` vs `rule6`, an extra `t` layer). It is recorded
as the obvious next experiment, not as a diagnosis.

## Scope of this entry

**Events the generator was asked to explain:** four, from two global events —
`xac` (`explenation generator.ml:869`) giving `X_i = t` / `X_i ≠ t`, and
`nac` (line 871) giving `N = p` / `N ≠ p`, both arc-consistent.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | 1 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | 1 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `N=p` | 1 | 1 | none — but `** DEFECT: 1 emitted rule(s) for N=p bind an index name twice; the LaTeX is ambiguous (D-0009) **` |
| `N \neq p` | 2 | 2 | none — but `** DEFECT: 2 emitted rule(s) for N \neq p bind an index name twice … (D-0009) **` |

Nothing was dropped and no branch was blocked: for these four events, over this decomposition,
five rules is the generator's complete output — and the completeness of that list says
nothing about their quality. **It is not the set of explanations of `nvalue`.** In particular
nothing here reasons across values (the counting argument, **E4**), and nothing bounds `N`
from a partial assignment, which is the pruning a solver would want.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/nvalues.tex`.

## Generated rules

Rendered from `cata/nvalues.tex` (`grep -o '\\frac' cata/nvalues.tex | wc -l` → 5).
`[1,n]` is the variable index set, `[1,m]` the value set, `p` ranges over `[1,n]`.

### Rule 1 — `X_i = t`

```
X_{i'} ≠ t ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
X_{i} ≠ t ,  ∀i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m]
N=p ,  ∀p ,  p ∈ [1,n]
------------------------------------------------------- ⊢
X_{i}=t
```

**Verdict:** `VACUOUS — no store in scope satisfies the premises, so it is sound only because
it can never fire`
**Reading(s) checked:** `5 (5 sound, 0 unsound)`, the listed ones all annotated
`(premises never hold)`: `forall i' ; (no binder) ; forall p`, `forall i' ; forall t ; forall
p`, `forall i' ; forall i ; forall p`, `forall i' ; forall i,forall t ; forall p`.
`cross-check: store sweep agrees with singleton reduction`

Premise 2 reads `∀i ∀t: X_i ≠ t` — every variable avoids every value. No store satisfies
that. Premise 3 reads `∀p: N = p`, which is equally unsatisfiable for `n ≥ 2` on its own; the
`gcc` repair comment (l.815-826) documents the same `∀p` collapse and calls it what it is.

### Rule 2 — `X_i ≠ t`

```
X_{i}=t ,  ∃i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m]
N=p ,  ∀p ,  p ∈ [1,n]
---------------------------------------------- ⊢
X_{i} ≠ t
```

**Verdict:** `VACUOUS`
**Reading(s) checked:** `5 (5 sound, 0 unsound)`, all `(premises never hold)`:
`(no binder) ; forall p`, `forall t ; forall p`, `exists i ; forall p`,
`exists i,forall t ; forall p`.

### Rule 3 — `N = p`

```
X_{i} ≠ t ,  ∀i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m] ,  ∀i ,  i ∈ [1,n]
X_{i}=t ,  ∃i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m] ,  ∀i ,  i ∈ [1,n]
------------------------------------------------------------------- ⊢
N=p
```

**Verdict:** `VACUOUS`
**Reading(s) checked:** `8 (8 sound, 0 unsound)`, all `(premises never hold)`.
**Also flagged by the generator:** `binds an index name twice … (D-0009)`. Both checks are
reported, as `catalog/gcc.md` does — they are different questions. Here they agree in
substance: `∀i` appears twice in each premise, and the eight readings the validator
enumerates are the consequence. The two premises are also direct contradictories of one
another once quantified, which is the vacuity.

### Rule 4 — `N ≠ p`

```
X_{i}=t ,  ∃i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m] ,  ∀i ,  i ∈ [1,n]
------------------------------------------------------------------ ⊢
N ≠ p
```

**Verdict:** `UNSOUND — every other reading is vacuous, so the only reading that can ever fire
is the unsound one`
**Reading(s) checked:** `4 (3 sound, 1 unsound)` — `(premises never hold) exists i,forall t`,
`(premises never hold) forall i,forall t`, **`[UNSOUND] forall t,exists i`**,
`(premises never hold) forall t,forall i`.
**counterexample:** `n=2 m=2 X=(1,2) N=2 [nvalue] p=2`
**Also flagged by the generator:** `binds an index name twice … (D-0009)`.

This is `docs/VALIDATOR.md`'s `UNSOUND(firing)` category (l.229-230) — "every reading that
survives is vacuous, so the only reading under which the rule could ever fire is an unsound
one". The counterexample is the clearest statement of the problem: `X = (1,2)` uses two
distinct values, so `nvalue` gives `N = 2`; the rule concludes `N ≠ 2`.

### Rule 5 — `N ≠ p`

```
X_{i} ≠ t ,  ∀i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m] ,  ∀i ,  i ∈ [1,n]
------------------------------------------------------------------- ⊢
N ≠ p
```

**Verdict:** `VACUOUS`
**Reading(s) checked:** `2 (2 sound, 0 unsound)`, both `(premises never hold)`:
`forall i,forall t`, `forall t,forall i`.
**Also flagged by the generator:** D-0009, same double `∀i`.

### Can any of these fire?

**No.** Four are `VACUOUS`, which is the validator's name for "cannot fire". The fifth fires
only under a reading that is unsound. Nothing in this entry is available to a solver.

This is a *different* failure from [`alldifferent.md`](alldifferent.md)'s, and the catalog now
has all three kinds side by side, which is worth stating once:

| entry | verdict | why it is not useful |
|---|---|---|
| `alldifferent` | `SOUND and MINIMAL` | premise contradicts the constraint for `n ≥ 3`; dead, and the flag misses it because `n = 2` is in scope |
| `all_equal` | `SOUND and MINIMAL` | premise *is* the conclusion under one admissible reading; alive and empty |
| `nvalue` | `VACUOUS` ×4, `UNSOUND` ×1 | premises unsatisfiable in any store at all; the flag catches it |

## Status

**`flagged`** — `catalog/README.md`'s legend: "every generated rule is flagged".

Established: at `n, m ∈ {2,3,4}` (all 9 pairs; store sweep held at `n = m = 2` because the
`N` auxiliary multiplies the store space, `docs/VALIDATOR.md:185`), no rule in this entry is
both sound and capable of firing, and rule 4 is unsound with a printed counterexample. Both
soundness methods agree (`store sweep agrees with singleton reduction` on all five). The
hand-encoded semantics passes its gccat cross-checks for this constraint —
`nvalue: NVAL determined by VARIABLES`, `nvalue contractible wrt VARIABLES when NVAL=1`,
`nvalue contractible wrt VARIABLES when NVAL=|VARIABLES|`, plus the four cross-entry
implications involving `nvalue`, all `ok`.

Not established: that index hygiene alone fixes it. `CHRISTMAS_LIST.md:130` and
`docs/ROADMAP.md:47` both say so, and both are plausible, but nobody has run the experiment —
and the `gccn` comparison above shows the sibling entry needed a change to the *ascending
operator*, not to binder names, to go from `VACUOUS` to `SOUND and MINIMAL`.

**`docs/VALIDATOR.md`'s per-entry table (l.279-288) is stale for this entry**: it records
`nvalues | 6 | 4 VACUOUS, 1 UNSOUND, 1 UNSOUND(firing)`. The sixth rule was removed by
`790bfa7` (see [`allequal.md`](allequal.md)). My run's five are above.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.** `CHRISTMAS_LIST.md:130` records the literature column as
`none`. Nothing is sourced into `catalog/_literature/`; this session has no web access and did
not search. No implication comparison against a paper is statable.

**And no comparison would be worth making yet.** Calibration asks whether the generated
premise implies the published one or the reverse. A premise that no store satisfies implies
everything vacuously, so scoring four of these five as "stronger than published" would be an
artefact of the defect, not a result. That is worth stating explicitly, because it is the one
case where the implication-strength axis breaks down: **`out of reach` is a verdict about the
published rule's expressibility; a vacuous premise is a defect in ours, and the two must not
be conflated.** When W1-T1 lands and the entry re-measures, calibration becomes answerable;
until then it is not.

The internal comparisons that *are* available:

- **Against `gcc`.** [`gcc.md`](gcc.md) is the same three-layer counting shape with a count
  channel, and it is the only 4/4 entry in the repo. The structural difference is `rule7` +
  `forallp` here versus `rule6` + `pointp` there. Whatever the fix is, `gccn` is the worked
  example of it.
- **Against `alldifferent`.** `docs/GCCAT.md:107` records that gccat's generalisation links
  transport no rule: "a rule for `alldifferent` is not a rule for `nvalue`". The validator
  checks the *semantic* implications (`alldifferent <=> nvalue(X,n)` and
  `nvalue(X,k) => atleast_nvalue(X,k)`, both `ok` in my run) but those are facts about
  assignments, not about explanations.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **no `G`-number blocks this decomposition.** `rule1`, `rule4` and `rule7` all exist and run; `decomps/nvalue.md` prices it E0 and adds no gap |
| `G2` | `var_name` is a closed variant and `N` is the borrowed letter for "this constraint's own count variable". Mechanically harmless here (one file per constraint), but it is why `count`'s `c` has nowhere to go |
| `G4` | one Boolean-sum family per rule, `failwith` otherwise. Not hit here (step 4 sums one family), but it is the wall between this shape and `global_cardinality`'s per-value sums |
| — | **the live blocker is roadmap W1-T1** (binder scope), which is also what D-0009 is about. The generator flags three of five rules for it |
| — | **E4** is what a *useful* `nvalue` rule would need — reasoning across values rather than within one sum. Not on the `G` list; it is an extension |

Extensions: **E0** (`CHRISTMAS_LIST.md:130`); **E4** for anything with pruning power.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/nvalues.tex  (5 rules) ----`, four
  `VERDICT   : VACUOUS …` and one
  `VERDICT   : UNSOUND — every other reading is vacuous, so the only reading that can ever
  fire is the unsound one` with `counterexample: n=2 m=2 X=(1,2) N=2 [nvalue] p=2`. Every
  rule reports `cross-check: store sweep agrees with singleton reduction`. Run totals:
  **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out
  of scope**; 19/19 invariants hold; all 11 controls behaved.
- `python3 tools/mzn_coverage.py --rank --json` → `nvalue` in
  `A no-literature + solver-decomposes`, `ecodes: ['E0']`, `line: 130`.
- `grep -o '\\frac' cata/nvalues.tex | wc -l` → 5.
- `cata/nvalues.tex` read, not run → the five rules and the diagnostics footer, including the
  two `(D-0009)` lines quoted above (one for `N=p`, one covering both `N \neq p` rules).
- `explenation generator.ml:839-842, 869, 871, 886` read, not run → the `nvalues` value, the
  two global events, the emitting call. Checked against the current file;
  `decomps/nvalue.md`'s "lines 406-409" and "line 396" do not resolve.
- `explenation generator.ml:377-378` read, not run → the two `(*incohérent?*)` comments on
  `rule7`'s branches.
- `explenation generator.ml:815-826, 827-829` read, not run → the `gccn` W1-T9 repair
  (`forallp` → `pointp`) and the shipped `gccn` value, for the comparison above. **The
  "obvious next experiment" is a suggestion, not a tested claim**, and no generator file was
  touched by this session.
- `docs/ROADMAP.md:47` read, before reporting → W1-T1 is `TODO`.
- `docs/VALIDATOR.md:185, 229-230, 279-288` read → store-sweep cap, the `UNSOUND(firing)`
  definition, and the stale per-entry table.
- `docs/GCCAT.md:107` read → generalisation links transport no rule.
- `CHRISTMAS_LIST.md:130`, `:96`, `:217`, `:106-108` read → literature, the E1 note on the
  `N`/`O` channel, the `_fn` wrapper note, the solver legend.
