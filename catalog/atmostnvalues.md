# `atmost_nvalue`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `atmost_nvalue`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **not ranked** — `atmost_nvalue` is a **gccat** constraint, not a MiniZinc 2.10.1 global (see below). `tools/mzn_coverage.py --rank` assigns it no tier because it is not in the release list |
| **Status** | `flagged` |
| **Generated** | 4 rules in `cata/atmostnvalues.tex` |
| **Validator** | 0 `SOUND and MINIMAL`; 1 `NOT MINIMAL`, 1 `UNSOUND`, 2 `VACUOUS` |
| **Calibration** | **pending** — `CHRISTMAS_LIST.md` has **no row** for this constraint, so neither a citation nor a searched-and-empty finding exists in-repo |
| **Last measured** | 2026-09-21, `make validate` (E2's own run), `python3 tools/mzn_coverage.py --rank --json`, `python3 tools/catalog_index.py`, `cmp`/`md5sum` on the two `.tex` files |

**This entry is not settled and must not be presented as if it were.**
`cata/atmostnvalues.tex` is **byte-identical** to `cata/atleastnvalues.tex` — measured, same
md5 — although the two decompositions differ. `atmost_nvalue` is **contractible** wrt
`VARIABLES` and `atleast_nvalue` is **extensible**; two constraints with opposite closure
properties cannot have the same explanation rules, so at least one of the two files is wrong
and nothing here says which. This is roadmap **W1-T5**, open.

## Constraint

`atmost_nvalue(NVAL, VARIABLES)` — the number of distinct values taken by `VARIABLES` is
**at most** `NVAL`.

**This is a gccat constraint, not a MiniZinc global.** It does not appear in
`tools/data/minizinc-2.10.1-globals.txt`; `tools/mzn_coverage.py --rank` therefore assigns it
no tier, and `tools/catalog_index.py` reports
`warning: UNMATCHED: 'atmostnvalues' has no corresponding release global`. **MiniZinc states
the same thing through `nvalue`** — `nvalue(n, x)` with an inequality on `n`, which is
[`nvalues.md`](nvalues.md)'s entry. The catalog's coverage claim is indexed on the 118
MiniZinc globals (`catalog/README.md`, "What the catalog claims"), so **this entry is outside
that denominator and does not count towards it.**

**Provenance of the signature:** gccat, via `docs/GCCAT.md`, which records this repo's
reading of the `Catmost_nvalue` entry page. No MiniZinc signature exists to cite. The
decomposition below is read off the generator and is quotable.

## Published explanation

**Citation: none available, and that is different from "none exists".**
`CHRISTMAS_LIST.md` — the repo's literature index — has **no row for `atmost_nvalue`**,
verified by `grep -n 'nvalue' CHRISTMAS_LIST.md` (three hits: l.96, l.130, l.217, none of
them this constraint). The index's scope is the MiniZinc release list and this constraint is
not on it, so the index never looked. The entry cannot say "no published rule exists"; it can
only say **nothing has been searched**.

**Rule shape:** **pending C2** — not stated here. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. This session has no web access and, per `CLAUDE.md`, does not
write a published rule shape from memory.

**Index the two together.** Whatever C2 finds for `atmost_nvalue` it should record for
`atleast_nvalue` in the same pass: gccat links them as `comparison swapped`
(`docs/GCCAT.md:105`), and this catalog now holds two entries whose only distinguishing
artifact is a decomposition value. **No claim is made here about what the literature
contains** — the point is only that the index has not looked, and that a row saying so would
be a complete answer.

## Solver support

| | |
|---|---|
| Chuffed | **unknown** — no `CHRISTMAS_LIST.md` row |
| Geas | **unknown** |
| Choco LCG | **unknown** |

There is no row to read, and the legend at `CHRISTMAS_LIST.md:106-108` has nothing to apply
to. The nearest indexed relative is `nvalue` (`CHRISTMAS_LIST.md:130`, `decomp`), but a
solver's treatment of `nvalue` is not evidence about `atmost_nvalue` and is not presented as
such.

## Decomposition used here

**Generator value:** `atmostnvalues`, `explenation generator.ml:847-850`
**Emitted by:** `explainall [xac;nbc] atmostnvalues "cata/atmostnvalues.tex"`, line 888
**Spec:** **none** — there is no `decomps/atmost_nvalue.md`. The nearest relative is
`decomps/nvalue.md`, shape **S3**.

```ocaml
let atmostnvalues = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
                     Decomp (1, rule1, [Global_devent (true, N, id, id, BC); Reified_devent (true, (B 4), id, id)]);
                     Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni); Reified_devent (true, (B 2), foralli, i_out)]);
                     Decomp (3, rule5, [Decomp_devent (true, (B 2), id, ont); Reified_devent (false, (B 4), imap [foralli;p_out], imap [i_out;t_out;forallp])])]
```

- **steps 1-3** — **identical, token for token, to `atleastnvalues`** (l.843-845):
  `B1_{i,t} ⇔ X_i = t` (AC), `B4_p ⇔ N ≥ p` (BC), `B2_t ⇔ ⋁_i B1_{i,t}`.
- **step 4, `rule5`** — a Boolean sum with `≤`, and `B4`'s reified sign **negated**:
  `¬B4_p ⇔ (Σ_t B2_t ≤ p)`. This is the entire difference between the two constraints as
  encoded: one schema name and one boolean.

**Note that step 2's channel is `rule1`, a reified *equivalence*.** `B4_p ⇔ N ≥ p` pins `N` to
the sum from both sides, so on a strict reading this decomposition says `nvalue`, and the "at
most" asymmetry lives only in `rule5`'s choice of arm. This session's reading of the source,
not a measurement; recorded because it is a candidate root cause for W1-T5 that nobody has
written down.

`B1`, `B2`, `B4` wash out; only `X` and `N` literals print (D-0004).

### W1-T5: the collision with `atleastnvalues`, and why it is not an accident

**Measured.** `cmp cata/atmostnvalues.tex cata/atleastnvalues.tex` is silent; both files hash
to `82aa49d8a547f1a9df196c2eed408aa1`. All four rules and both diagnostics footers coincide.

**The two changes at `Decomp 3` cancel exactly**, and the cancellation is traceable in the
code. `rule5` (`explenation generator.ml:343-355`) and `rule6` (l.357-369) are the same
four-branch body with the positive and negative variants interchanged in every branch —
`fre`↔`fnre` and `apforall`↔`napforall`. `ap` (l.192-196) takes its sign from the devent's
own boolean and `nap` (l.197-200) takes its negation, so negating `B4` interchanges what
`fre` and `fnre` produce. Two interchanges compose to the identity. On both descent paths:

- **explaining an `N` event** — the traversal enters `Decomp 3` through the `B4`
  `Reified_devent`, so `dname de = dname re`. Here `dsign de = false ≠ sign e`, so `rule5`
  takes its `else` arm → `apforall`; `atleastnvalues`' `rule6` with `dsign de = true = sign e`
  takes its `then` arm → `apforall`. Same node.
- **explaining an `X` event** — the traversal enters through the `B2` `Decomp_devent`, which
  is identical in both files, so the same arm is selected in each. `rule5` emits `fnre re`
  with `re`'s sign `false` → `not false` → a positive `B4`; `rule6` emits `fre re` with `re`'s
  sign `true` → the same positive `B4`.

So the byte-identity is **not** a printer bug and **not** a coincidence: as encoded, these are
the same decomposition written two ways, and **the format did not record what "at most"
means.** *(Read off the source, confirmed by the measured md5; no code was run to produce the
trace.)*

**The generator preserves the collision on purpose.** `explenation generator.ml:712-715`
records that `write_footer` deliberately does not name its own file, because the two files
"are byte-identical although their decompositions differ, and that collision is W1-T5's
evidence."

### The independent evidence: opposite closure properties

`docs/GCCAT.md:120-124`, read off the two gccat entry pages:

- `atleast_nvalue`: **extensible** wrt `VARIABLES`, and monotone — `NVAL` can be decreased.
- **`atmost_nvalue`: contractible wrt `VARIABLES`.**

"Two constraints with *opposite* closure properties cannot have the same explanation rules, so
`cata/atleastnvalues.tex` and `cata/atmostnvalues.tex` being byte-identical is a defect on
catalog grounds alone — an argument independent of W0-A's validator run, which reached the
same place."

`atmost_nvalue contractible wrt VARIABLES  gccat Catmost_nvalue  ok` is one of the 19
machine-checked invariants, and it holds in my run — so the semantics this entry is judged
against is the right one; it is the *rules* that collide.

**The dual of the wrong-side prediction.** `docs/GCCAT.md:126-128` derives, from
`atleast_nvalue`'s monotonicity, that `X` literals there can only tighten `NVAL`'s upper
bound. `atmost_nvalue` is contractible rather than monotone-in-`NVAL`, so **no such
prediction is derived for this side and none is invented here.** What is measured is that
this entry's unsound rule (rule 3) fails at `n=3, m=2, p=3` — with `p > m`, so the failure
needs a threshold above the value-set size — while the at-least side fails at `p = 1`,
inside the ordinary range. That asymmetry is what `docs/ROADMAP.md:51` tells W1-T5 to start
from, and my run reproduces it.

## Scope of this entry

**Events the generator was asked to explain:** four, from two global events —
`xac` (`explenation generator.ml:869`) giving `X_i = t` / `X_i ≠ t`, and
`nbc` (line 870) giving `N ≥ p` / `N < p`, bounds-consistent.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | 1 | none — `** DEFECT: 1 emitted rule(s) for X_{i}=t bind an index name twice; the LaTeX is ambiguous (D-0009) **` |
| `X_{i} \neq t` | 1 | 1 | none — same D-0009 flag |
| `N \geq p` | 1 | 1 | none — same D-0009 flag |
| `N<p` | 1 | 1 | none — same D-0009 flag |

Nothing was dropped and no branch was blocked. **All four rules carry the D-0009 flag**: not
one rule in this entry has LaTeX that determines what it means.

Before commit `790bfa7` this entry had five rules; the `EXOR`→`EXAND` repair removed one
`UNSOUND` rule — see [`allequal.md`](allequal.md). The two files stayed byte-identical through
it, "so W1-T5's evidence is preserved" (`explenation generator.ml:294-295`).

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/atmostnvalues.tex`.
**The footer does not name its own file** (by design, above), so the block is literally the
same text as `atleastnvalues`'.

## Generated rules

Rendered from `cata/atmostnvalues.tex` (`grep -o '\\frac' cata/atmostnvalues.tex | wc -l`
→ 4). **The LaTeX is identical to `cata/atleastnvalues.tex`'s; the verdicts are not**, because
the validator judges each against its own constraint's semantics. Rule 2 is the clearest case:
`VACUOUS` here, `AMBIGUOUS` with two refutable readings there. **One text cannot serve both,
and the divergent verdicts are the proof.**

### Rule 1 — `X_i = t`

```
X_{i'} ≠ t ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n]
X_{i} ≠ t' ,  ∀i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n] ,  ∀t' ,  t' ≠ t ,  t' ∈ [1,m] ,  t ∈ [1,m]
N ≥ p ,  ∀p ,  p ∈ [1,n]
--------------------------------------------------------------------------------------------- ⊢
X_{i}=t
```

**Verdict:** `SOUND but NOT MINIMAL — droppable: #1 (X_i' != t), #3 (N >= p)`
**Reading(s) checked:** `3 (3 sound, 0 unsound)` — `forall i' ; forall t' ; forall p`, and two
annotated `(premises never hold)`.
`cross-check: store sweep agrees with singleton reduction`
**Also flagged by the generator:** D-0009.

**This rule fires, and it says nothing about `atmost_nvalue`.** Drop the two droppable
premises and what remains is `∀t' ≠ t: X_i ≠ t' ⊢ X_i = t` — **domain exhaustion**, sound for
any constraint over `[1,m]`. The `NOT MINIMAL` flag understates it: the rule's entire content
is the constraint-independent remainder. The same rule, with the same droppable set, appears
in [`atleastnvalues.md`](atleastnvalues.md) — which is consistent, because a
constraint-independent rule *would* legitimately be shared, and is the one rule of the four
whose collision is not by itself evidence of a bug.

**On the `∀i' ≠ i` premise.** `catalog/alldifferent.md` shows a premise of that shape
(`∀i' ≠ i: X_{i'} = t`) contradicting its own constraint and never firing. Premise 1 here is
the opposite polarity — every other variable *avoids* `t` — and is satisfiable at every
arity. The shape alone does not kill a rule; the polarity decides.

### Rule 2 — `X_i ≠ t`

```
X_{i}=t' ,  ∃i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n] ,  ∀t' ,  t' ≠ t ,  t' ∈ [1,m] ,  t ∈ [1,m]
N<p ,  ∀p ,  p ∈ [1,n]
-------------------------------------------------------------------------------------------- ⊢
X_{i} \neq t
```

**Verdict:** `VACUOUS — no store in scope satisfies the premises, so it is sound only because
it can never fire`
**Reading(s) checked:** `5 (5 sound, 0 unsound)`, all annotated `(premises never hold)`:
`forall t' ; forall p`, `forall t',exists i ; forall p`, `exists i,forall t' ; forall p`,
`forall t',forall i ; forall p`.
**Also flagged by the generator:** D-0009.
`cross-check: store sweep agrees with singleton reduction`

**The byte-identical rule in [`atleastnvalues.md`](atleastnvalues.md) is `AMBIGUOUS`, with
two readings refuted by `n=2 m=2 X=(1,2) N=0 t=1,i=1`.** Here every reading is unsatisfiable
instead. Same premises, same conclusion, two incompatible characterisations — this is the
divergence `docs/ROADMAP.md:51` tells W1-T5 to start from.

### Rule 3 — `N ≥ p`

```
X_{i}=t ,  ∃i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m] ,  ∀i ,  i ∈ [1,n]
------------------------------------------------------------------------------------ ⊢
N \geq p
```

**Verdict:** `UNSOUND — every other reading is vacuous, so the only reading that can ever fire
is the unsound one`
**Reading(s) checked:** `4 (3 sound, 1 unsound)` — three `(premises never hold)`, and
**`[UNSOUND] forall t,exists i`**.
**counterexample:** `n=3 m=2 X=(1,1,2) N=2 [atmost] p=3`
**Also flagged by the generator:** D-0009.

**The counterexample needs `p > m`, and that is the asymmetry with the at-least side.**
`X = (1,1,2)` uses 2 distinct values over `m = 2`, and `atmost_nvalue` with `N = 2` is
satisfied; the rule concludes `N ≥ 3`. Note `p = 3 > m = 2`: the failure requires a threshold
above the value-set size, whereas `atleast`'s identical rule fails at `p = 1`. That is
`docs/VALIDATOR.md`'s `UNSOUND(firing)` class (l.229-230) in both cases, reached from
opposite ends of the `p` range.

### Rule 4 — `N < p`

```
X_{i} ≠ t ,  ∀i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n] ,  ∀t ,  t ∈ [1,m] ,  ∀i ,  i ∈ [1,n]
-------------------------------------------------------------------------------------- ⊢
N<p
```

**Verdict:** `VACUOUS — no store in scope satisfies the premises, so it is sound only because
it can never fire`
**Reading(s) checked:** `2 (2 sound, 0 unsound)`, both `(premises never hold)`:
`forall i,forall t`, `forall t,forall i`.
**Also flagged by the generator:** D-0009.

The premise reads `∀i ∀t: X_i ≠ t` — every variable avoids every value. Same unsatisfiable
shape as [`nvalues.md`](nvalues.md)'s rules, with `∀i` printed three times over one literal.

### Which rules can fire

Rule 1 fires and is constraint-independent. Rule 3 fires only under its one unsound reading.
Rules 2 and 4 never fire. **No rule in this entry both fires and is a sound statement about
`atmost_nvalue`.**

## Status

**`flagged`** — `catalog/README.md`'s legend: every generated rule is flagged.

Established, at `n, m ∈ {2,3,4}` with `N ∈ [0,n]` and the store sweep at `n, m ≤ 3`
(`docs/VALIDATOR.md:186`): one rule sound-but-redundant and constraint-independent, one
unsound on its only firing reading, two vacuous. Both soundness methods agree on all four.
The hand-encoded semantics passes its gccat cross-checks
(`atmost_nvalue contractible wrt VARIABLES`, `nvalue(X,k) => atmost_nvalue(X,k)`, both `ok`).

**Not settled, and this entry does not pretend otherwise:**

- **Which of the two files is wrong.** Writing `atmost_nvalue` as the polarity-dual of
  `atleast_nvalue` is the encoding that produced the collision, which makes *this* side the
  more suspicious of the two — but "more suspicious" is not a measurement, and nothing here
  establishes that the at-least side is right.
- **Whether the `rule1` equivalence channel (step 2) is the root cause.** Recorded above as a
  reading of the source, untested.
- **Whether index hygiene (W1-T1/D-0009) would change any verdict.** All four rules are
  flagged for it, so no verdict here is final about the *intended* rule.

**`docs/VALIDATOR.md`'s per-entry table (l.279-288) is stale for this entry**: it records
`atmostnvalues | 5 | 1 NOT MINIMAL, 1 UNSOUND, 2 VACUOUS, 1 UNSOUND(firing)`. Commit
`790bfa7` removed the fifth rule. My run's four are above.

**The roadmap row's rule numbering is stale by one, and its substance is confirmed.**
`docs/ROADMAP.md:51` refers to "rule 3" (AMBIGUOUS vs VACUOUS) and "rule 4" (unsound firing
reading); after `790bfa7` those are **rules 2 and 3**. The measurements hold exactly: at-most
fails at `p = 3 > m = 2`, at-least at `p = 1`.

## Calibration (W3-T5, D-0013)

**Verdict: pending.**

Not `no published rule`: that verdict means "`CHRISTMAS_LIST.md` records no explanation for
this constraint" (`catalog/TEMPLATE.md`'s table), and the index records *nothing at all* here,
because its scope is the MiniZinc release list and `atmost_nvalue` is not on it. A silence
that comes from not having looked is not a finding.

Not `out of reach`: that requires a published premise that cannot be expressed here, and no
published premise is in hand.

**What is needed to lift `pending`:** a `CHRISTMAS_LIST.md` row for `atleast_nvalue` /
`atmost_nvalue` — a citation, a searched-and-empty finding, or an explicit "outside this
index's scope" — then a `catalog/_literature/` shape if a paper exists. A C2 task.

**And calibration should not be attempted before W1-T5 closes.** Comparing a published
premise against a rule that is byte-identical to a *different* constraint's rule would
attribute the comparison to the wrong constraint. Order: W1-T5, then C2, then calibration.

The one comparison available now is internal and negative, and it is the same one
[`atleastnvalues.md`](atleastnvalues.md) makes: gccat's `comparison swapped` link
(`docs/GCCAT.md:105`) is "the only near-mechanical relation" between related constraints'
explanations, "and it is a renaming, not a derivation". The catalog's other
`comparison swapped` pair, [`increasing`](increasing.md)/[`decreasing`](decreasing.md), is
handled correctly — two sign-swapped decomposition values producing two *different*,
mirror-image `.tex` files, both validated 2/2. Here the same relation collapsed into an
identity. Same relation, opposite outcome, and that contrast is the most useful thing this
entry currently contributes.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **no `G`-number blocks this decomposition.** `rule1`, `rule4` and `rule5` all exist and run. W1-T5 is a *defect*, not a format gap: the encoding admitted two spellings of the same thing |
| `G2` | `var_name` is closed and `N` is the borrowed letter for this constraint's own count variable |
| `G4` | one Boolean-sum family per rule (`failwith` otherwise). Not hit — step 4 sums one family |
| — | **roadmap W1-T5** (the collision, `TODO`) and **W1-T1** (binder scope; all four rules carry the D-0009 flag) are the live blockers |
| — | **the format has no way to record an asymmetric channel.** `rule1` is a reified *equivalence*, so `B4_p ⇔ N ≥ p` pins `N` from both sides and the `≤`/`≥` distinction has to live entirely in the sum schema — where, as traced above, a sign flip erases it. Not on `docs/DECOMP_FORMAT_NOTES.md`'s numbered list and **not** proposed here as a new `G`-number; recorded as an observation for W2-T1, the format freeze |

Extensions: none priced — there is no `CHRISTMAS_LIST.md` row to carry an E-code. The nearest
indexed relative, `nvalue`, is **E0** (`CHRISTMAS_LIST.md:130`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/atmostnvalues.tex  (4 rules) ----`
  and the four verdicts quoted verbatim above, with their reading lists and the
  `n=3 m=2 X=(1,1,2) N=2 [atmost] p=3` counterexample. Run totals: **34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**; 19/19
  invariants hold, including `atmost_nvalue contractible wrt VARIABLES`; all 11 controls
  behaved. Note four of the eleven controls (`sound+minimal`, `sound, redundant premise`,
  `unsound`, `vacuous`) are built on `atmost`'s semantics (`docs/VALIDATOR.md:245-248`), so
  the checker is known to distinguish these four verdicts on *this* constraint specifically.
- `cmp cata/atmostnvalues.tex cata/atleastnvalues.tex` → silent (identical);
  `md5sum` → both `82aa49d8a547f1a9df196c2eed408aa1`. **Measured this session**, not quoted.
- `grep -o '\\frac' cata/atmostnvalues.tex | wc -l` → 4.
- `python3 tools/mzn_coverage.py --rank --json` → `atmost_nvalue` appears in **no** tier list
  (checked against all six), and `missing_from_list` is empty — it is not a release global
  rather than an indexing error.
- `python3 tools/catalog_index.py` → `warning: UNMATCHED: 'atmostnvalues' has no
  corresponding release global`.
- `grep -n 'nvalue' CHRISTMAS_LIST.md` → 3 hits (l.96, 130, 217), **none** for
  `atmost_nvalue`. This is the evidence for `pending` rather than `no published rule`.
- `cata/atmostnvalues.tex` read, not run → the four rules and the diagnostics footer,
  including all four `(D-0009)` lines.
- `explenation generator.ml:847-850` vs `843-846` read side by side, not run → the two-token
  difference.
- `explenation generator.ml:192-200, 343-355, 357-369` read, not run → the `ap`/`nap` sign
  handling and the `rule5`/`rule6` bodies. **The cancellation trace is reasoning about that
  code, not an instrumented run**; the md5 identity is the measurement it explains.
- `explenation generator.ml:294-295, 712-715` read, not run → the two files stayed identical
  through `790bfa7`, and the footer omits its own filename by design.
- `docs/GCCAT.md:105, 120-128` read → the closure properties, the "cannot have the same
  explanation rules" argument, the `comparison swapped` note, and the fact that the derived
  wrong-side prediction is stated for `atleast_nvalue` only.
- `docs/ROADMAP.md:51` read, **before reporting** (`CLAUDE.md`, "Verify before you report") →
  W1-T5 is `TODO`; its rule numbering is stale by one and its measurements hold.
- `docs/VALIDATOR.md:186, 229-230, 231, 245-248, 279-288` read → sizes, the verdict
  definitions, the controls built on `atmost`, and the stale per-entry table.
