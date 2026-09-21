# `atleast_nvalue`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `atleast_nvalue`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **not ranked** — `atleast_nvalue` is a **gccat** constraint, not a MiniZinc 2.10.1 global (see below). `tools/mzn_coverage.py --rank` assigns it no tier because it is not in the release list |
| **Status** | `flagged` |
| **Generated** | 4 rules in `cata/atleastnvalues.tex` |
| **Validator** | 0 `SOUND and MINIMAL`; 1 `NOT MINIMAL`, 1 `AMBIGUOUS`, 1 `UNSOUND`, 1 `VACUOUS` |
| **Calibration** | **pending** — `CHRISTMAS_LIST.md` has **no row** for this constraint, so neither a citation nor a searched-and-empty finding exists in-repo |
| **Last measured** | 2026-09-21, `make validate` (E2's own run), `python3 tools/mzn_coverage.py --rank --json`, `python3 tools/catalog_index.py`, `cmp`/`md5sum` on the two `.tex` files |

**This entry is not settled and must not be presented as if it were.**
`cata/atleastnvalues.tex` is **byte-identical** to `cata/atmostnvalues.tex` — measured, same
md5 — although the two decompositions differ. Two constraints with *opposite* gccat closure
properties cannot have the same explanation rules, so at least one of the two files is wrong
and nothing here says which. This is roadmap **W1-T5**, open.

## Constraint

`atleast_nvalue(NVAL, VARIABLES)` — the number of distinct values taken by `VARIABLES` is
**at least** `NVAL`.

**This is a gccat constraint, not a MiniZinc global.** It does not appear in
`tools/data/minizinc-2.10.1-globals.txt`; `tools/mzn_coverage.py --rank` therefore assigns it
no tier, and `tools/catalog_index.py` reports
`warning: UNMATCHED: 'atleastnvalues' has no corresponding release global`. **MiniZinc states
the same thing through `nvalue`** — `nvalue(n, x)` with an inequality on `n`, which is
[`nvalues.md`](nvalues.md)'s entry. The catalog's coverage claim is indexed on the 118
MiniZinc globals (`catalog/README.md`, "What the catalog claims"), so **this entry is outside
that denominator and does not count towards it.**

**Provenance of the signature:** gccat, via `docs/GCCAT.md`, which records this repo's
reading of the `Catleast_nvalue` entry page (arguments `NVAL`, `VARIABLES`; the argument names
used above are gccat's). No MiniZinc signature exists to cite. The decomposition below is read
off the generator and is quotable.

## Published explanation

**Citation: none available, and that is different from "none exists".**
`CHRISTMAS_LIST.md` — the repo's literature index, covering all 118 MiniZinc globals — has
**no row for `atleast_nvalue`**, verified by `grep -n 'nvalue' CHRISTMAS_LIST.md` (three hits:
l.96, l.130, l.217, none of them this constraint). Because the index is scoped to the
MiniZinc release list and this constraint is not on it, the index never looked. So the entry
cannot say "no published rule exists"; it can only say **nothing has been searched**.

**Rule shape:** **pending C2** — not stated here. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. This session has no web access and, per `CLAUDE.md`, does not
write a published rule shape from memory.

**What would close it:** a `CHRISTMAS_LIST.md` row for the two `*_nvalue` constraints, or an
explicit note that they are out of the index's scope. Either is a literature-session task
(C2), not this one's.

## Solver support

| | |
|---|---|
| Chuffed | **unknown** — no `CHRISTMAS_LIST.md` row |
| Geas | **unknown** |
| Choco LCG | **unknown** |

There is no row to read, and the legend at `CHRISTMAS_LIST.md:106-108` has nothing to apply
to. The nearest indexed relative is `nvalue` (`CHRISTMAS_LIST.md:130`, `decomp`), but a
solver's treatment of `nvalue` is not evidence about `atleast_nvalue` and is not presented as
such.

## Decomposition used here

**Generator value:** `atleastnvalues`, `explenation generator.ml:843-846`
**Emitted by:** `explainall [xac;nbc] atleastnvalues "cata/atleastnvalues.tex"`, line 887
**Spec:** **none** — there is no `decomps/atleast_nvalue.md`. The nearest relative is
`decomps/nvalue.md`, which specifies shape **S3** and the `p`-channel this decomposition
reuses.

```ocaml
let atleastnvalues = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
                      Decomp (1, rule1, [Global_devent (true, N, id, id, BC); Reified_devent (true, (B 4), id, id)]);
                      Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni); Reified_devent (true, (B 2), foralli, i_out)]);
                      Decomp (3, rule6, [Decomp_devent (true, (B 2), id, ont); Reified_devent (true, (B 4), imap [foralli;p_out], imap [i_out;t_out;forallp])])]
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency.
- **step 2, `rule1`** — `B4_p ⇔ N ≥ p`, **bounds** consistency (`nvalues` uses `AC` here; this
  is one of the two differences from that entry).
- **step 3, `rule4`** — `B2_t ⇔ ⋁_i B1_{i,t}`: value `t` is used.
- **step 4, `rule6`** — a Boolean sum with `≥`: `B4_p ⇔ (Σ_{t} B2_t ≥ p)`. This is the "at
  least" direction, and it is the **only** thing that distinguishes this decomposition from
  `atmostnvalues`.

**Note the channel in step 2 is `rule1`, a reified *equivalence*.** `B4_p ⇔ N ≥ p` pins `N` to
the sum from both sides, which is `nvalue`, not `atleast_nvalue`. Read strictly, the "at
least" asymmetry lives only in `rule6`'s choice of the `≥` arm of the sum, not in the channel.
This is this session's reading of the source, not a measurement, and it is recorded because it
is a candidate root cause for W1-T5 that nobody has written down.

`B1`, `B2`, `B4` wash out; only `X` and `N` literals print (D-0004).

### W1-T5: the collision with `atmostnvalues`, and why it is not an accident

**Measured.** `cmp cata/atleastnvalues.tex cata/atmostnvalues.tex` is silent; both files hash
to `82aa49d8a547f1a9df196c2eed408aa1`. All four rules and both diagnostics footers coincide
exactly.

**The two decompositions differ in exactly two tokens**, at `Decomp 3`
(l.846 vs l.850):

| | `atleastnvalues` (l.846) | `atmostnvalues` (l.850) |
|---|---|---|
| sum schema | `rule6` (Bool sum `≥`) | `rule5` (Bool sum `≤`) |
| `B4`'s reified sign | `Reified_devent (true, …)` | `Reified_devent (false, …)` |

**Those two changes cancel, and the cancellation is traceable in the code.** `rule5`
(`explenation generator.ml:343-355`) and `rule6` (l.357-369) are the same four-branch body
with the positive and negative variants interchanged in every branch — `fre`↔`fnre` and
`apforall`↔`napforall`. And `ap` (l.192-196) takes its sign from the devent's own boolean
while `nap` (l.197-200) takes its negation, so flipping `B4`'s sign interchanges what `fre`
and `fnre` produce. Two interchanges compose to the identity. Traced on both descent paths:

- **explaining an `N` event** — the traversal enters `Decomp 3` through the `B4`
  `Reified_devent` itself, so `dname de = dname re`. `rule6` with `dsign de = true = sign e`
  takes the `then` arm → `apforall`; `rule5` with `dsign de = false ≠ sign e` takes the `else`
  arm → `apforall`. Same node.
- **explaining an `X` event** — the traversal enters through the `B2` `Decomp_devent`, which
  is *identical* in both files, so `dname de ≠ dname re` and the same arm is selected in each.
  `rule6` emits `fre re` with `re`'s sign `true` → a positive `B4`; `rule5` emits `fnre re`
  with `re`'s sign `false` → `not false` → the same positive `B4`.

So the byte-identity is **not** a printer bug and **not** a coincidence: as encoded, these are
the same decomposition written two ways. Whatever "at most" is supposed to mean, this format
did not record it. *(Read off the source, confirmed by the measured md5; no code was run to
produce the trace.)*

**The generator preserves the collision on purpose.** The comment at
`explenation generator.ml:712-715` records that `write_footer` deliberately does not name its
own file, "because `cata/atleastnvalues.tex` and `cata/atmostnvalues.tex` are byte-identical
although their decompositions differ, and that collision is W1-T5's evidence." So the identity
is maintained as a visible symptom, not hidden.

### The independent evidence: opposite closure properties

`docs/GCCAT.md:120-124`, read off the two gccat entry pages:

- **`atleast_nvalue`: extensible wrt `VARIABLES`, and monotone — `NVAL` can be decreased.**
- `atmost_nvalue`: **contractible** wrt `VARIABLES`.

"Two constraints with *opposite* closure properties cannot have the same explanation rules, so
`cata/atleastnvalues.tex` and `cata/atmostnvalues.tex` being byte-identical is a defect on
catalog grounds alone — an argument independent of W0-A's validator run, which reached the
same place."

Both properties are also **machine-checked** against the validator's hand-encoded semantics,
and hold in my run: `atleast_nvalue extensible wrt VARIABLES  gccat Catleast_nvalue  ok`,
`atleast_nvalue monotone: NVAL can be decreased  gccat Catleast_nvalue  ok`. So the semantics
this entry is judged against is the right one; it is the *rules* that collide.

**Derived from the monotone property** (`docs/GCCAT.md:126-128`): the feasible set of `NVAL`
for `atleast_nvalue` is downward closed, so propagation from `X` literals can only ever
tighten `NVAL`'s **upper** bound. W1-T5 already records that the at-least rule "bounds `N`
from the wrong side" at `n = m = 2, p = 1`. My run's rule 3 counterexample is exactly that
point — see below.

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

Nothing was dropped and no branch was blocked. **All four rules carry the D-0009 flag**, which
is the worst ratio in the catalog: not one rule in this entry has LaTeX that determines what
it means. (`gcc` flags two of four; `nvalues` three of five; `alldifferent`, `allequal`,
`increasing`, `decreasing` and `element` flag none.)

Before commit `790bfa7` this entry had five rules; the `EXOR`→`EXAND` repair removed one
`UNSOUND` rule — see [`allequal.md`](allequal.md), which is where that repair is documented.
The two files stayed byte-identical through it, "so W1-T5's evidence is preserved"
(`explenation generator.ml:294-295`).

Source: the `%% generator diagnostics (W1-T3)` block at the foot of
`cata/atleastnvalues.tex`.

## Generated rules

Rendered from `cata/atleastnvalues.tex` (`grep -o '\\frac' cata/atleastnvalues.tex | wc -l`
→ 4). **The LaTeX below is identical to `cata/atmostnvalues.tex`'s; the verdicts are not**,
because the validator judges each against its own constraint's semantics. That divergence is
the sharpest available demonstration that one text cannot serve both.

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

**This rule fires, and it says nothing about `atleast_nvalue`.** Drop the two droppable
premises and what remains is `∀t' ≠ t: X_i ≠ t' ⊢ X_i = t` — **domain exhaustion**. That is
sound for *any* constraint over the value set `[1,m]`; it is not an explanation of this one.
The validator's `NOT MINIMAL` is the right flag and it understates the problem: the rule is
not merely carrying two spare premises, its entire content is the spare-free remainder, which
is constraint-independent.

**And note which universally quantified premise is alive here.** `catalog/alldifferent.md`
shows that a premise `∀i' ≠ i: X_{i'} = t` contradicts its constraint for `n ≥ 3` and can
never fire. Premise 1 here is the **opposite polarity** — `∀i' ≠ i: X_{i'} ≠ t`, every other
variable *avoids* `t` — which is satisfiable at every arity. So the `∀i' ≠ i` shape is not
dead by itself; the polarity decides, and this is the catalog's counterexample to the lazier
version of that heuristic.

### Rule 2 — `X_i ≠ t`

```
X_{i}=t' ,  ∃i ,  i ∈ [1,n] ,  ∀i ,  i ∈ [1,n] ,  ∀t' ,  t' ≠ t ,  t' ∈ [1,m] ,  t ∈ [1,m]
N<p ,  ∀p ,  p ∈ [1,n]
-------------------------------------------------------------------------------------------- ⊢
X_{i} \neq t
```

**Verdict:** `AMBIGUOUS — the .tex does not determine the rule`
**Reading(s) checked:** `5 (3 sound, 2 unsound)` — `forall t' ; forall p` sound,
**`forall t',exists i ; forall p` UNSOUND**, **`exists i,forall t' ; forall p` UNSOUND**,
`forall t',forall i ; forall p` sound.
**counterexample (unsound reading):** `n=2 m=2 X=(1,2) N=0 [atleast] t=1,i=1`
**Also flagged by the generator:** D-0009.
`cross-check: store sweep agrees with singleton reduction`

**The byte-identical rule in [`atmostnvalues.md`](atmostnvalues.md) is `VACUOUS`, not
`AMBIGUOUS`.** Same premises, same conclusion, different constraint — and against
`atleast_nvalue` two of the five readings are refutable while against `atmost_nvalue` none of
them can fire at all. One LaTeX string, two incompatible characterisations.

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
**counterexample:** `n=2 m=2 X=(1,2) N=0 [atleast] p=1`
**Also flagged by the generator:** D-0009.

**This is the "wrong side" defect, and gccat predicted it without running anything.**
`atleast_nvalue` is monotone with `NVAL` decreasable, so its feasible `NVAL` set is downward
closed and `X` literals can only tighten `N`'s **upper** bound. This rule concludes a
**lower** bound, `N ≥ p`. The counterexample is at `n = m = 2, p = 1`, exactly where W1-T5
records the failure (`docs/GCCAT.md:126-128`). `docs/VALIDATOR.md:229-230` names this verdict
class `UNSOUND(firing)`.

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
shape as [`nvalues.md`](nvalues.md)'s rules, and the same `∀i` printed three times over one
literal.

### Which rules can fire

Rule 1 fires and is constraint-independent. Rule 2 fires under two of its five readings and
is unsound under both of them. Rule 3 fires only under its one unsound reading. Rule 4 never
fires. **No rule in this entry both fires and is a sound statement about
`atleast_nvalue`.**

## Status

**`flagged`** — `catalog/README.md`'s legend: every generated rule is flagged.

Established, at `n, m ∈ {2,3,4}` with `N ∈ [0,n]` and the store sweep at `n, m ≤ 3`
(`docs/VALIDATOR.md:186`): one rule sound-but-redundant, one ambiguous with a refutable
reading, one unsound on its only firing reading, one vacuous. Both soundness methods agree on
all four. The hand-encoded semantics passes its gccat cross-checks
(`atleast_nvalue extensible wrt VARIABLES`, `atleast_nvalue monotone: NVAL can be decreased`,
`nvalue(X,k) => atleast_nvalue(X,k)`, all `ok`).

**Not settled, and this entry does not pretend otherwise:**

- **Which of the two files is wrong.** Both are candidates. The decomposition of
  `atmost_nvalue` as the polarity-dual of `atleast_nvalue` is the encoding that produced the
  collision, but nothing measured here says the `atleast` side is right.
- **Whether the `rule1` equivalence channel (step 2) is the root cause.** Recorded above as a
  reading of the source, untested.
- **Whether index hygiene (W1-T1/D-0009) would change any verdict.** All four rules are
  flagged for it, so no verdict here should be treated as final about the *intended* rule.

**`docs/VALIDATOR.md`'s per-entry table (l.279-288) is stale for this entry**: it records
`atleastnvalues | 5 | 1 NOT MINIMAL, 1 UNSOUND, 1 AMBIGUOUS, 1 UNSOUND(firing), 1 VACUOUS`.
Commit `790bfa7` removed the fifth rule. My run's four are above.

**The roadmap row's rule numbering is stale by one, and its substance is confirmed.**
`docs/ROADMAP.md:51` says "the identical text gets different verdicts (AMBIGUOUS vs VACUOUS on
rule 3), and rule 4's only firing reading is unsound in both … Against at-least it fails at
`n=m=2, p=1` … against at-most only at `p > m`." After `790bfa7` those are **rules 2 and 3**.
The measurements hold exactly: at-least's rule 3 fails at `n=2, m=2, p=1`; at-most's fails at
`n=3, m=2, p=3`, and `p = 3 > m = 2`.

## Calibration (W3-T5, D-0013)

**Verdict: pending.**

Not `no published rule`: that verdict means "`CHRISTMAS_LIST.md` records no explanation for
this constraint" (`catalog/TEMPLATE.md`'s table), and the index records *nothing at all* here,
because its scope is the MiniZinc release list and `atleast_nvalue` is not on it. A silence
that comes from not having looked is not a finding, and this catalog distinguishes the two.

Not `out of reach` either: that verdict requires a published premise that cannot be expressed
here, and no published premise is in hand.

**What is needed to lift `pending`:** a `CHRISTMAS_LIST.md` row for `atleast_nvalue` /
`atmost_nvalue` — a citation, or an explicit searched-and-empty finding, or an explicit
"outside this index's scope" — followed by a `catalog/_literature/` shape if a paper exists.
That is a C2 task.

**And calibration should not be attempted before W1-T5 closes, whatever the literature says.**
Comparing a published premise against a rule that is byte-identical to a *different*
constraint's rule would attribute the comparison to the wrong constraint. The ordering here is
W1-T5 first, C2 second, calibration third.

The one comparison available now is internal and negative: gccat's `comparison swapped` link
(`docs/GCCAT.md:105`) is described as "the only near-mechanical relation" between related
constraints' explanations, "and it is a renaming, not a derivation". The other
`comparison swapped` pair in this catalog, `increasing`/`decreasing`, is handled correctly —
two decomposition values that differ by a sign swap and produce two *different*, mirror-image
`.tex` files, both validated. Here the same relation collapsed into an identity. **Same
relation, opposite outcome**; see [`decreasing.md`](decreasing.md).

## Gaps

| gap | what it blocks here |
|---|---|
| — | **no `G`-number blocks this decomposition.** `rule1`, `rule4` and `rule6` all exist and run. W1-T5 is a *defect*, not a format gap: the encoding admitted two spellings of the same thing |
| `G2` | `var_name` is closed and `N` is the borrowed letter for this constraint's own count variable |
| `G4` | one Boolean-sum family per rule (`failwith` otherwise). Not hit — step 4 sums one family |
| — | **roadmap W1-T5** (the collision, `TODO`) and **W1-T1** (binder scope; all four rules carry the D-0009 flag) are the live blockers |
| — | **the format has no way to record an asymmetric channel.** `rule1` is a reified *equivalence*, so `B4_p ⇔ N ≥ p` pins `N` to the sum from both sides. This is not on `docs/DECOMP_FORMAT_NOTES.md`'s numbered list and is **not** proposed here as a new `G`-number — it is recorded as an observation for W2-T1, the format freeze |

Extensions: none priced — there is no `CHRISTMAS_LIST.md` row to carry an E-code. The nearest
indexed relative, `nvalue`, is **E0** (`CHRISTMAS_LIST.md:130`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/atleastnvalues.tex  (4 rules) ----`
  and the four verdicts quoted verbatim above, with their reading lists and both
  counterexamples. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope**; 19/19 invariants hold, including the two
  `Catleast_nvalue` closure checks; all 11 controls behaved.
- `cmp cata/atleastnvalues.tex cata/atmostnvalues.tex` → silent (identical);
  `md5sum` → both `82aa49d8a547f1a9df196c2eed408aa1`. **Measured this session**, not quoted.
- `grep -o '\\frac' cata/atleastnvalues.tex | wc -l` → 4.
- `python3 tools/mzn_coverage.py --rank --json` → `atleast_nvalue` appears in **no** tier list
  (checked against all six), and `missing_from_list` is empty — i.e. it is not a release
  global rather than an indexing error.
- `python3 tools/catalog_index.py` → `warning: UNMATCHED: 'atleastnvalues' has no
  corresponding release global`.
- `grep -n 'nvalue' CHRISTMAS_LIST.md` → 3 hits (l.96, 130, 217), **none** for
  `atleast_nvalue`. This is the evidence for `pending` rather than `no published rule`.
- `cata/atleastnvalues.tex` read, not run → the four rules and the diagnostics footer,
  including all four `(D-0009)` lines.
- `explenation generator.ml:843-846` vs `847-850` read side by side, not run → the two-token
  difference.
- `explenation generator.ml:192-200, 343-355, 357-369` read, not run → the `ap`/`nap` sign
  handling and the `rule5`/`rule6` bodies. **The cancellation trace is reasoning about that
  code, not an instrumented run**; the md5 identity is the measurement it explains.
- `explenation generator.ml:712-715` read, not run → the footer deliberately omits its own
  filename so the collision stays visible.
- `explenation generator.ml:294-295` read, not run → the two files stayed identical through
  `790bfa7`.
- `docs/GCCAT.md:105, 120-128` read → the closure properties, the "cannot have the same
  explanation rules" argument, the `comparison swapped` note, and the derived wrong-side
  prediction.
- `docs/ROADMAP.md:51` read, **before reporting** (`CLAUDE.md`, "Verify before you report") →
  W1-T5 is `TODO`; its rule numbering is stale by one and its measurements hold.
- `docs/VALIDATOR.md:186, 229-230, 231, 279-288` read → sizes, the `UNSOUND(firing)` and
  `NOT MINIMAL` definitions, and the stale per-entry table.
