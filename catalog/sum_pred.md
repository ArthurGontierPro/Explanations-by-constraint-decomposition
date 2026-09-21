# `sum_pred`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `sum_pred`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E9` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | **`encodable today, not encoded`** under reading (a) — measured; `nothing generated — blocked on G14` under reading (b). See Status |
| **Generated** | no generator entry — there is no `cata/sum_pred.tex`. The orphan [`cata/sum.tex`](sum.md) is the nearest artifact and is not this constraint |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `sum_pred` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:213` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `git show 3e4f17d`, and a **scratch generator run** (below) |

## Constraint

**No signature is asserted here, and the reason is load-bearing rather than procedural.**
`sum_pred` is not vendored: `tools/data/minizinc-2.10.1-globals.txt:122` carries the *name*
only, and `CHRISTMAS_LIST.md:213` gives literature, solver and route and no signature.
`decomps/sum_pred.md` records two readings and says which to settle first:

- **(a) plain reading** — a sum of an array of integer variables against a bound or a variable
  total, `∑_{i∈[1,n]} X_i = S`;
- **(b) selected-index-set reading** — a decision variable `I` selects which index set the sum
  ranges over, `∑_{j ∈ s[I]} c_j = S`.

**The two readings have different gaps**, which is why the spec recorded both, and this entry
keeps them apart throughout. Whoever pins the signature from the MiniZinc library settles half
of this page.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:122`.
`CHRISTMAS_LIST.md:213` files it under section `11. Maths and misc`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:213` reads, verbatim:

> none

**Rule shape:** nothing to state — no `catalog/_literature/sum_pred.md`, no paper fetched, no
web access.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:213`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21. The machine-filled stub read this correctly.

**Read that row for what it is.** `catalog/sum.md` makes the point and it applies here: a
linear sum is a primitive in every LCG solver in the legend, so the empty `[G]`/`[C]` cells
record the index's scope — *globals* — not an absence of explaining propagators in the world.

## Decomposition used here

**Generator value:** none today. **Emitted by:** nothing.
**Spec:** [`decomps/sum_pred.md`](../decomps/sum_pred.md); shape **S12** in
`decomps/_shapes.md` ("flat sum over integer-valued variables").

### The conflict this entry exists to settle

Two in-repo statements disagree about what a sum of integer variables costs.

1. **`decomps/sum_pred.md:26-34`** prices reading (a) at **G11 + G12 + G13** and concludes E9 is
   unbuilt. Its route: reify `B_{i,t} ⇔ X_i = t` on the **AC** grid, then form
   `∑_i ∑_t t · B_{i,t} = S`. That needs coefficients (G11), a schema that adds values rather
   than counting Booleans (G12) and an integer-valued auxiliary (G13).
2. **[`catalog/sum.md`](sum.md)** (session E1, 2026-09-21) recovered the deleted producer of
   `cata/sum.tex` from git and read it as an **order encoding over a BC channel**, needing
   "neither a weighted sum nor an integer-valued schema".

### Which the evidence supports: **(2), for reading (a), and it is now measured rather than read**

**First, the recovered source is where E1 says it is.** `git show 3e4f17d:'explenation
generator.ml' | sed -n '361,363p'` (run 2026-09-21) returns the `sum` value, and line 388 of the
same revision is `let _ = explainall [xbc;nbc] sum "cata/sum.tex"`. Both verified by this
session independently of E1's report.

**Second, the reading of it is right.** The three steps are `rule1` (BC) `B1_{i,t} ⇔ X_i ≥ t`,
`rule1` (BC) `B3_p ⇔ N ≥ p`, and one `rule6` — a plain, *unweighted* Boolean sum. The arithmetic
that makes an unweighted count add up to an integer sum is `Σ_{t∈[1,m]} [X_i ≥ t] = X_i`, so
`Σ_{i,t} B1_{i,t} = Σ_i X_i`. No coefficient appears anywhere, and no schema adds values.

**Third — and this is what the conflict actually needed — the route still runs.** Transcribed
into today's first-order index operators and appended to a **scratch copy** of the generator, it
emits **4 rules for the 4 events**, exit 0. Their premises reproduce the shipped
`cata/sum.tex`'s, differing only by duplicated binders. So `rule1` + `rule6` over a BC channel
is not a 2020 curiosity that the index-propagation rewrite made unavailable: it is an
expressible decomposition of an integer sum in the generator as it stands on 2026-09-21.

**So `decomps/sum_pred.md`'s G11 + G12 + G13 is a correct pricing of the decomposition that file
chose, and an over-pricing of the constraint.** The three gaps are consequences of channelling
on `=` (the AC grid), which forces the value `t` to be reintroduced as a coefficient. Channel on
`≥` instead and the coefficient disappears into the order encoding. The E9 route code at
`CHRISTMAS_LIST.md:213` is therefore **not established as necessary** for reading (a).

### Four qualifications, because the result should not be oversold

1. **Expressible is not good.** `make validate` scores `cata/sum.tex`'s four rules **0 SOUND
   and MINIMAL, 4 flagged** — 2 `SOUND but NOT MINIMAL`, 2 `VACUOUS` (`catalog/sum.md`, my own
   run agrees: `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`). The
   order encoding buys a decomposition, not a verdict.
2. **The transcription is not unique, and the faithful one fails.** Spelled exactly as 2020 did
   it — sums on the `Decomp_devent`'s *update* with `p_out` propagating — the run raises
   `Failure "missing index set prim"` (`explenation generator.ml:204`). It emits only when the
   sums are moved to match how today's shipped `rule5/6/7` entries are written. **One authoring
   works and one does not**; that is a fact about the port, and it corroborates `catalog/sum.md`'s
   observation that the commit which deleted `sum` was the index-propagation rewrite whose own
   message warns of errors in the other constraints.
3. **Every rule the working transcription emits is flagged by the generator itself** — all four
   carry `DEFECT: … bind an index name twice … (D-0009)`, which the shipped 2020 artifact does
   not. So the port is not free even where it runs.
4. **The order encoding assumes the domain.** `Σ_t [X_i ≥ t] = X_i` holds for `X_i ∈ [1,m]` with
   `t` over the same `[1,m]` — the printer's `D 2` (`:460`). It is not a general integer sum;
   it is a sum of variables whose domain is the printer's value range. Reading (b) is untouched
   by all of this: a variable choosing the summed extent is **G14** whatever the channel is.

## Scope of this entry

**Events the generator was asked to explain:** none under this name. There is no
`cata/sum_pred.tex`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

The four events of the **scratch** transcription were `X_i ≥ t`, `X_i < t`, `N ≥ p`, `N < p`
(from `xbc` and `nbc`, `explenation generator.ml:868`, `:870`), one candidate and one rule
each, `dropped F 0, cycle 0, duplicate 0, undefined index set 0`, and a D-0009 `DEFECT` line
on every one. That is scratch output, not a catalog artifact.

## Generated rules

**None under this name.** `cata/sum_pred.tex` does not exist.

The four rules of the orphan `cata/sum.tex` are rendered, with their verdicts, in
[`catalog/sum.md`](sum.md). **They are not this constraint's rules**: `sum` is not a MiniZinc
global under any spelling (`catalog/sum.md` measured that), and whether `sum_pred` is the
constraint that artifact is about depends on the signature question above.

## Status

**Reading (a): `encodable today, not encoded`.** **Reading (b): `nothing generated — blocked on
G14`.**

Under reading (a) there is no gap to name, and that is the finding. What is absent is an
authoring: no `sum_pred` value exists in `explenation generator.ml`, no `explainall` call writes
`cata/sum_pred.tex`, and the schemas it would need — `rule1` on a BC channel and `rule6` —
exist, ship today, and were run by this session against exactly this shape, emitting four rules.
Naming a G-number here would be inventing a blocker to satisfy the legend.

`encodable today, not encoded` is the status value added to `catalog/README.md`'s legend
(`:66`) on 2026-09-21, by the concurrent session that hit the same situation with
`strictly_increasing`/`strictly_decreasing`: "the current format can already express the
decomposition, but nothing in the generator does it, so **there is no gap to name**". This is
the second kind of case for it — there the argument is a parameter shift on a validated pair,
here it is a decomposition recovered from git and re-run. **The two runs behind the claim are
in "How this entry was produced"**, and the four qualifications above are part of it: encodable
is not validated, and the one artifact this shape ever produced is `flagged` 4 of 4.

What a next session should do, in order: (1) pin the signature; (2) if it is reading (a), port
the recovered decomposition (roadmap **W1-T6**, already rescoped to "port it forward"), using
the working transcription rather than the 2020 spelling, and expect D-0009 binder defects to
need fixing before the artifact means anything; (3) if it is reading (b), the entry is G14 and
stays empty.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:213`'s literature cell is `none`. With 0 rules under this name there is also
no premise to place in an implication order. `catalog/sum.md` reaches the same verdict for the
orphan and for the same row, which is the only row either name has.

## Gaps

| gap | what it blocks here |
|---|---|
| `G14` | **reading (b) only, and binding there**: no summation over a variable-determined index set. `cumulatives` hit the same wall from the scheduling side (`docs/DECOMP_FORMAT_NOTES.md:86`) |
| `G11`, `G12`, `G13` | **not established as binding for reading (a)** — see "The conflict this entry exists to settle". They are the price of the AC-grid decomposition `decomps/sum_pred.md` chose, not of the constraint. They return the moment coefficients are real, which is [`knapsack`](knapsack.md) |
| `G2` | `var_name` (`explenation generator.ml:3`) has no letter for "this constraint's own total"; the recovered `sum` borrows `N`, which is `nvalue`'s |
| `D-0009` | not a gap but an open decision, and measured live here: all four rules of the working transcription bind an index name twice |
| — | **the domain assumption** of the order encoding (`X_i ∈ [1,m]`, `t` over the same range) is not a numbered gap and should be, or should be argued away, before an entry ships |

Extensions: **E9** — `CHRISTMAS_LIST.md:213`, verbatim: "**E9** (was E3 — D-0011)". D-0011
(`docs/DECISIONS.md:259`) defines E9 as sums of integer-valued variables, gaps G12 + G13.
**This entry does not propose changing that code** — E9 is still what an unrestricted integer
sum needs — but records that reading (a) of *this* constraint has a route that avoids it.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E9"]`, `CHRISTMAS_LIST.md` line 213,
  section `11. Maths and misc`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`, `== 2 rules in 5 entries out of scope ==`.
  No line names a `sum_pred` entry; the `cata/sum.tex` block is quoted in `catalog/sum.md`.
- `CHRISTMAS_LIST.md:213` and `:106-109` read → the cells quoted above.
- `tools/data/minizinc-2.10.1-globals.txt:122` read → the name.
- `git show 3e4f17d:'explenation generator.ml' | sed -n '355,365p;386,390p'` (run 2026-09-21) →
  the `sum` value at **361-363** and `explainall [xbc;nbc] sum "cata/sum.tex"` at **388**,
  both verified independently of `catalog/sum.md`'s report of them.
- `explenation generator.ml` read, not run: `:3` (`var_name`), `:204` (`addprim`, the
  `missing index set prim` failure), `:343-383` (`rule5`/`rule6`/`rule7` and their
  `dee::[]` match), `:460` (the three printed ranges), `:763-798` (the index operators,
  including `sumi` and `sumt`, which **survive** in today's source), `:868`, `:870` (`xbc`,
  `nbc`).
- **Two scratch generator runs, 2026-09-21.** `explenation generator.ml` copied into this
  session's scratch directory; the recovered `sum` value appended with
  `explainall [xbc;nbc] … "cata/sumrec.tex"`, run under OCaml 5.1.1 with stderr redirected.
  **(i)** the faithful 2020 spelling, `imap [sumi;sumt;forallp]` updating and `p_out`
  propagating → exit **2**, `Failure "missing index set prim"`, no file written.
  **(ii)** the same three `Decomp`s with the sums spelled as today's `rule5/6/7` entries spell
  them (`imap [sumi;sumt]` updating, `ont` propagating, the `forall`/`out` chain on the reified
  side) → exit **0**, **4** `\frac` (`grep -o '\\frac' … | wc -l`), premises matching the shipped
  `cata/sum.tex` except for duplicated binders, and a D-0009 `DEFECT` line on each of the four
  events.
- **Nothing was added to the repository.** `explenation generator.ml` is untouched, no file
  under `cata/` was written or changed, and `make check`'s goldens are unaffected. Transcription
  (ii) is this session's own authoring; the claim that does not depend on it is the reading of
  `3e4f17d:361-363`, and the claim that does is labelled as a run.
- `catalog/sum.md` and `decomps/sum_pred.md` read, not run → the two conflicting statements,
  quoted above with their line numbers.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.
  **The signature is the open item** and half this entry is conditional on it.

**Discrepancies noted, not fixed** (neither file is this session's).

1. **`decomps/sum_pred.md:26-28`'s "The second line has **no schema**" is too strong.** Over an
   AC grid it is true; over the BC order encoding a plain `rule6` suffices, and it ran today.
   The file's *own* hedge — that the signature should be settled first — is the right
   instruction and is unaffected.
2. **`decomps/sum_pred.md:27` cites `rule5`/`rule6`/`rule7` at "source l.308–350".** Measured
   2026-09-21: they are at **343**, **357** and **371**, with the three `failwith`s at
   **355**, **369**, **383**. W1-T14's rot.
