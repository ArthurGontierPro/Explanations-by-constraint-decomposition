# `global_cardinality_closed`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `global_cardinality_closed`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **C** (`C literature + solver-decomposes`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. Ecodes `E0`, `E3`, `E4`, `E9`; the row is shared with `global_cardinality` at `CHRISTMAS_LIST.md:127` |
| **Status** | **`partly validated`** *by a second instrument* — **4 of 5** rules **SOUND and MINIMAL** at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**; the fifth is **SOUND but NOT MINIMAL**. `make validate` cannot see this file (**W1-T18**), so this is not a validator verdict. Was `encodable today, not encoded` until session A-1 encoded it, 2026-09-22 |
| **Generated** | **5** rules in `cata/global_cardinality_closed.tex` — **new 2026-09-22** (session A-1), from generator value `gccc`: `gcc`'s four plus the one that *is* closedness |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `global_cardinality_closed` entry, in scope or out: `validator.ml`'s lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **out of reach** — inherited from [`gcc.md`](gcc.md) and *reinforced* here: there is also no generated premise on this side to compare |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `make validate`, `grep -o '\frac' cata/global_cardinality_closed.tex \| wc -l`, and this session's own exhaustive sweep over every cover subset with per-premise droppability. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Read this before the rest of the entry

**The shipped `gcc` decomposition does not cover this constraint, and
[`catalog/gcc.md`](gcc.md) says so in as many words.** That entry's "What this catalog entry
actually covers" paragraph reads: the generator's decomposition is the **unrestricted** form over
a value range `[1,m]` with one occurrence variable `O_t` per value — counts as free variables,
no `low`/`up`, no `closed` — and "the MiniZinc variants `_closed`, `_low_up`,
`_low_up_closed` are **not** covered by this entry".

So `cata/gcc.tex`'s four rules are **not** evidence about `global_cardinality_closed`, and this entry does not
re-render them. What it establishes is the narrower thing that is true: which feature or
features of
`global_cardinality_closed` the format cannot express, and which numbered gaps those are.

## Constraint

`global_cardinality_closed(array[$X] of var int: x, array[$Y] of int: cover, array[$Y] of var int: counts)`

As `global_cardinality` — `counts[j]` is the number of `x[i]` equal to `cover[j]` — **plus
closedness: every `x[i]` must take a value that appears in `cover`.** The unrestricted form lets
an `x[i]` take a value nobody counts; the closed form forbids it.

**Provenance of the signature:** **not vendored in this repo.**
`tools/data/minizinc-2.10.1-globals.txt:65` carries the *name* only, and `docs/COVERAGE.md`
is explicit that the snapshot is names only. The signature line above is **recall and is marked
as such**; treat it exactly as [`gcc.md`](gcc.md) treats its own, which says "the signature line
above is recall; the decomposition line is a citation".

What *is* a citation is the FlatZinc-level definition of the base constraint, quoted at
`CHRISTMAS_LIST.md:127`: `fzn_global_cardinality` is
`forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)`. The list gives no
FlatZinc body for the `global_cardinality_closed` variant, so nothing is quoted for the closedness conjunct.

## Published explanation

**Citation:** Downing, Feydy, Stuckey 2012, *Explaining flow-based propagation*, CPAIOR,
LNCS 7298:146–162 — `CHRISTMAS_LIST.md:127`. The row covers `global_cardinality`, `_closed`,
`_low_up` and `_low_up_closed` together and describes the work as a generic explaining flow
propagator that explicitly replaces a specialised **gcc** propagator.

**Rule shape:** sourced into [`catalog/_literature/gcc.md`](_literature/gcc.md) by session C2.
**Nothing is restated here**; [`gcc.md`](gcc.md) renders C2's summary with its provenance tags
intact, and a second copy in this file would be a copy with the tags one step further from the
paper.

**One thing about that source does bear directly on this entry, and it is a point in this
variant's favour rather than against it.** C2's reading, carried through `gcc.md`: there is no
`gcc`-specific explanation rule in the paper at all — `gcc` is encoded as a flow network and
what is explained is the **generic** network-flow propagator, whose premises are
`⋀ ⟦f_uv ≥ l_uv⟧` over arcs leaving a cut and `⋀ ⟦f_uv ≤ u_uv⟧` over arcs entering it.
**Those `l_uv`/`u_uv` are exactly the kind of object `global_cardinality_closed` supplies** — closedness is the flow network's *sink-side* structure, the statement that every unit of flow leaving a variable node reaches a counted value.
So the published treatment is, if anything, *more* directly about this variant than about the
unrestricted form the generator ships. That does not make it comparable; see Calibration.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:127`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The row's
solver cell reads `decomp **[G]**` and covers all four `global_cardinality` names at once, so
this table is the *family's* support, not a separate measurement for `global_cardinality_closed`. That
combination — published literature and Chuffed still decomposing — is what puts the whole row
in tier C.

## Decomposition used here

**Generator value:** `gccc`, `explenation generator.ml:1285`.
**Emitted by:** `explainall [xac;ngbc] gccc "cata/global_cardinality_closed.tex"`, line
**1535** — with `gcc`'s own two seeds, unchanged.

| ctr | schema | meaning | from |
|---|---|---|---|
| 1 | `rule1` | `X_i = t ⇔ B1_{i,t}` (AC) | `gccn`, verbatim |
| 2 | `rule6` | `∑_i B1_{i,t} ≥ p ⇔ B2_{t,p}` | `gccn`, verbatim |
| 3 | `rule1` | `O_t ≥ p ⇔ B2_{t,p}` (BC) | `gccn`, verbatim |
| 4 | `rule1` | `X_i = t ⇔ B5_{i,t}` (AC) | **new — a second reification of the same literal** |
| 5 | `rule4` | `⋁_{t ∈ cover} B5_{i,t}` | **new — closedness** |

### The prescription in this entry did not terminate, and why

The 2026-09-21 version of this file said, under Status, "the `gccn` value unchanged, plus one
`Decomp (_, rule4, …)` over the **`B1`** family whose value index ranges over
`DPar ("cover", D 2)`, and one `explainall` line". **Written exactly like that, the generator
runs forever** — killed after 150 s, with a 0-byte `.tex` that `open_out` had already created.

The cause is a property of `find`, not of this constraint, and it is new to the catalog:

> With `B1` in **three** constraints, `rule4`'s surviving branch in ctr 4 calls `napprim`, which
> builds `¬B1` with a **primed value index** `t'`. That event is not in the chain `ch`, because
> `inl` compares *whole events* and a primed index list is structurally new. `find` re-enters
> ctr 2, whose `rule6` branch calls `apprim` and primes the **position** family instead, giving
> `B1_{i',t'}` — also new. The two constraints alternate, priming a different family each time,
> and the chain never repeats. **Cycle detection is by event equality, so an infinite path of
> pairwise-distinct events is invisible to it.**

**The repair is one line and is not a language change.** Give the closedness clause its own
reification `B5` of the same solver literal — exactly as `elem` gives `B1`/`B2`/`B3` to three
different globals. `B5` appears only in ctrs 4–5, so the loop cannot form: from `B5` the only
other constraint is a `rule1` that terminates in an `X` literal. Mathematically nothing changed
(`B1` and `B5` are the same boolean) and both wash out of the printed rules.

**Historical, kept: the two values this family already had.** `explenation generator.ml` defines
two and neither is this constraint: `gcc` at line **813** (`rule1` + `rule7`, a Boolean sum `=`,
with no occurrence variable) and `gccn` at line **827** (`rule1` → `rule6` → `rule1`, the
occurrence-variable channel). Both encode the **unrestricted** form. Nothing emits `gcc`;
`cata/gcc.tex` comes from `gccn`.
The only emitting call for the family used to be line **882**,
`explainall [xac;ngbc] gccn "cata/gcc.tex"`; there are now two.
**Spec:** none — there is no `decomps/global_cardinality_closed.md`, and there is no `decomps/global_cardinality.md`
either. The nearest relative is `decomps/count.md` (`count(x, v, c)`, i.e. `gcc` at a single
value), which [`gcc.md`](gcc.md) already names.

[`gcc.md`](gcc.md)'s **Decomposition used here** section renders `gccn`'s three steps and the
W1-T9 `pointp` repair in full; they are not copied here. What matters for this entry is the one
feature of `global_cardinality_closed` that has no encoding, and that is the Status section below.

## Scope of this entry

**Events the generator was asked to explain:** **four** — `X_i = t`, `X_i ≠ t` from `xac`, and
`O_t ≥ p`, `O_t < p` from `ngbc`, i.e. exactly the base's four. **Closedness adds no variable
and therefore no fifth event**; it restricts which assignments are legal, not which literals
exist, so it shows up as an extra *candidate* rather than an extra question. The 2026-09-21
version of this section predicted precisely that, and it was right:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | **2** | **2** | none |
| `X_{i} \neq t` | 2 | **1** | `F` 1 |
| `O_{t} \geq p` | 1 | **1** | none; binds `i` twice (D-0009) |
| `O_{t}<p` | 1 | **1** | none; binds `i` twice (D-0009) |

Beside [`gcc`](gcc.md)'s footer, which has **1** candidate on each of the first two events:
closedness contributes exactly one extra candidate to `X_i = t` (which becomes a rule) and one
to `X_i ≠ t` (which is `F` and is discarded — `⋁_{t ∈ cover} B5_{i,t}` is not a reified
constraint, so "this clause is false" is not a fact anything can explain; the same discard
[`member`](member.md) and [`alldifferent`](alldifferent.md) show).

## Generated rules

`grep -o '\frac' cata/global_cardinality_closed.tex | wc -l` → **5**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `∀i'≠i: X_{i'} ≠ t`, `O_t ≥ p`  ⊢  `X_i = t` | **SOUND**, **MINIMAL** |
| 2 | `∀t'≠t ∈ cover: X_i ≠ t'`, `t ∈ cover`  ⊢  `X_i = t` | **SOUND**, **NOT MINIMAL** |
| 3 | `∀i'≠i: X_{i'} = t`, `O_t < p`  ⊢  `X_i ≠ t` | **SOUND**, **MINIMAL** |
| 4 | `∀i: X_i = t`  ⊢  `O_t ≥ p` | **SOUND**, **MINIMAL** |
| 5 | `∀i: X_i ≠ t`  ⊢  `O_t < p` | **SOUND**, **MINIMAL** |

**Rules 1, 3, 4 and 5 are [`gcc`](gcc.md)'s, from the same derivations.** Rule 2 is the entry:
it is the whole content of `closed`, and it is the only rule in the catalog that reasons across
the *value* family for a single variable rather than across the *position* family.

### How the verdicts were obtained

**This session's own sweep, not `make validate`.** Exhaustive enumeration of every non-empty
`cover ⊆ [1,m]` and every `X ∈ cover^n`, for every `n, m ∈ {1,2,3,4,5}` — **`n = 1` included**.
Free indices `i, p ∈ [[1,n]]` and `t ∈ [[1,m]]`.

**0 counterexamples on all five rules at every size swept.** Firings in file order at
`n,m ≤ 4`: **1513 / 4462 / 682 / 490 / 6748**; at `n,m ≤ 5`:
**27513 / 86787 / 3552 / 1935 / 166908**; at `n = 1` alone: **129 / 129 / 444 / 129 / 444**
firings, **0** failures.

**Four minimal, one not — and the flag is on the new rule.** Rule 2's second premise
`t ∈ cover` is **droppable**: given the first premise and closedness, `X_i` lies in the cover
and differs from every *other* member, so `t ∈ cover` follows, and the rule stays sound with the
**same 86787 firings**. This is the same redundancy [`at_most`](at_most.md) reports for its
`i ∈ S` — a containment conjunct appended by the index machinery rather than asserted by the
decomposition — and it is reported, not hidden. Dropping the *first* premise fails 243306 times,
so that one is needed.

**On the two D-0009 flags.** Rules 4 and 5 bind `i` twice. Inherited from [`gcc`](gcc.md)
verbatim, where the identical pair carries the identical flag; both bindings are the same
`∀i ∈ [[1,n]]` over the same set, so the readings coincide and the sweep is unambiguous.

## Status

**`partly validated`** — **4 of 5** rules sound and minimal, **1** sound and **not** minimal.

**Two qualifications this status needs, both required by `catalog/README.md`:**

1. **It is not a `make validate` verdict.** That legend value is written for the validator's
   output, and the validator cannot see this file (**W1-T18**). The verdicts come from a sweep
   written for this entry, over a wider range than the validator's (`{1,…,5}` rather than
   `{2,3,4}`, `n = 1` included).
2. **The non-minimal rule is the new one**, and its redundant conjunct is the index machinery's,
   not the decomposition's. See "How the verdicts were obtained".

**And the entry's own prediction did not survive contact with the generator.** The
prescription written here on 2026-09-21 was correct about the *schemas* and hangs the generator
when run; see "Decomposition used here" for the non-termination and its one-line repair. That
is the second time in this session's slice that `encodable today, not encoded` turned out to be
true of the vocabulary and silent about what happens when you run it — [`count`](count.md) is
the other.

**Two sobering precedents were named here in advance, and here is how they turned out.** This
entry warned that "`among` got two rules from G8's closure and both are measured **UNSOUND**".
That did not repeat: all five rules here are sound, and the difference is exactly the one
`among`'s own caveat names — `among`'s count variable is channelled nowhere (**G5**), while this
entry inherits `gccn`'s working occurrence channel. The other warning — that Calibration stays
`out of reach` — **does** hold, unchanged, below.

**Historical, kept.**

**This status changed on 2026-09-22.** The previous one — `nothing generated — blocked on G8` —
is retired because G8 closed that day (session G-1, commits `4547daf` and `1e747ee`), and this
entry had already argued that G8 was *the whole* of the difficulty. That argument is quoted
below and it is now an argument for the new status rather than the old one. There is no gap left
to name, which is the legend condition `catalog/README.md` attaches to this value.

**What the block was.** The one feature this variant adds is a disjunction over a value
*subset*. Closedness is `∀i: ⋁_{t ∈ cover} B1_{i,t}` — mechanically a `rule4` disjunction over
the value family, a schema the generator already has and already uses (`regular`). What it did
not have was a way to say `t ∈ cover` when `cover` is a proper subset of the printer's value
range: **G8** was "`ind_set` names only whole predefined ranges — no subrange, no exclusion"
(`docs/DECOMP_FORMAT_NOTES.md:76`).

**Why it is gone.** `ind_set` now carries four further formers (`explenation generator.ml:48-52`)
and two of them write exactly this set. `DPar (name, parent)` names a parameter subset and
prints its own containment — `"cover,~cover \\subseteq \\llbracket1,m\\rrbracket"`
(`:536`) — which is the faithful reading of MiniZinc's `cover` argument, a parameter array of
covered values. `DSub (parent,a,b)` would write it instead as a literal subrange if an instance
warranted one (`:534`). Either is admitted by `ind_set_defined` (`:520-525`), and admitted
*without* relaxing W1-T2: these formers define themselves by being printed, so they are not
`D_4`. `D of int` beyond 3 and `D2` are untouched and still refused, which is why `range`,
`roots`, `regular` and `table` still emit nothing.

**And the degenerate case, which is why G8 was the whole of it.** If `cover` is the entire value
range `[1,m]`, closedness is vacuous and `global_cardinality_closed` *is* `global_cardinality` —
the shipped `gccn` would already be it. Everything separating this entry from [`gcc.md`](gcc.md)
sat in the one construct G8 named.

**What would have to be written** *(and it was, 2026-09-22 — with one correction: the clause
must hang off its own reification `B5`, not off `B1`, or the generator does not terminate)*.
The `gccn` value at `explenation generator.ml:909` unchanged,
plus one `Decomp (_, rule4, …)` over the `B1` family whose value index ranges over
`DPar ("cover", D 2)`, and one `explainall` line. `oni`/`ont` and their set-taking siblings
`oniin`/`ontin` already accept an `ind_set` argument, which is the interface `at_most`
(`:994-995`) and `among` (`:942-943`) use. **Nothing was run**: no value was authored, no
artifact produced, no rule of this constraint seen or judged. Two sobering precedents apply and
neither is predicted away here — `among` got two rules from G8's closure and both are measured
**UNSOUND**, and this entry's Calibration below stays `out of reach` for reasons G8 never
touched.

This is on top of, not instead of, everything that already blocks the base entry from reaching
the published rule: `gcc.md`'s own Gaps table lists G1, G4, G11 and G12/G13, and its calibration
is `out of reach` for reasons G8 does not touch.

Nothing here is validated, flagged or refuted *by `make validate`*: it does not scan `cata/`,
and the 2026-09-22 run's totals (**34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
flagged; 4 rules in 5 entries out of scope**) contain no line for this name. The verdicts above
are a second instrument's.

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.**

Two independent reasons, and the first is the one that would survive even if the second were
fixed:

1. **Structural, inherited from [`gcc.md`](gcc.md) and unchanged by this variant.** The
   published premise is indexed by "the arcs crossing the cut `C`", where `C` is the set of
   nodes searched for an augmenting path or an SCC of the *residual* graph. The printer
   quantifies over `[1,n]`, `[1,m]` and an undefined `D_k` beyond (`CLAUDE.md`, "Traps"); `C` is
   the output of a graph algorithm run at propagation time. `gcc.md` gives three such obstacles
   and calls each independently fatal. **None of them is about the missing bounds**, which is
   precisely why adding the bounds would not close the comparison.
2. **There is no premise on this side.** Zero generated rules means nothing to place in an
   implication order even if (1) were resolved.

**And this entry sharpens `gcc.md`'s own prediction, which is the reason to say it here.** That
entry records, as its settled reading of C2's sourcing: "the constraint mismatch is real (the
paper's network carries cardinality *bounds*, this decomposition has none) but it is not the
binding reason — the binding reason is structural, and **it would still hold if the bounds
were added**." `global_cardinality_closed` is the constraint that *has* the bounds. So the prediction is now
attached to the name it was about, and it remains a prediction rather than a measurement,
because nothing is generated here to test it against. **`E4` is necessary but not sufficient**
(`gcc.md`, from C2): counting across sums would reach the cardinality literals; it would not
produce a cut of a residual graph.

**Not `no published rule exists`, and not `incomparable`.** A paper is cited on this row, so the
first is false; and `incomparable` requires both sides expressible in a common vocabulary, which
`gcc.md` establishes is not the case. `out of reach` is a first-class verdict (D-0013), not a
failure to compare.

## Gaps

| gap | what it blocks here |
|---|---|
| **`G8`** | **CLOSED 2026-09-22** (`4547daf`, `1e747ee`), and **spent 2026-09-22** by this entry. It was the binding one and the only one unique to this variant: `ind_set` named only whole predefined ranges, so `⋁_{t ∈ cover} B1_{i,t}` had no encoding. `DPar ("cover", D 2)` now writes it and the shipped rule 2 prints it as `t' ∈ cover, cover ⊆ [[1,m]]`. `docs/DECOMP_FORMAT_NOTES.md:76` still lists this gap as open; that file is not this session's to edit |
| — (unnumbered, new 2026-09-22) | **`find`'s cycle detection cannot see an alternating-prim loop.** Putting a second clause on an *already reified* family makes `apprim` and `napprim` alternate between the position and value families, so every event on the path is structurally new and `inl` never matches. The generator does not terminate and writes a 0-byte file. Worked around here by a duplicate reification (`B5`); **not fixed**, and it will bite the next entry that hangs a clause off a shared auxiliary. It is a **rule-engine** defect, not a format gap |
| `G1` | inherited from [`gcc.md`](gcc.md): a bare integer threshold cannot reach the printed rule. Not binding *here* — `_closed` adds no threshold — but it still blocks the family's `low`/`up` siblings |
| `G12`/`G13` | inherited: `length(xs) >= sum(count)` sums *integer* variables, a fourth kind of schema (E9, D-0011) |
| — | the published flow rule is blocked by **no gap on this list**: its premises are indexed by a run-time graph cut, so **E4 is necessary but not sufficient** (Calibration, from C2 via `gcc.md`) |

Extensions: **E0** for `_low_up`'s shape, **E3** + **E9** for the full form, **E4** for the flow
explanation — `CHRISTMAS_LIST.md:127`, with the E3→E9 sharpening at **D-0011** (the trailing
`sum(count)` is over *integer* variables). E4 carries the calibration caveat above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

### 2026-09-22 (session A-1) — what changed

- `explenation generator.ml` edited (this session owns it): decomposition value `gccc` at line
  **1285**, `caveat` block and `explainall` call at **1535**, plus a source comment recording
  the non-termination and its repair. Seeds unchanged — `xac` and `ngbc` are `gcc`'s own. Run
  under OCaml 5.1.1 in the `baguette` switch; exit 0, empty stderr;
  `cata/global_cardinality_closed.tex` produced and committed.
- **The specced authoring was written first, run, and killed after 150 s** with a 0-byte `.tex`.
  That is the measurement behind the non-termination finding; it is not an inference from the
  code.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, no `FAIL`;
  every pre-existing non-orphaned `cata/*.tex` byte-identical, orphan set unchanged. The warning
  census did **not** move for this entry (0 / 6 / 41 / 66 before and after) — `gccc` introduces
  no new constructor site that `span` had not already introduced.
- `make validate` (run 2026-09-22, redirected then grepped) → unchanged totals, and it names no
  entry of this name — W1-T18.
- An exhaustive sweep over every non-empty `cover ⊆ [1,m]` and every `X ∈ cover^n`, for every
  `n,m ∈ {1,2,3,4,5}`, `n = 1` included, with per-premise droppability. Written and run by this
  session; all counts quoted from the run.
- `grep -o '\frac' cata/global_cardinality_closed.tex | wc -l` → **5**.
- Line numbers re-checked by `grep -n` after the final edit (W1-T14). **The 2026-09-21 numbers
  below have moved**; they are left as written and dated.

### 2026-09-21 — the original entry

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `global_cardinality_closed` in
  `C literature + solver-decomposes`, ecodes `E0`, `E3`, `E4`, `E9`, `CHRISTMAS_LIST.md` line 127,
  section `2. Counting and cardinality`.
- `make validate` (run 2026-09-21, redirected to a file then grepped, per `CLAUDE.md` "Verify
  before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==`
  and `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. **No line mentions
  this name**, which is the measurement behind the **Validator** row.
- `ls cata/` → 16 `.tex` files; `global_cardinality_closed.tex` is not among them.
- `grep -n 'explainall' 'explenation generator.ml'` → 15 emitting calls, lines 879–893; the only
  one for this family is line **882**, `explainall [xac;ngbc] gccn "cata/gcc.tex"`.
- `grep -n '^let gccn\|^let gcc ' 'explenation generator.ml'` → `gcc` at **813**, `gccn` at
  **827** (both re-measured today; they match `gcc.md` and are recorded because line numbers in
  this repo rot).
- `grep -n 'ind_set_defined' 'explenation generator.ml'` → line **459**,
  `let ind_set_defined s = match s with D 1 | D 2 | D 3 -> true | D _ -> false | D2 _ -> false`.
- `grep -n 'sommes multiples' 'explenation generator.ml'` → lines **355, 369, 383** (see the
  discrepancy note below).
- `CHRISTMAS_LIST.md:127` read → the citation, the solver cells, the E-route and the
  `fzn_global_cardinality` body quoted above.
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `catalog/gcc.md` read, not run → the coverage disclaimer, the decomposition chain, the
  `out of reach` verdict and its three obstacles, and the "would still hold if the bounds were
  added" prediction. **No statement about the Downing et al. paper originates in this file**;
  every one is C2's, via `gcc.md`, with its tags left where they are.
- `tools/data/minizinc-2.10.1-globals.txt:65` read → the name and the release it ships in.
- **Not fetched, not read:** any paper. No web access was used.
- **The G8 attribution and the degenerate-case argument are reasoning, labelled as such in
  place.** They are read off `docs/DECOMP_FORMAT_NOTES.md:76`, `explenation generator.ml:459` and
  the semantics of closedness; no code was run and no rule was generated to check them.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **Two in-repo line numbers for the `failwith "sommes multiples pas encore implémentés"`
   site, and both are wrong.** `docs/DECOMP_FORMAT_NOTES.md` says "generator lines 177-219" and
   `decomps/_shapes-ext.md` says "source l.320/334/348". Measured today with
   `grep -n 'sommes multiples'`: **355, 369, 383**. The gap (G4) is unaffected; only its pointers
   have rotted.
2. **There is no `decomps/global_cardinality_closed.md`**, nor any `decomps/` spec for the base
   `global_cardinality`. [`gcc.md`](gcc.md) already records the second as "noted, not fixed"; the
   first is recorded here for the same reason. `decomps/count.md` is the nearest relative
   (`count(x, v, c)` is `gcc` at a single value) and says nothing about closedness.
