# `among`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `among`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` |
| **Status** | `flagged` — **2 rules, both `UNSOUND`.** See the warning immediately below |
| **Generated** | **2** rules in `cata/among.tex` — back from 0, as of 2026-09-22 |
| **Validator** | out of scope, and its reason string is now stale. My `make validate` (2026-09-22): `cata/among.tex (2 rules, UNPARSED: index set: s)`, reason `index set D_4 is never defined by the printer (W1-T2), AND among's count variable appears in no atom, …`. **There is no `D_4` in the artifact any more**; the second half of that reason is the half that still holds |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:129` records `none` |
| **Last measured** | 2026-09-22, `make check`, `make validate`, `grep -o '\frac' cata/among.tex \| wc -l`, and reads of `cata/among.tex` and `explenation generator.ml`. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

> ## ⚠ Both shipped rules are unsound
>
> `cata/among.tex` contains **two rules and both of them are unsound**. Measured by exhaustive
> check over all stores at `n,m ≤ 4` and all `s`: **rule 1 fires in 3374 cases and fails in all
> 3374**; **rule 2 fires in 16832 cases and fails in 4462**. Do not use either. They are
> flagged in the artifact's own `%% CAVEAT` footer — the loud-failure behaviour W1-T3
> established — but a reader of the catalog must not have to open the `.tex` to find that out,
> which is why this warning is above everything else in the entry.
>
> **The two figures above are *not* validator verdicts.** `make validate` reports this entry
> out of scope and judges nothing. They are **G-1's own exhaustive check**, carried into the
> artifact's footer by the generator's `caveat` mechanism and quoted from there.

**And the cause is `G5`, not `G8`.** That distinction is the point of this entry. `G8` — the
gap that used to empty this file — is closed: the value set `s` is now sayable and prints.
Closing it is what let these two rules be emitted at all. It could not make them sound,
because what is unsound about them was never the set: ctr 3 channels `among`'s count variable
nowhere, so any rule this decomposition can state is a rule about `X` alone, and `among`
restricts `X` only *jointly* with its count. **A gap being closed is not a rule being
sound, and this entry is the standing example.**

## Constraint

`among(var int: n, array[int] of var int: x, set of int: v)`

`n` is the number of indices `i` with `x[i] ∈ v`.

**Provenance of the signature:** not vendored in this repo. `tools/data/minizinc-2.10.1-globals.txt:23`
carries the *name* only. The signature line above is copied from `decomps/among.md`
("Signature", which spells the parameter set `s`), which is itself recorded there without a
citation; treat it as recall, not as a citation. What is quotable in-repo is
`CHRISTMAS_LIST.md:129`, which gives literature, solver and route and no signature.
**The generator spells the set `s`**, and so does the printed rule; `v` and `s` are the same
argument under two names.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:129` reads
`| `among` | none | decomp | **E0** — already in `cata/among.tex` |` — the `Lit.` column is the
literal string `none`.

**Rule shape:** there is nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only, and no file for `among` is expected, because the index records no
paper to make one from.

This is a **tier A** constraint in the ranking's own words — `A no-literature +
solver-decomposes` — which is the tier where a derived schema would be the *only* schema. That
is what makes two unsound rules worth reporting loudly rather than quietly deleting.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | absent (no `[C]`, no `[C✗]`) |

Source: `CHRISTMAS_LIST.md:129`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**Generator value:** `among`, `explenation generator.ml:942-944` (re-measured today; this entry
previously cited `:851-853`).
**Emitted by:** `explainall [xac] among "cata/among.tex"`, line **1048**, under a
`caveat := [...]` block at **1037-1047** whose text the artifact reproduces verbatim.
**Spec:** `decomps/among.md` (shape **S3** in `decomps/_shapes.md`)

```ocaml
Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule4, [Decomp_devent (true, (B 1), id, ontin (DPar ("s",D 2))); Reified_devent (true, (B 2), id, t_out)]);
Decomp (3, rule7, [Decomp_devent (true, (B 2), id, oni)])
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i = t`, arc consistency: the shared per-`(i,t)`
  channelling grid that `gcc` and `nvalue` also use.
- **step 2, `rule4`** — a disjunction over the *parameter set*: `B2_i ⇔ ⋁_{t ∈ s} B1_{i,t}`,
  i.e. "`X_i` takes a value in `s`".
- **step 3, `rule7`** — a Boolean sum with `=`: `Σ_i B2_i` against the count.

**What changed on 2026-09-22.** Step 2's value set used to be `D 4` — an anonymous
per-decomposition counter that the printer could not define and W1-T2 refused, which is why
this file shipped with no rule at all. It is now `DPar ("s", D 2)`, a **named parameter
subset**, which prints its own containment (`s,~s \subseteq \llbracket1,m\rrbracket`) and is
therefore accepted by `ind_set_defined` (`explenation generator.ml:520-525`) without relaxing
W1-T2: `D of int` beyond 3 and `D2` are still refused, which is why `table`, `regular`, `roots`
and `range` still emit nothing. That is **G8**, closed, and the generator's own comment at
`:933-941` says in terms that it makes the set sayable and leaves the rules as they were.

**Step 3 is unchanged and is where the entry's whole problem lives.** It is a *single*
`Decomp_devent` with no `Reified_devent`, the same "implicit constant" shape `alldifferent`
uses for its own `≤ 1`. So (a) the threshold never reaches the page — `rule5/6/7` take the
`Decomp` as their `c` argument, and nothing here supplies a `DCard` the way `atmost` now does
(**G1**, `docs/DECOMP_FORMAT_NOTES.md:10`); and (b) `reified_devent` returns the placeholder
`T` for a constraint carrying none, so the branch that would *conclude* something about `n`
never fires (**G5**, `docs/DECOMP_FORMAT_NOTES.md:61-70`, and `decomps/among.md`'s closing
"Finding"). `nvalues` (`explenation generator.ml:921-924`) shows the two-step `N`-channel shape
that would fix this without an engine change.

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i = t` and `X_i ≠ t`, from the `xac`
global event (arc consistency, `explenation generator.ml:1012`). **Nothing was asked about `n`,
and nothing could have been:** there is no `N`-channel step, so the event vocabulary has no
literal to name the count with (G5 above).

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |

Both candidates now survive; `undefined index set` is **0**, where it was 1 per event before
G8. The two `REFUSED … D4 … (W1-T2)` lines this entry used to quote are gone from the artifact.

**What is *not* in the table, and cannot be.** No event mentions the count `n`, so no row for
it exists and no rule below concludes anything about it. That is the asymmetry that makes both
rules unsound: `among(n,x,s)` constrains the pair, and a rule that only ever mentions one half
of the pair has to be a tautology to be sound. Neither of these is a tautology.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/among.tex`.

## Generated rules

Rendered from `cata/among.tex` (single line, no trailing newline;
`grep -o '\\frac' cata/among.tex | wc -l` → **2**; `make check` independently prints
`ok among.tex (2 frac-occurrences)`). `~~~~` in the LaTeX separates the conjunct groups
contributed by different atomic constraints, and is rendered as separate premise lines here.

### Rule 1 — `X_i = t`

```
X_{i} ≠ t' ,  ∀t' ,  t' ≠ t ,  t' ∈ s ,  s ⊆ [1,m] ,  t ∈ s ,  s ⊆ [1,m]
X_{i} ≠ t ,  ∀t ,  t ∈ s ,  s ⊆ [1,m] ,  ∀i ,  i ∈ [1,n]
------------------------------------------------------------------------ ⊢
X_{i} = t
```

**Verdict:** `UNSOUND`.
**Measured by:** G-1's exhaustive check over all stores at `n,m ≤ 4` and all `s` — **not** by
`make validate`, which reports this entry out of scope and issues no verdict. **3374 firing
cases, 3374 counterexamples: it fails every single time it fires.**

Reading the premise explains the 100% failure rate, and this paragraph is a **reading of the
printed rule, not a second measurement**: the first group says `X_i` avoids every `t' ∈ s`
other than `t`, the second says `X_i` avoids *every* `t ∈ s` — the two together say `X_i` takes
no value in `s` at all — and the conclusion is `X_i = t` for a `t ∈ s`. The rule also binds
the name `t` twice (once free in the conclusion, once under the second group's `∀t`), which is
the ambiguity D-0009 is about; the artifact's diagnostics do **not** flag it here.

### Rule 2 — `X_i ≠ t`

```
X_{i} = t ,  ∃t ,  t ∈ s ,  s ⊆ [1,m] ,  ∀i ,  i ∈ [1,n]
-------------------------------------------------------- ⊢
X_{i} ≠ t
```

**Verdict:** `UNSOUND`.
**Measured by:** the same exhaustive check. **16832 firing cases, 4462 counterexamples.**

Premise and conclusion are the same literal under a quantifier prefix that does not separate
them. Again: `t` is bound twice and `i` is bound twice, and nothing in the rule mentions the
count.

**Both verdicts are quoted from the artifact's own footer**, which reads, verbatim:

```
%% ARE UNSOUND, measured by exhaustive check over all n,m <= 4 and all s: rule 1 has
%% 3374 firing cases and fails in all 3374; rule 2 fires 16832 times and fails in 4462.
```

## Status

**`flagged`**

Every generated rule in this entry is flagged, and both are flagged `UNSOUND`, which is the
legend's condition for this status. Three things to keep straight:

- **The verdicts are not the validator's.** `make validate` puts this entry out of scope and
  judges nothing; the `UNSOUND` verdicts are G-1's exhaustive check at `n,m ≤ 4`, recorded in
  the artifact's `%% CAVEAT` footer. This entry says "measured", never "validated".
- **`G8` is closed and the rules are still unsound.** The previous status here was
  `nothing generated — blocked on G8`; that status is retired because the block is gone, not
  because the situation improved. Arguably it got worse: an entry that generated nothing made
  no false claim, and this one ships two.
- **The cause is `G5` — a decomposition bug, not a format gap.** Step 3 uses the single-
  `Decomp_devent` `rule7` shape, so `among`'s count variable is channelled nowhere and no rule
  concludes anything about it. `nvalues` shows the `N`-channel shape that would fix it, and it
  needs no engine change. Until that repair lands, this decomposition cannot state a sound
  non-trivial rule, because the only literals it can talk about are `X` literals and `among`
  constrains `X` only jointly with the count.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:129` gives `none` in the literature column, so there is no published shape to
compare against and no `catalog/_literature/among.md` to read. This is the verdict the
vocabulary reserves for exactly this case, and it is not a stand-in for "not compared yet": the
index was built by a full session of web research (`CLAUDE.md`, "Context budget") and its `none`
is an assertion, not a blank.

**The arrival of two rules does not move it, and would not even if a paper surfaced.**
Calibration compares premises on implication strength between *sound* rules; an unsound rule
has no place in that order, because it fires in states where the constraint does not entail its
conclusion. So this entry stands, against any future published `among` explanation, where it
stood before: nothing to compare yet, for a new reason.

## Gaps

| gap | what it blocks here |
|---|---|
| `G5` | **the binding one, and it is not a format gap.** Step 3's single-`Decomp_devent` `rule7` channels the count nowhere, so every rule is over `X` alone and both shipped rules are unsound. The repair is `nvalues`' `N`-channel, in the decomposition, not in the engine |
| `G8` | **closed 2026-09-22.** The parameter set is `DPar ("s", D 2)` and prints; the two branches this entry used to lose to W1-T2 now survive. Closing it made the rules *sayable*, not *sound* |
| `G1` | still open here: `rule7`'s comparison constant reaches no printed rule. `at_most` now carries a `DCard` threshold and `among` does not; giving it one is part of the same repair as G5 |
| `G3` | only if `among`'s general MiniZinc signature is wanted, where the channel elements may be variables rather than a parameter set. D-0003 and `decomps/among.md` both take the parameter reading, so this is not binding today |
| — (not a gap) | **W1-T18**: the validator's in-scope lists are hardcoded, so no verdict in this entry is its. Here it at least *names* the file — because `among` was already on its out-of-scope list — but with a reason string written against the pre-G8 artifact |

Extensions: **E0** (`CHRISTMAS_LIST.md:129`, "already in `cata/among.tex`" — a claim that was
false of the output from W1-T2 until 2026-09-22 and is now true of the output and misleading
about it, since the output is two unsound rules).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `grep -o '\\frac' cata/among.tex | wc -l` → **2**. (`grep -c` returns 1 for every entry —
  `CLAUDE.md`, "Traps".)
- `make check` (run 2026-09-22, redirected then grepped) → `ok among.tex (2 frac-occurrences)`,
  `GATE PASSED`. Reproducibility only.
- `make validate` (run 2026-09-22, redirected then grepped, per `CLAUDE.md` "Verify before you
  report") → in the out-of-scope block: `cata/among.tex  (2 rules, UNPARSED: index set: s)`,
  with the reason string quoted in the header table. Run totals: **34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged**; **4 rules in 5 entries out of scope** (it was
  `2 rules in 5 entries` on 2026-09-21 — the two new rules here are the difference).
- `cata/among.tex` read, not run → the two rules, the diagnostics footer and the `%% CAVEAT`
  block. **Both `UNSOUND` verdicts and both pairs of counts are quoted from that block**, which
  records G-1's exhaustive check at `n,m ≤ 4`; neither was produced by this session and neither
  is a validator verdict.
- `explenation generator.ml` read, not run: `:48-52` (the four new `ind_set` formers),
  `:520-525` (`ind_set_defined`), `:536` (`printind_set`'s `DPar` case), `:933-941` (the G8
  comment, which states in the source that the count is still unchannelled), `:942-944`
  (`among`), `:921-924` (`nvalues`' `N`-channel), `:1012` (`xac`), `:1037-1048` (the caveat
  block and the `explainall` call). All line numbers re-measured today (W1-T14).
- `CHRISTMAS_LIST.md:129` and `:106-109` read → citation row and solver legend.
- `docs/DECOMP_FORMAT_NOTES.md:10`, `:61-70`, `:87` read → G1, G5, G8 at their current lines
  (this entry previously cited `:76` for G8).
- `docs/ROADMAP.md:62` read → W1-T18, opened 2026-09-22.
- The reading of *why* rule 1 fails in 100% of its firing cases is exactly that — a reading of
  the printed premise, offered as explanation of a measurement someone else made, not as a
  measurement of its own.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`validator.ml`'s out-of-scope reason for this entry is half stale.** It still says
   `index set D_4 is never defined by the printer (W1-T2)`; there is no `D_4` in
   `cata/among.tex` any more, and the parse now stops at the *named* set `s`
   (`UNPARSED: index set: s`). The second clause — "among's count variable appears in no atom,
   so the rules constrain X alone" — is still exactly right, and is the same finding G-1's
   caveat reaches from the other side. Whoever owns `validator.ml` under W1-T18 should fix both
   at once.
2. `decomps/among.md` states "`cata/among.tex` contains four `\frac{...}` rules and every one
   concludes `X_i=t` or `X_i \neq t`". Measured today: **2** rules. The second half is right;
   the count has now been wrong in three different directions (4 in the spec, 0 after W1-T2,
   2 today).
3. `decomps/among.md` cites the decomposition at "generator lines 418-420" and the E-code at
   `CHRISTMAS_LIST.md:126`. Both stale: the value is at **942-944** and line 126 is a
   table-separator row; the `among` row is **129**.
4. `docs/DECOMP_FORMAT_NOTES.md:61-64` (G5) cites "generator lines 418-420" and "generator lines
   406-409" for `nvalues`; measured today the values are at **942-944** and **921-924**.
5. **Two different pre-W1-T2 rule counts for this entry**, recorded when it held 0 rules and
   left unresolved: `docs/VALIDATOR.md:329` says `among` held **3** rules, `docs/ROADMAP.md:48`
   books the W1-T2 change as `among 2→0`. Neither number was re-measured then or now — the
   rules in the file today are not those rules, since the set they quantify over changed.
