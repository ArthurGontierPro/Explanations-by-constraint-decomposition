# `count`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `count`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | **`generated, unvalidated`** *by this catalog's instrument* — `make validate` cannot see this file (**W1-T18**). Measured by a second instrument: all **4** shipped rules **SOUND** and **MINIMAL** at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**. Was `encodable today, not encoded` until session A-1 encoded it, 2026-09-22 |
| **Generated** | **4** rules in `cata/count.tex` — **new 2026-09-22** (session A-1), and **no decomposition value was added**: the file is `gccn` with both seeds pinned to the counted value |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `count` entry, in scope or out: `validator.ml`'s lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `make validate`, `grep -o '\frac' cata/count.tex \| wc -l`, and two exhaustive assignment sweeps — one of the shipped rules, one of the S3 authoring this entry specced. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Constraint

`count(array[int] of var int: x, int: v, var int: c)` — `c` is the number of indices `i` with
`x[i] = v`. Per D-0003 the value `v` is taken as a parameter; a variable `v` is G3.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:42` carries the *name* only; the line above is
transcribed from `decomps/count.md` ("Signature"), which cites `CHRISTMAS_LIST.md` for the
parameter reading but gives the arity without a citation. **Treat the arity as recall.**
`CHRISTMAS_LIST.md:128` files it under `2. Counting and cardinality`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:128` reads, verbatim:

> none specific

**Rule shape:** nothing to state — there is no `catalog/_literature/count.md`, no paper was
fetched by this session and no web access was used. See [`at_most.md`](at_most.md),
"Published explanation", for why `none specific` yields `no published rule exists` rather than
`pending sourcing`.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:128`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** **`gccn`, `explenation generator.ml:909` — the shipped `gcc`
decomposition, unchanged and unextended.**
**Emitted by:** `explainall [xacv;ncvbc] gccn "cata/count.tex"`, line **1382**. The two seeds
are `xacv` (**1229**, `at_most`'s, which pins `X`'s value index to `{v}`) and `ncvbc`
(**1235**, this session's only new value: `gcc`'s occurrence-variable seed with its value index
pinned the same way).

**`count(x,v,c)` is `gcc` at one value, and that is the whole entry.** `gccn`'s constraint 2 is
`∑_i B1_{i,t} ≥ p ⇔ B2_{t,p}`; pin `t` to the parameter `v` and it *is* `count`'s defining
constraint, written in the `BC` (order-encoding) vocabulary the generator already uses for
every bounded variable. So this entry cost **one seed event and one `explainall` line** — no
decomposition value, no constructor, no schema, no printer case.
**Spec:** [`decomps/count.md`](../decomps/count.md); shape **S3** in `decomps/_shapes.md`
("reify-and-count with a **channelled** count variable").

### The S3 chain this entry specced — written, run, and measured mostly vacuous

Kept, because the negative result is the finding. The specced chain is three atomic
constraints:

1. `B_i ⇔ X_i = v` — `rule1`, AC, over `i ∈ [1,n]`.
2. `B'_p ⇔ C = p` — `rule1`, AC, over the count values `p`. This is the channel `nvalues`
   uses for `N` (`explenation generator.ml:840`).
3. `∑_i B_i = p ⇔ B'_p` — `rule7`, matched against the `p`-channel of step 2.

**Step 2 is what makes this S3 rather than S2**, and `decomps/_shapes.md` is emphatic about
why: the count channel is "the only thing in the corpus that lets a derived rule **conclude
something about a count variable** rather than only about the `X` literals". It is precisely
what the shipped `among` lacks — gap **G5**.

**Where the spec is wrong, and it took a run to see it.** `decomps/count.md` says step 3 is
`nvalues`' `B4` step "minus the intermediate per-value existential that `nvalue`/`among` need
and `count` does not (there is exactly one target value `v`, not a set)". Dropping that step is
not free: it leaves the value family unbound on the reified side, and the printer requires a
value index on every `X` literal. Measured — see "Scope of this entry", run (a).

**And where it is wrong for a second, deeper reason, measured 2026-09-22.** With the value
index supplied by `at_most`'s `DPar ("{v}", D 2)` seed and the count channel written on `gcc`'s
`O` letter, the S3 chain compiles and emits **5 rules** — and a sweep over every `X ∈ [1,m]^n`,
every `v` and every `n,m ∈ {1,…,5}` scores them:

| # | rule | firings | failures | verdict |
|---|---|---|---|---|
| 1 | `∀i: X_i ≠ v`, `c = p`  ⊢  `X_i = v` | **0** | 0 | **VACUOUS** |
| 2 | `∀i: X_i = v`, `c = p`  ⊢  `X_i ≠ v` | 225 | **225** | **UNSOUND** |
| 3 | `∀i: X_i ≠ v` and `∀i: X_i = v`  ⊢  `c = p` | **0** | 0 | **VACUOUS** |
| 4 | `∀i: X_i = v`  ⊢  `c ≠ p` | 225 | **75** | **UNSOUND** |
| 5 | `∀i: X_i ≠ v`  ⊢  `c ≠ p` | 39228 | 0 | **SOUND**, minimal |

**The cause is `rule7`, not the spec's arithmetic and not a gap.** `rule5` and `rule6` reach the
summed family through `apprim`/`napprim`, which builds a sibling index `i'` *constrained to
differ* from the conclusion's own index — that is where `alldifferent`'s and `gcc`'s
`∀i' ≠ i` comes from. `rule7` uses `apforall`/`napforall` instead, and its own source carries
`(*incohérent?*)` on those very lines (`explenation generator.ml:443-444`). The premise
therefore quantifies over **all** of `[[1,n]]`, *including* the index the conclusion is about,
and reads `∀i: X_i ≠ v` beside a conclusion `X_i = v`. It contradicts itself, so it never
fires.

**This is W1-T9 defect 3 in a different schema.** That defect made `gcc`'s rules 1–2 vacuous
for the analogous reason — a universal binder where a free parameter was meant — and was
repaired by changing the *index operator*. Here the binder is chosen by the *schema*, so
repairing it means editing `rule7`, which changes every entry that uses it (`gcc`, `nvalues`,
`roots`, `range`, `among`). **Not patched on the strength of one entry**; recorded here and in
the source comment above `ncvbc`.

## Scope of this entry

**Events the generator was asked to explain, in the shipped entry:** **four** — `X_i = v`,
`X_i ≠ v`, `c ≥ p`, `c < p` — from the seeds `xacv` and `ncvbc`. Read off the
`%% generator diagnostics (W1-T3)` footer of `cata/count.tex`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t, t ∈ {v}` | 1 | **1** | none |
| `X_{i} ≠ t, t ∈ {v}` | 1 | **1** | none |
| `O_{t} ≥ p, t ∈ {v}` | 1 | **1** | none; **binds `i` twice (D-0009)** |
| `O_{t}<p, t ∈ {v}` | 1 | **1** | none; **binds `i` twice (D-0009)** |

No `F` discard, no cycle cut, no duplicate, no undefined index set. The two D-0009 flags are
inherited from `cata/gcc.tex` verbatim — the same two rules carry them there — and are not
introduced by pinning the value.

**Historical, kept: the three 2026-09-21 scratch runs** (bounded in "How this entry was
produced") asked the generator for the four events `X_i = t`, `X_i ≠ t`, `N = p`, `N ≠ p`, over
three authorings of S3.

**(a) The spec as written** — steps 1-3, no intermediate step, reified side
`imap [foralli;p_out]` / `imap [i_out;forallp]`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | 1 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | 1 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `N=p` | — | — | **run aborted**: `Failure "hd"`, `printglobal_eventtex`, `explenation generator.ml:512` |
| `N \neq p` | — | — | not reached |

The two `X` rules are written to the file, then the run exits 2. The `X` literal that survives
into the `N = p` explanation carries neither a `P`- nor a `T`-family index, and line 512 takes
`hd` of exactly that list. **This is a printer crash reachable from a decomposition in this
repo's own spec corpus.**

**(b) The same, with the value family universally bound on the reified side**
(`imap [foralli;forallt;p_out]`): exit 0, **5** rules, three of which conclude `N = p` or
`N ≠ p` — so the S3 channel does do what G5 says `among` cannot. But `∀t` says "for every
value", and `count(x, v, c)` counts **one** value. The run therefore prices the honest cost:
S3 emits, and what it emits is closer to `nvalue` than to `count`.

**(c) `count` as `among` with a value set, plus the channel `among` is missing** — step 2 of
`among` (`explenation generator.ml:852`, `ontin (D 4)`) with the `nvalues` count channel added:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **0** | `undefined index set 1` — `REFUSED … (D4) — W1-T2` |
| `X_{i} \neq t` | 1 | **0** | `undefined index set 1` — `REFUSED … (D4) — W1-T2` |
| `N=p` | 1 | **0** | `undefined index set 1` — `REFUSED … (D4) — W1-T2` |
| `N \neq p` | 2 | **0** | `undefined index set 2` — `REFUSED … (D4) — W1-T2` |

Exit 0, **0 rules**, every candidate refused on the undefined `D_4`. **This is `among`'s
result, arrived at independently**, and it is the finding that sets this entry's status:
fixing G5 does not unblock `count`, because G8 blocks it first.

## Generated rules

`grep -o '\frac' cata/count.tex | wc -l` → **4**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `∀i'≠i ∈ [[1,n]]: X_{i'} ≠ v`, `c ≥ p`  ⊢  `X_i = v` | **SOUND**, **MINIMAL** |
| 2 | `∀i'≠i ∈ [[1,n]]: X_{i'} = v`, `c < p`  ⊢  `X_i ≠ v` | **SOUND**, **MINIMAL** |
| 3 | `∀i ∈ [[1,n]]: X_i = v`  ⊢  `c ≥ p` | **SOUND**, **MINIMAL** |
| 4 | `∀i ∈ [[1,n]]: X_i ≠ v`  ⊢  `c < p` | **SOUND**, **MINIMAL** |

Rule 1 is the one that does work during search: the count is known to be at least `p ≥ 1` and
every other variable has been shown incapable of taking `v`, so this one must take it. Rule 2 is
its dual. Rules 3 and 4 are the count variable's own two directions.

### How the verdicts were obtained

**This session's own sweep, not `make validate`.** Exhaustive enumeration of every
`X ∈ [1,m]^n` with `c = #{i : X_i = v}`, for every `v ∈ [1,m]` and every `n, m ∈ {1,2,3,4,5}` —
**`n = 1` included**. `v` is swept as part of the model (it is a parameter of the constraint);
the free indices are `i` and `p`, each over `[[1,n]]`.

**0 counterexamples on all four rules at every size swept.** Firings at `n,m ≤ 4`:
**736 / 200 / 100 / 2018**; at `n,m ≤ 5`: **10571 / 600 / 225 / 39228**; at `n = 1` alone:
**15 / 40 / 15 / 40** firings, **0** failures.

**Minimality** by dropping each premise in turn: every drop produces counterexamples
(79068 / 185860 for rule 1, 79068 / 825 for rule 2, 96876 for rule 3, 26841 for rule 4 at
`n,m ≤ 5`), so all four are minimal over the range. Restricted to `n = 1` **alone**, rules 1
and 2 have a vacuous universal premise which is then droppable — the same qualification
[`minimum`](minimum.md) and [`member`](member.md) carry, and it does not touch soundness.

**On the two D-0009 flags.** Rules 3 and 4 bind `i` twice, and the footer says so. Both
bindings are the same `∀i ∈ [[1,n]]` over the same set, so the two readings coincide and the
sweep is unambiguous; what is wrong is the LaTeX, which is redundant. Inherited from
[`gcc`](gcc.md), where the identical pair carries the identical flag.

### The two authorings, side by side

This is the entry's most transferable result, so it is stated once, plainly:

| | S3 as specced (`rule7`, exact count) | shipped (`gccn`, order-encoded count) |
|---|---|---|
| decomposition value needed | a new one | **none** — `gccn` unchanged |
| rules | 5 | 4 |
| sound | **1** | **4** |
| vacuous | 2 | 0 |
| unsound | 2 | 0 |

**The difference is entirely `rule7` versus `rule6`,** i.e. `apforall` versus `apprim` on the
summed family. A constraint whose natural reading is an *equality* on a count is better served
here by the two *inequality* directions the order encoding gives, because those are the schemas
whose sibling index excludes the conclusion's own.

## Status

**`generated, unvalidated`** — by this catalog's instrument. `make validate` cannot see this
file (**W1-T18**); the verdicts above come from a sweep written for this entry.

**This entry has now held three statuses.** `nothing generated — blocked on G8` until
2026-09-22 morning; `encodable today, not encoded` after G8 closed; `generated, unvalidated`
since session A-1 encoded it the same day. The middle one lasted hours, which is the pattern
[`strictly_increasing`](strictly_increasing.md#the-status-this-entry-used-to-carry-and-what-its-life-cycle-shows)
records: it is the one legend value a session closes by typing.

**Historical, kept — what the block was and how it fell.**

**This status changed on 2026-09-22 and the previous one — `nothing generated — blocked on G8` —
is retired, not softened.** G8 was closed that day (session G-1, commits `4547daf` and
`1e747ee`), and the wall the paragraphs below measured is the one it took down. There is now no
gap to name, which is why this entry uses the legend value `catalog/README.md` added for exactly
that case rather than inventing a G-number.

**What the block was, and why it is gone.** The measured obstacle was the *value*: `v` cannot be
a bare parameter, because an `X` literal with no value index raises `Failure "hd"` at
`explenation generator.ml:512`, so `v` had to be written as a one-element value **set** — and
`ind_set` had no former for one. `ind_set` now has four (`explenation generator.ml:48-52`), and
`DPar` is the one this needs: `at_most`'s seed event is
`Set (T 1, IN, DPar ("\\{v\\}", D 2))` (`:1022`), which keeps the value index `t` the printer
demands and pins it to the singleton `{v}`. `ind_set_defined` admits it (`:520-525`) because
`printind_set` renders its own containment (`:536`), so it is not a `D_4`. `cata/at_most.tex`
ships the result. The same seed serves `count`.

**What was never the block, restated because it is now the whole of the work.** The **count
variable** `c` is the easy part: `nvalues`' `N` channel works (`explenation generator.ml:921-924`,
a `rule7` whose `Reified_devent` carries `N`), and scratch run (b) emitted three rules concluding
about it. **G5 is not `count`'s defect** — it is shipped `among`'s missing count channel, and S3
has the channel by construction. That distinction is now load-bearing, because `among` is the
cautionary case: G8's closure gave it two rules and both are measured **UNSOUND**
([`among.md`](among.md)), precisely because its count is channelled nowhere. `count` does not
share that fault, but nothing about this status predicts a verdict.

**What would have to be written** — a decomposition value in the generator's `(*Decompositions*)`
block, on the `at_most` pattern at `explenation generator.ml:994-995`:

1. `Decomp (1, rule1, [Global_devent (X …); Reified_devent ((B 1) …)])` — `B1_i ⇔ X_i = t`.
2. `Decomp (1, rule1, [Global_devent (N …); Reified_devent ((B 4) …)])` — the count channel,
   copied from `nvalues` (`:922`). `G2` still applies: `var_name` has no letter meaning "the
   count of a given value", so `c` borrows `N`.
3. `Decomp (2, rule7, [Decomp_devent ((B 1) …); Reified_devent ((B 4) …)])` — the Boolean sum
   `=`, with the `Reified_devent` present, which is what separates this from `among`'s G5 bug.

plus a seed `Global_event` restricting `t` to `DPar ("\\{v\\}", D 2)` and one `explainall`
line. **Nothing here was run.** This is a reading of the generator's types and of the two
demonstrators G-1 shipped, not a measurement: no value was authored, no artifact was produced,
and no rule of this constraint has been seen, let alone judged.

> **RUN 2026-09-22, and the prediction was half right.** The three steps above do compile and
> do emit — the `DPar ("{v}", D 2)` seed is exactly what was needed, and the count channel does
> conclude about `c`. But **four of the five rules it emits are vacuous or unsound**, for the
> `rule7` reason set out under "Decomposition used here". What was shipped instead needs no new
> decomposition value at all. The prediction was right about the *encodability* and silent about
> the *quality*, which is precisely the distinction `encodable today, not encoded` is not
> allowed to blur.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:128` names no paper. There are **4** rules in the repository as of
2026-09-22, so the second half of this verdict's old justification ("0 rules, nothing to order")
no longer applies; the first half stands on its own and is what the verdict rests on. Note, as `catalog/at_most.md` does, that this is a statement about the
*row*: the same file cites Downing, Feydy and Stuckey 2012 for `global_cardinality`
(`:127`), and `count` is a one-value `global_cardinality`. Nobody has read that paper for this
purpose; `catalog/_literature/gcc.md` sources it for `gcc` and its content is not transferred
here.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **CLOSED 2026-09-22** (`4547daf`, `1e747ee`). It was the binding one, measured: `ind_set` named only whole predefined ranges, so the counted value `v` had no one-element set and `D_4` was refused by W1-T2. `DPar` now writes it — see Status. The row is kept because the measurement above it was real |
| — (unnumbered) | **the printer requires a value index on every `X` literal** — the parameter reading of `v` raises `Failure "hd"` at `explenation generator.ml:512`. Measured twice (here and under [`at_most.md`](at_most.md)); it is in neither `docs/DECOMP_FORMAT_NOTES.md` nor `docs/ROADMAP.md`, and it is the sibling of W1-T10 and W1-T15 in the same printer |
| `G2` | **paid, twice, and one half of it is a printer bug found by paying it.** `var_name` (`explenation generator.ml:3`) has no letter for "the count of a given value", so `c` borrows `O`. It also carries the value index, printing `O_{t} ≥ p, t ∈ {v}` — `gcc`'s notation, not `count`'s `c ≥ p`. **`N` cannot be borrowed instead:** `printvartex`'s `N` case prints `printitex (hd (index_list v))`, the **first** index only, so a two-index count variable prints as `N = t` and silently drops `p`. Measured by running it, 2026-09-22, not read off the code. `O` routes through `printglobal_eventtex` and prints both |
| `G5` | **not `count`'s.** G5 is the shipped `among`'s missing count channel; the shipped `gccn` authoring has the channel by construction, and rules 3–4 conclude about `c` |
| — (unnumbered, new 2026-09-22) | **`rule7` binds the summed family universally where `rule5`/`rule6` exclude the conclusion's own index** (`apforall` vs `apprim`, `explenation generator.ml:443-444`, where the source already says `(*incohérent?*)`). Measured here: it makes 4 of the S3 authoring's 5 rules vacuous or unsound. It is a **rule-engine** defect, not a format gap, and it is why this entry ships `rule6`'s order-encoded pair instead |
| `G1` | not binding: `count`'s comparison is against a *variable*, which the channel carries, not against a bare constant |
| `G3` | only for the general MiniZinc form with `v` a variable |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`, verbatim: "**E0** — this is `rule5/6/7` exactly as
built". With G8 closed, that cell is now right about the index sets as well as the schemas,
which it was not when this entry was written.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

### 2026-09-22 (session A-1) — what changed

- `explenation generator.ml` edited (this session owns it): **no decomposition value added.**
  One seed, `ncvbc`, at line **1235**; one `caveat` block and `explainall` call at **1382**;
  one long source comment recording the `rule7` measurement. Run under OCaml 5.1.1 in the
  `baguette` switch; exit 0, empty stderr; `cata/count.tex` produced and committed.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, no `FAIL`.
  Every pre-existing non-orphaned `cata/*.tex` reproduces byte-for-byte, as does `exp.tex`; the
  orphan set is unchanged. **The warning census moved by two**, at `-w +40+41+42` (36 → 38) and
  `-w +a` (61 → 63): the new seed writes `O` and `T 1`, each ambiguous between `ind_name` and
  `var_name` like every other such site. The census *reports*; it does not fail. The
  `Makefile`'s expected-value line is now stale and the `Makefile` is not this session's.
- `make validate` (run 2026-09-22, redirected then grepped) → **34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged; 4 rules in 5 entries out of scope.** Unchanged, and it names
  no `count` entry — the direct measurement of W1-T18.
- **Two exhaustive assignment sweeps, both written and run by this session**, over every
  `X ∈ [1,m]^n`, every `v` and every `n,m ∈ {1,2,3,4,5}`, `n = 1` included, with per-premise
  droppability: one of the four shipped rules, one of the five the S3 authoring emits. All
  counts above are quoted from those runs.
- The S3 authoring was **written into the generator, compiled and run** before being replaced;
  its value is preserved verbatim in the source comment above `ncvbc` so the negative result can
  be reproduced without re-deriving it.
- `grep -o '\frac' cata/count.tex | wc -l` → **4**.
- Line numbers re-checked by `grep -n` after the final edit (W1-T14). **The 2026-09-21 numbers
  below have moved**; they are left as written and dated.

### 2026-09-21 — the original entry

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 128.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`, `== 2 rules in 5 entries out of scope
  (underspecified artifact) ==`. No line names a `count` entry.
- `CHRISTMAS_LIST.md:128`, `:127`, `:106-109` read → the cells quoted above.
- `tools/data/minizinc-2.10.1-globals.txt:42` read → the name.
- `explenation generator.ml` read, not run: `:3` (`var_name`), `:245-246`
  (`reified_devent`'s placeholder), `:459-464` (`ind_set_defined`, `printind_set`'s raises),
  `:512` (the `hd` in `printglobal_eventtex`), `:839-842` (`nvalues`, the `N` channel),
  `:851-853` (`among`, the `ontin (D 4)` step).
- **Three scratch generator runs, 2026-09-21.** `explenation generator.ml` was copied into this
  session's scratch directory; each run appended one S3 authoring plus
  `explainall [xac;nac] … "cata/r4_count*.tex"` and was run with OCaml 5.1.1
  (`eval $(opam env --switch=baguette --set-switch); ocaml <copy>.ml`), stdout and stderr
  redirected to files and then grepped. (a) exit **2**, `Failure "hd"`, backtrace naming
  `printglobal_eventtex` at line 512, 2 rules written before the abort. (b) exit **0**, 5
  `\frac`. (c) exit **0**, 0 `\frac`, the four `REFUSED … (D4) — W1-T2` diagnostics quoted in
  "Scope of this entry".
- **Nothing was added to the repository.** `explenation generator.ml` is untouched, no file
  under `cata/` was written or changed, and `make check`'s goldens are unaffected. The three
  authorings are this session's own; a fourth could behave differently. The claims that do not
  depend on the authoring are the ones read off `:459`, `:512` and `:852`.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/count.md:9` cites the `count` row at `CHRISTMAS_LIST.md:125`.** Measured
   2026-09-21: the row is at **128**. The quoted text ("E0 — this is rule5/6/7 exactly as
   built") is correct.
2. **`decomps/count.md:20,23` cite `nvalues` at "generator lines 406-407" and "line 409".**
   Measured: `nvalues` is at **839-842**. W1-T14's rot.
3. **`decomps/count.md:24-25`'s "minus the intermediate per-value existential … `count` does
   not [need]" is contradicted by run (a).** Dropping that step aborts the printer. The file's
   G2 note is sound; this sentence is not.
4. **[`catalog/count_fn.md`](count_fn.md) quotes this entry's Status.** It read `not reviewed`
   off the stub on 2026-09-21, then `nothing generated — blocked on G8`; as of 2026-09-22 it is
   `encodable today, not encoded`. U2 updated that quotation in the same commit as this change.

5. **Everything above discrepancy 4 was measured on 2026-09-21 and G8 closed on 2026-09-22.**
   The three scratch runs, the `Failure "hd"` at `:512` and the four `REFUSED … (D4)`
   diagnostics all still stand as records of what the format was; they are no longer a record of
   what it is. Only the Status section has been re-decided, and it says so.
