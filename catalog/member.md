# `member`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `member`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E0']` |
| **Status** | **`generated, unvalidated`** for the fragment this repo decomposes (`y` a parameter) — encoded 2026-09-22 by session A-1, and `make validate` cannot see it (**W1-T18**); measured sound and minimal by a second instrument at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**. Still **`nothing generated — blocked on G3`** for MiniZinc's var-target signature. **Two fragments, two statuses — read the fragment statement below before quoting either.** |
| **Generated** | **1** rule in `cata/member.tex` — **new 2026-09-22**, from generator value `member`. One event answered, one refused; see Scope |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `member` entry, in scope or out: `validator.ml`'s entry lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:195` records the literature column as `none` |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `make validate`, `grep -o '\frac' cata/member.tex \| wc -l`, and this session's own exhaustive assignment sweep with per-premise droppability. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Constraint

`member(array[int] of var int: x, var int: y)`

`y` occurs somewhere in `x`: `exists(i)(x[i] = y)`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:93` carries the *name* only. The body
`exists(i)(x[i]=y)` is quoted verbatim from `CHRISTMAS_LIST.md:195`'s route cell and is
in-repo. **The `var int: y` in the signature is recall**, and it is the load-bearing part of
this entry, so it is flagged rather than presented as sourced: MiniZinc ships `member` over
several argument types and this repo records none of them.

**Which fragment this entry covers (D-0012).** `decomps/member.md` decomposes `member` with
**`y` a parameter**, matching D-0003's choice to decompose for explanation quality and the
same move `at_least.md` makes for its `v`. **If `y` is a decision variable, that
decomposition is not of this constraint**, and the gap that separates the two is G3. Both
readings are treated below; they have different answers and the entry says which is which.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:195`'s literature column reads, verbatim, `none`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. No web access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:195`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `decomp`. No native explaining propagator in any of the three solvers
surveyed; whatever explanations a solver gives come from the primitives its decomposition
flattens to.

## Decomposition used here

**Generator value:** `member`, `explenation generator.ml:1076`.
**Emitted by:** `explainall [xacv] member "cata/member.tex"`, line **1292**. The seed `xacv`
is `at_most`'s, unchanged — it pins the value index to the parameter, which is exactly the
parameter-target fragment this entry is about.
**Spec:** `decomps/member.md`. Shape **P4** in `decomps/_shapes-perm.md:104-112`,
renumbered **S4** ("quantified indicator over one index family") in `decomps/_shapes.md`,
which lists `member` first among S4's instances.

The decomposition authored there, in that file's own terms:

- `B_i ⇔ X_i = y`, `i ∈ [1,n]`, `rule1`, AC, with **`y` a parameter**;
- `∃i: B_i`, a single `rule4` existential clause — "the same shape `nvalue.md` uses for its
  `B2_t ⇔ ∃i: B1_{i,t}` step, minus the outer `t` index".

`decomps/member.md` prices it **E0** and calls it a "three-line instance, no new derivation
needed", and under "What's known-broken" it says, in full: "Nothing — not shipped, no defect
to inherit."

## Scope of this entry

**Events the generator was asked to explain:** **two** — `X_i = v` and `X_i ≠ v`, from the
single seed `xacv`. Read off the `%% generator diagnostics (W1-T3)` footer of
`cata/member.tex`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t, t ∈ {v}` | 1 | **1** | none |
| `X_{i} ≠ t, t ∈ {v}` | 1 | **0** | `F` 1 — `** NO RULE EMITTED **` |

**One event answered, one refused, and the refusal is the truth about the constraint rather
than a defect of the derivation.** `member(x,v)` gives no reason for any particular variable
*not* to take `v`; the second constraint of the decomposition has no `Reified_devent`, so
`rule4`'s negative branch resolves to `Lit F` and `filter_branches` discards and counts it.
That is the same `dropped F 1` [`alldifferent`](alldifferent.md) shows for its own unanswerable
event, and W1-T3 established that every `F` discard in the corpus is legitimate
(`CLAUDE.md`, "Traps": all 22 drops were `F`, no `IM`/`FE`/`R` ever occurred).

**`member` was the cheapest unwritten entry in this slice, and it stayed cheap.** Every
schema it needs already runs: `rule1` is the reification every shipped entry starts with,
and the `rule4` existential step is the one `nvalues` uses at
`explenation generator.ml:841` (`Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni); …])`). Nothing in `docs/DECOMP_FORMAT_NOTES.md`'s eighteen gaps
touches the parameter-target reading. What is missing is the two `Decomp`s themselves and
the `explainall` line, and **the reason they are missing is that `member` was specified in
wave two and the generator has not been extended since** — the value list at
`explenation generator.ml:804-864` is the 2020 set.

> **DISCHARGED 2026-09-22.** The two `Decomp`s and the `explainall` line were written, and
> they are the sketch below **verbatim** — see "What this means in practice", which this entry
> wrote on 2026-09-21 as an untested guess and which turned out to be the shipped value
> character for character.

**The variable-target reading is a different constraint and is blocked.** With `y` a
decision variable, `B_i ⇔ X_i = y` compares two decision variables, which is **G3**:
`docs/DECOMP_FORMAT_NOTES.md:34` states it and explicitly anticipates this case —
"`count`'s and `among`'s general MiniZinc signatures allow `v`/elements of the channel to be
variables, and that would need this". MiniZinc's `member` is in the same position. This is
read off the gap statement and the type definitions (`Global_event` at l.50 carries one
`var_name`; index slots take `ind_name`, l.5, l.16), **not** measured.

## Generated rules

`grep -o '\frac' cata/member.tex | wc -l` → **1**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `∀i'≠i ∈ [[1,n]]: X_{i'} ≠ v`  ⊢  `X_i = v` | **SOUND**, **MINIMAL** |

This is the textbook `member` propagation: every *other* variable has been shown incapable of
taking `v`, so this one must. It is `alldifferent`'s rule with every sign flipped, which is
what the decomposition being `alldiff`'s with `rule4` for `rule5` amounts to.

### How the verdicts were obtained

**This session's own sweep, not `make validate`.** Exhaustive enumeration of every
`X ∈ [1,m]^n` containing `v`, for every `v ∈ [1,m]` and every `n, m ∈ {1,2,3,4,5}` — **`n = 1`
included**. `v` is swept as part of the model because it is a parameter of the constraint, not
a free index of the rule; the rule's only free index is `i`.

**0 counterexamples at every size swept.** Firings: **736** at `n,m ≤ 4`, **10571** at
`n,m ≤ 5`, of which **15** are at `n = 1`. **Minimal** over the range: dropping the single
premise fails **57648** times at `n,m ≤ 5`.

### `n = 1` here is the mirror image of `alldifferent`'s hole, and that is the finding

`catalog/README.md` records that an independent sweep found **30 counterexamples at `n = 1`**
for the `alldifferent` rule `make validate` certifies. The two rules have the *same* structural
feature — a universal premise over `i' ≠ i` that is **vacuous at `n = 1`**, so the rule
concludes from nothing — and opposite outcomes:

| | `alldifferent` | `member` |
|---|---|---|
| premise at `n = 1` | vacuous | vacuous |
| conclusion | `X_i ≠ t` | `X_i = v` |
| entailed by the constraint at `n = 1`? | **no** — one variable may take `t` | **yes** — `member(X,v)` with one variable forces it |
| verdict at `n = 1` | **UNSOUND**, 30 counterexamples | **SOUND**, 15 firings, 0 failures |

**So a vacuous premise is not by itself the bug.** Concluding something the constraint does not
force is. That distinction is worth having in the catalog explicitly, because "the premise goes
vacuous at `n = 1`" has so far been used as shorthand for "the rule fails at `n = 1`", and here
it is shorthand for nothing at all.

Restricted to `n = 1` **alone**, the premise is droppable (15 firings either way), so this
entry's minimality — like [`minimum`](minimum.md)'s rule 2 — is a claim about the range swept.

## Status

**`generated, unvalidated`** for the parameter-target fragment (encoded 2026-09-22, session
A-1; `make validate` cannot see it, **W1-T18**);
**`nothing generated — blocked on G3`** for the var-target signature, unchanged. D-0012 requires
the fragment to be named, and here it changes the status, not just the prose.

**The G3 half is untouched and stays untouched.** Nothing this session did bears on it: `xacv`
pins the value index to a *parameter*, which is precisely the fragment that was never blocked.
The var-target reading still compares two decision variables. **It is not in the class
[`maximum`](maximum.md) rescued**, either — `m ≥ x_i` factors through a shared threshold and
`X_i = y` does not, because an equality between two variables is not recovered from
independently thresholded halves in an AC vocabulary.

**Historical, kept:** what the status row said before this session, and why the value existed.

**A note on the value, re-measured after it landed.** `catalog/README.md`'s status legend
now defines `encodable today, not encoded` — a seventh row, added 2026-09-21 at
`catalog/README.md:66`: "The current format can already express the decomposition, but
nothing in the generator does it, so **there is no gap to name**. Use this rather than
inventing a G-number to satisfy the row above." That is exactly this entry's position for the parameter-target fragment.
**`catalog/TEMPLATE.md` does not yet carry it** (measured: `grep -c 'encodable today'
catalog/TEMPLATE.md` → 0), and R5's own `catalog/strictly_increasing.md` and
`catalog/strictly_decreasing.md` Status rows still read `**nothing generated** — and **no
status-legend value fits**`, which the legend has now overtaken. Both are routed under
`## Cross-session requests` in `WORKLOG.md`; neither file is this session's.

**An earlier draft of this entry filed the whole constraint under
`nothing generated — blocked on G3` and argued the legend had a hole.** The hole was real;
the new value fills it, and forcing the parameter fragment under a gap number was the
distortion the value exists to prevent. Corrected here.

**What this meant in practice — and what it cost when somebody did it.** This paragraph was
written on 2026-09-21 as a guess. Session A-1 added exactly the value below, **unchanged**,
plus one `explainall` line and one `caveat` block. The estimate of "an hour" was generous for
the encoding and short for the measurement: the sweep is the expensive half.

If somebody spends an hour adding

```ocaml
let member = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni)])]
```

— **written as a sketch, shipped as the value: this is `explenation generator.ml:1076-1077`
character for character** — and an `explainall` line, this entry stops being empty and becomes
`generated, unvalidated` and then whatever `make validate` says. Nothing in the format had to
change first. That was not true of any other entry in this slice except
[`inverse`](inverse.md).

**One correction to the sentence above, learned by doing it:** it becomes `generated,
unvalidated` and then *nothing*, because `make validate` cannot see a new entry at all
(**W1-T18**). The verdicts in this entry come from a sweep written for it, not from the
catalog's own instrument, and the Status row says so.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:195`'s literature column reads `none`, and per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing`: no paper is cited.
Not `out of reach`: that needs a published premise to be out of reach of. Nothing was
searched and no comparison is fabricated.

The solver cell is `decomp` with no `[G]` and no `[C]`, so unlike [`inverse`](inverse.md)
and `element` there is not even an unpublished implementation to note. **Two of the catalog's
three sources are empty for `member`** — as of 2026-09-22 the third is not: one rule is
generated and measured. That sentence used to read "all three", and the reason it no longer
does is that somebody typed it.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the MiniZinc signature only.** `B_i ⇔ X_i = y` with `y` a decision variable is a variable-vs-variable comparison (`docs/DECOMP_FORMAT_NOTES.md:34`, which anticipates exactly this case for `count`/`among`) |
| — | **nothing blocks the parameter-target fragment, and this is now measured rather than argued.** `rule1` + `rule4` over one index family is shape S4; the shipped value uses `alldiff`'s own two `Decomp`s with `rule4` in `rule5`'s seat and `at_most`'s own seed. **No constructor, schema, printer case or seed was added.** One user array, so **no G2 either** — unlike [`inverse`](inverse.md) and `write`, nothing has to borrow a letter |
| `G17` | no pivot-elimination pass. Not biting: `B_i` is reification scaffolding and washes out, as `decomps/member.md` says |

Extensions: **E0** (`CHRISTMAS_LIST.md:195`, route cell "**E0** — `exists(i)(x[i]=y)`").
E0 means *no extension needed*, which is consistent with everything above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

### 2026-09-22 (session A-1) — what changed

- `explenation generator.ml` edited (this session owns it): value `member` at line **1076**,
  `caveat` block and `explainall` call at **1292**. Run under OCaml 5.1.1 in the `baguette`
  switch; exit 0, empty stderr; `cata/member.tex` produced and committed.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, no `FAIL`.
  Every pre-existing non-orphaned `cata/*.tex` reproduces byte-for-byte, as does `exp.tex`;
  the orphan set is unchanged (`sum.tex`). **The warning census did not move**: 0 / 6 / 36 / 61.
- `make validate` (run 2026-09-22, redirected then grepped) → **34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged; 4 rules in 5 entries out of scope.** Unchanged by this
  entry, and it names no `member` entry at all — the direct measurement of W1-T18. **Note the
  out-of-scope count is 4, not the 2 the 2026-09-21 run below reports and the `Makefile` still
  says.** Stale number elsewhere, not a regression.
- An exhaustive assignment sweep over every `X ∈ [1,m]^n` containing `v`, for every `v` and
  every `n,m ∈ {1,2,3,4,5}`, with per-premise droppability. Written and run by this session;
  counts quoted from the run.
- `grep -o '\frac' cata/member.tex | wc -l` → **1**.
- Line numbers re-checked by `grep -n` after the final edit (W1-T14). **The 2026-09-21 numbers
  below have moved**, because this session inserted values above them; they are left as written
  and dated rather than silently renumbered.

### 2026-09-21 — the original entry

- `python3 tools/mzn_coverage.py --rank --json` → `member` in `A no-literature +
  solver-decomposes`, `ecodes: ['E0']`, `CHRISTMAS_LIST.md` line 195, section
  `9. Ordering, sorting, channelling`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `member.tex`. `grep -c -i 'member' 'explenation generator.ml'`
  → 0.
- `explenation generator.ml` read, not run → `ind_name` at **5**, `index` at **16**,
  `Global_event` at **50** (the G3 typing argument); `nvalues` at **839-842**, its existential
  `rule4` step at **841** (already running); the decomposition block at **804-864**.
- `CHRISTMAS_LIST.md:195` and `:106-109` read → the literature cell (`none`), the solver
  cell (`decomp`), the E0 route cell, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:93` read → the name.
- `decomps/member.md` read → the authored decomposition, the parameter choice and its
  D-0003 justification, the E0 pricing, "Nothing — not shipped, no defect to inherit";
  `decomps/_shapes-perm.md:104-112` (P4) and `decomps/_shapes.md` (S4) read → the shape.
- `docs/DECOMP_FORMAT_NOTES.md:34` read → G3 and its explicit anticipation of
  variable-valued targets.
- `grep -n 'encodable today, not encoded' catalog/README.md catalog/TEMPLATE.md` →
  **seven** legend values now, the new one at `README.md:66`; `TEMPLATE.md` has none.
  Re-measured after the legend landed mid-session; an earlier draft said it was defined
  nowhere, which was true when written.
- **The sketched `let member = …` in Status is a sketch and was not compiled**, and the
  fragment argument is reasoning over the source, labelled as such in place. *(2026-09-22: the
  sketch is now the shipped value, verbatim.)*

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`encodable today, not encoded` is now defined at `catalog/README.md:66` and still not
   in `catalog/TEMPLATE.md`.** Measured 2026-09-21, after `19e0af1` landed the legend row
   mid-session. `catalog/strictly_increasing.md` and `catalog/strictly_decreasing.md`, which
   reached this state independently and named it, still carry `**nothing generated** — and
   **no status-legend value fits**` and are now overtaken by the legend.
