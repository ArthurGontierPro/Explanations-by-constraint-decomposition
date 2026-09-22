# `span`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `span`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | **`generated, unvalidated`** *by this catalog's instrument* — `make validate` cannot see this file (**W1-T18**). Measured by a second instrument: all **8** rules **SOUND** and **MINIMAL** at every `n,m ∈ {1,2,3,4,5}`, **`n = 1` included**. Was `nothing generated — blocked on G3` until 2026-09-22; **that verdict is retracted** and the retraction is the entry |
| **Generated** | **8** rules in `cata/span.tex` — **new 2026-09-22** (session A-1), from generator value `spn` |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `span` entry, in scope or out: `validator.ml`'s lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:152` records `none` |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `make validate`, `grep -o '\frac' cata/span.tex \| wc -l`, and this session's own exhaustive assignment sweep with per-premise droppability. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Constraint

**No signature is asserted here.** `span` is not vendored:
`tools/data/minizinc-2.10.1-globals.txt:115` carries the *name* only, and
`CHRISTMAS_LIST.md:152` — the row it shares with [`alternative`](alternative.md) — gives
literature, solver and route and no signature.

`decomps/span.md` works from a **reconstructed** reading, and flags it as reconstructed: a task
with start `S` and end `E` spans a set of subtask intervals, with `S = min_i(start_i)` and
`E = max_i(end_i)`. That file's own words: "**Flagging this as reconstructed, not confirmed** …
if the real signature differs this file should be redone, not patched." **This entry inherits
the hedge and does not upgrade it.** What follows holds *under that reading*; the blocking gap
would have to be re-established under any other.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:115`.
`CHRISTMAS_LIST.md:152` files it under section `4. Sequencing and sliding`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:152` reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/span.md`, no paper was
fetched by this session and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:152`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21: no `[G]`, no `[C]`, no `[C✗]`. The machine-filled stub read this
correctly. The row is shared with `alternative`, so both entries carry the same three cells.

## Decomposition used here

**Generator value:** `spn`, `explenation generator.ml:1247`.
**Emitted by:** `explainall [xbc;ebc;sspan;espan] spn "cata/span.tex"`, line **1462**. Seeds:
`xbc` (the start array, unchanged since 2020), `ebc` (**1275**, the end array — `gcc`'s letter
`O` with an array position), `sspan` (**1276**, the span's own `S`) and `espan` (**1277**, its
`E`).

**`span` is `minimum` and `maximum` side by side, and that is the entire decomposition:**

| ctr | schema | meaning | borrowed from |
|---|---|---|---|
| 1 | `rule1` | `start_i ≥ t ⇔ B1_{i,t}` (BC) | `minim`, verbatim |
| 2 | `rule3` | `B2_t ⇔ ⋀_{i} B1_{i,t}` | `minim`, verbatim |
| 3 | `rule1` | `S ≥ t ⇔ B2_t` (BC) | `minim`, verbatim |
| 4 | `rule1` | `end_i ≥ t ⇔ B3_{i,t}` (BC) | `maxi`, verbatim |
| 5 | `rule4` | `B4_t ⇔ ⋁_{i} B3_{i,t}` | `maxi`, verbatim |
| 6 | `rule1` | `E ≥ t ⇔ B4_t` (BC) | `maxi`, verbatim |

The two halves **share no variable**, so `ctrs` separates them by name and they never interact.
**Nothing was added to the language** — no constructor, no schema, no printer case, no index
operator. The whole entry is one decomposition value assembled from two existing ones, plus
three seed events.

### The claim this entry overturns, kept in full

`decomps/span.md` still opens with a correction header reading "`span` has no shape and is
listed among the G3-blocked constraints", and this file adopted it. **Both are wrong, and they
are wrong by inheritance**: the header's authority is `decomps/maximum.md`'s "not a derivation
gap, it is a missing primitive", which session X-max retracted on 2026-09-22 by shipping
`cata/maximum.tex`. `docs/G3-AUDIT.md` (commit `abadc0f`) then called `span` "the cheapest entry
in the audit" because its halves *are* `minimum` and `maximum`. This entry is the artifact that
settles it.

**Step 2 of the old argument was right and is untouched.** `decomps/span.md`'s "Shape D" —
`range`/`roots` read as a ∀-bound plus an ∃-tight pair — really was a misreading: `range` and
`roots` are Boolean sums (`rule6`/`rule7`), not `rule3`/`rule4`. The shape `span` actually needs
is not Shape D; it is `minimum`'s and `maximum`'s, which did not exist when that was written.
**A correct refutation of one candidate shape was taken as a proof that no shape exists.** That
is the same error `maximum` made, in the same file family, twice.

**Historical, kept: the contradiction this entry used to be downstream of.** `decomps/_shapes.md`'s "Contradictions between sessions" §1 states it
in one line — "`span` is claimed E0 by one session and impossible by another, and the second is
right" — and the argument has two steps:

1. `S = min_i(start_i)` compares two **decision variables**. `Global_event`/`ind_modifs`
   express `X_i = t` for `t` an index-derived domain *value*, never `X_i = Y_i`
   (`docs/DECOMP_FORMAT_NOTES.md:38-45`, **G3**). `decomps/maximum.md` calls this "not a
   derivation gap, it is a missing primitive", and `span`'s min over subtask starts is
   `minimum` under another name.
2. **The precedent the E0 claim rested on does not exist.** `decomps/span.md` reused
   "Shape D" — `range`/`roots` read as a ∀-bound plus an ∃-tight pair. Read off the source,
   `range` (`explenation generator.ml:859-861`) is `rule1` + `rule6` + `rule7` and `roots`
   (`:856-858`) is `rule1` + two `rule7`s, each a **Boolean sum** over a value-restricted
   family. `rule6` is `∑ ≥` and `rule7` is `∑ =`; ∀ and ∃ are `rule3`/`rule4`. Shape D was a
   misreading of two schemas and `decomps/_shapes.md` deletes it.

**This entry adopts that resolution rather than reopening it**, and re-checked step 2 against
the source today: `range` and `roots` are at the lines above and are Boolean sums.

## Scope of this entry

**Events the generator was asked to explain:** **eight** — `start_i ≥ t`, `start_i < t`,
`end_i ≥ t`, `end_i < t`, `S ≥ t`, `S < t`, `E ≥ t`, `E < t`. Read off the
`%% generator diagnostics (W1-T3)` footer of `cata/span.tex`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 1 | **1** | none |
| `X_{i}<t` | 1 | **1** | none |
| `O_{i} \geq t` | 1 | **1** | none |
| `O_{i}<t` | 1 | **1** | none |
| `N \geq t` | 1 | **1** | none |
| `N<t` | 1 | **1** | none |
| `V \geq t` | 1 | **1** | none |
| `V<t` | 1 | **1** | none |

**Eight events, eight candidates, eight rules, and a clean sheet on every diagnostic** — no `F`
discard, no cycle cut, no duplicate, no undefined index set, no empty premise, no index bound
twice. It is the largest entry in the catalog with a clean sheet, and it is clean for the dull
reason that it is two clean entries stacked.

**The old "no scratch experiment was run" paragraph said a run could not even be attempted**,
because "G3 means the atom `S ≤ start_i` has no representation in the `event` type at all".
That was true of the atom and false of the constraint: under the order encoding the comparison
factors through `t` and never appears. The paragraph is a good example of the audit's own
warning — a correct reading of the types, a wrong inference about the constraint.

## Generated rules

`grep -o '\frac' cata/span.tex | wc -l` → **8**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `S ≥ t`  ⊢  `start_i ≥ t` | **SOUND**, **MINIMAL** |
| 2 | `∀i'≠i: start_{i'} ≥ t`, `S < t`  ⊢  `start_i < t` | **SOUND**, **MINIMAL** |
| 3 | `∀i'≠i: end_{i'} < t`, `E ≥ t`  ⊢  `end_i ≥ t` | **SOUND**, **MINIMAL** |
| 4 | `E < t`  ⊢  `end_i < t` | **SOUND**, **MINIMAL** |
| 5 | `∀i: start_i ≥ t`  ⊢  `S ≥ t` | **SOUND**, **MINIMAL** |
| 6 | `∃i: start_i < t`  ⊢  `S < t` | **SOUND**, **MINIMAL** |
| 7 | `∃i: end_i ≥ t`  ⊢  `E ≥ t` | **SOUND**, **MINIMAL** |
| 8 | `∀i: end_i < t`  ⊢  `E < t` | **SOUND**, **MINIMAL** |

Rules 2 and 3 are the ones that do work: the span bound is known to exclude `t` and every
*other* subtask has been pushed to the wrong side of it, so this subtask must carry the bound.

### How the verdicts were obtained

**This session's own sweep, not `make validate`.** Exhaustive enumeration, for every
`n, m ∈ {1,2,3,4,5}` — **`n = 1` included** — of every start array with `S = min_i start_i` and,
**separately**, every end array with `E = max_i end_i`.

**Sweeping the halves separately is licensed by the artifact itself**, not assumed: no rule in
`cata/span.tex` mentions a variable of the other half, so an assignment to one half cannot
affect any rule about the other. The rule table above is the evidence, rule by rule.

**0 counterexamples on all eight rules at every size swept.** Firings in file order at
`n,m ≤ 4`: **2438 / 349 / 359 / 652 / 686 / 1098 / 1592 / 192**; at `n,m ≤ 5`:
**37329 / 4158 / 4173 / 10488 / 7995 / 18204 / 23903 / 2296**; at `n = 1` alone:
**35 / 20 / 35 / 20 / 35 / 20 / 35 / 20** firings, **0** failures. **All eight minimal** over
the range: every premise, dropped, produces counterexamples.

**Cross-check, and it is a strong one.** The four end-array counts reproduce
[`maximum`](maximum.md)'s figures **exactly** (`4173 / 10488 / 23903 / 2296` at `n,m ≤ 5`,
session X-max's numbers) and the four start-array counts reproduce
[`minimum`](minimum.md)'s **exactly**. Three entries, two sessions, one instrument, numbers that
had to agree and do. If `span` really is `minimum` and `maximum` stacked, its counts must be
theirs — and they are.

Restricted to `n = 1` **alone**, rules 2 and 3 have a vacuous universal premise which is then
droppable, so their minimality is a claim about the range swept. Soundness at `n = 1` is
unaffected: the companion premise (`S < t`, `E ≥ t`) carries the content.

## Status

**`generated, unvalidated`** — by this catalog's instrument. `make validate` cannot see this
file (**W1-T18**); the verdicts above come from a sweep written for this entry.

**`nothing generated — blocked on G3` is retracted, not softened.** The gap number was the
whole of the old status and it was wrong: `S = min_i start_i` factors through a shared
threshold, `docs/G3-AUDIT.md` says so for all 24 of G3's other claimants, and the artifact now
in `cata/` says so for this one.

**The route cell turns out to be right, for the wrong reason, and this entry now says *that*.**
`CHRISTMAS_LIST.md:152` prices `span` at **E0**. The previous version of this file called that
"wrong and inherited from a withdrawn reading" and proposed **E2** instead. **On this evidence
E0 is correct** — `span` needs no extension at all, since it is built from schemas and operators
that all shipped before this session started. The E0 cell survived a refutation it did not
deserve to survive. It is still true that its *provenance* was the withdrawn Shape D reading;
being right by accident is worth recording separately from being right.

**The signature hedge is NOT discharged.** Everything above holds under
`decomps/span.md`'s reconstructed reading (`S = min_i start_i`, `E = max_i end_i`, two subtask
arrays). If the real MiniZinc signature differs — in particular if `end_i` arrives as
`start_i + d_i` rather than as its own array — this entry needs redoing, not patching.
`docs/G3-AUDIT.md:127` flags exactly that alternative and prices it **G15** (`OpShiftC`), not
G3. **Nobody in this repo has the signature**, and no session has fabricated one.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:152`'s literature cell is `none` — the condition `catalog/TEMPLATE.md`
attaches to this verdict. There are **8** rules in the repository as of 2026-09-22, so the old
second half of this justification ("with 0 rules there is no premise to order") no longer
applies; the empty literature cell carries the verdict on its own. Not `pending sourcing`: the
row cites nothing.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **nothing. Refuted for this constraint** by the shipped artifact, on the same evidence as [`maximum`](maximum.md) and [`minimum`](minimum.md), and in agreement with `docs/G3-AUDIT.md:127`. `S = min_i start_i` factors through a shared threshold; the order encoding performs the factoring; no variable-vs-variable atom survives |
| `G2` | **the real cost, and here it stops being cosmetic.** Four letters are spent: `X` the start array, `O` the end array, `N` the span's own `S`, `V` its own `E`. `var_name` (`explenation generator.ml:3`) is a closed variant of seven names, and exactly **two** of them — `X` and `O` — route through `printglobal_eventtex`, the only printer that can carry an *(array position, value)* pair. **A constraint over two user arrays spends both; a third array would have nowhere to go.** That is a count, not a legibility complaint, and `span` is the first entry in the catalog to hit it |
| — | **one consolation on the same axis:** because `S` and `E` really are scalars, the one-index scalar printer is used *within* its contract and they print as `N ≥ t` and `V ≥ t` — cleaner than [`maximum`](maximum.md)'s `O_{} ≥ t`, which borrows an array letter for a scalar. The same printer silently drops a second index when it is given one; see [`count`](count.md) |
| `G15` | **not this entry's, but it is the one that would bite** if `end_i` turns out to be `start_i + d_i`. `docs/G3-AUDIT.md:127` prices that reading at G15 (`OpShiftC`), and the signature is unknown |

Extensions: the route cell says **E0** and — contrary to what this entry said on 2026-09-21 —
**that is correct**: nothing was extended. See Status for why its provenance is still suspect.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering); `docs/G3-AUDIT.md` for
the audit that reopened this entry.

## How this entry was produced

### 2026-09-22 (session A-1) — what changed

- `explenation generator.ml` edited (this session owns it): decomposition value `spn` at line
  **1247**, seeds `ebc`/`sspan`/`espan` at **1275-1277**, `caveat` block and `explainall` call
  at **1462**. Run under OCaml 5.1.1 in the `baguette` switch; exit 0, empty stderr;
  `cata/span.tex` produced and committed.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, no `FAIL`.
  Every pre-existing non-orphaned `cata/*.tex` reproduces byte-for-byte, as does `exp.tex`; the
  orphan set is unchanged. **The warning census moved by five**, at `-w +40+41+42` (36 → 41)
  and `-w +a` (61 → 66): the new value and seeds add `O`, `N`, `V` and `T 1` constructor sites,
  each ambiguous between `ind_name` and `var_name` like every other one. The census *reports*;
  it does not fail, and the `Makefile`'s expected-value line is not this session's to update.
- `make validate` (run 2026-09-22, redirected then grepped) → unchanged totals, and it names no
  `span` entry — the direct measurement of W1-T18.
- An exhaustive assignment sweep over every start array (with `S = min`) and, separately, every
  end array (with `E = max`), for every `n,m ∈ {1,2,3,4,5}`, `n = 1` included, with per-premise
  droppability. Written and run by this session; counts quoted from the run, and cross-checked
  against [`minimum`](minimum.md)'s and [`maximum`](maximum.md)'s.
- `grep -o '\frac' cata/span.tex | wc -l` → **8**.
- `docs/G3-AUDIT.md` read (`:127`, `:270-281`) → the audit's verdict on this constraint and its
  G15 alternative.
- Line numbers re-checked by `grep -n` after the final edit (W1-T14). **The 2026-09-21 numbers
  below have moved**; they are left as written and dated.

### 2026-09-21 — the original entry

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 152,
  section `4. Sequencing and sliding`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`; no line names a `span` entry.
- `CHRISTMAS_LIST.md:152` and `:106-109` read → the literature, solver and route cells.
- `tools/data/minizinc-2.10.1-globals.txt:115` read → the name.
- `decomps/span.md` read → the reconstructed signature, the withdrawn Shape D / E0 claim, and
  the W3-D correction header, quoted above.
- `decomps/_shapes.md` read → "Not covered by any shape" (G3, five constraints) and
  "Contradictions between sessions" §1 and §2.
- `explenation generator.ml:856-858` and `:859-861` read, not run → `roots` and `range`, which
  are Boolean sums and not a ∀/∃ pair; `:3` (`var_name`).
- `docs/DECOMP_FORMAT_NOTES.md:38-45` and `:92-94` read → G3's wording, its link to E2, and the
  three families that hit it.
- **No scratch run**, for the reason in "Scope of this entry".
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.
  **The signature is the open item**, inherited from `decomps/span.md` and not resolved here.

**Discrepancies noted, not fixed.**

1. **`decomps/span.md` still opens with "`span` has no shape and is listed among the G3-blocked
   constraints".** Refuted by `cata/span.tex`. Not this session's file.
2. **`decomps/_shapes.md`'s "Not covered by any shape" table still lists all five of `maximum`,
   `minimum`, `arg_max`, `arg_min` and `span` against G3.** Three of the five now ship. Not this
   session's file; `catalog/maximum.md` reported the same thing on 2026-09-22.
3. **The `Makefile`'s warning-census expectation line** is five behind after this change. Not
   this session's file.
4. **The E0 route cell**, below — now believed correct, for reasons other than the ones it was
   written for.

`CHRISTMAS_LIST.md:152` still prices `span` at **E0**, from
the reading `decomps/_shapes.md` withdrew on 2026-09-18. The row also covers `alternative`,
whose E0 is a separate question ([`alternative.md`](alternative.md)), so the cell cannot simply
be changed — it needs splitting. That file is not this session's.
