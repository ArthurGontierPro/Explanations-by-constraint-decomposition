# `at_least`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `at_least`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G1` — **and on `G8` for the counted value.** See Status |
| **Generated** | no generator entry — there is no `cata/at_least.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `at_least` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, and a **scratch generator run** (below) |

## Constraint

`at_least(int: n, array[int] of var int: x, int: v)` — the value `v` occurs at least `n` times
in `x`. `n` and `v` are parameters.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:29` carries the *name* only; the line above is
transcribed from `decomps/at_least.md` ("Signature"), which records it without a citation.
**Recall, not a citation.** `CHRISTMAS_LIST.md:128` files it under `2. Counting and cardinality`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:128` reads, verbatim:

> none specific

**Rule shape:** nothing to state — no `catalog/_literature/at_least.md` exists, no paper was
fetched and no web access was used. See [`at_most.md`](at_most.md), "Published explanation",
for why `none specific` gives `no published rule exists` rather than `pending sourcing`; the
row is shared and the reasoning is not repeated here.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:128`, solver cell `decomp`, legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21: no `[G]`, no `[C]`, no `[C✗]`. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/at_least.md`](../decomps/at_least.md); shape **S2** in `decomps/_shapes.md`.

1. `B_i ⇔ X_i = v` — `rule1`, AC.
2. `∑_i B_i ≥ n` — `rule6`, single `Decomp_devent`, no `Reified_devent`.

**This is `at_most` with the comparator flipped, and that is the whole difference.**
`decomps/_shapes.md`'s convention 2 states it — "`{rule5, rule6, rule7}` is one schema family,
parameterised by the comparator `≤ / ≥ / =`; `at_most`/`at_least`/`exactly` differ in nothing
else" — and the entry for the shape, its two gaps and their consequences is
[`at_most.md`](at_most.md). **G1 is one defect, not three.**

## Scope of this entry

**Events the generator was asked to explain:** none in the repository. What follows is from a
**scratch run** (see "How this entry was produced"), which is not a catalog artifact.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |

**The empty answer is the mirror image of `at_most`'s**, and that is a point in the shape's
favour: a `≥`-direction sum derives `X_i = t` and cannot derive `X_i ≠ t`, exactly as the
`≤`-direction derives the negative and not the positive. Nothing is lost silently — the drop is
one legitimate `F` (a branch reaching a constraint that is not reified), the kind W1-S measured
to be the only kind that occurs across all 16 shipped entries.

## Generated rules

**None in this repository.** `cata/at_least.tex` does not exist.

**What the shape emits when run** (scratch, 2026-09-21) — one rule:

```
X_{i'} ≠ t,  ∀i',  i' ≠ i,  i' ∈ [1,n],  i ∈ [1,n]
--------------------------------------------------- ⊢
X_{i} = t
```

**Verdict:** none. The artifact is not in the tree and `make validate` never saw it.

**Read it against the invisible threshold.** As printed, the rule says: if every *other*
position misses `t`, then position `i` holds `t`. That is sound when the threshold is `n` — the
array length, i.e. "all of them" — and unsound for any smaller `n`, which is the majority of
`at_least`'s instances. The soundness of the printed rule therefore depends on a number the
printed rule does not contain. **This is what G1 costs, stated for one rule**; it is reasoning
about the emitted text, not a validator verdict, and no validator can reach it while the
constant is absent from the artifact.

## Status

**`nothing generated — blocked on G1`** — and on **G8** for the counted value `v`.

Nothing is generated because no `at_least` value exists in the generator. Authoring one is
`rule1` + `rule6`, both of which already exist and are already exercised
(`atleastnvalues`, `explenation generator.ml:845-848`, uses `rule6` in a channelled form), so
the block is not in the schemas. It is in the two things the format cannot print: the threshold
`n` (**G1**) and the counted value `v` (**G8**; baking it in instead raises `Failure "hd"` at
`explenation generator.ml:512` — measured, see [`at_most.md`](at_most.md)). Both are shared with
`at_most`, `exactly` and `all_different`, and fixing S2 once fixes all four.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:128` names no paper. With 0 rules there is also no premise to compare, so
the verdict would be unavailable even if a shape were sourced. See [`at_most.md`](at_most.md)
for the two qualifications that apply equally here.

## Gaps

| gap | what it blocks here |
|---|---|
| `G1` | **the named one.** The threshold `n` never reaches the page; worse here than for `at_most`, because the emitted rule is *sound only at* `n` = the array length. See "Generated rules" |
| `G8` | no singleton value set, so the counted value `v` has no expression |
| — (unnumbered) | the printer requires a value index on every `X` literal (`:512`, `Failure "hd"`). Measured under [`at_most.md`](at_most.md); not in `docs/DECOMP_FORMAT_NOTES.md` and not on the roadmap |
| `G3` | only for the general form with `v` a variable; not binding under D-0003's parameter reading |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`: "**E0** — this is `rule5/6/7` exactly as built".
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier `A`, ecodes `["E0"]`,
  `CHRISTMAS_LIST.md` line 128.
- `make validate` (2026-09-21, redirected then grepped) → `== 34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged ==`; no line names `at_least`.
- `CHRISTMAS_LIST.md:128` and `:106-109` read → the cells quoted above.
- `tools/data/minizinc-2.10.1-globals.txt:29` read → the name.
- `explenation generator.ml:845-848` read → `atleastnvalues`, the existing `rule6` use;
  `:512` → the `hd` site; `:245-246` → `reified_devent`'s placeholder.
- **Scratch generator run, 2026-09-21** — a copy of `explenation generator.ml` in this session's
  scratch directory, with `rule1` + `rule6` appended and `explainall [xac] … "cata/r4_atleast.tex"`.
  OCaml 5.1.1, exit 0, 1 `\frac`, footer as quoted. **Nothing was added to the repository:** the
  generator is untouched, no `cata/` file changed, `make check`'s goldens are unaffected.
- **Not fetched, not read:** the MiniZinc library, any paper. No web access.

**Discrepancy noted, not fixed.** `decomps/at_least.md:20-25` cites
`Decomp (2, rule5, …)` at "generator line 388" and `reified_devent`'s placeholder at "line 111";
measured 2026-09-21 they are at **809** and **245-246**. W1-T14's rot, and the value names still
resolve.
