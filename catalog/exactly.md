# `exactly`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `exactly`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G1` — **and on `G8` for the counted value.** See Status |
| **Generated** | no generator entry — there is no `cata/exactly.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `exactly` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, and a **scratch generator run** (below) |

## Constraint

`exactly(int: n, array[int] of var int: x, int: v)` — the value `v` occurs exactly `n` times in
`x`. `n` and `v` are parameters. It is `count(x, v, c)` with `c` fixed to the constant `n`, so
it needs no count channel — which is the one structural difference from
[`count`](count.md).

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:62` carries the *name* only; the line above is
transcribed from `decomps/exactly.md` ("Signature") and is **recall, not a citation**.
`CHRISTMAS_LIST.md:128` files it under `2. Counting and cardinality`.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:128`'s literature column reads, verbatim:

> none specific

**Rule shape:** nothing to state — no `catalog/_literature/exactly.md`, no paper fetched, no web
access. See [`at_most.md`](at_most.md) for why this row gives `no published rule exists` rather
than `pending sourcing`.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:128`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/exactly.md`](../decomps/exactly.md); shape **S2** in `decomps/_shapes.md`.

1. `B_i ⇔ X_i = v` — `rule1`, AC.
2. `∑_i B_i = n` — `rule7`, single `Decomp_devent`, no `Reified_devent`.

**Same shape as `at_most` and `at_least`, comparator `=`** (`decomps/_shapes.md`, convention 2).
`rule7` is already exercised in exactly this single-`Decomp_devent` form by `gcc`
(`explenation generator.ml:813-814`) and `among` (`:851-853`). The shape analysis, and the two
gaps that empty this entry, are in [`at_most.md`](at_most.md) and are not repeated.

## Scope of this entry

**Events the generator was asked to explain:** none in the repository. The table is from a
**scratch run** (see "How this entry was produced").

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |

**`exactly` is the only one of the three that answers both events**, and for a structural
reason: `rule7` takes both the `≤` and the `≥` branch, so neither polarity is an `F` discard.
Nothing was dropped at all.

## Generated rules

**None in this repository.** `cata/exactly.tex` does not exist.

**What the shape emits when run** (scratch, 2026-09-21) — two rules:

```
X_{i} ≠ t,  ∀i,  i ∈ [1,n]                 X_{i} = t,  ∀i,  i ∈ [1,n]
---------------------------- ⊢             ---------------------------- ⊢
X_{i} = t                                  X_{i} ≠ t
```

**Verdict:** none; the artifact is not in the tree and `make validate` never saw it.

**Both rules quantify `∀i` over the very index the conclusion names.** Read literally, rule 1
says "if every position misses `t`, then position `i` holds `t`" with `i` bound twice over. This
is the same collapse `catalog/sum.md` and `catalog/gcc.md` discuss for premises whose quantifier
swallows the conclusion's index, and it is what D-0009 ("the `.tex` does not determine the
rule") is about. Two things are worth separating: the generator's own D-0009 counter did **not**
flag these — the footer carries no `DEFECT` line — because it counts an index *bound twice*, and
here `i` is bound once and then reused. So this is a **reading of the emitted text**, not a
machine verdict, and it is evidence that the D-0009 counter does not catch every ambiguous
binder.

## Status

**`nothing generated — blocked on G1`** — and on **G8** for the counted value `v`.

Nothing is generated because no `exactly` value exists in the generator; both schemas do exist.
`decomps/exactly.md` calls G1 "arguably the sharpest case of the three, since `exactly`'s
defining feature *is* the precise count `n`", and this entry agrees: what the scratch run emits
is a value-generic `= `-sum rule over the whole value range, not `exactly(n, x, v)`. To be
`exactly` it needs the threshold (**G1**) and the counted value as a singleton set (**G8**;
baking it in raises `Failure "hd"` at `explenation generator.ml:512` — measured, see
[`at_most.md`](at_most.md)).

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.** `CHRISTMAS_LIST.md:128` names no paper, and with 0 rules
in the repository there is no premise to place in an implication order. See
[`at_most.md`](at_most.md) for the two qualifications.

## Gaps

| gap | what it blocks here |
|---|---|
| `G1` | **the named one**, and `decomps/exactly.md` calls it the sharpest instance: `exactly`'s content is the number `n` and the number cannot be printed |
| `G8` | no singleton value set for `v` |
| — (unnumbered) | the printer requires a value index on every `X` literal (`:512`, `Failure "hd"`); measured under [`at_most.md`](at_most.md) |
| `D-0009` | not a gap but an open decision, and visible here: both emitted rules quantify `∀i` over the index the conclusion names, and the generator's D-0009 counter does not flag it |
| `G3` | only for the general form with `v` a variable |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`: "**E0** — this is `rule5/6/7` exactly as built".
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier `A`, ecodes `["E0"]`, line 128.
- `make validate` (2026-09-21, redirected then grepped) → `== 34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged ==`; no line names `exactly`.
- `CHRISTMAS_LIST.md:128`, `:106-109` read → the cells quoted above.
- `tools/data/minizinc-2.10.1-globals.txt:62` read → the name.
- `explenation generator.ml:813-814` and `:851-853` read → the two existing single-`Decomp_devent`
  `rule7` uses (`gcc`, `among`); `:512` → the `hd` site.
- **Scratch generator run, 2026-09-21** — a copy of the generator in this session's scratch
  directory with `rule1` + `rule7` appended and `explainall [xac] … "cata/r4_exactly.tex"`.
  OCaml 5.1.1, exit 0, **2** `\frac` (`grep -o`), footer as quoted, no `DEFECT` line.
  **Nothing was added to the repository:** generator untouched, no `cata/` file changed,
  `make check` goldens unaffected.
- **Not fetched, not read:** the MiniZinc library, any paper. No web access.

**Discrepancy noted, not fixed.** `decomps/exactly.md:18-20` cites `nvalues`' analogous `B4`
step at "generator lines 406-409"; measured 2026-09-21 `nvalues` is at **839-842**. W1-T14.
