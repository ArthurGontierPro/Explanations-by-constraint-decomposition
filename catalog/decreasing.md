# `decreasing`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `decreasing`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — no literature + solver decomposes (`tools/mzn_coverage.py --rank`, ecodes `E0`) |
| **Status** | `validated: sound and minimal at n,m <= 4` |
| **Generated** | 2 rules in `cata/decreasing.tex` |
| **Validator** | 2 `SOUND and MINIMAL`, 0 flagged |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:193` records "none specific" |
| **Last measured** | 2026-09-21, `make validate` (E2's own run) and `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`decreasing(array [$X] of var int: x)`

The array is non-increasing: `x[i] >= x[i+1]` for every adjacent pair.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:49` carries the *name* only. The signature above is
recall, not a citation; the decomposition below is read off the generator and is quotable.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:193` covers `increasing`, `decreasing` and the
`strictly_*` variants in one row: `| none specific | decomp | **E0** — **already correct in
the repo**; cata/increasing.tex and cata/decreasing.tex are cleanly dual |`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only.

**Noted contradiction**, carried from [`increasing.md`](increasing.md): that row's phrase
"already correct in the repo" uses a word `catalog/README.md` forbids. The defensible claim is
`validated: sound and minimal at n,m <= 4`.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:193`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.

## Decomposition used here

**Generator value:** `decr`, `explenation generator.ml:832-833`
**Emitted by:** `explainall [xbc] decr "cata/decreasing.tex"`, line 883
**Spec:** `decomps/increasing.md` (one file for the four monotone variants). **Its line
citation "lines 688-691" is stale** — the values are at 830-833 today.

```ocaml
let decr = [Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
            Decomp (2, rule4, [Decomp_devent (true, (B 1), id, id); Decomp_devent (false, (B 1), imoin 1, iplus 1)])]
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i ≥ t`, **bounds** consistency, identical to `incr`.
- **step 2, `rule4`** — the same two-literal clause with **the two `Decomp_devent` signs
  swapped**. `incr` asserts `¬B1_{i,t} ∨ B1_{i',t}`; `decr` asserts `B1_{i,t} ∨ ¬B1_{i',t}`,
  with the same pair of shift operators (`imoin 1` descending, `iplus 1` ascending) on the
  second literal. Unfolding `B1_{i,t} ⇔ X_i ≥ t`, `decr`'s clause says
  `X_{i'} ≥ t ⇒ X_i ≥ t` where `i'` is the neighbour the shift selects — the non-increasing
  direction, and exactly what rule 1 below prints as `X_{i'} ≥ t, i'=i+1 ⊢ X_i ≥ t`.

**`decr` is `incr` with exactly the two signs swapped and nothing else** — verified by reading
the two values side by side, which is also what `decomps/increasing.md` claims and what
`CHRISTMAS_LIST.md:193` means by "cleanly dual". `B1` washes out (D-0004); only `X` literals
print.

## Scope of this entry

**Events the generator was asked to explain:** two, both from `xbc`
(`explenation generator.ml:868`) — `X_i ≥ t` and `X_i < t`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i}<t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |

No equality event was asked, and none is answerable: the decomposition reifies a bound. The
two `F` drops are legitimate (W1-T3 measured all 22 drops across the catalog as `F`).

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/decreasing.tex`.

## Generated rules

Rendered from `cata/decreasing.tex` (`grep -o '\\frac' cata/decreasing.tex | wc -l` → 2).

### Rule 1 — `X_i ≥ t`

```
X_{i'} ≥ t ,  i'=i+1
--------------------- ⊢
X_{i} ≥ t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(no binder)`.
`cross-check: store sweep agrees with singleton reduction`

### Rule 2 — `X_i < t`

```
X_{i'} < t ,  i'=i-1
--------------------- ⊢
X_{i} < t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(no binder)`.
`cross-check: store sweep agrees with singleton reduction`

**Both rules fire**, for the same reason as `increasing`'s: the premise is a single literal
about the adjacent variable, reached by an index *equation* and not by a binder, so it is
satisfiable under the constraint at every interior index. The boundary conditions are
unprinted — rule 1 has no instance at `i = n`, rule 2 none at `i = 1`.

**The two `.tex` files are the exact index-mirror of one another:** `increasing` pairs
`i'=i-1` with `≥` and `i'=i+1` with `<`; `decreasing` pairs them the other way. Nothing else
differs. That is the strongest "cleanly dual" statement available from the artifacts, and it
is a byte-level reading, not an inference from the source.

## Status

**`validated: sound and minimal at n,m <= 4`**

Both rules are sound and minimal at `n, m ∈ {2,3,4}`, all 9 pairs, store sweep at `n, m ≤ 3`
(`docs/VALIDATOR.md:184`). No ambiguous reading; the generator flags no D-0009 defect for this
entry.

**Floor, not strength.** Minimality means the single premise is not droppable. It does not
rank this schema against a chained one, and it says nothing about whether a bounds propagator
would explain a pruning this way. What is worth recording is the *negative* control: one of
the validator's own self-tests is `index equation unsound` built on `decreasing`
(`docs/VALIDATOR.md:252`, expected `UNSOUND`, got `UNSOUND`), so the checker is known to
distinguish this entry's index equation from a wrong one rather than passing everything.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.** `CHRISTMAS_LIST.md:193` records "none specific"; nothing is
sourced into `catalog/_literature/`; this session has no web access and did not search.

The one comparative statement available is internal, and it is the same one
[`increasing.md`](increasing.md) makes: gccat's `comparison swapped` link
(`docs/GCCAT.md:105`) is "the only near-mechanical relation" between constraints' explanations
in the whole catalog, "and it is a renaming, not a derivation". Here the renaming holds
exactly — and it holds because two *separately authored* decomposition values happen to be
sign-swapped, not because anything transports a rule. The contrast to draw is with
[`atleastnvalues.md`](atleastnvalues.md) / [`atmostnvalues.md`](atmostnvalues.md), the other
`comparison swapped` pair in this catalog, where the generator produces **byte-identical**
output for two constraints with opposite closure properties. Same relation, opposite outcome:
here the two constraints get two different, mirror-image files, each validated 2/2; there they get one file, which cannot be a sound rule for both.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **none.** `rule1` + `rule4` + `OpShift` cover this decomposition completely |
| `G8` | only for a guarded variant: `ind_set` names whole ranges, so the boundary restriction on `i'=i±1` cannot be printed |

Extensions: **E0** (`CHRISTMAS_LIST.md:193`). `strictly_decreasing` is priced E0 in
`decomps/increasing.md` but has no decomposition value and emits no file, so it is **not**
covered by this entry.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/decreasing.tex  (2 rules) ----`,
  two `VERDICT   : SOUND and MINIMAL`. Run totals: **34 rules checked in 11 entries: 13 SOUND
  and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**; 19/19 invariants hold
  (including `decreasing contractible wrt VARIABLES  gccat Cdecreasing  ok`); all 11 controls
  behaved.
- `python3 tools/mzn_coverage.py --rank --json` → `decreasing` in
  `A no-literature + solver-decomposes`, `ecodes: ['E0']`, `line: 193`.
- `grep -o '\\frac' cata/decreasing.tex | wc -l` → 2; `cmp` against `cata/increasing.tex`
  → they differ (the index-mirror above), unlike the `atleast`/`atmost` pair.
- `explenation generator.ml:830-831` vs `832-833` read side by side, not run → the two-sign
  swap. Line 868 (`xbc`) and line 883 (the emitting call) likewise.
- `CHRISTMAS_LIST.md:193`, `:106-108` read → literature, solver, legend.
- `docs/GCCAT.md:105` read → `comparison swapped`.
- `docs/VALIDATOR.md:184, 252` read → sizes, and the `index equation unsound` control.
