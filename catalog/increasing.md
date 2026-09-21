# `increasing`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `increasing`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — no literature + solver decomposes (`tools/mzn_coverage.py --rank`, ecodes `E0`) |
| **Status** | `validated: sound and minimal at n,m <= 4` |
| **Generated** | 2 rules in `cata/increasing.tex` |
| **Validator** | 2 `SOUND and MINIMAL`, 0 flagged |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:193` records "none specific" |
| **Last measured** | 2026-09-21, `make validate` (E2's own run) and `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`increasing(array [$X] of var int: x)`

The array is non-decreasing: `x[i] <= x[i+1]` for every adjacent pair.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:70` carries the *name* only; the snapshot has no
signatures. The signature above is recall, not a citation. What is quotable in-repo is the
decomposition below, read off the generator.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:193` — the row for
`increasing`, `decreasing`, `strictly_*` — reads `| none specific | decomp | **E0** —
**already correct in the repo**; cata/increasing.tex and cata/decreasing.tex are cleanly
dual |`.

**Rule shape:** there is nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only, and no paper is cited for this constraint anywhere in the
literature index.

**Noted contradiction, not a finding about the literature.** That same row calls the entry
"already correct in the repo". `catalog/README.md` ("Never write 'correct'") and `CLAUDE.md`
both forbid that word for a catalog entry; the defensible statement is the one in the header
table, `validated: sound and minimal at n,m <= 4`. The row predates the validator and its
wording was not updated.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:193`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.

## Decomposition used here

**Generator value:** `incr`, `explenation generator.ml:830-831`
**Emitted by:** `explainall [xbc] incr "cata/increasing.tex"`, line 884
**Spec:** `decomps/increasing.md` (covers `increasing`, `decreasing` and both `strictly_*`
variants in one file). **Its line citation "lines 688-691" no longer resolves** — the value is
at 830-831 after W1-T3/W1-T7 moved the file. Same value, same text.

```ocaml
let incr = [Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
            Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true, (B 1), imoin 1, iplus 1)])]
```

- **step 1, `rule1`** — `B1_{i,t} ⇔ X_i ≥ t`, **bounds** consistency. This is the reification
  of a *bound*, not of an equality: `increasing` never asks whether `X_i = t`.
- **step 2, `rule4`** — a two-literal clause `¬B1_{i,t} ∨ B1_{i-1,t}`, i.e.
  `B1_{i,t} ⇒ B1_{i-1,t}`: if `X_i ≥ t` then `X_{i-1} ≥ t`. The two index operators are
  `imoin 1` descending (`i-1`) and `iplus 1` ascending (`i+1`), which is the whole content of
  the constraint.

`B1` washes out; only `X` literals are printed (D-0004). Confirmed by reading the `.tex`:
no `B` appears.

## Scope of this entry

**Events the generator was asked to explain:** two, both from `xbc`
(`Global_event (true, X, [Ind (I 1,[]); Ind (T 1,[])], BC)`, `explenation generator.ml:868`) —
`X_i ≥ t` and its negation `X_i < t`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i}<t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |

No `X_i = t` event was asked and none could be answered: the decomposition reifies a bound
(`BC`), so an equality literal has no reified counterpart to descend into. **Nothing here
explains an equality, and the two `F` drops are legitimate** — W1-T3 measured that all 22
branch drops across all 16 entries were `F`, and no `IM`/`FE`/`R` ever occurred
(`CLAUDE.md`, "Traps"; `docs/ROADMAP.md:49`).

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/increasing.tex`.

## Generated rules

Rendered from `cata/increasing.tex` (`grep -o '\\frac' cata/increasing.tex | wc -l` → 2).
`[1,n]` is the variable index set.

### Rule 1 — `X_i ≥ t`

```
X_{i'} ≥ t ,  i'=i-1
--------------------- ⊢
X_{i} ≥ t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(no binder)`.
`cross-check: store sweep agrees with singleton reduction`

### Rule 2 — `X_i < t`

```
X_{i'} < t ,  i'=i+1
--------------------- ⊢
X_{i} < t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(no binder)`.
`cross-check: store sweep agrees with singleton reduction`

**These two rules fire.** Unlike `alldifferent`'s single rule, neither premise is universally
quantified: each names exactly one other variable, the adjacent one, through an index
*equation* rather than a binder. The only states they cannot reach are the boundary ones —
rule 1 has no instance at `i = 1` and rule 2 none at `i = n`, because `i-1` and `i+1` fall
outside `[1,n]`. The `.tex` does not say so; it prints `i'=i-1` with no range condition, and
the validator's index-equation handling supplies the bound (its two `index equation` controls,
`docs/VALIDATOR.md:251-252`, are built on exactly this entry and on `decreasing`).

## Status

**`validated: sound and minimal at n,m <= 4`**

Both generated rules are sound and minimal at the enumerated sizes: `n, m ∈ {2,3,4}`, all 9
pairs, with the store sweep at `n, m ≤ 3` (`docs/VALIDATOR.md:184`). No reading is ambiguous
and the generator flags no D-0009 defect for this entry.

**Sound and minimal is a floor, not strength.** Minimality here means neither rule has a
droppable premise — each has exactly one, and dropping it leaves an empty premise. It does not
say the pair is the strongest schema available: a rule chaining two steps
(`X_{i-2} ≥ t ⊢ X_i ≥ t`) is equally sound, and nothing in this method's output orders the
two. What can be said, and is unusual in this catalog, is that these rules **fire**: the
premise is one literal about one adjacent variable, so it is satisfiable in the presence of
the constraint at every interior index.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.** `CHRISTMAS_LIST.md:193` records "none specific" for this
family, and that row is the repo's own literature index — one session of web research covering
all 118 MiniZinc globals (`CLAUDE.md`, "Context budget"). No paper shape exists in
`catalog/_literature/` to compare against, and **this session did not search the web** (no
access, and the protocol says grep the index instead).

So there is no implication comparison to state. Two things can be said in its place, and both
are about this repo rather than about the literature:

- **The `increasing`/`decreasing` pair is the one near-mechanical rule transport in the whole
  catalog.** `docs/GCCAT.md:105` records that gccat's typed `See also` links carry explanations
  between constraints in essentially one case: `comparison swapped`
  (`atleast_nvalue`/`atmost_nvalue`, `increasing`/`decreasing`) — "and it is a renaming, not a
  derivation". The two entries here are that renaming, and the generator produces both
  independently rather than transporting one to the other. Compare
  [`atleastnvalues.md`](atleastnvalues.md), where the same `comparison swapped` relation is
  handled by the generator as an *identity* and is therefore a defect.
- **`strictly_increasing` is not covered by this entry.** `decomps/increasing.md` prices it at
  **E0** — same two schemas, threshold shifted by one — but it has no decomposition value and
  emits no file.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **none.** Every schema this decomposition needs (`rule1` BC channel, `rule4` two-literal clause, `OpShift` on the `i` family) exists and runs |
| `G8` | would be needed only for a *guarded* variant (`ind_set` names whole ranges only, so "`i ∈ [2,n]`" cannot be written) — which is why the boundary condition on `i'=i-1` is implicit rather than printed |

Extensions: **E0** (`CHRISTMAS_LIST.md:193`).
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/increasing.tex  (2 rules) ----`,
  two `VERDICT   : SOUND and MINIMAL` lines, each with `readings  : 1 (1 sound, 0 unsound)`
  and `cross-check: store sweep agrees with singleton reduction`. Run totals: **34 rules
  checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of
  scope**; 19/19 encoding invariants hold; all 11 controls behaved.
- `python3 tools/mzn_coverage.py --rank --json` → `increasing` in
  `A no-literature + solver-decomposes`, `ecodes: ['E0']`, `line: 193`.
- `grep -o '\\frac' cata/increasing.tex | wc -l` → 2.
- `cata/increasing.tex` read, not run → the two rules and the diagnostics footer.
- `explenation generator.ml:830-831, 868, 884` read, not run → the `incr` value, the `xbc`
  global event and the emitting call. Line numbers checked against the current file, not
  copied from `decomps/increasing.md`, which cites 688-691 and is stale.
- `CHRISTMAS_LIST.md:193` and `:106-108` read → literature column, solver column, legend.
- `docs/GCCAT.md:105` read → the `comparison swapped` observation.
- `docs/VALIDATOR.md:184, 251-252` read → enumerated sizes and the two index-equation controls.
