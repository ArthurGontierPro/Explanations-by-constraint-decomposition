# `all_different_except`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `all_different_except`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G8` |
| **Generated** | no generator entry — there is no `cata/all_different_except.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `all_different_except` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:117` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `explenation generator.ml` read |

## Constraint

`all_different_except(array[int] of var int: x, set of int: v)` — the values in `x` are
pairwise distinct, **except** that any number of them may take a value in the excepted set `v`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:18` carries the *name* only. The line above is the
reading `decomps/all_different.md` works from, where the excepted value is "a parameter for the
general one"; that file states it without a citation, so **treat the arity as recall**, and note
that it writes `v_0` for a single excepted value where MiniZinc's name (`_except`, not
`_except_value`) suggests a set. The gap analysis below is the same either way — a range minus
one point and a range minus a set are both things `ind_set` cannot name.
`CHRISTMAS_LIST.md:117` files it under section `1. AllDifferent family`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:117` — the row that covers
`all_different_except` and `all_different_except_0` together — reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/all_different_except.md`,
no paper was fetched by this session and no web access was used.

**The neighbouring row does cite one, and it is not transferable.**
`CHRISTMAS_LIST.md:116` cites Downing, Feydy and Stuckey 2012, *Explaining alldifferent*, for
`all_different`; `catalog/_literature/alldifferent.md` sources it and `catalog/alldifferent.md`
calibrates against it. **Nothing from that file is carried into this entry**: the excepted
value changes the constraint's Hall-set structure, which is exactly what that paper's §5/§6
explanations are about, and asserting the transfer would be writing a published rule shape from
memory. Whether it transfers is a question for whoever sources `_literature/` next.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:117`, solver cell `decomp **[G]**`; legend at
`CHRISTMAS_LIST.md:106-109`. Verified 2026-09-21. The machine-filled stub read this correctly —
note the `[G]`, which the other twelve entries in this session's slice do not have: Geas
implements this one natively while Chuffed decomposes it.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/all_different.md`](../decomps/all_different.md), which covers the family in
one file; shape **S2** in `decomps/_shapes.md` ("reify-and-count: Boolean sum against a bare
threshold"), where `all_different_except` and `all_different_except_0` are listed as instances
with the annotation "guarded index set, G8".

The chain is `all_different`'s, with one change:

1. `B_{i,t} ⇔ X_i = t` — `rule1`, AC.
2. `∑_i B_{i,t} ≤ 1` — `rule5`, single `Decomp_devent` — **for `t` ranging over the value range
   minus the excepted value(s)** instead of over the whole range.

That is the entire difference, and `CHRISTMAS_LIST.md:117`'s route cell says as much, verbatim:
"**E0**, same shape with a guard on the excepted value". Step 1 and step 2's schemas are
`alldiff` at `explenation generator.ml:808-809`, shipped and validated 1 of 1 by
`make validate`.

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/all_different_except.tex`
and so no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**What the artifact would be if the guard were dropped.** `alldiff`'s own artifact:
`cata/alldifferent.tex`, one rule, `X_i ≠ t ← X_{i'} = t, ∀i' ≠ i`. Dropping the guard is not
an approximation of this constraint, it is the *other* constraint — the rule is unsound for
`all_different_except` at any `t` in the excepted set, since two positions may both take it.
So there is no "partial" entry available here, which is why the status is `nothing generated`
and not a weaker rule with a caveat.

## Generated rules

**None.** `cata/all_different_except.tex` does not exist.

## Status

**`nothing generated — blocked on G8`.**

`G8` is "**`ind_set` names only whole predefined ranges** — no subrange, no exclusion", and
`docs/DECOMP_FORMAT_NOTES.md:80` names `all_different_except*` as the constraint that hit it.
Measured against the source today, that is exactly right and there is no way around it:

- `ind_set` is `D of int | D2 of ind_name list` (`explenation generator.ml:6`) — two
  constructors, neither of which is "a named range minus a point or a set";
- `ind_set_defined` (`:459`) admits `D 1`, `D 2` and `D 3` and nothing else, and
  `printind_set_int` (`:460`) prints them as `[1,n]`, `[1,m]`, `[1,n]`. A fourth `D k` is
  **refused** by W1-T2 rather than printed;
- `D2`, the list-of-index-names hook that might have expressed an explicit value set, is used
  by no decomposition and **raises** in the printer (`:464`). `docs/DECOMP_FORMAT_NOTES.md:100-111`
  records that W2-A's "checked negative" on `D2` was **withdrawn** for this reason.

**The decomposition can be written on paper and not encoded** — `decomps/all_different.md`'s own
conclusion, and this entry adopts it rather than reopening it. Everything else about the
constraint is free: the two schemas exist, the threshold is 1 as it is for `all_different`, and
the E0 route cell is right about the schemas.

**One thing G8 would *not* fix, kept here so it is not rediscovered as a surprise.** The
`all_different` shape emits one rule and cannot emit the `X_i = t` direction; `CLAUDE.md` and
`decomps/all_different.md` both record that this needs counting across sums, **E4**, and is not
a bug. An `_except` entry, once G8 lands, would inherit exactly that: one rule, not two.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:117`'s literature cell is `none`, the condition `catalog/TEMPLATE.md`
attaches to this verdict; and with 0 rules there is no premise to place in an implication order
in either direction.

**Not `pending sourcing`, and not a transfer from `all_different`.** Pending is for a row citing
something unread; this row cites nothing. And `catalog/alldifferent.md`'s verdict — coincides
with Downing §4 at `n = 2`, strictly weaker for every `n ≥ 3` — is **about a different
constraint**: it is stated of a rule this entry does not have, against a paper this row does not
cite. Recording that non-transfer is the point of the verdict here.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **the binding one and the only one.** No subrange, no exclusion: the summed value family cannot be `[1,m] \ v`. `docs/DECOMP_FORMAT_NOTES.md:80` names this constraint against it |
| `E4` | not a gap — the missing `X_i = t` direction, inherited from `all_different` and unchanged by G8 |
| `G1` | **not** binding here, unlike the counting family: the threshold is 1, the same invisible 1 `all_different` already lives with, and `all_different_except` does not vary it |

Extensions: **E0** — `CHRISTMAS_LIST.md:117`, verbatim: "**E0**, same shape with a guard on the
excepted value". The cell is right that no new *schema* is needed and silent about the index
set, which is the whole of the block. Closing G8 belongs to **E2**/W2-T1.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 117,
  section `1. AllDifferent family`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`; no line names an `all_different_except` entry.
- `CHRISTMAS_LIST.md:117`, `:116`, `:106-109` read → this row's three cells, the
  `all_different` citation named in "Published explanation", and the solver legend.
- `tools/data/minizinc-2.10.1-globals.txt:18` read → the name.
- `explenation generator.ml` read, not run: `:6` (`ind_set`'s two constructors), `:459-460`
  (`ind_set_defined` and the three defined ranges), `:464` (`printind_set`'s `D2` raise),
  `:808-809` (`alldiff`).
- `docs/DECOMP_FORMAT_NOTES.md:80` read → G8's wording and the constraints named against it;
  `:96-107` → the withdrawal of the `D2` checked negative.
- `decomps/all_different.md` and `decomps/_shapes.md` (S2) read → the family spec and the shape.
- **No scratch run for this entry.** The one substitution that matters cannot be written down:
  there is no `ind_set` value for "range minus a point", so there is nothing to hand the
  generator. The neighbouring measurement that stands in for it is [`count`](count.md)'s, where
  a `D 4` value set produced `REFUSED … (D4) — W1-T2` on all four events.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.

**Discrepancies noted, not fixed** (`decomps/` is not this session's).

1. **`decomps/all_different.md:17` says `_except` is "blocked by gap G6" — that number moved.**
   In the consolidated wave-two numbering (`docs/DECOMP_FORMAT_NOTES.md:76-90`) this gap is
   **G8** and **G6 is now the 2-D constant table** that blocks `table`. The file is using its
   own pre-consolidation, per-family numbering ("was perm G6" in the reconciliation table), and
   a reader who takes the G6 at face value today lands on the wrong gap.
2. **`decomps/all_different.md:8` and `:20-21` cite stale line numbers.** It gives `alldiff` at
   "l.808–809" — **correct**, measured today — but `printind_set` at "line 375" and `ind_set` at
   "line 6"; measured, `printind_set` is at **462-464** and `ind_set` at **6**.
3. **The same file says `D2` "doesn't handle it beyond `\"setfils\"` — a placeholder string".**
   That string no longer exists: W1-T2 replaced it with a raise
   (`explenation generator.ml:464`), as `docs/DECOMP_FORMAT_NOTES.md:105-107` records. The gap
   is unchanged; only the symptom is.
