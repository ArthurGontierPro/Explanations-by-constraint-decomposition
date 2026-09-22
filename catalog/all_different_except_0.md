# `all_different_except_0`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `all_different_except_0`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

**This entry shares a row, a spec, a shape and — until 2026-09-22 — a gap with
[`all_different_except`](all_different_except.md).** Everything below that is not specific to
the excepted value being fixed at `0` is stated there and not duplicated here. **The sibling
now generates a rule and this variant still does not**, and the difference is no longer a gap:
see "Decomposition used here".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `encodable today, not encoded` — **changed 2026-09-22.** `G8` closed, nothing was authored for this variant, so there is no gap left to name |
| **Generated** | **0** — there is no `cata/all_different_except_0.tex` and no generator value for it. The sibling's artifact, `cata/alldifferent_except.tex`, is schematic in the excepted parameter |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-22) names no entry under this name — and would not see one if it existed, since `validator.ml`'s lists are hardcoded and it never scans `cata/` (**W1-T18**) |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:117` records `none` |
| **Last measured** | 2026-09-22, `make check`, `make validate`, `ls cata/`, and reads of `explenation generator.ml` and `cata/alldifferent_except.tex` |

## Constraint

`all_different_except_0(array[int] of var int: x)` — the values in `x` are pairwise distinct,
except that any number of them may be `0`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:19` carries the *name* only; the line above is the
reading `decomps/all_different.md` works from ("fixed at `0` for the `_0` variant"), recorded
there without a citation. **Treat the arity as recall.** `CHRISTMAS_LIST.md:117` files it under
section `1. AllDifferent family`.

**There is a third name for the same object.** `CHRISTMAS_LIST.md:120` carries a row
`alldifferent_except_0` (alias) | — | — | as above`. It is the older MiniZinc spelling and the
list marks it an alias with empty literature and solver cells. `docs/COVERAGE.md:137-139` names
that row as one of three in the file with no E-code, and `catalog/count_fn.md` records
(measured 2026-09-21) that the line it gives for it, 118, is stale and the row is at **120**.
Nothing in this entry rests on that row. **Note that the generator's new artifact is spelled
`cata/alldifferent_except.tex`** — the alias spelling — which is a coincidence of the `cata/`
naming convention, not a statement that the artifact is the `_0` variant.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:117`'s literature column reads, verbatim:

> none

**Rule shape:** nothing to state — no `catalog/_literature/all_different_except_0.md` exists,
no paper was fetched and no web access was used. See
[`all_different_except.md`](all_different_except.md), "Published explanation", for why the
`all_different` citation on the neighbouring row (`CHRISTMAS_LIST.md:116`, Downing, Feydy and
Stuckey 2012) is **not** transferred here.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:117`, solver cell `decomp **[G]**`; legend at
`CHRISTMAS_LIST.md:106-109`. Verified 2026-09-21. The row covers both `_except` and
`_except_0`, so the cells are shared; the `[G]` is Geas' native propagator.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** [`decomps/all_different.md`](../decomps/all_different.md), which covers
`all_different`, both `_except` variants and `symmetric_all_different` in one file; shape
**S2** in `decomps/_shapes.md`.

**The difference from [`all_different_except`](all_different_except.md), in one sentence:** the
excluded value is the constant `0` rather than a parameter, so the summed value family is
`[1,m] \ {0}` — a *fixed* hole instead of an instance-dependent one.

**That difference used to buy nothing, because neither hole could be written. Now both can.**
`ind_set` gained `DExc of ind_set * ind_elt list` (`explenation generator.ml:50`), and
`ind_elt` is `EInt of int | EInd of ind_name | EPar of string` (`:47`) — so the sibling's
`DExc (D 2, [EPar "v"])` has a constant counterpart, `DExc (D 2, [EInt 0])`, already supported
by both `ind_set_defined` (`:520-525`) and `printind_set` (`:535`). **Nothing in the repository
writes it.** There is no `alldiffexc0` value and no `explainall … "cata/all_different_except_0.tex"`
call, which is exactly the condition `catalog/README.md`'s legend added
`encodable today, not encoded` for: do not invent a G-number for it.

**One wrinkle survives the fix, and it is a naming problem, not a gap.** The value range the
printer names is `D 2`, rendered `\llbracket1,m\rrbracket` (`:526`), and `0` is not in it. So
`DExc (D 2, [EInt 0])` would print `[1,m] \ {0}` — a hole punched in a range that does not
contain it. The rule would still be sound (excluding a value that is not there excludes
nothing, and the constraint's real content is `all_different` on `[1,m]`), but it would say
something misleading, and the honest encoding respells the range instead. **This paragraph is
read off `:526` and `:535`, not measured.** It is the same class of problem as W1-T2's
"`D_4` means a different set in each decomposition": index sets are named, not defined, from
the printer's side.

## Scope of this entry

**Events the generator was asked to explain:** none. There is no
`cata/all_different_except_0.tex` and so no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**What the artifact would look like, without asserting that it would be identical.** The
sibling's one rule is schematic in the excepted parameter:
`X_i ≠ t, t ∈ [1,m] \ {v} ⊣ X_{i'} = t ∀i' ≠ i`. This constraint is that schema at `v = 0`,
and at `v = 0` the side condition is vacuous over `[1,m]` — see the wrinkle above. **G-1's
exhaustive check ran "over all `n,m ≤ 4` and all `v`"; the footer does not say which values `v`
ranged over, and `0 ∉ [1,m]`, so its soundness figures are not carried into this entry.**

## Generated rules

**None.** `cata/all_different_except_0.tex` does not exist (`ls cata/`, 2026-09-22: 18 files,
none under this name).

## Status

**`encodable today, not encoded`**

The status changed on 2026-09-22 and the previous one — `nothing generated — blocked on G8` —
is retired. `G8` is closed: `DExc` names a range minus listed constants, `EInt` supplies the
constant, and the sibling entry demonstrates the whole mechanism on a parameter. What is
missing here is **an authoring step nobody has taken**, not a capability. `catalog/README.md`'s
legend says to use this value rather than invent a G-number for exactly that situation.

Two things this status does not claim. It does not claim the resulting rule would be sound —
nothing has been generated, so nothing has been measured, and the sibling's figures are not
transferable (see "Scope"). And it does not claim the encoding would be *clean*: the
`0 ∉ [1,m]` wrinkle above is real and would want the range respelled, which `DSub` can now do
and which nobody has done either.

**What the variant would inherit if it were authored**, from the sibling, measured there:
one rule and not two (the `X_i = t` direction needs **E4**), soundness only for `n ≥ 2`, and a
premise naming every other variable, so it fires only at `n = 2`.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:117` names no paper, and with 0 rules there is no premise to place in an
implication order. Not `pending sourcing`, and **not** a transfer of `catalog/alldifferent.md`'s
verdict against Downing et al. §4 — see [`all_different_except.md`](all_different_except.md),
"Calibration", where the non-transfer is argued once and where the arrival of a generated rule
is recorded as not changing it.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **closed 2026-09-22.** `DExc (D 2, [EInt 0])` is writable and printable today; nothing writes it. That is why the status is `encodable today, not encoded` and why no gap is named in it |
| `E4` | not a gap — the missing `X_i = t` direction, inherited from `all_different` and unchanged by G8 |
| `G1` | not binding: the threshold is `all_different`'s invisible 1 and this variant does not vary it |
| — (not a gap) | **the printed range `[1,m]` does not contain `0`**, so the natural encoding states a vacuous exclusion. A naming problem in `printind_set_int` (`:526`), the same family as W1-T2's per-decomposition `D_k`; `DSub` is the machinery that would respell the range |
| — (not a gap) | **W1-T18**: even with an artifact, `make validate` would not see it |

Extensions: **E0** — `CHRISTMAS_LIST.md:117`, verbatim: "**E0**, same shape with a guard on the
excepted value". Now true of the machinery as well as the schema.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering; **G8 at line 87**,
re-measured today — this entry previously cited `:80`).

## How this entry was produced

- `ls cata/` (2026-09-22) → 18 files; **no `all_different_except_0.tex`**, and a new
  `alldifferent_except.tex`, which is the sibling's artifact and not this one's.
- `make check` (run 2026-09-22, redirected then grepped) → `GATE PASSED`, with
  `ok alldifferent_except.tex (1 frac-occurrences)`. Nothing under this entry's name appears.
- `make validate` (run 2026-09-22, redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`, `== 4 rules in 5 entries out of scope ==`; no
  line names this entry.
- `explenation generator.ml` read, not run: `:46-52` (`ind_bound`, `ind_elt`, `ind_set` — six
  constructors now, where this entry used to quote two), `:520-525` (`ind_set_defined`),
  `:526` (`printind_set_int`, the three named ranges and the W1-T2 raise), `:533`
  (`printind_set`'s `D2` raise), `:535` (`printind_set`'s `DExc` case), `:1006-1007`
  (`alldiffexc`), `:1023` (`xacx`). All line numbers measured today (W1-T14).
- `cata/alldifferent_except.tex` read, not run → the sibling's rule and its `%% CAVEAT` footer,
  including the phrase "all `v`" that this entry declines to read as covering `v = 0`.
- `CHRISTMAS_LIST.md:117`, `:120`, `:116`, `:106-109` read → this row, the alias row, the
  `all_different` citation and the solver legend.
- `tools/data/minizinc-2.10.1-globals.txt:19` read → the name.
- `catalog/README.md` read → the status legend, including `encodable today, not encoded` and
  its instruction not to invent a gap number for this case.
- `catalog/all_different_except.md` (this session's sibling entry) read → everything this entry
  defers to rather than restating.
- **No scratch run.** The substitution that matters is now writable, but writing it means
  adding a value and an `explainall` call to `explenation generator.ml`, which is the rule
  engine and is not this session's file.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.

**Discrepancies noted, not fixed.** The three recorded in
[`all_different_except.md`](all_different_except.md) apply here unchanged, with one correction
that was checked today rather than inherited: **`decomps/all_different.md` no longer says
"G6"** — it was fixed on 2026-09-21 to say `G8` with a note. What is stale in it now is that it
presents G8 as blocking, and that it quotes `ind_set` as two constructors at generator line 6
(measured today: six, at `:48-52`).
