# `member`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `member`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E0']` |
| **Status** | **`encodable today, not encoded`** for the fragment this repo decomposes (`y` a parameter); **`nothing generated — blocked on G3`** for MiniZinc's var-target signature. **Two fragments, two statuses — read the fragment statement below before quoting either.** |
| **Generated** | **0** rules — there is no `cata/member.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:195` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

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

**Generator value:** none. There is no `member` value in `explenation generator.ml`
(`grep -c -i 'member' 'explenation generator.ml'` → `0`) and no
`explainall … "cata/member.tex"` call.
**Emitted by:** nothing.
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

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` / `X_{i} ≠ t` (would be, from `xac`) | — | **0** | not run: no generator value exists |

**`member` is the cheapest unwritten entry in this slice, and that is the finding.** Every
schema it needs already runs: `rule1` is the reification every shipped entry starts with,
and the `rule4` existential step is the one `nvalues` uses at
`explenation generator.ml:841` (`Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni); …])`). Nothing in `docs/DECOMP_FORMAT_NOTES.md`'s eighteen gaps
touches the parameter-target reading. What is missing is the two `Decomp`s themselves and
the `explainall` line, and **the reason they are missing is that `member` was specified in
wave two and the generator has not been extended since** — the value list at
`explenation generator.ml:804-864` is the 2020 set.

**The variable-target reading is a different constraint and is blocked.** With `y` a
decision variable, `B_i ⇔ X_i = y` compares two decision variables, which is **G3**:
`docs/DECOMP_FORMAT_NOTES.md:34` states it and explicitly anticipates this case —
"`count`'s and `among`'s general MiniZinc signatures allow `v`/elements of the channel to be
variables, and that would need this". MiniZinc's `member` is in the same position. This is
read off the gap statement and the type definitions (`Global_event` at l.50 carries one
`var_name`; index slots take `ind_name`, l.5, l.16), **not** measured.

## Generated rules

**None.** There is no `cata/member.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`encodable today, not encoded`** for the parameter-target fragment;
**`nothing generated — blocked on G3`** for the var-target signature. D-0012 requires the
fragment to be named, and here it changes the status, not just the prose.

**A caveat on the first value, measured rather than assumed.** The orchestrator records
`encodable today, not encoded` as newly defined in `catalog/README.md` and
`catalog/TEMPLATE.md`. As of this commit it is **in neither**: the legend still lists six
values, ending at `nothing generated — blocked on G<n>` with "the gap number is required,
not optional", and `grep -rn 'encodable today' catalog/` finds the phrase only in prose —
`catalog/strictly_increasing.md:184`, `catalog/strictly_decreasing.md:186`,
`catalog/value_precede.md:26`, and this slice. R5's own shipped Status row for
`strictly_increasing` still reads `**nothing generated** — and **no status-legend value
fits**`. This entry uses the value the orchestrator directs and records that the definition
has not landed. Reported, not fixed: `catalog/README.md` is not this session's.

**An earlier draft of this entry filed the whole constraint under
`nothing generated — blocked on G3` and argued the legend had a hole.** The hole was real;
the new value fills it, and forcing the parameter fragment under a gap number was the
distortion the value exists to prevent. Corrected here.

**What this means in practice.** If somebody spends an hour adding

```ocaml
let member = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule4, [Decomp_devent (true, (B 1), id, oni)])]
```

— **a sketch, not a tested value; nothing here was compiled** — and an `explainall` line,
this entry stops being empty and becomes `generated, unvalidated` and then whatever
`make validate` says. Nothing in the format has to change first. That is not true of any
other entry in this slice except [`inverse`](inverse.md).

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:195`'s literature column reads `none`, and per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing`: no paper is cited.
Not `out of reach`: that needs a published premise to be out of reach of. Nothing was
searched and no comparison is fabricated.

The solver cell is `decomp` with no `[G]` and no `[C]`, so unlike [`inverse`](inverse.md)
and `element` there is not even an unpublished implementation to note. **All three of the
catalog's sources are empty for `member`** — and here, uniquely in this slice, the third one
is empty for no reason stronger than that nobody has typed it.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the MiniZinc signature only.** `B_i ⇔ X_i = y` with `y` a decision variable is a variable-vs-variable comparison (`docs/DECOMP_FORMAT_NOTES.md:34`, which anticipates exactly this case for `count`/`among`) |
| — | **nothing blocks the parameter-target fragment**, which is why its status is `encodable today, not encoded` rather than a gap number. `rule1` + `rule4` over one index family is shape S4 and runs today inside `nvalues` (l.841). One user array, so **no G2 either** — unlike [`inverse`](inverse.md) and `write`, nothing has to borrow a letter |
| `G17` | no pivot-elimination pass. Not biting: `B_i` is reification scaffolding and washes out, as `decomps/member.md` says |

Extensions: **E0** (`CHRISTMAS_LIST.md:195`, route cell "**E0** — `exists(i)(x[i]=y)`").
E0 means *no extension needed*, which is consistent with everything above.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

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
- `catalog/README.md` status legend read, and `grep -rn 'encodable today' catalog/` run →
  six legend values, the new one absent from the legend and present in four entries' prose.
  That is the evidence for the Status caveat, and the grep is a run.
- **The sketched `let member = …` in Status is a sketch and was not compiled**, and the
  fragment argument is reasoning over the source, labelled as such in place.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`encodable today, not encoded` is used by this entry and is defined in neither
   `catalog/README.md`'s legend nor `catalog/TEMPLATE.md`.** Measured 2026-09-21. The value
   is the right one — it is exactly this entry's position, and `catalog/strictly_increasing.md`
   and `catalog/strictly_decreasing.md` reached it independently — but until the legend
   carries it, four entries use a status the format does not define, which is the same kind
   of defect as an artifact quantifying over an undefined `D_k`.
