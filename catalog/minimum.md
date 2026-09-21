# `minimum`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `minimum`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecodes `['E2']` (shared row with `maximum`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/minimum.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:196` records the literature column as `none found` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`minimum(var int: m, array[int] of var int: x)`

`m = min_i(x_i)`: `m` is the smallest element of `x`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:94` carries the *name* only. The decomposition
`∀i: m ≤ x_i` and `∃i: m = x_i` is quoted from `decomps/maximum.md`, which states it for this
constraint; the MiniZinc type signature and argument order above are recall.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:196`'s literature column reads, verbatim,
`none found`.

**That phrasing is not the same as the bare `none` used on most rows**, and the difference
is recorded rather than smoothed over: `catalog/element.md` reads `none found` as "a
searched-and-empty finding", i.e. somebody looked. Either way the verdict below is the
same, because `catalog/README.md` and `catalog/TEMPLATE.md` give one verdict for an empty
literature cell.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. No web access was used and no search was made by this
session.

## Solver support

| | |
|---|---|
| Chuffed | native — see the caveat below |
| Geas | absent |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:196`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: **native** (`minimum.cpp`) **[C]**.

**The named file is `minimum.cpp` and the row carries two constraint names.** So the
citation directly supports "`minimum` has a native explaining propagator in Chuffed"; that
`maximum` does too is an inference from the shared row, not from the parenthetical. It is a
very likely inference — a max propagator is a min propagator with the sign flipped — but
this entry marks it as an inference rather than letting the stub's flat `Chuffed | native`
stand for a citation.

## Decomposition used here

**Generator value:** none. There is no such value in `explenation generator.ml`
(`grep -c -i 'minimum' 'explenation generator.ml'` → `0`) and no
`explainall … "cata/minimum.tex"` call.
**Emitted by:** nothing.
**Spec:** `decomps/maximum.md` — titled `# maximum, minimum, arg_max, arg_min, sort,
arg_sort`, so it covers this name, in its first section.
**Shape: none.** `decomps/_shapes.md`'s "Not covered by any shape" table lists exactly five
constraints — `maximum`, `minimum`, `arg_max`, `arg_min`, `span` — all attributed to
**G3**, with the note that they "are not 'unshaped work'; they are a missing primitive".

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.
**Nor could one be authored**: this is the rarer case in the catalog where the blockage is
upstream of the decomposition, not downstream of it.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` / `M \geq t` (would be) | — | **0** | not run: both conjuncts compare two decision variables (G3) |

**The block, verified against the type definitions rather than inferred.** Both conjuncts of
`∀i: m ≤ x_i` and `∃i: m = x_i` compare `m` to `x_i` — **two decision variables** — never a
variable against a domain-derived value. Reading the source:

- `Global_event of bool*var_name*index list*consistancy` (`explenation generator.ml:50`)
  carries **one** `var_name` and a list of `index`es;
- `index` is `Ind of ind_name*ind_modifs list` (l.16) and `ind_name` is the closed enum
  `I | T | P | R of int` (l.5);
- the comparison target is therefore always an index-derived value — `printconstex` (l.509)
  renders the event as `X_{…} = t` or `X_{…} ≥ t` with `t` an `ind_name`, and there is no
  constructor anywhere in `event`, `decomp_event`, `ind_modifs` or `ind_op` that takes a
  **second** `var_name` as the target.

So the atom `m ≥ x_i` has no representation. `decomps/maximum.md` states this and this
entry confirms it by the same method: **"No decomposition can be authored in the current
encoding — this is not a derivation gap, it is a missing primitive."**

**The one place in the repo that disagreed has been settled, and against the disagreement.**
`decomps/span.md` claimed `span` was E0 by reusing `range`/`roots` as a ∀-bound-plus-∃-tight
pair. `decomps/_shapes.md`'s "Contradictions" section resolves it: `range` and `roots` are
Boolean **sums** (`rule6`/`rule7`), not quantifiers, so they are no precedent for min/max at
all, and `span`'s min/max "is `minimum` under another name". The reading that stands is this
one. That matters here because it means **no shipped entry is a template for `minimum`**,
and a session looking for one will find `range`/`roots` and be misled.

## Generated rules

**None.** There is no `cata/minimum.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G3`**

`docs/DECOMP_FORMAT_NOTES.md:34` states G3 as "only variable-vs-domain-value comparisons
exist, never variable-vs-variable", and `:88-89` adds that three independent families hit
it — the counting pilot, `maximum`/`minimum`/`arg_max`/`arg_min`, and `lex_less` — which
"make it load-bearing".

**This is the strongest form of "nothing generated" in the catalog.** For
[`inverse`](inverse.md) the value is writable and unwritten; for [`sort`](sort.md) an atom
is unwritable but a shape exists; here there is **no shape**, because the first atom anyone
would write cannot be typed. Closing G3 does not finish `minimum` either — somebody must
then author the decomposition and decide how `∃i: m = x_i` is encoded, which the format's
existing ∃ machinery (shape S4, `rule4`) can plausibly carry once the atom exists. That
second step is unstarted.

**G2 applies to the name as well**: `var_name` (l.3) is `X | B of int | T | I | V | N | O`
and none of its constructors means "this constraint's own scalar bound". `V` and `N` are
`element`'s and `nvalue`'s. That is a legibility cost, not the blocker, and it is
`docs/DECOMP_FORMAT_NOTES.md:23`'s G2 on a new constraint.

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:196`'s literature column reads `none found`. Per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists` — the searched-and-empty phrasing is stronger
evidence for it than a bare `none`, not weaker. Not `pending sourcing`: no paper is cited.
Not `out of reach`: that verdict needs a published premise to be out of reach of.

**Worth recording beside it, because it changes what "no literature" means here:**
`minimum` has a native explaining propagator in Chuffed and a `[C]` in Choco LCG. So, as
with `element` and [`inverse`](inverse.md), explaining implementations exist without a paper
describing them. Calibrating against an implementation is not possible from this repo: no
solver source is vendored, and `CLAUDE.md` forbids web-searching ahead of the index.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the wall, and a missing primitive rather than a derivation gap.** Only variable-vs-domain-value comparisons exist; `m ≥ x_i` compares two decision variables and cannot be typed (`docs/DECOMP_FORMAT_NOTES.md:34`, reinforced at `:88-89`; `decomps/_shapes.md`'s "Not covered by any shape" table) |
| `G2` | a **legibility cost**: `var_name` (l.3) has no constructor for this constraint's own scalar bound, so `m` must borrow `V` or `N` (`docs/DECOMP_FORMAT_NOTES.md:23`) |
| — | **not a gap: the decomposition is also unwritten.** Closing G3 leaves a second step nobody has taken |

Extensions: **E2** (`CHRISTMAS_LIST.md:196`, route cell "**E2** (var-var atoms)").
`CHRISTMAS_LIST.md:232-233` names `minimum` among the constraints E2 unlocks and calls E2
the "biggest single unlock".
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `minimum` in `B no-literature +
  solver-native`, `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 196, section
  `9. Ordering, sorting, channelling`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `minimum.tex`. `grep -c -i 'minimum' 'explenation generator.ml'`
  → 0.
- `explenation generator.ml` read, not run → `var_name` at **3**, `ind_name` at **5**,
  `index` at **16**, `Global_event` at **50**, `printconstex` at **509**. These are the
  evidence for G3 being a typing wall rather than an authoring gap.
- `CHRISTMAS_LIST.md:196`, `:106-109` and `:232-233` read → the literature cell
  (`none found`), the solver cell and its `minimum.cpp` parenthetical, the E2 route cell,
  the legend, the "biggest single unlock" assessment.
- `tools/data/minizinc-2.10.1-globals.txt:94` read → the name.
- `decomps/maximum.md` read → the two-conjunct decomposition and the "missing primitive"
  statement; `decomps/_shapes.md` ("Not covered by any shape", and "Contradictions" 1 and 2)
  read → the five unshaped constraints and the `span` resolution.
- `docs/DECOMP_FORMAT_NOTES.md:23, 34, 88-89` read → G2, G3 and the "three independent
  families" reinforcement.
- **Nothing was compiled and no decomposition was written.** The source reading above is a
  reading; the greps and `make validate` are runs.

**Discrepancies noted, and the ones in this file fixed.**

1. **Over-read stub field, corrected here: `Chuffed | native`.** The shared row's
   parenthetical names `minimum.cpp`; attributing a Chuffed native to both names is an
   inference from the row, and the entry now says so.
2. **Wrong stub field, fixed here: `Spec: none — this constraint has no
   `decomps/minimum.md`.`** It is covered by `decomps/maximum.md`, whose title line is
   `# maximum, minimum, arg_max, arg_min, sort, arg_sort`. `tools/catalog_stub.py` matches
   filenames only, so only the name that happens to match the file got a spec link.
3. **`decomps/span.md`'s E0 claim is withdrawn by `decomps/_shapes.md`** and the file was
   left in place for its next owner. Recorded here because a reader hunting a min/max
   template will find it.
