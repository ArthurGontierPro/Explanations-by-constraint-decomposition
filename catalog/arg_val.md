# `arg_val`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `arg_val`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E1` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on E1` — **and on `G3` under the "first occurrence" reading.** See Status |
| **Generated** | no generator entry — there is no `cata/arg_val.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `arg_val` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:134` records `none` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `explenation generator.ml` read |

## Constraint

**No signature is written here.** `arg_val` is not vendored in this repo:
`tools/data/minizinc-2.10.1-globals.txt:28` carries the *name* only, there is no
`decomps/arg_val.md`, and `CHRISTMAS_LIST.md:134` gives literature, solver and route and no
signature. `catalog/TEMPLATE.md` forbids presenting recall as a citation, and here the arity
decides which gap binds — see Status — so the entry keeps the question open instead of
answering it from memory.

What is quotable is the shape of the name and one route cell. The `arg_*` family in this
catalog is `arg_max`, `arg_min`, `arg_sort` and `arg_val`; the first three are filed in
`CHRISTMAS_LIST.md` §9 and `arg_val` in §2 (`2. Counting and cardinality`), which is itself
informative — the list groups it with the counting constraints, not with the ordering ones.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:28`.
`CHRISTMAS_LIST.md:134` files it under section `2. Counting and cardinality`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:134` reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/arg_val.md`, no paper was
fetched by this session and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:134`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21: no `[G]`, no `[C]`, no `[C✗]`. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. **Emitted by:** nothing.
**Spec:** **none** — there is no `decomps/arg_val.md`, and `decomps/_shapes.md` lists no shape
for `arg_val` under any of its twelve. It is one of the corpus's unspecified names.

**The half that already exists.** `arg_val` returns a *position* in an array, and this format
already has a position-valued user variable: `element`'s index `I`. `var_name` is
`X | B of int | T | I | V | N | O` (`explenation generator.ml:3`), `elem` channels `I` with a
`rule1` exactly as it channels `X` and `V` (`:834-838`), and `cata/element.tex` prints `I = i`
literals. So the *index variable* is not obviously the blocker, and to that extent the row's
**E1** pricing ("open `var_name`") looks generous: the letter exists. **This is reasoning off
the generator's type and `element`'s value, not a measurement, and it is conditional on the
arity** — if `arg_val` also returns or consumes something the seven letters do not cover, E1 is
the right price after all.

**The half that does not exist.** If `arg_val` means the **first** (smallest) index at which the
value occurs — the reading its name and its `arg_max`/`arg_min` siblings suggest — then the
decomposition needs "`i` is the least index such that `X_i = v`", i.e. a comparison between the
returned index variable and every other candidate index. That is variable-vs-variable, **G3**,
the wall `decomps/maximum.md` calls "not a derivation gap, it is a missing primitive" and
`decomps/_shapes.md` uses to exclude `maximum`, `minimum`, `arg_max`, `arg_min` and `span` from
all twelve shapes. Under the weaker reading — "`v` occurs at `i`", with uniqueness left to the
model — G3 does not bite and the constraint is `element` with the value fixed.

**Both readings meet one wall.** `v` is a value, and a value baked in as a parameter cannot be
printed: an `X` literal carrying no value index raises `Failure "hd"` at
`explenation generator.ml:512`. Measured under [`at_most.md`](at_most.md). Written as a
one-element value set instead, it is **G8**, refused by W1-T2 — measured under
[`count.md`](count.md).

## Scope of this entry

**Events the generator was asked to explain:** none. There is no `cata/arg_val.tex`, no
`explainall` call, and therefore no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

**No scratch experiment was run for this entry**, and the reason is worth stating rather than
leaving as a silence: the runs behind the neighbouring counting entries each transcribed a
decomposition that *exists in `decomps/`*. `arg_val` has none, so authoring one here would be
inventing the constraint and then measuring the invention. The two walls named above are
carried over from measurements made on constraints that do have specs.

## Generated rules

**None.** `cata/arg_val.tex` does not exist.

## Status

**`nothing generated — blocked on E1`** — the row's own route — **and on `G3` under the "first
occurrence" reading.**

Nothing is generated because no decomposition for `arg_val` exists anywhere in this repo: no
generator value, no `decomps/` spec, no shape in `decomps/_shapes.md`. Writing one is blocked on
which constraint `arg_val` is, and this session could not settle that: the MiniZinc library is
not vendored here and there was no web access.

**What the next owner should do first, in order.** (1) Pin the signature from the library.
(2) If it carries "first"/least-index semantics, the entry is G3-blocked and belongs beside
`arg_max`/`arg_min` in `decomps/_shapes.md`'s "Not covered by any shape" table, *not* in §2's
counting family — and the E1 route in `CHRISTMAS_LIST.md:134` is then under-priced. (3) If it
does not, it is `element` (shape **S6**, `catalog/element.md`, validated 2 of 6) with the value
side fixed, and the binding gap is G8 for that fixed value.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:134` names no paper, which is the condition `catalog/TEMPLATE.md` attaches
to this verdict. It is not `pending sourcing`: that is for a row citing something unread, and
this row cites nothing. Independently, with 0 rules there is no premise to compare.

## Gaps

| gap | what it blocks here |
|---|---|
| `E1` | the route cell's own pricing — a `var_name` family for the returned index. **Possibly over-priced**: `element`'s `I` already is one (`explenation generator.ml:3`, `:834-838`); see "Decomposition used here" |
| `G3` | **conditional, and probably the real blocker**: "least index such that" compares two decision variables. Same wall as `arg_max`, `arg_min`, `maximum`, `minimum`, `span` (`decomps/_shapes.md`, "Not covered by any shape") |
| `G8` | the value `v` as a one-element value set; refused by W1-T2, measured on [`count`](count.md) |
| — (unnumbered) | the printer requires a value index on every `X` literal — baking `v` in raises `Failure "hd"` at `explenation generator.ml:512`. Measured under [`at_most.md`](at_most.md); recorded in neither `docs/DECOMP_FORMAT_NOTES.md` nor `docs/ROADMAP.md` |

Extensions: **E1** — `CHRISTMAS_LIST.md:134`, whose route cell is the single token `**E1**`.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E1"]`, `CHRISTMAS_LIST.md` line 134,
  section `2. Counting and cardinality`.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`; no line names an `arg_val` entry.
- `CHRISTMAS_LIST.md:134` and `:106-109` read → the literature, solver and route cells.
- `tools/data/minizinc-2.10.1-globals.txt:28` read → the name.
- `ls decomps/` and a grep of `decomps/_shapes.md` → **no** `arg_val` spec and **no** shape
  mentioning it.
- `explenation generator.ml:3` read → `var_name`'s seven constructors, including `I`;
  `:834-838` → `elem`, the three-`rule1` channel that uses `I`; `:512` → the `hd` site.
- `catalog/element.md` read, not run → that `element` is shape S6 and validated 2 of 6 rules.
- **No scratch run for this entry**, deliberately; see "Scope of this entry".
- **Not fetched, not read:** the MiniZinc library (not vendored here) and any paper. No web
  access was used. **The signature is the open item**, and both conditional statements above
  are marked as conditional in place.
