# `sliding_sum`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `sliding_sum`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E1+E2` as `tools/mzn_coverage.py` parses the row; **`E9` per D-0011** — see Gaps |
| **Status** | `nothing generated — blocked on G12` — **and on `G13`**, which is independent of it |
| **Generated** | **0** rules — there is no `cata/sliding_sum.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:151` reads `none directly` for this constraint; the paper it names is for the neighbouring **sequence** family |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: this one is blocked outright, and its spec stops at the maths on purpose

`sliding_sum` is the only constraint in this session's fourteen for which **no rule schema
applies at all.** Every other entry is blocked on something the format cannot *say*; this one
is blocked on a kind of rule the engine does not *have*.

`decomps/sliding_sum.md:34-39` states the position, and it is a deliberate one:

> **Rule schemas: none apply as-is.** This constraint cannot be given a `decomps/<name>.md`
> rule derivation under the current encoding — it can only be specified at the maths level, as
> done above, pending E1/E2. Recording that explicitly rather than forcing it through
> `rule1`/`rule3` and producing a decomposition that looks encoded but silently drops the
> arithmetic (the `DECOMP_FORMAT_NOTES.md` G1 pattern: plausible-looking output that omits the
> constant that matters).

**That is the entry.** The spec is complete, and what it records is an absence that was checked
rather than a derivation that was skipped.

## Constraint

`sliding_sum(int: low, int: up, int: seq, array[int] of var int: x)`

Every window of `seq` consecutive elements of `x` has a sum within `[low, up]`.

**Provenance of the signature:** `decomps/sliding_sum.md:3-5`, which states it directly. That
spec gives no citation of its own and this checkout holds no `.mzn` file
(`tools/data/minizinc-2.10.1-globals.txt:112` carries the *name* only), so treat the argument
list as recall — but recall written down in-repo before this session, not this session's.

## Published explanation

**Citation:** none for this constraint. The literature column of `CHRISTMAS_LIST.md:151`
reads, verbatim:

> none directly; the **sequence** family is covered by Downing et al. 2012 *Explaining
> flow-based propagation*

> **Stub heading corrected.** The auto-stub headed this section **`Literature: absent.`** above
> a verbatim quote that names a paper. The quote was right and the heading was a mis-summary:
> the cell says "none **directly**" and then points at a *different* family. This entry keeps
> the quote and drops the heading, because "absent" and "none for this constraint, one for its
> neighbour" are different facts and the second is the one the row states.

**Rule shape:** nothing to source for `sliding_sum`. `catalog/_literature/` holds
`alldifferent.md`, `cumulative.md` and `gcc.md` only (`ls catalog/_literature/`, 2026-09-21);
there is no `sliding_sum.md` and no `sequence.md` in it. **No published rule shape is stated in
this entry, from memory or otherwise.** No web access was used and no paper was fetched.

**What this entry does not say about Downing et al. 2012.** It does not say the paper covers
`sliding_sum`; the row says it covers the **sequence** family, which is a different constraint.
It does not say what is in the paper, because no session has sourced it into
`catalog/_literature/` and `catalog/README.md` step 2 forbids writing a shape from memory. The
row is quoted and left as a pointer for C2.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:151`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. No solver
on the row ships an explaining propagator for this constraint; all three reach it through its
decomposition's primitives.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `sliding_sum`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/sliding_sum.md` (39 lines) — a **maths-level** specification, explicitly not
a rule derivation. Shape **S11**, "recursive integer accumulator"
(`decomps/_shapes.md:251-262`), which names this constraint as its standalone instance at
`:256-257`; it was Shape **E** in `decomps/_shapes-seq.md:79-87`.

MiniZinc's own decomposition, from `decomps/sliding_sum.md:9-10`:

```
S_0 = 0 ;  S_i = X_i + S_{i-1}          i ∈ [1,n]     integer running total, NOT Boolean
low ≤ S_{i+seq} - S_i ≤ up              every valid i
```

**Why no schema fits, in the generator's own terms** (`decomps/sliding_sum.md:18-24`, checked
against the current file):

- every summing schema — `rule5`, `rule6`, `rule7` — sums **occurrences of a Boolean
  `Decomp_devent`**. That is cardinality: "how many indices satisfy this condition". `S_i = X_i
  + S_{i-1}` is arithmetic on the value of `X_i` itself. `decomps/_shapes.md:253-254` puts it in
  one line: "**No schema exists**: `rule5`/`6`/`7` count Booleans."
- `var_name` is a closed variant, `X | B of int | T | I | V | N | O`
  (`explenation generator.ml:3`), and every constructor but `X` is read as Boolean or
  index-like by the printers' own case analysis. There is no case that could carry an
  integer-valued `S_i` even under a borrowed name.

**D-0004 licenses the auxiliary rather than forbidding it**, and that is unusual enough to
state. `decomps/sliding_sum.md:12-16` records `S_i` as an exception: this is one of the
constraints D-0004 (`docs/DECISIONS.md:78`) names as having no known auxiliary-free
decomposition, so `S_i` must be **recorded and justified** rather than eliminated —
"`S_i` means sum of `x_1..x_i`, and if it appears in a printed explanation the reader needs
that told to them". `decomps/_shapes.md:260-262` says the same for S11 as a whole: "the
accumulator leaks by licence and the entry must print its definition beside the rules." **So
G17 is *not* this entry's gap**, unlike every other auxiliary-carrying entry this session
reviewed — there is nothing to eliminate, only something to explain.

## Scope of this entry

**Events the generator was asked to explain:** **none**, and here that is stronger than
elsewhere: not "the decomposition has not been encoded" but "there is nothing to encode it
with". There is no `cata/sliding_sum.tex` and no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` (would be, from `xbc`, `explenation generator.ml:868`) | — | **0** | not run: no rule schema sums integer values (G12) |

**Unlike [`value_precede`](value_precede.md), there is no three-outcome question here.** That
entry could not say what the generator would do because nobody had run it; this one does not
reach the generator at all, because writing the input would require inventing a schema. The
failure is at the format, not at the walk.

**Nor is it "nothing is explainable about `sliding_sum`".** The decomposition is standard, is
written down at `decomps/sliding_sum.md:9-10`, and is four lines long. What is missing is a
fourth kind of rule schema and a variable slot to hold its result.

## Generated rules

**None.** There is no `cata/sliding_sum.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G12`** — and on **`G13`**.

The two are listed together because they are independent, and `decomps/_gaps-seq.md:26-41`
(consolidated as G12 and G13) argued each separately:

- **G12** — no rule schema sums integer *values*. The sharpening that matters:
  `docs/DECOMP_FORMAT_NOTES.md:80` calls it "**a fourth kind of schema, not a generalisation of
  the three**", against a reading of `CHRISTMAS_LIST.md`'s **E1** line as "extend the existing
  sum schemas". It cannot be extended: `rule5`/`6`/`7` are structurally about counting how many
  Booleans hold.
- **G13** — `var_name` has no integer-valued auxiliary at all
  (`docs/DECOMP_FORMAT_NOTES.md:81`). Closing G12 without G13 would give a schema with nowhere
  to put `S_i`.

`docs/DECOMP_FORMAT_NOTES.md:80-81` attributes **both** gaps to `sliding_sum` and to nothing
else in their "constraints" column, which makes this entry the sole witness for two of the
eighteen consolidated gaps.

Nothing here is validated, flagged or refuted, and **no part of this status rests on a run** —
it rests on reading the three summing schemas and the `var_name` variant, which is what
`decomps/sliding_sum.md:26-27` says it did too ("confirmed by reading the generator rather than
only trusting the list entry").

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:151` records no explanation for `sliding_sum` — "none **directly**" — which
is the condition `catalog/TEMPLATE.md` attaches to this verdict. Three qualifications, because
this row is less clean than a bare `none`:

- **The row names a paper for a neighbouring constraint**, Downing et al. 2012 on the
  **sequence** family. That is a pointer for C2, not a citation for this entry, and nothing in
  `catalog/_literature/` sources it. If a later session sources it and finds it covers
  `sliding_sum` after all, the verdict changes — that would be new evidence, not a contradiction
  of this one.
- **The verdict is about the repo's literature index, not about the literature.** That index
  cost one session of web research over all 118 MiniZinc globals (`CLAUDE.md`, "Context
  budget"); this session did not search the web and has no access.
- **There are 0 generated rules on this side anyway**, so no implication order could be stated
  even if a shape were sourced — and unlike the other blocked entries, there is no prospect of
  one under the current engine at all.

**Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G12` | **the binding one.** No rule schema sums integer *values*; `rule5`/`6`/`7` count Boolean occurrences. A fourth kind of schema, not a generalisation (`docs/DECOMP_FORMAT_NOTES.md:80`) |
| `G13` | independent of G12: `var_name` (`explenation generator.ml:3`) has no integer-valued constructor, so there is nowhere to hold `S_i` (`docs/DECOMP_FORMAT_NOTES.md:81`) |
| — | **`G17` is NOT this entry's.** D-0004 licenses `S_i` rather than requiring its elimination (`decomps/sliding_sum.md:12-16`, `decomps/_shapes.md:260-262`), so there is no pivot to remove — the entry would have to *print* the accumulator's definition instead |
| — | **`G3` is NOT this entry's.** The window test compares sums against the parameters `low`/`up`, not two decision variables |

**Extensions — two codings are live in the repo and this entry does not adjudicate between
them.** Both are recorded because a reader will meet both:

- **`E1 + E2`** — `CHRISTMAS_LIST.md:151`'s own route cell ("Needs a new integer family
  (**E1**) and threshold arithmetic `u − t` (**E2**)"), which `tools/mzn_coverage.py --rank`
  parses out and which `decomps/sliding_sum.md:26-32` confirms clause by clause. Legend:
  `CHRISTMAS_LIST.md:96` (E1, "open `var_name`"), `:97` (E2, "richer side conditions").
- **`E9`** — `docs/DECISIONS.md:245-266` (**D-0011**, decided 2026-09-18) creates E9, "sums of
  integer-valued variables — adding values, not counting", assigns gaps **G12, G13** to it, and
  names `sliding_sum` in its constraints column (`:261`). `decomps/_shapes.md:260` prices S11
  at E9 accordingly, and `CHRISTMAS_LIST.md:100` carries the new legend row.

D-0011 corrected seven rows in place, all of them rows that had said `E3` (`:268-269`); row 151
said `E1+E2` and was not among them, which is why the two codings still coexist. **D-0011's own
rule is that "an argued decision record outranks an index" (`:254`)**, which points at `E9` —
but changing `CHRISTMAS_LIST.md:151` is not this session's to do, and the gap numbers `G12`
and `G13` are the same under either coding, so nothing in this entry turns on it.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `ls cata/` → 16 `.tex` files, none named `sliding_sum.tex`.
- `ls catalog/_literature/` → `README.md`, `alldifferent.md`, `cumulative.md`, `gcc.md`. No
  file for this constraint or for the sequence family.
- `python3 tools/mzn_coverage.py --rank` → `sliding_sum` under
  `A no-literature + solver-decomposes`, ecode `E1+E2`, `§4. Sequencing and sliding:151`.
  Confirms the stub's tier row and shows which coding the tool parses.
- `explenation generator.ml` read, not run → `:3` (`var_name`, the closed variant with no
  integer slot), `:355`, `:369`, `:383` (the three summing schemas' `failwith` sites, via
  `docs/DECOMP_FORMAT_NOTES.md:43-46`'s re-measured numbers), `:868` (`xbc`), `:879-893` (the
  fifteen `explainall` calls — none is this name). **Every line number was checked against the
  current file today** (W1-T14).
- `CHRISTMAS_LIST.md:151`, `:96`, `:97`, `:100`, `:106-108` read → the literature, solver and
  route cells, the E1/E2/E9 legend rows, and the solver legend.
- `decomps/sliding_sum.md` (all 39 lines), `decomps/_shapes.md:251-262`,
  `decomps/_shapes-seq.md:79-87`, `decomps/_gaps-seq.md:26-41` read → the maths-level spec, the
  D-0004 exception, S11 / Shape E, and the two gaps in their per-file numbering.
- `docs/DECOMP_FORMAT_NOTES.md:80, 81, 85` and `docs/DECISIONS.md:78, 245-272` read → G12, G13,
  G17's scope, D-0004 and D-0011.
- `tools/data/minizinc-2.10.1-globals.txt:112` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above, and
  nothing is said about Downing et al. 2012's content.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **Two E-codings coexist for this constraint** — `E1+E2` on `CHRISTMAS_LIST.md:151` and
   `decomps/sliding_sum.md:26`, `E9` in `docs/DECISIONS.md:261` and `decomps/_shapes.md:260`.
   Both are recorded under Gaps; the gap numbers are the same either way.
2. **`decomps/_gaps-seq.md:26-33` numbers the integer-sum gap `G7`**, which is a *different*
   gap in the consolidated list (`docs/DECOMP_FORMAT_NOTES.md:75`, "value set indexed by
   another index"). Its own `G7`/`G8` are the consolidated `G12`/`G13`, as that file's own
   right-hand column records. A reader arriving from `_gaps-seq.md` will otherwise attribute
   this entry's blocker to the `lex_chain` family's.
