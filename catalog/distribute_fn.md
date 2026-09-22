# `distribute_fn`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `distribute_fn`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

**This entry is a pointer.** `distribute_fn` is the **functional form** of
[`distribute`](distribute.md) and is not a separate constraint. Everything this
method has to say about it is in [`catalog/distribute.md`](distribute.md); nothing is duplicated here,
because duplicating it would present one object as two. The decision, the evidence for it and
its one qualification are in **"The `*_fn` decision"** below.

| | |
|---|---|
| **Tier** | **unclassified** (`- unclassified`) — `python3 tools/mzn_coverage.py --rank`, 2026-09-21. **This is an artifact of a blank cell, not a property of the constraint** — see below. The base `distribute` ranks **A** (`A no-literature + solver-decomposes`) |
| **Status** | **resolves to [`distribute.md`](distribute.md)**, whose Status row reads `nothing generated — blocked on G4` (re-read 2026-09-22; it read `not reviewed` when this entry was written, before the base was reviewed). **No status-legend value is asserted for `distribute_fn` itself**, and this entry generates nothing of its own |
| **Generated** | **0** — there is no `cata/distribute_fn.tex`, and there should not be one. The rules for this constraint are the rules in [`distribute.md`](distribute.md) |
| **Validator** | out of scope: no artifact. `make validate` reads `cata/*.tex` and there is no file under this name; the base entry's verdicts are the verdicts |
| **Calibration** | **resolves to [`distribute.md`](distribute.md)**. `CHRISTMAS_LIST.md:217` records the literature column for this row as `—`; that is a statement about the *row*, not a finding that no paper explains distribute, so `no published rule exists` is **not** claimed here |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, `ls cata/`, and reads of `CHRISTMAS_LIST.md:217`, `CHRISTMAS_LIST.md:132` and `catalog/distribute.md` |

## Constraint

`distribute_fn(...)` — **not vendored in this repo.** The MiniZinc library is not checked in:
`tools/data/minizinc-2.10.1-globals.txt:60` carries the *name* `distribute_fn` and nothing else,
and `docs/COVERAGE.md` is explicit that the snapshot is names only. **No signature is written
here**, from recall or otherwise.

What *is* quotable in this repo is the whole of what it says about the `*_fn` family, and it is
one clause. `CHRISTMAS_LIST.md:217`, route cell, verbatim:

> not separate constraints; they call the predicate form

Read with the `distribute` row at `CHRISTMAS_LIST.md:132`, that says `distribute_fn` introduces a
result — an `array of var int`: the number of occurrences of each value in `value` — and posts `distribute` over it.

**Provenance of the name:** `tools/data/minizinc-2.10.1-globals.txt:60`.
`CHRISTMAS_LIST.md:217` files it under section `11. Maths and misc`, in the row that names all
eleven `*_fn` variants together.

## The `*_fn` decision

**Eleven release globals end in `_fn`** — `among_fn`, `bin_packing_load_fn`, `count_fn`,
`distribute_fn`, `global_cardinality_fn`, `global_cardinality_closed_fn`, `inverse_fn`,
`nvalue_fn`, `range_fn`, `roots_fn`, `sort_fn` — and `CHRISTMAS_LIST.md:217` gives all eleven
one row, with `—` for literature and `—` for solver. Session **R2** reviewed them as a group and
took the option of **one short entry per name, each resolving to its base**, rather than a single
shared page. Two reasons, and both are about what the catalog measures:

1. **The denominator is per release global.** `catalog/README.md` ("What the catalog claims")
   claims coverage of 118 of 118 names, and `tools/catalog_index.py` counts one file per name.
   Collapsing eleven names into one page would either lose eleven rows or need a change to a
   tool and an index this session does not own.
2. **A pointer is a finding, and an absence is not.** Saying "`distribute_fn` is `distribute` under
   another syntax, so its explanation is `distribute`'s" is a checkable claim. Leaving eleven files
   as stubs says only that nobody looked.

**The thing that had to be established first: does the functional form change the explanation?**
**It does not.** The argument is three steps over this method's own machinery, and it is
*reasoning read off the generator's design, not a measurement*:

1. This method explains **events** — literals `(sign, variable, index list, AC|BC)` — derived
   from a **decomposition**, a list of atomic constraints each tagged with one of the 7 rule
   schemas (`CLAUDE.md`, "The generator's design, in one paragraph").
2. `CHRISTMAS_LIST.md:217` says the functional form *calls the predicate form*. So it posts the
   same atomic constraints over the same variables; the result is a solver variable either way,
   just bound in an expression rather than passed as an argument. The list of `Decomp`s is
   therefore identical, and so is the set of literals available as events.
3. `find`'s AND/OR traversal, `an`'s DNF flattening and the LaTeX printer are functions of that
   list and that event. Identical inputs, identical rules. **There is nothing for a
   `cata/distribute_fn.tex` to contain that `cata/`'s `distribute` artifact does not already contain.**

**A second in-repo source, found after the decision and agreeing with it.**
`docs/DECOMP_FORMAT_NOTES.md:129` closes the wave-two gap survey with a list of constraints that
produced no new gap, and the last line of it reads, verbatim:

> the `*_fn` variants — not separate constraints; no gap recorded.

That is an independent statement: `CHRISTMAS_LIST.md:217` is the literature-and-solver index,
while this is the *format* analysis, arrived at by asking what each constraint demands of the
`event`/`ind_modifs`/rule-schema encoding. The two agree, and the second is the stronger of the
pair for this entry's purposes — "no gap recorded" is exactly the claim that the functional
syntax costs this method nothing.

**The qualification, stated once and not hidden.** Step 2 rests on `CHRISTMAS_LIST.md:217`, an
index this repo wrote, **not** on the MiniZinc library, which is not vendored here. If some
`*_fn` body did something other than declare a result and post the predicate — added a
`closed`-style side condition, say, or restricted the result's domain — step 2 would fail for
that one name. **Checking that needs the library and this session had no web access**; it is
recorded as the one open item, not waved away. Nothing in this repo contradicts row 217.

**A second qualification that turns out not to bite.** A *function* is total: used in an
expression it asserts the result exists and is unique. That would be an extra constraint if the
result were not already determined by the other arguments — but for `distribute_fn` it is
(each card is a function of `value` and `base`), so the functional form adds no literal and no explanation. *This is reasoning
about the eleven signatures, not a citation*; it is the step a reader should check first if the
decision is ever revisited.

**What this settles.** `docs/COVERAGE.md:137-139` lists row 217 as one of three rows in
`CHRISTMAS_LIST.md` carrying no E-code, and unlike the other two it attaches no "defensible" to
it. This entry supplies the missing route and its reason: **the route of `distribute_fn` is the route
of `distribute`**, because it is the same decomposition. `CHRISTMAS_LIST.md:132`'s route cell
for `distribute` reads, verbatim:

> **E0** + **E3**

That transfer is a reading of R2's, offered to whoever owns `CHRISTMAS_LIST.md`; **this session
did not edit that file**, and row 217 still reads `—`.

**And what it does not settle.** The *tier* stays `unclassified` in the tool's output, and that
is a genuine defect worth naming: `tools/mzn_coverage.py` ranks on the literature and solver
columns, row 217 leaves both blank, so all eleven `*_fn` names land in `- unclassified` while
their bases are spread across **A**, **B**, **C** and **out of scope**. `distribute` is
**A**. The eleven are not unclassifiable; they are unclassified because a row that
describes a *syntactic* family has nothing to put in a *solver* column. Fixing it means either
filling row 217 or teaching the tool the `_fn` → base mapping, and neither file is this
session's.

## Published explanation

**Citation:** none under this name. `CHRISTMAS_LIST.md:217` gives the literature column of the
`*_fn` row as `—`, which records that the row names no paper — it is **not** the finding that
no paper explains this constraint. The citation that applies is `distribute`'s, at
`CHRISTMAS_LIST.md:132`, and it is quoted in [`distribute.md`](distribute.md).

**Rule shape:** see [`distribute.md`](distribute.md). Nothing about any paper's content is stated
here; no paper was fetched by this session and no web access was used.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

**Source: the `distribute` row, `CHRISTMAS_LIST.md:132`** — not the `*_fn` row, whose solver
cell is `—`. Solver-column legend at `CHRISTMAS_LIST.md:106-109`.

**This is a correction to the machine-filled stub, and the reason to make it.** The stub read
the `—` at `CHRISTMAS_LIST.md:217` mechanically and rendered `Chuffed: unspecified`,
`Geas: absent`, `Choco LCG: absent`. Two of those three are wrong as statements about the
world: a solver never sees `distribute_fn`, it sees the `distribute` the function posts, so the
right row is the base's. The stub's derivation was correct *for the cell it read*; the cell is
the wrong cell for this question.

## Decomposition used here

**Generator value:** none, and this is not a gap. `explenation generator.ml` has no value named
`distribute_fn` and should not: the decomposition to encode is `distribute`'s.
**Emitted by:** nothing — `ls cata/` (2026-09-21) lists 16 `.tex` files and none is
`distribute_fn.tex`.
**Spec:** none — there is no `decomps/distribute_fn.md`, and the 43 specs under `decomps/` are
named for predicate forms. [`distribute.md`](distribute.md) records whether `distribute` has one.

See **"The `*_fn` decision"** above for why an identical decomposition under a second name would
be a duplicate rather than a new entry.

## Scope of this entry

**Events the generator was asked to explain:** none under this name. The generator was never
invoked for `distribute_fn`, so there is no `%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| — | — | — | no artifact exists |

The finite question this method was asked about this constraint was asked under the name
`distribute`, and [`distribute.md`](distribute.md)'s **Scope of this entry** section states it, including
the events that came back empty. **This entry adds no scope of its own and claims none.**

## Generated rules

**None under this name**, by design rather than by failure: `grep -o '\\frac' cata/distribute_fn.tex`
has no file to read. The generated rules for this constraint are rendered in
[`distribute.md`](distribute.md).

## Status

**resolves to [`distribute.md`](distribute.md)** — that entry's Status row reads `nothing generated — blocked on G4` (re-read 2026-09-22).

**No value from `catalog/README.md`'s six-value status legend is asserted here**, and that is
deliberate rather than evasive: all six are verdicts about *generated rules*, this name has
none of its own, and inventing one would double-count the base entry's evidence under a second
name. What **is** established, and is this entry's content, is the resolution itself: `distribute_fn`
is `distribute` in functional syntax, the decomposition and therefore the explanation are the same
object, and the argument for that is above with its two qualifications attached.

## Calibration (W3-T5, D-0013)

**Verdict: resolves to [`distribute.md`](distribute.md).**

No comparison is stated here and none should be: with no rule generated under this name there is
no premise to place in an implication order, and the published side is `distribute`'s. Note in
particular that **`no published rule exists` is not being claimed** — the `—` in
`CHRISTMAS_LIST.md:217`'s literature column is the absence of a *cell*, not the presence of a
negative result, and `catalog/TEMPLATE.md` reserves that verdict for rows that record `none`.

Whatever verdict [`distribute.md`](distribute.md) reaches is `distribute_fn`'s verdict, for the same reason
the rules are the same rules.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **none of its own.** The functional syntax costs this method nothing; see "The `*_fn` decision" |
| (base's) | whatever [`distribute.md`](distribute.md)'s Gaps table lists for `distribute` applies here unchanged |

Extensions: **none recorded by the list** — `CHRISTMAS_LIST.md:217`'s route cell is
"not separate constraints; they call the predicate form" and `tools/mzn_coverage.py` parses no
E-code from it. R2's reading, above: the applicable route is `distribute`'s, quoted verbatim in
"The `*_fn` decision" from `CHRISTMAS_LIST.md:132`.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering) for what the numbered
gaps mean; none is attributed to `distribute_fn` itself.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → `distribute_fn` in `- unclassified`,
  no E-codes parsed, `CHRISTMAS_LIST.md` line 217; and `distribute` in `A no-literature + solver-decomposes`.
  The two tiers for one object are the artifact reported above.
- `CHRISTMAS_LIST.md:217` read → the `*_fn` row: literature `—`, solver `—`, route
  "not separate constraints; they call the predicate form", quoted verbatim above.
- `CHRISTMAS_LIST.md:132` read → the `distribute` row: the solver cells in the table above and
  the route cell quoted verbatim in "The `*_fn` decision".
- `CHRISTMAS_LIST.md:106-109` read → the solver-column legend.
- `tools/data/minizinc-2.10.1-globals.txt:60` read → the name, and that the snapshot carries
  names only.
- `catalog/distribute.md` read, not run → the base entry's Status row, quoted above as
  `nothing generated — blocked on G4`, and the fact that it carries the rules, scope and calibration this entry defers to.
- `ls cata/` → 16 `.tex` files, none named `distribute_fn.tex`.
- `make validate` (run 2026-09-21, output redirected to a file then grepped, per `CLAUDE.md`
  "Verify before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL,
  21 flagged ==`, `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. No line of
  that run mentions `distribute_fn`, which is the measurement behind the **Validator** row.
- `docs/COVERAGE.md:137-139` read → the three-rows-without-an-E-code passage discussed above.
- `docs/DECOMP_FORMAT_NOTES.md:129` read → "the `*_fn` variants — not separate constraints;
  no gap recorded", quoted verbatim above as the second in-repo source.
- **The three-step argument that the functional form does not change the explanation is
  reasoning, labelled as such in place**, from `CLAUDE.md`'s description of the generator and
  from `CHRISTMAS_LIST.md:217`. It is not a measurement and no code was run to support it.
- **Not fetched, not read:** the MiniZinc library. It is not in this repo, and no web access was
  used. That is the open item recorded in "The `*_fn` decision".

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`docs/COVERAGE.md:137-139` cites stale line numbers.** It names lines 118, 174 and 213 for
   the three E-code-less rows; measured 2026-09-21 with `sed -n`, those rows are at
   **120** (`alldifferent_except_0`), **178** (`geost`) and **217** (the `*_fn` row).
2. **`tools/mzn_coverage.py` cannot rank a `*_fn` name**, for the structural reason given above.
   Recorded as a defect of the input row, not of the tool.
