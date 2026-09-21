# `lex_chain_greatereq_orbitope`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_chain_greatereq_orbitope`, and no
> claim of that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the
> catalog claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` (shared row with the four `lex_chain_*` names and the other orbitope) |
| **Status** | `nothing generated — blocked on G3` — **and, for a chain of instance-dependent length, on `G7`** |
| **Generated** | **0** rules — there is no `cata/lex_chain_greatereq_orbitope.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:144` literature cell reads `none` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/*.tex`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: rows *and* columns, and that is the only difference

`decomps/orbitope.md:3-6`, in full, is the whole of what this repo establishes about the
constraint:

> Instance of `lex_chain` (`decomps/lex_chain.md`): row-wise and column-wise lex ordering
> combined (the standard orbitope symmetry-breaking shape is `lex2` applied to rows **and**
> `lex2` applied to columns of the same matrix). Column ordering reuses the same Shape B chain
> with the roles of `I` (column index) and `R` (row index) swapped. No new schema, no new index
> family — same G3 blocker as `lex_less`. E0.

So this is [`lex_chain_greatereq`](lex_chain_greatereq.md) applied twice to the same matrix, along two
axes. **It is not a new shape and it is not a new gap.** Everything about the chain is
[`lex_chain_lesseq`](lex_chain_lesseq.md)'s, which is this family's base entry; what follows
states only the swap and its consequences.

**Which of the two wave-two claims applies here: both, exactly as for the un-suffixed
`lex_chain_*` names.**

- **The `R` row-index checked negative STANDS**, and this entry leans on it twice rather than
  once. `docs/DECOMP_FORMAT_NOTES.md:94-95` records it for "`lex2`, the orbitopes and
  `var_sqr_sym`" by name. Re-checked against the current generator: `ind_name = I of int |
  T of int | P of int | R of int` (`:5`), `ind_fam` carries `FR` (`:38`), `printind_name`
  renders `R a` as `r` (`:430`), and `table` addresses its rows with `onr` (`:864`) from the
  three-index event `x3ac` (`:875`). **Swapping the roles of `I` and `R` needs nothing that
  addressing rows does not already need**, because `fam_ind`/`fam_of`/`fam_letter` (`:85-87`)
  treat the four families uniformly.
- **The `D2` variable-length-chain checked negative was WITHDRAWN.** The number of chained
  pairs is instance data; `D2 of ind_name list` is the right hook and `printind_set` **raises**
  on it (`explenation generator.ml:464`). `docs/DECOMP_FORMAT_NOTES.md:96-107`: "treat
  variable-length chains as blocked on the same missing printer as G7." An orbitope chains
  along **two** axes, so it meets that wall twice.

**A sharpening of the first claim, measured today.** The `R` family's only use in the repo
pairs it with the index set `D 4` (`onr = OpOn (FR, D 4)`, `:766`), and `D 4` is not a set the
printer defines — `ind_set_defined` admits `D 1 | D 2 | D 3` only (`:459`), `printind_set_int`
raises otherwise (`:461`). That is why W1-T2 refuses `table`'s branches: `grep -o '\frac'
cata/table.tex | wc -l` → **0**, and no `r` index appears anywhere in `cata/*.tex`. The negative
stands, but **`R` has never reached a page**; an orbitope would be the first artifact to print
two index families over the same matrix, and it would have to define both their sets.

## Constraint

`lex_chain_greatereq_orbitope(...)` — **the argument list is not established here and this entry
will not invent one.**

A matrix is in orbitope form under a non-increasing lexicographic ordering: the row-and-column symmetry-breaking shape of `decomps/orbitope.md:3-6`, with the comparator of [`lex_chain_greatereq`](lex_chain_greatereq.md) — that is, [`lex_chain_lesseq_orbitope`](lex_chain_lesseq_orbitope.md) with each pair's operands exchanged (`CHRISTMAS_LIST.md:143`: "an argument swap, not a new shape").

**Provenance of the signature:** not vendored in this repo, and **not recoverable from it**.
`tools/data/minizinc-2.10.1-globals.txt:81` carries the *name* only; this checkout holds
no `.mzn` file; `decomps/orbitope.md` describes the constraint in prose (quoted in full above)
and gives no argument list; and `CHRISTMAS_LIST.md:144` groups the name under `*_orbitope`
without a signature. Every sibling entry in this family states a signature and marks it recall
— here even recall would have to guess at the orbitope *kind* parameter that distinguishes the
partitioning and packing variants, so the line above is left open instead. **This is the one
field of this entry that a later session must still fill**, from MiniZinc's own library.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:144` reads, verbatim:

> none

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. **No published rule shape is stated in this entry, from memory or otherwise.**
No web access was used and no paper was fetched. The adjacency to `CHRISTMAS_LIST.md:142`'s
Chu & Stuckey citation, and why this entry takes its own row instead, is set out in
[`lex_chain_lesseq`](lex_chain_lesseq.md#published-explanation).

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:144`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. One
solver cell covers all six names on the row.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes any `lex_chain_*` or
orbitope, and none of the fifteen `explainall` calls (lines 879-893) mentions one.
**Emitted by:** nothing.
**Spec:** **`decomps/orbitope.md`** — its first line is `# orbitope (covers `*_orbitope`)` —
which is a six-line pointer to `decomps/lex_chain.md`.

> **Stub field corrected.** The auto-stub read `**Spec:** none — this constraint has no
> `decomps/lex_chain_greatereq_orbitope.md`.` That probe is an exact-filename `os.path.isfile` and
> it misses a spec written to cover a family under the family's name. Two specs cover this
> constraint — `decomps/orbitope.md` directly and `decomps/lex_chain.md` behind it — and this
> entry is written against both.

Shape **S5 + M-row, twice** (`decomps/_shapes.md:155-174` and `:48`; `:165-169` lists
`orbitope` among S5's twelve instances by name). Per adjacent pair along either axis, the chain
is [`lex_chain_greatereq`](lex_chain_greatereq.md)'s, unchanged. `tied_i` is a **genuine
auxiliary**: an accumulated fact with no `Global_devent` standing for it, unlike `increasing`'s
`B_1` (`explenation generator.ml:830-831`), which is a reification of `X_i ≥ t` in the same
`Decomp` and is substituted back before anything prints.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex_chain_greatereq_orbitope.tex`
and therefore no `%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i,r}=t` (would be, from a three-index event like `x3ac`) | — | **0** | not run: the pairwise comparison has no representation (G3) |

Four walls, enumerated once in
[`lex_chain_lesseq`](lex_chain_lesseq.md#scope-of-this-entry) and not re-derived: **G3** stops
the pairwise comparison; **W1-T10**'s raise (`explenation generator.ml:488`, `:517`) would make
the auxiliary a loud failure writing no file; **G17** would leave `tied_i` in the premises; and
**G7** leaves the number of chained pairs unstatable — here along two axes rather than one.
None has been run against, because the first blocks the input.

## Generated rules

**None.** There is no `cata/lex_chain_greatereq_orbitope.tex` (`ls cata/` → 16 files, none of this
name; 2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`** — and, for a chain of instance-dependent length, on
**`G7`**.

The second axis costs no gap of its own. That is the substantive finding and it is a *negative*
one: `decomps/orbitope.md:5-6` prices column ordering as "the same Shape B chain with the roles
of `I` and `R` swapped — no new schema, no new index family", and reading the generator's
uniform family handling (`:85-87`) agrees. G3 is the binding gap and is not this constraint's
alone (`docs/DECOMP_FORMAT_NOTES.md:88-90`: three independent families). G7 sits beside it,
independent of it.

Nothing here is validated, flagged or refuted. **One field of this entry is open and says so**:
the argument list — see Constraint.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:144` records no explanation for this constraint, the condition
`catalog/TEMPLATE.md` attaches to this verdict. It is a statement about the repo's literature
index — one session of web research over all 118 globals (`CLAUDE.md`, "Context budget") — and
not about the literature; this session did not search the web. It differs on purpose from
[`lex_lesseq`](lex_lesseq.md)'s `pending sourcing (C2)`, whose row names a paper.

**Orbitopes have their own symmetry-breaking literature outside this repo**, and this entry
makes no statement about it: nothing is sourced in `catalog/_literature/`, no paper was fetched,
and `catalog/README.md` step 2 forbids writing a shape from memory. `no published rule` here
means what the catalog defines it to mean — the repo's index records none — and a later session
sourcing one would change the verdict, not contradict it.

There are in any case **0** generated rules on this side, so no implication order could be
stated even if a shape were sourced. **Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** The pairwise variable-vs-variable comparison has no representation, along either axis (`docs/DECOMP_FORMAT_NOTES.md:34-41`) |
| `G7` | the chain's length is instance data, on two axes; `D2 of ind_name list` is the right hook and raises for want of a printer (`explenation generator.ml:464`). W2-A's checked negative was **withdrawn** (`docs/DECOMP_FORMAT_NOTES.md:96-107`) |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule (`:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117` |
| — | **neither row indexing nor the `I`/`R` swap is a gap** — checked negative, re-checked today, and named for the orbitopes specifically at `docs/DECOMP_FORMAT_NOTES.md:94-95` |

Extensions: **E0** (`CHRISTMAS_LIST.md:144` and `decomps/orbitope.md:6`), with the route cell's
own rider, verbatim: "**E0**, but MiniZinc's decomposition branches on instance data — one entry
per variant". Read it with `decomps/lex_less.md:27-31`'s qualification: E0 means the rule
*schemas* exist; here neither the event vocabulary nor the index-set printer does.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `grep -o '\frac' cata/table.tex | wc -l` → **0**; the same over all 16 files gives the
  per-entry census. A search for an `r` index across `cata/*.tex` returns nothing.
- `ls cata/` → 16 `.tex` files, none named `lex_chain_greatereq_orbitope.tex`.
- `python3 tools/mzn_coverage.py --rank` → `A no-literature + solver-decomposes`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:144`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:5`, `:38`, `:85-87` (the uniform family
  handling that makes the `I`/`R` swap free), `:430`, `:459`, `:461`, `:464`, `:488`, `:517`,
  `:766`, `:830-831`, `:862-864`, `:875`, `:879-893`. **Every line number was checked against
  the current file today** (W1-T14).
- `CHRISTMAS_LIST.md:142`, `:144`, `:106-108` read → literature, solver and route cells, legend.
- `decomps/orbitope.md` (all 6 lines), `decomps/lex_chain.md`, `decomps/lex_lesseq.md`,
  `decomps/_shapes.md:48, 155-174`, `decomps/_shapes-seq.md:31-62` read → the pointer, the
  family spec, the chain, M-row, S5.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-95, 96-107, 115-117` and
  `docs/DECISIONS.md:78` read → the gaps, the two checked negatives, W1-T10, D-0004.
- `tools/data/minizinc-2.10.1-globals.txt:81` read → the name.
- **Not established:** the argument list. Recorded as open under Constraint rather than guessed.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.

**Discrepancies noted, not fixed:** four, listed in
[`lex_chain_lesseq`](lex_chain_lesseq.md#how-this-entry-was-produced). They apply here too and
are not repeated.
