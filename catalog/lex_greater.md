# `lex_greater`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_greater`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecode `E0` (shared row with `lex_greatereq`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/lex_greater.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:143` literature cell reads `none — added 2026-09-18, W3-C` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: this is an argument swap, not a new constraint

MiniZinc defines `lex_greater(x,y)` as `lex_less(y,x)`. `CHRISTMAS_LIST.md:143` states that
in the route cell itself, verbatim:

> **E0** — `decomps/_shapes-seq.md`'s Shape B (Boolean state chain, `lex_less`/`lex_lesseq`)
> applies unchanged: MiniZinc defines `lex_greater(x,y)` as `lex_less(y,x)` and `lex_greatereq`
> symmetrically, an argument swap, not a new shape

So **everything in this entry is established in [`lex_less`](lex_less.md)** — the S5
accumulated-state chain, the `tied_i` auxiliary, the G3 wall, the W1-T10 printer raise, the G17
pivot problem — and is cited rather than re-derived. What this file adds is the swap, the
separate literature row, and the separate tier.

**Which of the two wave-two claims about this family applies here: neither.** The `R`
row-index checked negative (`docs/DECOMP_FORMAT_NOTES.md:94-95`) is about matrices and this is a
single pair of vectors; the withdrawn `D2` claim (`:96-107`) is about chains of
instance-dependent length and this is one comparison. Both are live for
[`lex_chain_greater`](lex_chain_greater.md); neither is live here.

## Constraint

`lex_greater(array[int] of var int: x, array[int] of var int: y)`

`x` is lexicographically strictly greater than `y` — equivalently `lex_less(y, x)`. Both
operands are arrays of decision variables.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:85` carries the *name* only, and this checkout holds no
`.mzn` file. The signature above is [`lex_less`](lex_less.md#constraint)'s with the operands
exchanged, which is what `CHRISTMAS_LIST.md:143` says the definition is; treat it as recall.

**That both operands are variable arrays is the whole entry**, exactly as in `lex_less`. See
Gaps, G3.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:143` reads, verbatim:

> none — added 2026-09-18, W3-C

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only; there is no `lex_greater.md` in it. **No published rule shape is stated in this
entry, from memory or otherwise.** No web access was used and no paper was fetched.

**One adjacency, stated and not converted into a citation.** The `_less`/`_lesseq` row
(`CHRISTMAS_LIST.md:142`) cites Chu & Stuckey, *Symmetries and lazy clause generation*
(IJCAI 2011), and says in the same cell that *no dedicated `lex` explanation paper was found*.
Since `lex_greater` is that constraint with its arguments swapped, anything that row's paper
contained would apply here too — but the paper is unread, `:143` is its own row and reads
`none`, and this entry takes the row it is filed under. The verdict below is therefore
`no published rule`, which is what `catalog/TEMPLATE.md` defines for a `CHRISTMAS_LIST.md` row
recording no explanation, and it is **not** `pending sourcing (C2)`, which is what
[`lex_less`](lex_less.md) carries because *its* row names a paper.

## Solver support

| | |
|---|---|
| Chuffed | native (`lex.cpp`, the same file as the `_less`/`_lesseq` pair) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:143`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.
**Stub field corrected:** the auto-stub's Chuffed cell read bare `native`; the row's own
parenthetical names the file and says it is shared with `lex_less`, which is the fact that makes
the argument-swap reading a solver-level observation and not only a modelling one.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `lex_greater`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** none under this name. **Stub field qualified:** `os.path.isfile("decomps/lex_greater.md")`
is indeed `False`, but the decomposition is `decomps/lex_less.md`'s with the operands exchanged,
per `CHRISTMAS_LIST.md:143`. Shape **B** in `decomps/_shapes-seq.md:31-62`, renumbered **S5**
in `decomps/_shapes.md:155-174`.

```
tied_1  = true                                    base case: nothing compared yet
tied_{i+1} ⇔ tied_i ∧ (Y_i = X_i)                 rule3, fixed shift by 1
tied_i → Y_i ≤ X_i                                rule4 guard, every i
∃ i : tied_i ∧ Y_i < X_i                          rule4, one clause per position
```

That is `decomps/lex_less.md:8-25` with `X` and `Y` exchanged, and nothing else. `tied_i` is a
**genuine auxiliary**: an accumulated fact with no `Global_devent` standing for it, unlike
`increasing`'s `B_1`, which is a reification of `X_i ≥ t` in the same `Decomp` and is
substituted back before anything prints.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex_greater.tex` and
therefore no `%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`) | — | **0** | not run: `Y_i = X_i` has no representation (G3) |

The three walls, in the order they would be met, are established in
[`lex_less`](lex_less.md#scope-of-this-entry) and not re-derived: **G3** stops the first line;
**W1-T10**'s raise (`explenation generator.ml:488`, `:517`) would make the auxiliary a loud
failure rather than a silent one; **G17** would leave `tied_i` in the premises even if a rule
printed. Which of `lex_less`'s three outcomes occurs is not established, because nobody can run
it.

## Generated rules

**None.** There is no `cata/lex_greater.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

The binding gap is variable-vs-variable comparison, and swapping the operands does not move it:
`Y_i = X_i` is as unrepresentable as `X_i = Y_i`. `docs/DECOMP_FORMAT_NOTES.md:88-90` records
that three independent families hit G3, which is what makes it load-bearing rather than one
constraint's complaint.

Nothing here is validated, flagged or refuted. **The swap is free and it buys nothing**: it
costs no gap that `lex_less` does not already pay, and it removes none either.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:143` records no explanation for this constraint, which is exactly the
condition `catalog/TEMPLATE.md` attaches to this verdict. Two further points, so the verdict is
not read as stronger than it is:

- **It is a statement about the repo's literature index, not about the literature.** That index
  cost one session of web research over all 118 globals (`CLAUDE.md`, "Context budget") and is
  the source this catalog is required to use; this session did not search the web.
- **It differs from [`lex_less`](lex_less.md)'s `pending sourcing (C2)` on purpose.** Row 142
  names a paper and row 143 does not. The distinction the catalog draws is between "the list
  records no explanation" and "the list records one and nobody has sourced its shape"; this
  entry is the first and `lex_less` is the second.

There is in any case **0** generated rules on this side, so no implication order could be stated
even if a shape were sourced. **Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `Y_i = X_i` and `Y_i ≤ X_i` have no representation, so the decomposition cannot be written at all (`docs/DECOMP_FORMAT_NOTES.md:34-41`) |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule — D-0004's cost in coverage, not just in rule length (`:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the two printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117` explains why this is a bug and not a format gap |
| — | **G7 is *not* this entry's.** The withdrawn `D2` claim covers instance-dependent chain length; a single `lex_greater` is one pair. It is live for [`lex_chain_greater`](lex_chain_greater.md) |

Extensions: **E0** (`CHRISTMAS_LIST.md:143`), with `decomps/lex_less.md:27-31`'s qualification:
E0 means the rule *schemas* exist; here the **event vocabulary** does not.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `ls cata/` → 16 `.tex` files, none named `lex_greater.tex`.
- `python3 tools/mzn_coverage.py --rank` → `lex_greater` under `B no-literature + solver-native`,
  ecode `E0`, `§3. Value ordering, precedence, symmetry:143`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:5` (`ind_name`), `:488`, `:517` (the printers
  that raise on a bare `B`), `:879-893` (the fifteen `explainall` calls — none is this name).
  Line numbers checked against the current file today.
- `CHRISTMAS_LIST.md:142`, `:143`, `:106-108` read → the two literature cells, the solver cells,
  the legend.
- `decomps/lex_less.md`, `decomps/_shapes-seq.md:31-62`, `decomps/_shapes.md:155-174` read →
  the four-line decomposition, Shape B / S5, the instances list and the "what varies" row.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-95, 96-107, 115-117` read → G3, G17, the
  three families, the `R` checked negative that stands, the `D2` one that was withdrawn, and
  why `"ERROR B "` is W1-T10.
- `tools/data/minizinc-2.10.1-globals.txt:85` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
