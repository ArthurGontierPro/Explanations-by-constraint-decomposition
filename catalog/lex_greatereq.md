# `lex_greatereq`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_greatereq`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecode `E0` (shared row with `lex_greater`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/lex_greatereq.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:143` literature cell reads `none — added 2026-09-18, W3-C` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: two reductions, both already done

`lex_greatereq(x,y)` is `lex_lesseq(y,x)` — `CHRISTMAS_LIST.md:143` says so in its route cell
("`lex_greatereq` symmetrically, an argument swap, not a new shape"). So this entry is the
composition of two reductions that other entries already carry, and it re-derives neither:

1. **the argument swap**, established with its citation in [`lex_greater`](lex_greater.md);
2. **the relaxed comparator**, established in [`lex_lesseq`](lex_lesseq.md) — the per-position
   disjunction drops the "strict somewhere" requirement, so a fully tied array is accepting.
   `decomps/_shapes.md:52-64`, convention 1, is why that is not a shape difference:
   `{rule3, rule4}` is one schema family because `Decomp_devent` carries a free sign bit.

Everything about the chain itself — S5, the `tied_i` accumulated-state auxiliary, G3, the
W1-T10 printer raise, G17 — is [`lex_less`](lex_less.md)'s.

**Which of the two wave-two claims about this family applies here: neither**, for the same
reason as [`lex_greater`](lex_greater.md#read-this-first-this-is-an-argument-swap-not-a-new-constraint).
The `R` row-index checked negative that **stands** (`docs/DECOMP_FORMAT_NOTES.md:94-95`) is
about matrices; the `D2` chain-length claim that was **withdrawn** (`:96-107`) is about chains.
This constraint is one comparison between two vectors and needs neither.

## Constraint

`lex_greatereq(array[int] of var int: x, array[int] of var int: y)`

`x` is lexicographically greater than or equal to `y` — equivalently `lex_lesseq(y, x)`. Both
operands are arrays of decision variables.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:86` carries the *name* only; this checkout holds no
`.mzn` file. The line above is [`lex_lesseq`](lex_lesseq.md#constraint)'s signature with the
operands exchanged. Treat it as recall.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:143` reads, verbatim:

> none — added 2026-09-18, W3-C

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. **No published rule shape is stated in this entry, from memory or otherwise.**
No web access was used and no paper was fetched.

The adjacency to `CHRISTMAS_LIST.md:142`'s Chu & Stuckey citation, and the reason this entry
reads `no published rule` where [`lex_less`](lex_less.md) reads `pending sourcing (C2)`, are
set out once in [`lex_greater`](lex_greater.md#published-explanation) and apply unchanged.

## Solver support

| | |
|---|---|
| Chuffed | native (`lex.cpp`, the same file as the `_less`/`_lesseq` pair) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:143`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.
**Stub field corrected:** the auto-stub's Chuffed cell read bare `native`; the row names the
file and says it is shared with the `_less`/`_lesseq` pair.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `lex_greatereq`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** none under this name — `os.path.isfile("decomps/lex_greatereq.md")` is `False`, and
that stub field is accurate. The decomposition is `decomps/lex_lesseq.md`'s (itself a six-line
pointer to `decomps/lex_less.md`) with the operands exchanged. Shape **B** in
`decomps/_shapes-seq.md:31-62`, renumbered **S5** in `decomps/_shapes.md:155-174`.

```
tied_1  = true
tied_{i+1} ⇔ tied_i ∧ (Y_i = X_i)                 rule3, fixed shift by 1
tied_i → Y_i ≤ X_i                                rule4 guard, every i
tied_n is accepting                               ← the relaxation, from lex_lesseq
```

`tied_i` is a **genuine auxiliary** — an accumulated fact with no `Global_devent` standing for
it, unlike `increasing`'s `B_1` (`explenation generator.ml:830-831`), which is a reification of
`X_i ≥ t` in the same `Decomp` and is substituted back before anything prints.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format. There is no `cata/lex_greatereq.tex` and therefore no
`%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`) | — | **0** | not run: `Y_i = X_i` has no representation (G3) |

Three walls, established in [`lex_less`](lex_less.md#scope-of-this-entry) and not re-derived:
**G3** stops the first line; **W1-T10**'s raise (`explenation generator.ml:488`, `:517`) would
make the auxiliary a loud failure rather than a silent one; **G17** would leave `tied_i` in the
premises even if a rule printed.

## Generated rules

**None.** There is no `cata/lex_greatereq.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

Neither reduction moves the gap. The swap leaves `Y_i = X_i` as unrepresentable as `X_i = Y_i`,
and the relaxed comparator changes which `rule4` clause is written, not which literals exist —
`lex_lesseq`'s own wording, and it survives the swap. Nothing here is validated, flagged or
refuted.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:143` records no explanation for this constraint. The argument for that
verdict, and the reason it differs from [`lex_lesseq`](lex_lesseq.md)'s
`pending sourcing (C2)`, is stated once in
[`lex_greater`](lex_greater.md#calibration-w3-t5-d-0013). There are in any case **0** generated
rules on this side, so no implication order could be stated even if a shape were sourced.
**Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `Y_i = X_i` and `Y_i ≤ X_i` have no representation (`docs/DECOMP_FORMAT_NOTES.md:34-41`) |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule (`:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117` |
| — | **G7 is *not* this entry's** — it is the `lex_chain_*` family's, and this is a single pair |

Extensions: **E0** (`CHRISTMAS_LIST.md:143`), with `decomps/lex_less.md:27-31`'s qualification:
E0 means the rule *schemas* exist; here the **event vocabulary** does not.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope (underspecified artifact)**.
- `ls cata/` → 16 `.tex` files, none named `lex_greatereq.tex`.
- `python3 tools/mzn_coverage.py --rank` → `B no-literature + solver-native`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:143`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:488`, `:517`, `:830-831` (`incr`, the auxiliary
  that *does* wash out), `:879-893`. Line numbers checked against the current file today.
- `CHRISTMAS_LIST.md:142`, `:143`, `:106-108` read → literature cells, solver cells, legend.
- `decomps/lex_lesseq.md`, `decomps/lex_less.md`, `decomps/_shapes-seq.md:31-62`,
  `decomps/_shapes.md:52-64, 155-174` read → the pointer file, the decomposition, Shape B / S5,
  convention 1.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-95, 96-107, 115-117` read → the gaps, the
  `R` negative that stands and the `D2` one that was withdrawn.
- `tools/data/minizinc-2.10.1-globals.txt:86` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
