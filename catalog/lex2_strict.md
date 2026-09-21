# `lex2_strict`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex2_strict`, and no claim of that kind
> is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E0` (shared row with `lex_less`, `lex_lesseq`, `lex2`, `strict_lex2`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/lex2_strict.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — `CHRISTMAS_LIST.md:142` records that no dedicated `lex` explanation paper was found |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: the strict row ordering, and a naming question this repo cannot settle

`lex2_strict` is [`lex2`](lex2.md) with `lex_less` in place of `lex_lesseq` on each adjacent row
pair: the rows are **strictly** increasing, so no two rows may be equal. Everything else in
this entry is established in [`lex_less`](lex_less.md), [`lex_lesseq`](lex_lesseq.md) and
[`lex2`](lex2.md) and is cited rather than re-derived — the **S5** accumulated-state chain, the
`tied` auxiliary, the **M-row** replication over the existing `R` index family, and the **G3**
wall that stops all of them.

**The naming question, stated and left open.** `lex2_strict` and `strict_lex2` look like two spellings of
one constraint, and `decomps/lex2.md:3-6` flags exactly that — "`CHRISTMAS_LIST.md` §3 lists
all three together with one literature/route entry, which reads as MiniZinc treating them as
near-duplicates; **not independently confirmed** — flagging rather than asserting
`strict_lex2 = lex2_strict`". This session did not settle it either, and here is precisely what
it did and did not establish:

- **Measured:** `tools/data/minizinc-2.10.1-globals.txt` lists `lex2` at line 77,
  `lex2_strict` at line 78 and `strict_lex2` at line 117, so MiniZinc 2.10.1 exports **three
  distinct names**. `CHRISTMAS_LIST.md:142` gives them **one** row, with one citation, one
  solver cell and one route.
- **Not established:** whether two of the three are aliases in the stdlib. No `.mzn` file is
  vendored in this checkout (`find . -name '*.mzn'` → empty, 2026-09-21), so there is nothing
  here to read, and this session has no web access.

**Why the catalog should care rather than shrug.** This repo already ships two entries that
are byte-identical despite coming from different decompositions —
`cata/atleastnvalues.tex` and `cata/atmostnvalues.tex` (verified identical by `cmp`,
2026-09-21). Two names that *ought* to differ producing one artifact is a failure mode with a
shipped precedent, so "they are probably the same" is exactly the inference this catalog
should not make on its own.

## Constraint

`lex2_strict(array[int,int] of var int: x)`

The rows of the matrix `x` are lexicographically **strictly** increasing: each adjacent pair of
rows satisfies `lex_less`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:78` carries the *name* only. `decomps/lex2_strict.md` is five lines and is a pointer that raises the alias question itself: "Possibly a duplicate name for `strict_lex2` … not independently confirmed, flagged rather than asserted; either way, same shape as `lex2.md`." It gives no
argument list, so the signature above is this entry's rendering of `lex2`'s prose with the
comparator strengthened. Treat it as recall, and as the weakest line in this file.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:142`, literature cell, verbatim:

> Chu & Stuckey, *Symmetries and lazy clause generation* (IJCAI 2011) — static symmetry
> breaking is LCG-compatible provided the added constraints have explaining propagators; no
> dedicated `lex` explanation paper found

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session.

## Solver support

| | |
|---|---|
| Chuffed | native (`lex.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:142`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers all five names on the row; it is not evidence of a propagator specific to
this name.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `lex2_strict`, and none of
the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/lex2_strict.md` → `decomps/lex2.md` (which covers `lex2`, `strict_lex2` and `lex2_strict`
together); shape **B** in `decomps/_shapes-seq.md:31-62`, renumbered **S5** in
`decomps/_shapes.md:155-175`, plus modifier **M-row** (`decomps/_shapes.md:44-47`).
`decomps/_shapes.md:166-170` lists this name explicitly among S5's twelve instances.

The decomposition this project would use: [`lex_less`](lex_less.md#decomposition-used-here)'s
chain — the strict one, with the "`∃ i: tied_i ∧ X_i < Y_i`" clause kept — replicated over the
row index `r`, one instance per adjacent row pair:

```
tied_{r,1}  = true
tied_{r,i+1} ⇔ tied_{r,i} ∧ (X_{r,i} = X_{r+1,i})      rule3, fixed shift by 1 in i
tied_{r,i}  → X_{r,i} ≤ X_{r+1,i}                       rule4 guard
∃ i : tied_{r,i} ∧ X_{r,i} < X_{r+1,i}                  rule4 per position — the strict clause
```

**The strictness costs nothing extra here.** It is one more `rule4` disjunction over literals
the format already cannot express; it introduces no constant (unlike
[`disjunctive_strict`](disjunctive_strict.md), whose strictness is a predicate on a duration
and therefore G1) and no new variable (unlike [`disjunctive_opt`](disjunctive_opt.md)'s
`Ex_i`, which is G2). That contrast is worth stating: in this corpus a `_strict` suffix is
sometimes free and sometimes a gap, depending on whether it is a clause or a predicate on a
parameter.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex2_strict.tex` and therefore
no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{r,i}=t` (would be, from a three-index `xac`-style event) | — | **0** | not run: `X_{r,i} = X_{r+1,i}` has no representation (G3) |

The walls, in the order they would be met, all established elsewhere: **G3** stops the first
line ([`lex_less`](lex_less.md#scope-of-this-entry)); **W1-T10**'s raise would make the `tied`
auxiliary a loud failure rather than a silent one; **G17** would leave it in the premises even
if a rule printed. **M-row adds no fourth wall** — see [`lex2`](lex2.md#read-this-first-a-matrix-is-a-modifier-not-a-shape)
for the checked negative on the `R` index family, and for the sharpening that `R` has never
appeared in any generated artifact.

## Generated rules

**None.** There is no `cata/lex2_strict.tex` (`ls cata/` → 16 files, none of this name; 2026-09-21).
Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

Same gap as every other member of the lex family: only variable-vs-domain-value comparisons
exist. Neither the strictness nor the matrix adds a blocker — that is the whole content of
this entry, and it is worth a file rather than a footnote because both look like they should.

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two independent failures, either sufficient: no published shape is in the repo
(`catalog/_literature/` has no file for Chu & Stuckey 2011, and `catalog/README.md` step 2
forbids writing one from memory), and there are **0** generated rules, so there is no premise
to place in an implication order.

**A prior, recorded as a prior.** `CHRISTMAS_LIST.md:142` states that no dedicated `lex`
explanation paper was found; if that holds on reading, the eventual verdict is
`no published rule exists`. Not claimed here: the row is a previous session's note and the
paper is unread.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `X_{r,i} = X_{r+1,i}` is variable-vs-variable; the decomposition cannot be written |
| `G17` | no pivot-elimination pass, so `tied_{r,i}` cannot be removed from a finished rule |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printer path that now **raises** (`explenation generator.ml:488`, `:517`) |
| — | **not a gap: the row index** (`R`/`FR` exist and `table`'s decomposition uses them), and **not a gap: the strictness** (one more `rule4` clause) |

Extensions: **E0** (`CHRISTMAS_LIST.md:142`), with `decomps/lex_less.md:27-31`'s
qualification: E0 means the *schemas* exist, and here the **event vocabulary** does not.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `lex2_strict.tex`.
- `cmp cata/atleastnvalues.tex cata/atmostnvalues.tex` → identical; the shipped precedent cited
  in "Read this first".
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 142. Confirms the
  stub's tier row; D-0014 left it untouched.
- `tools/data/minizinc-2.10.1-globals.txt` read → `lex2` 77, `lex2_strict` 78, `strict_lex2`
  117: three distinct exported names. `find . -name '*.mzn'` → empty.
- `explenation generator.ml` read, not run → `:488`/`:517` (the raising printers),
  `:879-893` (the fifteen `explainall` calls — none is `lex2_strict`).
- `CHRISTMAS_LIST.md:142`, `:106-109` read → the citation, the one-row treatment of all five
  names, the solver legend.
- `decomps/lex2_strict.md`, `decomps/lex2.md`, `decomps/lex_less.md`, `decomps/_shapes.md:44-47,155-175`,
  `decomps/_shapes-seq.md:31-62` read → the pointer chain, S5, M-row, the alias flag.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 94-95` read → G3, G17, the three families
  that hit G3, the row-index checked negative.
- **Not fetched, not written:** no paper. The alias question is left open above rather than
  answered, because nothing in this repo answers it.
