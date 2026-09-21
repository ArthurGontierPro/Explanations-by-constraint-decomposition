# `var_perm_sym`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `var_perm_sym`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecodes `E0`, `E2` (shared row with `var_sqr_sym`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/var_perm_sym.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — the row cites Chu & Stuckey 2011, which `CHRISTMAS_LIST.md:142` describes as carrying no dedicated `lex` explanation |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` (re-run after D-0014) |

## Read this first: a symmetry-breaking constraint is a pile of `lex_lesseq`s, and it needs two gaps, not one

`var_perm_sym` breaks symmetry under a permutation group acting on a variable array. The
standard way to express that — and the one `decomps/var_perm_sym.md:8-11` gives — is a
**`lex_lesseq` between the array and each of its images under the group's generators**, one
comparison per generator, *not* one for the whole group. So the shape is
[`lex_lesseq`](lex_lesseq.md)'s: **S5**, the accumulated-state chain, with everything about
`tied_i`, the `rule3` conjunction and the `rule4` guard established there.

**And that is why this entry names two gaps where the lex entries name one.**

1. **G3**, inherited: `X_i = X_{σ(i)}` is variable-vs-variable, so no comparison can be
   written at all. Identical to [`lex_lesseq`](lex_lesseq.md#status).
2. **G7**, and this one is *not* in the lex entries: **the number of comparisons is instance
   data.** A permutation group is given by a generator set whose size is a property of the
   instance, not of the constraint's arity. `decomps/var_perm_sym.md:13-16` calls this "the
   same instance-count point as `lex_chain.md`" — and `lex_chain`'s escape hatch was
   **withdrawn**. `docs/DECOMP_FORMAT_NOTES.md:96-104` records the withdrawal in terms: W2-A
   had recorded `ind_set`'s `D2 of ind_name list` as a working way to give an index set as an
   explicit list; W2-B and W2-C independently found `D2` is used by nothing and had no usable
   printer, so **"treat variable-length chains as blocked on the same missing printer as G7"**.

   That applies here unchanged. `decomps/_shapes.md:171-175` says the same in S5's "what
   varies" row.

**A correction to how that withdrawal is described, measured today.**
`docs/DECOMP_FORMAT_NOTES.md:99-100` and `decomps/lex_chain.md:6-7` both say `D2`'s printer
"emits the literal string `\"setfils\"`". It no longer does: `printind_set`
(`explenation generator.ml:463-464`) **raises** `Generator_failure` on `D2`, naming W1-T2 and
G7. The conclusion — `D2` is unusable — is unchanged and if anything firmer; only the
observable moved, from garbage in the `.tex` to a named failure and no file. This is the same
W1-T2/W1-T10 pattern as the `"ERROR B "` string recorded in [`lex_less`](lex_less.md).

## Constraint

`var_perm_sym(array[int] of var int: x, array[int, int] of int: p)`

Breaks symmetry of the array `x` under a permutation group, given by the permutations `p`.

**Provenance of the signature:** not vendored in this repo, and **weak**.
`tools/data/minizinc-2.10.1-globals.txt:129` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/var_perm_sym.md:3-6` states
its own provenance as "read off `CHRISTMAS_LIST.md` §3 alone — not independently checked
against a spec text", and gives no argument list. The signature above is this entry's
rendering of that prose; **treat it as recall, and as the weakest line in this file.** In
particular, whether the permutations arrive as a matrix, a set of arrays or a group
description is not established here, and it is exactly the thing the G7 point above turns on.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:145`, literature cell, verbatim:

> Chu & Stuckey 2011 (above)

— i.e. the same citation the lex row carries, *Symmetries and lazy clause generation*
(IJCAI 2011), which `CHRISTMAS_LIST.md:142` describes as establishing that static symmetry
breaking is LCG-compatible **provided the added constraints have explaining propagators**, and
which the same line says is not a dedicated `lex` explanation paper.

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session.

**A remark about the citation's shape rather than its content**, and it is the reason this
constraint sits in tier D at all: the cited result is a *conditional* — symmetry breaking is
LCG-compatible **given** explaining propagators for the added constraints. This method's
output would be precisely such an explanation. Stating that is not a claim about the paper's
rules; it is an observation about how the row's own sentence is structured, and it is the
closest thing to a calibration target this entry has until C2 sources the paper.

## Solver support

| | |
|---|---|
| Chuffed | native (`sym-break.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | absent (no `[C]` on the row) |

Source: `CHRISTMAS_LIST.md:145`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. Note
this is a **different file** from the lex family's `lex.cpp` (`:142`) and carries **neither**
solver marker, where the lex row carries `[C]` — so despite sharing a shape and a citation,
this constraint has the thinner solver story of the two rows.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `var_perm_sym`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/var_perm_sym.md`; shape **B** in `decomps/_shapes-seq.md:31-62`, renumbered
**S5** in `decomps/_shapes.md:155-175`, which names `var_perm_sym` among S5's twelve instances.

The decomposition this project would use, one instance per group generator `σ`:

```
lex_lesseq( [X_1, …, X_n] , [X_{σ(1)}, …, X_{σ(n)}] )
```

expanded through [`lex_lesseq`](lex_lesseq.md#decomposition-used-here)'s chain:

```
tied_{σ,1}  = true
tied_{σ,i+1} ⇔ tied_{σ,i} ∧ (X_i = X_{σ(i)})            rule3, fixed shift by 1 in i
tied_{σ,i}  → X_i ≤ X_{σ(i)}                             rule4 guard
```

**Two things about this that are not `lex_lesseq`'s, and both are honest weaknesses rather
than findings.** First, `σ(i)` is an index *permuted by instance data*, which is not a fixed
shift like `iplus 1`; no `ind_op` constructor (`explenation generator.ml:39-49`) applies a
data-given permutation to an index, and this session found no gap number covering that —
`G10` is "no variable in index position", which is a decision variable, not a constant
permutation. Second, `decomps/var_perm_sym.md:13-16` states its own confidence: "Not
independently re-derived beyond that; low confidence, flagged rather than asserted." **This
entry does not upgrade that confidence**; it reports the spec and marks it.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/var_perm_sym.tex` and
therefore no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`) | — | **0** | not run: `X_i = X_{σ(i)}` has no representation (G3), and the number of comparisons is instance data (G7) |

## Generated rules

**None.** There is no `cata/var_perm_sym.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

G3 is named because it is the first wall and the one shared with the rest of S5. **G7 is
equally binding and is not behind it**: closing G3 would let a single generator's comparison be
written and would still leave the instance-dependent generator *count* unencodable. The Gaps
table carries both, and the status legend takes one number.

There is a third obstacle with no gap number, recorded above rather than invented into the
list: applying a data-given permutation to an index. `ind_op` has a shift, a sum, a prim and a
sequence, and nothing that permutes.

Nothing here is validated, flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two independent failures, either sufficient: no published shape is in the repo
(`catalog/_literature/` has no file for Chu & Stuckey 2011, and `catalog/README.md` step 2
forbids writing one from memory), and there are **0** generated rules, so there is no premise
to place in an implication order.

**A prior, recorded as a prior and different from the lex family's.** For `lex_less` the prior
is that the eventual verdict is `no published rule exists`, because
`CHRISTMAS_LIST.md:142` says no dedicated `lex` explanation paper was found. Here the prior is
weaker still: the citation is the *same* paper, reached by a "(above)" cross-reference, so if
it contains no lex rule it contains no symmetry-breaking rule either. **Neither is claimed** —
the row is a previous session's note and the paper is unread.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the first wall.** `X_i = X_{σ(i)}` is variable-vs-variable; no comparison can be written |
| `G7` | **equally binding, and not shared with `lex2`.** The generator set is instance data, so the number of `lex_lesseq` comparisons is not fixed by the arity. `D2 of ind_name list` is the right hook, is used by nothing, and now **raises** rather than printing `"setfils"` (`explenation generator.ml:463-464`) |
| `G17` | no pivot-elimination pass, so `tied_{σ,i}` cannot be removed from a finished rule |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printer path that now **raises** (`:488`, `:517`) |
| — (no number) | **applying a data-given permutation to an index.** No `ind_op` constructor does it (`:39-49`); `G10` is about a *decision variable* in index position and does not cover it. Recorded here rather than numbered, because numbering gaps is `docs/DECOMP_FORMAT_NOTES.md`'s job and this session does not own it |

Extensions: **E0 / E2** (`CHRISTMAS_LIST.md:145`). `decomps/var_perm_sym.md:13-16` reads the
`/E2` half as the instance-count point — the same one that is now G7 — and flags the reading as
low confidence; this entry keeps the flag.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `var_perm_sym.tex`.
- `python3 tools/mzn_coverage.py --rank --json`, **re-run 2026-09-21 after D-0014** → tier
  `D literature + solver-native`, ecodes `["E0", "E2"]`, `CHRISTMAS_LIST.md` line 145, section
  `3. Value ordering, precedence, symmetry`. Confirms the stub's tier row; D-0014 left it
  untouched.
- `explenation generator.ml` read, not run → `:39-49` (`ind_op`'s full constructor list — the
  basis for "nothing permutes"), `:463-464` (`printind_set` raises on `D2`), `:488`/`:517`
  (the printers that raise on a bare `B`), `:879-893` (the fifteen `explainall` calls — none
  is `var_perm_sym`).
- `CHRISTMAS_LIST.md:145`, `:142`, `:106-109` read → the citation and its "(above)"
  cross-reference, the conditional form of the cited result, the solver cells and legend.
- `decomps/var_perm_sym.md`, `decomps/lex_lesseq.md`, `decomps/lex_chain.md`,
  `decomps/_shapes.md:155-175`, `decomps/_shapes-seq.md:31-62` read → the per-generator
  `lex_lesseq` reading, its own low-confidence flag, S5's instance list, the `D2` correction.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 75, 85, 88-90, 96-104` read → G3, G7, G17, the three
  families that hit G3, and the withdrawal of the `D2` checked negative.
- **Not fetched, not written:** no paper.

**Discrepancy noted, not fixed (this session does not own those files).**
`docs/DECOMP_FORMAT_NOTES.md:99-100` and `decomps/lex_chain.md:6-7` say `D2`'s printer "emits
the literal string `\"setfils\"`". Measured 2026-09-21: it **raises** (`explenation generator.ml:464`),
under W1-T2. The conclusion drawn from it — `D2` is not usable, and variable-length chains are
blocked on the same missing printer as G7 — is unaffected.
