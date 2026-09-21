# `lex_lesseq`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `lex_lesseq`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E0` (shared row with `lex_less`, `lex2`, `strict_lex2`, `lex2_strict`) |
| **Status** | `nothing generated — blocked on G3` |
| **Generated** | **0** rules — there is no `cata/lex_lesseq.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **pending sourcing (C2)** — `CHRISTMAS_LIST.md:142` records that no dedicated `lex` explanation paper was found |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Read this first

`lex_lesseq` is [`lex_less`](lex_less.md) with one clause relaxed, and **everything in this
entry except that clause is established there**: the S5 shape, the `tied_i` accumulated-state
auxiliary, the G3 wall, the W1-T10 printer raise, and the G17 pivot problem. This file states
what differs and cites rather than duplicates, because the two are one decomposition and two
entries that drift apart would be worse than one entry that is too long.

**What differs, in one line** (`decomps/lex_lesseq.md:3-6`): the per-position disjunction drops
the "strict somewhere" requirement, so `tied_n` — fully tied through the last position — is an
**accepting** outcome instead of a violation.

**Why that is not a shape difference.** `decomps/_shapes.md:52-64`, convention 1, treats
`{rule3, rule4}` as one schema family because `Decomp_devent` carries a free sign bit on every
summand, so a De Morgan flip is not a new shape. Relaxing one disjunct of one `rule4` clause is
strictly less than that. Both constraints are **S5**, and `decomps/_shapes.md:166-170` lists
them side by side as its `∧`-form instances.

## Constraint

`lex_lesseq(array[int] of var int: x, array[int] of var int: y)`

`x` is lexicographically less than or equal to `y`; both arrays the same length, and both are
arrays of decision variables.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:88` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). `decomps/lex_lesseq.md` gives no
signature of its own — it is a six-line pointer to `decomps/lex_less.md` — so the line above is
`lex_less`'s signature with the comparator relaxed. Treat it as recall.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:142`, literature cell, verbatim:

> Chu & Stuckey, *Symmetries and lazy clause generation* (IJCAI 2011) — static symmetry
> breaking is LCG-compatible provided the added constraints have explaining propagators; no
> dedicated `lex` explanation paper found

**Rule shape:** **pending sourcing — see `catalog/_literature/`**, which holds `alldifferent`,
`cumulative` and `gcc` only. **No published rule shape is stated in this entry, from memory or
otherwise.** No web access was used and no paper was fetched by this session. The row's own
"no dedicated `lex` explanation paper found" is quoted above rather than paraphrased; see
[`lex_less`](lex_less.md#published-explanation) for why this entry does not convert it into a
verdict.

## Solver support

| | |
|---|---|
| Chuffed | native (`lex.cpp`) |
| Geas | absent (no `[G]` on the row) |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:142`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. One
solver cell covers all five names on the row.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `lex_lesseq`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/lex_lesseq.md`, which is a pointer to `decomps/lex_less.md`; shape **B** in
`decomps/_shapes-seq.md:31-62`, renumbered **S5** in `decomps/_shapes.md:155-175`.

```
tied_1  = true
tied_{i+1} ⇔ tied_i ∧ (X_i = Y_i)                 rule3, fixed shift by 1
tied_i → X_i ≤ Y_i                                rule4 guard, every i
tied_n is accepting                               ← the only difference from lex_less
```

**`tied_i` is a genuine auxiliary** — an accumulated fact with no `Global_devent` standing for
it, unlike `increasing`'s `B_1`, which is a reification of `X_i ≥ t` in the same `Decomp` and
is substituted back before anything prints. The consequences are
[`lex_less`](lex_less.md#scope-of-this-entry)'s three outcomes, unchanged.

**A remark this entry can make that `lex_less`'s cannot.** `lex_lesseq`, not `lex_less`, is the
comparator the symmetry-breaking entries reach for: `decomps/var_perm_sym.md:8-11` expresses
canonical-ordering symmetry breaking as one `lex_lesseq` between the array and each of its
images under a generator. So this constraint is load-bearing for four further tier-D entries
([`var_perm_sym`](var_perm_sym.md), [`var_sqr_sym`](var_sqr_sym.md), and the `lex2` pair), and
its G3 blocker is theirs.

## Scope of this entry

**Events the generator was asked to explain:** **none.** The decomposition cannot be written in
the input format, so the generator was never asked. There is no `cata/lex_lesseq.tex` and
therefore no `%% generator diagnostics (W1-T3)` footer.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`) | — | **0** | not run: `X_i = Y_i` has no representation (G3) |

Three walls, in the order they would be met — established in
[`lex_less`](lex_less.md#scope-of-this-entry) and not re-derived: **G3** stops the first line;
**W1-T10**'s raise would make the auxiliary a loud failure rather than a silent one; **G17**
would leave `tied_i` in the premises even if a rule printed.

## Generated rules

**None.** There is no `cata/lex_lesseq.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G3`**

Same gap, same reason, as [`lex_less`](lex_less.md#status): only variable-vs-domain-value
comparisons exist, and `X_i = Y_i` is the second line of the decomposition.
`docs/DECOMP_FORMAT_NOTES.md:88-90` records that three independent families hit G3, which is
what makes it load-bearing rather than one constraint's complaint.

Nothing here is validated, flagged or refuted. The relaxed comparator neither helps nor hurts:
it changes which `rule4` clause is written, not which literals exist.

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Two independent failures, either sufficient: no published shape is in the repo
(`catalog/_literature/` has no file for Chu & Stuckey 2011, and writing one from memory is
forbidden by `catalog/README.md` step 2), and there are **0** generated rules on this side, so
there is no premise to place in an implication order.

**A prior, recorded as a prior.** `CHRISTMAS_LIST.md:142` states that no dedicated `lex`
explanation paper was found; if that holds on reading, the eventual verdict is
`no published rule exists`. This entry does not claim it — the row is a previous session's
note and the paper is unread.

**Not compared on minimality**: `catalog/README.md` records that none of the three sourced
papers proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G3` | **the binding one.** `X_i = Y_i` and `X_i ≤ Y_i` have no representation, so the decomposition cannot be written |
| `G17` | no pivot-elimination pass, so `tied_i` cannot be removed from a finished rule (D-0004's cost in coverage) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the printer path that now **raises** (`explenation generator.ml:488`, `:517`) |
| `G7` | **not this entry's, but the family's** — `lex_chain_*`'s instance-dependent pair count routes to `D2`'s missing printer (`docs/DECOMP_FORMAT_NOTES.md:96-104`). A single `lex_lesseq` pair does not need it |

Extensions: **E0** (`CHRISTMAS_LIST.md:142`), with `decomps/lex_less.md:27-31`'s qualification:
E0 means the rule *schemas* exist; here the **event vocabulary** does not.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name. Run
  totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5
  entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `lex_lesseq.tex`.
- `python3 tools/mzn_coverage.py --rank --json` → tier `D literature + solver-native`, ecodes
  `["E0"]`, `CHRISTMAS_LIST.md` line 142. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:488`, `:517` (the printers that raise on a bare
  `B`), `:879-893` (the fifteen `explainall` calls — none is `lex_lesseq`).
- `CHRISTMAS_LIST.md:142`, `:106-109` read → the citation and the solver legend.
- `decomps/lex_lesseq.md`, `decomps/lex_less.md`, `decomps/var_perm_sym.md:8-11`,
  `decomps/_shapes-seq.md:31-62`, `decomps/_shapes.md:52-64,155-175` read → the one-clause
  difference, Shape B / S5, convention 1, and the symmetry-breaking dependency.
- `docs/DECOMP_FORMAT_NOTES.md:34-41, 85, 88-90, 96-104` read → G3, G17, the three families,
  the `D2` withdrawal.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
