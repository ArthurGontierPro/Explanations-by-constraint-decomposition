# `inverse_in_range`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `inverse_in_range`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecodes `['E0', 'E2']` (shared row with `inverse`) |
| **Status** | `encodable today, not encoded` — **G8 closed on 2026-09-22; G9 and G2 were always costs, not walls.** Re-decided by U2, 2026-09-22. See Status |
| **Generated** | **0** rules — there is no `cata/inverse_in_range.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:199` records the literature column as `none` |
| **Last measured** | 2026-09-21 for the tier and validator rows. **Status re-decided 2026-09-22 (U2)** against `explenation generator.ml` after commits `4547daf`/`1e747ee`; no new run |

## Constraint

`inverse_in_range(array[int] of var int: f, array[int] of var int: invf)`

The `inverse` channel restricted to sub-ranges: `f` and `invf` are inverse where both are
in range, rather than over the whole of `[1,n]`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:74` carries the *name* only, and the argument names
above are recall. What is in-repo and quotable is the *shape* statement:
`decomps/inverse.md` says `inverse_in_range` is "same shape, index sets restricted to
sub-ranges of `[1,n]` rather than the full array", and `decomps/_shapes-perm.md:92-95` says
it "differs only in index set (a sub-range of `[1,n]` rather than all of it)". **The exact
range semantics of the MiniZinc global — which elements are exempt and how — is not stated
anywhere in this repo**, and this entry does not invent it.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:199`'s literature column reads, verbatim, `none`,
for the row shared with `inverse`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. No web access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | see the caveat below |
| Geas | `[G]` present |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:199`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `native (inverse per Chuffed docs) **[G] [C]**`.

**The Chuffed cell is about `inverse`, and this entry does not read it as covering
`inverse_in_range`.** The parenthetical names one constraint — "`inverse` per Chuffed docs" —
and the row carries two. The stub this entry replaces rendered the cell as a flat
`Chuffed | native` for both names; that over-reads a shared row. What the row supports is
"`inverse` is native in Chuffed"; whether `inverse_in_range` is native, decomposed, or absent
is **not established here**, and the `[G]`/`[C]` markers are likewise row-level rather than
per-name.

## Decomposition used here

**Generator value:** none. There is no such value in `explenation generator.ml` and no
`explainall … "cata/inverse_in_range.tex"` call.
**Emitted by:** nothing.
**Spec:** `decomps/inverse.md` — titled `# inverse, inverse_in_range`, so it covers this
name. Shape **P3** in `decomps/_shapes-perm.md:53-100`, renumbered **S6** in
`decomps/_shapes.md`, whose "what varies" row for S6 lists exactly this case: "whether the
index set of the channel is the whole range (`inverse`), a subrange (`inverse_in_range`,
G8), or excludes a **variable** position (`write`, G18)".

The authored decomposition is [`inverse`](inverse.md)'s, with the two `rule1` channels and
the two `rule4` clauses ranging over a sub-range instead of `[1,n]`. Nothing else differs.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=j` / `X_{i} ≠ j` (would be, from an `xac`-like event) | — | **0** | not run: no generator value exists, and the sub-range it would quantify over is not nameable (G8) |

**This is the one of the S6 family where a gap genuinely blocks, and that is worth stating
against its sibling.** [`inverse`](inverse.md)'s zero is "nobody wrote the value"; this one's
zero would survive somebody writing it. `ind_set` is `D of int | D2 of ind_name list`
(`explenation generator.ml:6`), `ind_set_defined` admits `D 1 | D 2 | D 3` and nothing else
(l.459), and `printind_set_int` defines those three as `[1,n]`, `[1,m]`, `[1,n]` (l.460).
There is no constructor for "the sub-range `[lo,hi]`" and no printer for one, so a branch
quantifying over a sub-range would be refused by `filter_branches` exactly as `table`'s `D_4`
branch is. **G8 is a wall for this constraint, not a cost.**

## Generated rules

**None.** There is no `cata/inverse_in_range.tex` (`ls cata/` → 16 files, none of that
name), so `grep -o '\frac'` has no file to count.

## Status

**`encodable today, not encoded`**

**This status changed on 2026-09-22**, and the change is the narrowest of the three U2 made:
this entry already held that G8 was the *only* wall and that G9 and G2 were costs. G8 closed
that day (session G-1, commits `4547daf` and `1e747ee`), so the wall is gone and the costs are
what remain — which is precisely [`inverse`](inverse.md)'s position, and `inverse` already
carries this status.

**What the block was, and the prediction this entry made about it.** `docs/DECOMP_FORMAT_NOTES.md:76`
states G8 as "`ind_set` names only whole predefined ranges — no subrange, no exclusion", and
names `all_different_except*` and **`inverse_in_range`** as the constraints that hit it. This
entry read it against the source and called it absolute, adding that closing it would need "a
new `ind_set` constructor, a printer for it, and admission by `ind_set_defined`" plus a naming
scheme that does not repeat the `D_k` mistake. **All four arrived together.** `ind_set` gained
four formers (`explenation generator.ml:48-52`); `printind_set` prints each
(`:531-537`); `ind_set_defined` admits them (`:520-525`); and the naming problem was answered by
making each former *render its own meaning*, so a set is never a bare `D_4` whose definition
lives elsewhere. `DSub (parent, a, b)` is the one this constraint needs — it prints
`\\llbracket a,b \\rrbracket` (`:534`) — and it is the sub-range `decomps/inverse.md` and
`decomps/_shapes-perm.md:92-95` both say is the entire difference from `inverse`.

**Two things the new status does not say.** It does not say the rules would be good:
`alldifferent_except`, G8's shipped exclusion demonstrator, inherits `alldifferent`'s weakness
and fires only at `n = 2`, and `among` got two rules from the same closure that are measured
UNSOUND. And it does not say the decomposition can be written *faithfully* yet — **the exact
range semantics of the MiniZinc global is not stated anywhere in this repo** (see "Constraint"),
so whoever writes the value has to source it first. `DSub` takes two literal `int` endpoints
(`:49`), which is what "a sub-range of `[1,n]`" needs and is *not* enough for an endpoint that
depends on a running index — see [`sliding_among`](sliding_among.md), where that distinction is
the reason the status did not change.

**G9 and G2 still apply, still as costs.** There is no `Global ⇔ Global` channel schema, so the
two-array channel re-derives `element`'s multi-`Decomp` detour by hand (G9); and `var_name` has
no letter *meaning* a second user array, so `Y` borrows `O` and prints as `gcc`'s occurrence
array (G2). Neither stops the value being written, which is why neither is named in the status.

**Nothing here is validated, flagged or refuted.** There is no artifact, and nothing was run.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:199`'s literature column reads `none`. Per `catalog/TEMPLATE.md`'s
vocabulary that is the verdict `no published rule exists` — not `pending sourcing`, which is
for a row citing something unread, and not `out of reach`, which requires a published premise
to be out of reach of. No comparison is fabricated and nothing was searched.

As with [`inverse`](inverse.md): "no literature" is not "no explaining implementation". The
row carries `[G]` and `[C]`. No solver source is vendored here, so an implementation cannot
be calibrated against either.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **CLOSED 2026-09-22** (`4547daf`, `1e747ee`). It was the binding one and a wall: `ind_set` named only whole predefined ranges, so a channel over a sub-range could not be written or printed. `DSub` now writes it (`explenation generator.ml:49`, `:534`) — see Status. `docs/DECOMP_FORMAT_NOTES.md:76` still lists it as open; that file is not this session's to edit |
| `G9` | a **cost**: no `Global ⇔ Global` channel schema, so the channel re-derives `element`'s detour (`docs/DECOMP_FORMAT_NOTES.md:77`) |
| `G2` | **not in this constraint's spec; read off the source.** `var_name` (l.3) has no letter *meaning* a second user array; `Y` borrows `O` (l.522, `gccn` l.829). A legibility cost — see [`inverse`](inverse.md), Status |
| `G17` | no pivot-elimination pass. Not biting: the reification booleans wash out |

Extensions: **E0, E2** (`CHRISTMAS_LIST.md:199`). The row's "close to **E0**" assessment is
about the *channel*; the sub-range was the part that was not, and as of 2026-09-22 it is.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

**Numbering warning.** `decomps/inverse.md` predates the consolidation and calls this gap
**"G6"** and the channel gap **"G7"**. Consolidated, they are **G8** and **G9**
(`docs/DECOMP_FORMAT_NOTES.md:76-77`, "was" column: `perm G6` → G8, `perm G7` → G9).
`decomps/_shapes-perm.md:92-95` says "same G6-style exclusion/subrange gap as
`all_different_except`" and means the same thing.

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `inverse_in_range` in `B no-literature +
  solver-native`, `ecodes: ['E0', 'E2']`, `CHRISTMAS_LIST.md` line 199, section
  `9. Ordering, sorting, channelling`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `inverse_in_range.tex`.
- `explenation generator.ml` read, not run → `ind_set` at **6**, `var_name` at **3**,
  `ind_set_defined` at **459**, `printind_set_int` at **460**, `printvartex`'s `O` case at
  **522** and `gccn`'s `Global_devent (true, O, …)` at **829**, W1-T2's reasoning on the
  `D_k` counter at **437-447**. These are the evidence that G8 is a wall rather than a cost.
- `CHRISTMAS_LIST.md:199` and `:106-109` read → the literature cell (`none`), the solver
  cell and its `inverse`-only parenthetical, the E2 route cell, the legend.
- `tools/data/minizinc-2.10.1-globals.txt:74` read → the name.
- `decomps/inverse.md` and `decomps/_shapes-perm.md:53-100`, `decomps/_shapes.md` (S6) read
  → the authored decomposition, the sub-range difference, the local gap numbering.
- `docs/DECOMP_FORMAT_NOTES.md:76-77` read → G8, G9 and the "was" column.

**Discrepancies noted, and the ones in this file fixed.**

1. **Wrong stub field, fixed here: `Spec: none — this constraint has no
   `decomps/inverse_in_range.md`.`** It is covered by `decomps/inverse.md`, whose title line
   is `# inverse, inverse_in_range`. `tools/catalog_stub.py` tests for a file named after the
   constraint, so every constraint covered by a multi-constraint spec was recorded as having
   none. The same correction applies to `sort`, `arg_sort`, `minimum`,
   `symmetric_all_different`, `writes` and `writes_seq`.
2. **Over-read stub field, corrected here: `Chuffed | native`.** The shared row's
   parenthetical says "`inverse` per Chuffed docs" and names one constraint, not two. See
   "Solver support".
3. **`decomps/inverse.md` uses pre-consolidation gap numbers** (its "G6" is G8, its "G7" is
   G9).
