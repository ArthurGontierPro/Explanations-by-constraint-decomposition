# `writes`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `writes`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecodes `['E2']` (shared row with `write`, `writes_seq`) |
| **Status** | `nothing generated — blocked on G18` — **`k` times over, plus an `all_different` side condition `write` does not have. See Status.** |
| **Generated** | **0** rules — there is no `cata/writes.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:216` records the literature column as `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`writes(array[int] of var int: a, array[int] of var int: i, array[int] of var int: v, array[int] of var int: b)`

[`write`](write.md) at several positions at once: `b` is `a` with each position `i[k]`
overwritten by `v[k]`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:133` carries the *name* only. `decomps/write.md`
states only that "`writes` does several positions at once" and gives the argument list for
`write` alone; **the four-array signature above is recall extrapolated from that sentence**
and is flagged rather than presented as sourced. `CHRISTMAS_LIST.md:216` files the name
under `11. Maths and misc`.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:216`'s literature column reads, verbatim, `none`,
for the row shared with `write` and `writes_seq`.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`,
`cumulative` and `gcc` only. No web access was used and no search was made.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:216`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The
cell reads, verbatim: `decomp`, and it is a **row-level** cell covering three names.

## Decomposition used here

**Generator value:** none. There is no such value in `explenation generator.ml` and no
`explainall … "cata/writes.tex"` call. (The four matches for the string `write` in that file
are `write_footer` and a comment about stderr, l.645, 716, 727, 741.)
**Emitted by:** nothing.
**Spec:** `decomps/write.md` — titled `# write, writes, writes_seq`, so it covers this name,
in its "What differs per variant" section. Shape **S6** in `decomps/_shapes.md`, the same
shape `element` and [`inverse`](inverse.md) instantiate.

`decomps/write.md`'s statement for this variant, quoted in full:

> "`writes` — `k` updates. The guard becomes `∀j ∉ {I_1..I_k}`, i.e. a conjunction of `k`
> disequalities; same G18, `k` times. The updates must also be pairwise distinct or the
> constraint is unsatisfiable unless the values agree — an `all_different`-flavoured side
> condition (**S2**) on the index array."

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name
exists, so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `A_{j}=t` / `B_{j}=t` (would be) | — | **0** | not run: the unwritten-cells channel needs `∀j ∉ {I_1..I_k}`, a `k`-fold variable-determined exclusion (G18) |

**Everything in [`write`](write.md)'s Scope applies here and is not repeated.** G18 is
`docs/DECOMP_FORMAT_NOTES.md:86`, produced by this family and by nothing else; the type-level
reason it is a wall is that `Rel`'s second argument is an `ind_name` (l.10) and the excluded
position is a `var_name`.

**What is different, and it is the reason this entry is not a pointer to `write`.**

1. **The exclusion is a set, not a point.** `∀j ∉ {I_1..I_k}` needs `k` disequalities
   against `k` different decision variables. G18's one-line statement is written for the
   single-point case (`∀j ≠ I`), and `decomps/write.md` prices the generalisation as "same
   G18, `k` times". **Whether `k` disequalities is the same gap or a compounding of it is
   not settled here**; what is checkable is that `k` is instance-dependent, and
   instance-dependent chain length is separately recorded as blocked on `D2`'s missing
   printer — `docs/DECOMP_FORMAT_NOTES.md:96-104` withdraws W2-A's checked negative on
   exactly this and routes variable-length chains to the same wall as G7. **So `writes` may
   be carrying a second, unnumbered blocker that `write` does not.** Reasoning, not a
   finding, and recorded so it is not lost.
2. **There is an extra obligation `write` does not have**: the update indices must be
   pairwise distinct. That is shape **S2** (`rule1` + a Boolean sum), which runs today in
   `alldiff` (`explenation generator.ml:808-809`) — and inherits **G1** with it, so the
   implicit "at most 1" would never reach the page (`docs/DECOMP_FORMAT_NOTES.md:10`;
   `cata/alldifferent.tex` demonstrates the silence).

## Generated rules

**None.** There is no `cata/writes.tex` (`ls cata/` → 16 files, none of that name), so
`grep -o '\frac'` has no file to count.

## Status

**`nothing generated — blocked on G18`**

Everything [`write`](write.md)'s Status records holds: G18 blocks the *quantifier* form,
`decomps/write.md`'s clause-per-position workaround (`B_j = A_j ∨ I = j`) needs only `rule1`
and `rule4` and **has never been tested**, G9 costs the channel detour, and G2 costs the
second user array its own name — `B 1` makes `printvartex` **raise** (l.517), while `O`
prints as an indexed array (l.522) and is already used that way by `gccn` (l.829), so the
array is encodable today wearing `gcc`'s name.

**Two things are worse here than in `write`.** The workaround's clause becomes
`B_j = A_j ∨ I_1 = j ∨ … ∨ I_k = j`, one `rule4` clause of width `k+1` per position, with
`k` instance-dependent — see Scope item 1 for why that may be a second blocker rather than
a bigger instance of the first. And the `all_different` side condition adds G1 to the list.

**What is *not* worse.** Nothing in the written-cell half changes: it is still `element`'s
S6, `k` copies of it, and copies of a shape that already emits rules elsewhere are not
a new gap.

**Nothing here is validated, flagged or refuted.** There is no artifact.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:216`'s literature column reads `none`; per `catalog/TEMPLATE.md`'s
vocabulary that is `no published rule exists`. Not `pending sourcing` (no paper is cited),
not `out of reach` (no published premise to be out of reach of). Nothing was searched.

The solver cell is `decomp` with no `[G]` and no `[C]`: no unpublished implementation to
note either.

## Gaps

| gap | what it blocks here |
|---|---|
| `G18` | **the recorded one, `k` times.** `∀j ∉ {I_1..I_k}` with each `I_m` a decision variable; `Rel`'s second argument is an `ind_name` (l.10) — `docs/DECOMP_FORMAT_NOTES.md:86` |
| — | **possible second blocker, unnumbered: `k` is instance-dependent.** Variable-length chains are routed to `D2`'s missing printer at `docs/DECOMP_FORMAT_NOTES.md:96-104` (W2-A's checked negative, **withdrawn**). Whether that applies to a `k`-fold exclusion is not settled in the repo. Reasoning, flagged |
| `G2` | **a legibility cost.** Two user arrays; `B 1` makes `printvartex` **raise** (l.517), but `O` is a genuine second-array letter (l.522, `gccn` l.829), so the array is encodable today wearing `gcc`'s name. `decomps/write.md`'s "would print as a Boolean auxiliary" is wrong in both directions |
| `G1` | inherited with the `all_different` side condition on the index array: the threshold never reaches the page (`docs/DECOMP_FORMAT_NOTES.md:10`) |
| `G9` | a **cost**: no `Global ⇔ Global` channel schema (`docs/DECOMP_FORMAT_NOTES.md:77`) |
| — | **the workaround is unchecked, not blocked**, and it widens to `k+1` literals per clause here |

Extensions: **E2** (`CHRISTMAS_LIST.md:216`, route cell "**E2** (array update = `element`
family)"); `CHRISTMAS_LIST.md:232-233` names `write*` among the constraints E2 unlocks.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering; G18 is wave three's
single addition (`:86`, `:106-112`).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` → `writes` in `A no-literature +
  solver-decomposes`, `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 216, section
  `11. Maths and misc`.
- `make validate` (run 2026-09-21, redirected then grepped) → 11 in-scope entries, none of
  them this one. Totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21
  flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 files; no `writes.tex`. `grep -n -i 'write' 'explenation generator.ml'` →
  4 lines, all `write_footer` or a stderr comment (l.645, 716, 727, 741).
- `explenation generator.ml` read, not run → `var_name` at **3**, `Rel` at **10**,
  `printvartex`'s `B i` raise at **517** and its `O` case at **522**, `gccn`'s `Global_devent (true, O, …)` at **829**, `alldiff` at **808-809**.
- `CHRISTMAS_LIST.md:216`, `:106-109`, `:232-233` read → the literature, solver and route
  cells, the legend, the E2-unlock list.
- `tools/data/minizinc-2.10.1-globals.txt:133` read → the name.
- `decomps/write.md` ("What differs per variant") read → the `k`-fold guard, the
  `all_different` side condition, the workaround; `decomps/_shapes.md` (S6, S2) read → the
  shapes.
- `docs/DECOMP_FORMAT_NOTES.md:10, 77, 86, 96-104, 106-112` read → G1, G9, G18, the
  withdrawn checked negative on variable-length chains, the wave-three addendum.
- **Scope item 1 (the possible second blocker) is reasoning, labelled as such in place.**
  Nothing was compiled and no decomposition was written.

**Discrepancies noted, and the one in this file fixed.**

1. **Wrong stub field, fixed here: `Spec: none — this constraint has no
   `decomps/writes.md`.`** It is covered by `decomps/write.md`, whose title line is
   `# write, writes, writes_seq`. `tools/catalog_stub.py` matches filenames only.
