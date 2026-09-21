# `seq_precede_chain`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `seq_precede_chain`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` (its own row) |
| **Status** | `nothing generated — blocked on G17` |
| **Generated** | **0** rules — there is no `cata/seq_precede_chain.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:141` literature cell reads `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first

`seq_precede_chain(x)` is [`value_precede`](value_precede.md) applied to every consecutive pair
of values in the array's domain. `decomps/seq_precede_chain.md:5-9`:

> Same instance-of relationship as `decomps/value_precede_chain.md` — `seq_precede_chain(x)` is
> `value_precede(v, v+1, x)` for every consecutive pair of values `v` in the array's domain
> (the "chain" is over the *value* domain, not an externally given sequence `c`). Same Shape B,
> same auxiliary-leak caveat as `decomps/value_precede.md`. No new file.

Everything about one copy — the S5 accumulated-state chain, the `b_i` auxiliary, why **G3 does
not apply**, why G17 does, and the W1-T10 raise — is established in
[`value_precede`](value_precede.md) and is not re-derived here.

## Which of the two wave-two claims applies — and a disagreement, recorded not resolved

**The `R` row-index negative STANDS and is irrelevant here**: it is about matrices
(`docs/DECOMP_FORMAT_NOTES.md:94-95`) and this constraint chains over values.

**The `D2` variable-length-chain negative was WITHDRAWN, and
`docs/DECOMP_FORMAT_NOTES.md:96-98` lists `seq_precede_chain` inside its scope. This entry
disagrees, and records the disagreement rather than settling it.** The withdrawal is about an
index set given as an *explicit list* — `D2 of ind_name list` — which is what
[`value_precede_chain`](value_precede_chain.md)'s externally given sequence `c` needs. That is
its own spec's distinction, drawn at `decomps/seq_precede_chain.md:7-8`: **the chain here is
over the value domain, not an externally given sequence.** Read against the generator, the
value domain is not an explicit list at all:

- it is the index set `D 2`, which `printind_set_int` **defines** as `\llbracket1,m\rrbracket`
  (`explenation generator.ml:460`) and `ind_set_defined` admits (`:459`);
- quantifying over it is `forallt = OpForall (FT, D 2)` (`:790`) or `ont = OpOn (FT, D 2)`
  (`:764`), both of which shipped decompositions already use (`:758-761`, the generator's own
  census of live operators);
- stepping `v` to `v+1` inside it is `tplus`/`tmoin` (`:794-795`), whose printer path is the
  `Addint` case (`:471`, `:503`) that `incr`'s `imoin 1`/`iplus 1` already exercise, with
  `printind_name` rendering a `T`-family index as `t` (`:430`).

So the quantifier this constraint needs looks like one the format can already write, and `D2`
looks like the wrong hook for it. **Three reasons this is stated as a disagreement and not as
a correction**, and the status row below does not rely on it:

1. `tplus` and `tmoin` are **used by no shipped decomposition** — the generator's own census at
   `:758-761` lists the live operators and neither is among them — so the composition
   `imap [imoin 1; tmoin 1]` has never been printed, let alone validated.
2. Nothing here was run. This is reasoning from reading the vocabulary, which `CLAUDE.md`
   requires be labelled as such.
3. `docs/DECOMP_FORMAT_NOTES.md` is not this session's file, and its checked-negatives section
   is the repo's record of exactly this kind of claim being made, withdrawn and re-made. The
   right next step is a measurement, not a third edit.

**Either way the status is unchanged**, because `G17` blocks this constraint whether or not
`G7` does.

## Constraint

`seq_precede_chain(array[int] of var int: x)`

For every value `v`, if `v+1` occurs in `x` then `v` occurs at an earlier position: the values
used by `x` are introduced in increasing order, with no gaps before their first use. The
standard value-symmetry break for an array over a fully interchangeable value set.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:110` carries the *name* only, and this checkout holds
no `.mzn` file. `decomps/seq_precede_chain.md:6` writes the constraint as `seq_precede_chain(x)`
and gives its meaning, which is where the argument list above comes from; the MiniZinc types
are recall.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:141` reads, verbatim:

> none

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only. **No published rule shape is stated in this entry, from memory or otherwise.**
No web access was used and no paper was fetched.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:141`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.

**The contrast with [`value_precede`](value_precede.md) is the point of this row**, and its own
spec makes it: `decomps/seq_precede_chain.md:3-5` reads this constraint as "decomposed only, no
dedicated propagator noted", against `value_precede*`'s native `value-precede.cpp` with `[G]`
and `[C]` besides. **One correction to that spec, measured:** it says the row has "no solver
column filled in". The column is filled — `CHRISTMAS_LIST.md:141`'s solver cell reads `decomp`,
quoted above — and the spec's *conclusion* from it is right while its description of the row is
not.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes this constraint, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/seq_precede_chain.md` (9 lines, a pointer to `decomps/value_precede.md`).
Shape **S5** (`decomps/_shapes.md:155-174`), named among its twelve instances at `:165-166` in
the "∨ form, guarded literal `X_i = t`, E0" group.

Per value `v`, from `decomps/value_precede.md:8-10` with `s = v`, `t = v+1`:

```
b_1 = false                                       base: nothing precedes position 1
b_{i+1} ⇔ b_i ∨ (X_i = v)       i ∈ [1,n_x-1]     rule4, fixed shift by 1
X_i = v+1 → b_i                 i ∈ [1,n_x]       rule3 (or its rule4 contrapositive), AC
```

and that block is repeated for every `v` in the value domain. The `v → v+1` step is the shift
this entry's disagreement above is about.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No `explainall` call names this
constraint, so there is no `cata/seq_precede_chain.tex` and no
`%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`, `explenation generator.ml:869`) | — | **0** | not run: the decomposition has not been encoded |

**G17 is the wall, and which way it fails is not established.** `b_i` is a genuine
accumulated-state auxiliary with no `Global_devent` standing for it, so nothing substitutes it
back and no pass removes it afterwards. The three outcomes are
[`value_precede`](value_precede.md#scope-of-this-entry)'s, unchanged and unestablished: the
AND/OR walk unfolds the recursion to an `X`-only base case and a rule prints; or it meets the
recursion as a cycle and cuts it (`R`), which `filter_branches`
(`explenation generator.ml:622-630`) warns about and drops, losing the candidate; or a bare
`b_i` reaches a printer and the generator **raises** (`:488`, `:517`, W1-T10;
`docs/ROADMAP.md:54` records the task `DONE` and the probe — exits non-zero, names the failure,
writes no file).

## Generated rules

**None.** There is no `cata/seq_precede_chain.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G17`**

Same gap and same reason as [`value_precede`](value_precede.md#status), of which this is a
replication: `docs/DECOMP_FORMAT_NOTES.md:85` scopes G17 to "every shape with a genuine
auxiliary", and S5 is that shape.

**`G7` is deliberately not in this row**, unlike
[`value_precede_chain`](value_precede_chain.md)'s — see the disagreement recorded above. It may
belong there; `docs/DECOMP_FORMAT_NOTES.md:98` says it does. This entry does not put a gap in
its status row on the strength of an argument it could not run, and the choice is visible
rather than silent. It changes nothing operationally: G17 blocks this constraint either way.

**G3 does not apply**, as for the whole precede group: the guarded literal is `X_i = v` against
a parameter (D-0003, `docs/DECISIONS.md:52`), not `X_i = Y_i`. Nothing here is validated,
flagged or refuted.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:141` records no explanation for this constraint, the condition
`catalog/TEMPLATE.md` attaches to this verdict. It is a statement about the repo's literature
index — one session of web research over all 118 MiniZinc globals (`CLAUDE.md`, "Context
budget") — and not about the literature; this session did not search the web and has no access.

There are **0** generated rules on this side, so no implication order could be stated even if a
shape were sourced. **Not compared on minimality**, per `catalog/README.md`.

## Gaps

| gap | what it blocks here |
|---|---|
| `G17` | **the binding one.** No pivot-elimination pass, so `b_i` cannot be removed from a finished rule — D-0004's cost in coverage, not just rule length (`docs/DECOMP_FORMAT_NOTES.md:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the two printers that now **raise** (`explenation generator.ml:488`, `:517`); `docs/DECOMP_FORMAT_NOTES.md:115-117`, which names this family |
| `G7` | **listed, and deliberately not in the status row.** `docs/DECOMP_FORMAT_NOTES.md:96-98` scopes the withdrawn `D2` negative to include this constraint; this entry argues from the generator's vocabulary that the value domain is `D 2` and not an explicit list, and records the disagreement unresolved (see "Which of the two wave-two claims applies") |
| — | **`G3` is NOT this entry's** — the guarded literal is `X_i = v` against a parameter (`decomps/_shapes.md:165-166`) |

Extensions: **E0** (`CHRISTMAS_LIST.md:141`), and per `decomps/seq_precede_chain.md:8` the
E-code and the auxiliary-leak caveat are `value_precede`'s.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `ls cata/` → 16 `.tex` files, none named `seq_precede_chain.tex`.
- `python3 tools/mzn_coverage.py --rank` → `A no-literature + solver-decomposes`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:141`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:6` (`ind_set`), `:430` (`printind_name`, the
  `T`-family letter), `:459`, `:460` (`ind_set_defined`, `D 2` = `[1,m]`), `:464` (the `D2`
  raise), `:471`, `:503` (the two `Addint` printer cases), `:488`, `:517` (the printers that
  raise on a bare `B`), `:622-630` (`filter_branches`), `:758-761` (the generator's own census
  of which index operators the decompositions use), `:764` (`ont`), `:790` (`forallt`),
  `:794-795` (`tplus`/`tmoin`, defined and unused), `:869` (`xac`), `:879-893`. **Every line
  number was checked against the current file today** (W1-T14).
- `CHRISTMAS_LIST.md:140`, `:141`, `:106-108` read → this row's literature, solver and route
  cells, the `value_precede*` row it is contrasted with, and the legend.
- `decomps/seq_precede_chain.md` (all 9 lines), `decomps/value_precede.md`,
  `decomps/value_precede_chain.md`, `decomps/_shapes.md:155-174` read → the pointer, the
  decomposition, S5 and its instances.
- `docs/DECOMP_FORMAT_NOTES.md:85, 94-95, 96-107, 115-117` and `docs/DECISIONS.md:52, 78`
  read → G17, the two checked negatives, W1-T10, D-0003, D-0004.
- `docs/ROADMAP.md:54` read → W1-T10 `DONE` and its probe.
- `tools/data/minizinc-2.10.1-globals.txt:110` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
- The `G7` disagreement and the three-outcome analysis are **reasoning, labelled as such in
  place**, from the index-operator vocabulary and the printer lines. Nothing about either was
  run, and neither is load-bearing for the status row.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`decomps/seq_precede_chain.md:3-4` says `CHRISTMAS_LIST.md` lists this constraint with
   "no solver column filled in".** The cell reads `decomp` (`:141`). Its conclusion —
   "decomposed only, no dedicated propagator noted" — is what the cell says; the description of
   the row is not.
2. **The three listed in [`value_precede`](value_precede.md#how-this-entry-was-produced)** —
   the stale `incr` line number in `decomps/value_precede.md:15`, the four files that still say
   a bare `B` prints `"ERROR B "`, and `CHRISTMAS_LIST.md:140`'s "already works".
