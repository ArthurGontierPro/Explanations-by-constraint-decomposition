# `disjunctive_strict`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `disjunctive_strict`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecode `E2` (shared row with `disjunctive`, `_opt`, `disjunctive_strict_opt`) |
| **Status** | `nothing generated — blocked on G1` — **still, after G1's partial closure on 2026-09-22**: what closed is a threshold on a Boolean sum; `d_i = 0` is a constant in a *guard*. Re-checked by U2, 2026-09-22. See Status |
| **Generated** | **0** rules. There is no `cata/disjunctive_strict.tex`; the near-miss artifact is `cata/cumulative.tex`, and it is the **non-strict** sibling — see below |
| **Validator** | out of scope: nothing of this name to validate. The artifact it is closest to, `cata/cumulative.tex`, is itself reported out of scope ("UNPARSED: index equation offset: t'=t-d_{i}") |
| **Calibration** | **out of reach** — the published §6 explanations are indexed by a run-time compulsory-part set, and there is no generated rule on this side either |
| **Last measured** | 2026-09-21 for the tier, validator and calibration rows. **Status re-checked 2026-09-22 (U2)** against `explenation generator.ml` after commits `4547daf`/`1e747ee`; unchanged, and no new run |

## Read this first: what separates this entry from `disjunctive`, and it is one time point

[`catalog/disjunctive.md`](disjunctive.md) establishes that `cata/cumulative.tex` is really
the `disjunctive` artifact. This entry's question is whether that artifact is also
`disjunctive_strict`'s, and the answer is **no, and the difference cannot be stated in this
format at all.**

The two constraints differ on exactly one case: a **zero-duration** task. `disjunctive` lets a
`d_i = 0` task sit anywhere; `disjunctive_strict` still forbids it overlapping another task at
its start point (`decomps/disjunctive_strict.md:3`).

Substituting `d_i = 0` into the shipped overlap indicator settles which of the two the artifact
encodes. The `cumul` value's step 2 (`explenation generator.ml:811`) is
`B2_{i,t} ⇔ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1}` (`decomps/_shapes-ext.md:246-249`); at `d_i = 0` the
two conjuncts are a literal and its own negation, so `B2_{i,t}` is **false at every `t`** and
the task occupies no time point. That is the **non-strict** semantics. *This is a substitution
into the shape as written down in the spec, read off the source — it is reasoning, not a
measurement*, and it cannot be measured, because the validator cannot parse `t' = t − d_i` at
all (`make validate`, this session).

So the honest position: **on instances where every `d_i ≥ 1` the two constraints coincide and
the shipped artifact covers both; the entire difference between them lives in the one case the
format cannot express.** That coincidence is not coverage, and this entry does not count it as
such.

## Constraint

`disjunctive_strict(array[int] of var int: s, array[int] of var int: d)`

As `disjunctive` — tasks with starts `s_i` and durations `d_i` do not overlap — but a
zero-duration task may not overlap another task either.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:57` carries the *name* only; this checkout holds no
`.mzn` file (`find . -name '*.mzn'` → empty, 2026-09-21). The wording above is transcribed from
`decomps/disjunctive_strict.md:3`, which records it without a citation of its own; treat it as
recall.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:169`, literature cell, verbatim:

> implied by the cumulative papers (unary is the special case)

pointing at Schutt, Feydy, Stuckey, Wallace 2011 and Schutt, Feydy, Stuckey CPAIOR 2013
(`CHRISTMAS_LIST.md:167`).

**Rule shape:** the Constraints 2011 paper is sourced in
[`catalog/_literature/cumulative.md`](_literature/cumulative.md) and is rendered, with C2's
tags, in [`catalog/disjunctive.md`](disjunctive.md#published-explanation). It is not repeated
here. **Nothing in that file distinguishes the strict from the non-strict unary resource**, and
`catalog/_literature/cumulative.md` states in its own words that the paper gives no unary
special case of its explanations at all. No paper was fetched by this session.

## Solver support

| | |
|---|---|
| Chuffed | native (`disjunctive.cpp`) |
| Geas | **`[G]`** present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:169`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The row
covers all four `disjunctive*` names with one solver cell, so this table is the family's, not
this name's specifically.

## Decomposition used here

**Generator value:** none of this name. The nearest is `cumul`,
`explenation generator.ml:810-812`, which is the non-strict reading (see above).
**Emitted by:** nothing under this name.
**Spec:** `decomps/disjunctive_strict.md`; shape **SCH-1** (`decomps/_shapes-ext.md:238-271`),
renumbered **S9** in `decomps/_shapes.md:226-238`, which lists `disjunctive_strict` as one of
S9's three instances.

`decomps/disjunctive_strict.md:5-7` says the strictness "changes only which time points a
zero-duration task occupies … a boundary condition on the same `rule3` conjunction, not a new
schema", and that is right about the *shape*. What it does not say, and what this entry adds,
is that the boundary condition is a **case split on the value of a duration**:

```
B2_{i,t}  ⇔  (d_i > 0 ∧ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1})  ∨  (d_i = 0 ∧ t = s_i)
```

and a `Decomp` carries no predicate over an `ind_const`. `ind_const` is
`C of int` (`explenation generator.ml:7`) and its printer renders every instance as the bare
letter `d` (`:466`); the constant is never captured as an event, an index, or anything else the
printer or the traversal walks. That is **G1**, stated for a duration rather than for a
threshold.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No decomposition of this name exists,
so there is no `%% generator diagnostics (W1-T3)` footer and no candidate count.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_i ≥ t` / `X_i < t` (would be, from `xbc`) | — | **0** | not run: the strictness condition is not encodable (G1) |

**Why there are 0 rules, in one sentence:** the only schema chain available is `cumul`'s, and
running it would produce the non-strict constraint's rules under this constraint's name — the
same class of mislabelling that [`catalog/cumulative.md`](cumulative.md) calls the most
misleading thing in the catalog. Getting *this* constraint needs the `d_i = 0` clause, and that
needs G1.

## Generated rules

**None.** There is no `cata/disjunctive_strict.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). The two rules in `cata/cumulative.tex` are rendered in
[`catalog/disjunctive.md`](disjunctive.md#generated-rules) and belong to the non-strict
sibling; they are deliberately **not** reproduced here.

## Status

**`nothing generated — blocked on G1`**

Nothing was generated, and the gap is G1: this constraint is distinguished from its sibling by
a predicate on a duration constant, and a constant cannot reach a rule, an index or a branch in
this format — it exists only as an OCaml literal inside an index closure.
`docs/DECOMP_FORMAT_NOTES.md:10-21` states G1 for `at_least`/`at_most`/`exactly`'s threshold
`n`; **this entry is a fourth constraint pinned to it, and the first where the un-sayable
constant is what separates one global from another** rather than what a rule fails to mention.

Two things this status does *not* say. It does not say the shape is missing — S9 exists and
runs. And it does not say `d_i = 0` is rare or uninteresting: it is the entire content of the
`_strict` suffix.

**Re-checked 2026-09-22 (U2), after G-1 closed part of G1 in commits `4547daf` and `1e747ee`.
The status is unchanged, and the reason is that G1 turns out to name two different things.**
What closed is *a threshold on a Boolean sum*: `DCard (name, parent, op, bound)` carries a
cardinality into the index data (`explenation generator.ml:52`, printed `:537`), so
`at_most(c)` can say "a witness set `S` with `|S| = c+1`" and `cata/at_most.tex` prints its own
`c`. That is the shape `docs/DECOMP_FORMAT_NOTES.md:10-21` describes when it states G1 for
`at_least`/`at_most`/`exactly`.

**This entry is the fourth constraint pinned to G1 and the only one where the constant is not a
threshold on a sum.** `d_i = 0` is a per-task predicate on a duration constant, deciding whether
a pair of tasks may overlap at all — a *guard* on the decomposition, not a bound on a count.
None of the four new `ind_set` formers reaches it: `DCard` bounds a set's size, `DSub` takes two
literal `int` endpoints, `DExc` removes named elements, `DPar` names a parameter subset
(`explenation generator.ml:48-52`). A set can now be *named*; a constant still cannot be
*compared* anywhere the printer walks. So the sentence this entry was written to make survives
the closure intact, and it is now sharper rather than weaker: **this is the first constraint
where the un-sayable constant is what separates one global from another**, and it is the one
part of G1 that 2026-09-22 did not touch.

*A reading of `explenation generator.ml`'s types and printers, not a measurement; nothing was
run.*

## Calibration (W3-T5, D-0013)

**Verdict: out of reach.**

Two reasons, either sufficient:

1. **Nothing on this side.** 0 generated rules, so no premise to place in an implication order.
2. **The published side is structurally out of reach**, exactly as for
   [`disjunctive`](disjunctive.md#calibration-w3-t5-d-0013): the sourced paper's §6
   explanations quantify over a compulsory-part set `B`, a profile sequence and a chosen list
   of time points, all built by scanning the time-table profile at propagation time
   (`catalog/_literature/cumulative.md`, "Schema or per-propagation?", `QUOTED`). A run-time
   object has no index set here, so no implication either way is statable. Reaching those rules
   is **E4**.

**What is *not* out of reach, and is inherited rather than re-derived.** The paper's own
**TimeD** decomposition (§5.1, `QUOTED`) is a schema, and `catalog/disjunctive.md` shows the
shipped `cumul` chain is TimeD at `r_i = 1`, `c = 1`. That comparison is available to the
non-strict sibling once G15 and G1 close. It does **not** transfer to `disjunctive_strict`
without a further step nobody has taken: TimeD as quoted has no zero-duration clause either, so
what the strict variant should even be compared *against* is not established.

**Not compared on minimality.** The sourced paper proves nothing minimal (`QUOTED`, preprint
p.13, two open questions).

## Gaps

| gap | what it blocks here |
|---|---|
| `G1` | **the binding one, and the half of it that 2026-09-22 did not close.** `DCard` now carries a constant into a rule as a *threshold on a Boolean sum's witness set* (`cata/at_most.tex`). `d_i = 0` is a constant in a **guard**, and no `ind_set` or `ind_bound` former compares one (`explenation generator.ml:46`, `:48-52`). This is what separates this constraint from `disjunctive`, and the whole of it |
| `G15` | inherited from the shape: `t' = t − d_i` is the validator's measured `UNPARSED`, so even the non-strict sibling's rules cannot be checked. Closing G1 without G15 would give an unmeasurable entry |
| `G3` | **`fzn_disjunctive`'s general form only** — variable durations make the atoms variable-vs-variable (`CHRISTMAS_LIST.md:169`). Not needed for the constant-duration form this entry covers |
| — | the **global** window-and-subset explanation is **E4**; see Calibration |

Extensions: **E2** per `CHRISTMAS_LIST.md:169`; `decomps/disjunctive_strict.md:9` prices the
constant-duration form **E0** and the variable-duration form **E2**, "exactly as `disjunctive`".
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected then grepped) → no entry of this name; the
  `cata/cumulative.tex` out-of-scope reason quoted above, verbatim. Run totals: **34 rules
  checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope.**
- `ls cata/` → 16 `.tex` files, none named `disjunctive_strict.tex`.
- `python3 tools/mzn_coverage.py --rank --json` → tier `D literature + solver-native`, ecodes
  `["E2"]`, `CHRISTMAS_LIST.md` line 169, section `6. Scheduling`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:810-812` (`cumul`), `:7` (`ind_const = C of int`),
  `:466` (`printind_const`, every constant prints as `d`), `:343-355` (`rule5` has no bound
  argument — see `catalog/disjunctive.md`).
- `decomps/disjunctive_strict.md`, `decomps/disjunctive.md`, `decomps/_shapes-ext.md:238-271`,
  `decomps/_shapes.md:226-238` read → the signature, SCH-1/S9's maths and instance list.
- `CHRISTMAS_LIST.md:169`, `:167`, `:106-109` read → literature, solver and route cells.
- `catalog/_literature/cumulative.md` read, **not fetched** → TimeD, the per-propagation
  finding, the open minimality questions; C2's tags carried across.
- The `d_i = 0` substitution in "Read this first" and the case-split display in "Decomposition
  used here" are **reasoning, labelled as such in place**, from the spec's maths and the
  generator source. Neither was run; neither can be.
