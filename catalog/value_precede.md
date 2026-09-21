# `value_precede`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `value_precede`, and no claim of that
> kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **B** — `B no-literature + solver-native`, ecode `E0` (shared row with `value_precede_chain`) |
| **Status** | `nothing generated — blocked on G17` |
| **Generated** | **0** rules — there is no `cata/value_precede.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:140` literature cell reads `none` |
| **Last measured** | 2026-09-21, `make validate`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: this one is *not* blocked by G3, and that makes it the family's cheapest entry

Every other entry this session reviewed in the lex and precedence family is stopped at the
first line by **G3** — only variable-vs-domain-value comparisons exist. `value_precede` is not.
Its guarded literal is `X_i = t` for `t` a parameter (D-0003, `docs/DECISIONS.md:52`, records
that decompositions are authored here and `s`/`t` are taken par), which is exactly the literal
`rule1`'s AC channel already produces. `decomps/_shapes.md:165-166` says so in the shape list:
`value_precede` is S5's "∨ form, guarded literal `X_i = t`, **E0**", where `lex_less` on the
same line is "∧ form, guarded literal `X_i = Y_i`, blocked by **G3**".

**So the decomposition is encodable today, and it has simply not been encoded.** What stands
between it and a catalog entry is not the input format's expressiveness but its one genuine
auxiliary. That is the finding of this entry, and it is the reason the gap cited below is
`G17` rather than `G3`.

## The roadmap's "good early win" framing, corrected — and why the correction stands

`CHRISTMAS_LIST.md:140`'s route cell reads, verbatim:

> **E0** — MiniZinc's decomposition is a Boolean state chain (`b[i]` with `xis -> b[i+1]`,
> `not xis -> b[i]==b[i+1]`), structurally identical to the `increasing` entry that already
> works. **Good early win.**

`decomps/value_precede.md:33-40` checked that claim and corrected it. Quoting its finding
rather than paraphrasing:

> True at the level of "`rule4` plus a fixed shift by 1" — the recursion mechanics match.
> **False** at the level that matters for this catalog: `increasing`'s chained `B_1` *is* the
> explained literal (`X_i≥t`), so it needs zero genuine auxiliaries; `value_precede`'s `b_i` is
> an accumulated fact with no single-literal equivalent, so it is a real auxiliary of exactly
> the kind D-0004 says must be justified and may leak.

Read against the generator today, the correction holds and sharpens. `incr`
(`explenation generator.ml:830-831`) is two `Decomp`s: a `rule1` **BC** channel
`B1_{i,t} ⇔ X_i ≥ t` and a `rule4` two-literal clause over `B1` with `imoin 1`/`iplus 1`. `B1`
washes out because the same `Decomp` defines it as a `Global_devent`, which is why
`cata/increasing.tex` prints only `X` literals. `value_precede`'s `b_i` is defined in terms of
**itself** — `b_{i+1} ⇔ b_i ∨ (X_i = s)` — and `decomps/_shapes.md:337-341` makes that the
declared reason S1 and S5 are different shapes rather than one, verbatim:

> - **S1 vs S5.** `_shapes-seq.md` calls them "the same mechanical skeleton". **Rejected**:
>   S1's `rule4` relates two copies of a family that *is* a reification of `X_i op t`, so the
>   printer substitutes it away; S5's recursion defines its Boolean in terms of **itself** plus
>   a literal, giving an auxiliary with no `Global_devent` behind it. That difference is the
>   whole of W1-T10's `"ERROR B "` and the whole of D-0004's cost here.

Two notes on the row itself, neither a finding about the constraint:

- **"the `increasing` entry that already works" uses a phrase this catalog forbids.**
  `catalog/README.md`, "Never write 'correct'", bans `correct` and `works` alike. The
  defensible statement about that entry is [`increasing`](increasing.md)'s own header row,
  `validated: sound and minimal at n,m <= 4`. The row predates the validator; the same wording
  problem was fixed on `CHRISTMAS_LIST.md:193` on 2026-09-18 and this row was not swept with it.
- **"Good early win" is still half right.** It is wrong that this is `increasing` again. It is
  right that, of the fourteen entries this session reviewed, this is the only one whose
  decomposition the current input format can express — see Status.

## Constraint

`value_precede(int: s, int: t, array[int] of var int: x)`

If the value `t` occurs in `x`, then some earlier position of `x` holds `s`. A value-symmetry
breaking constraint: it fixes which of two interchangeable values may appear first.

**Provenance of the signature:** `decomps/value_precede.md:3-4`, which states it directly
("`value_precede(int: s, int: t, array[int] of var int: x)` — if `t` occurs in `x`, some
earlier position holds `s` first. `s`, `t` par (per D-0003)"). That spec gives no citation of
its own and this checkout holds no `.mzn` file, so treat the argument list as recall — but,
unlike every other entry in this family, **it is recall written down in-repo before this
session**, and the `s`/`t`-are-parameters decision is `docs/DECISIONS.md:52`'s, not a
convenience adopted here. `tools/data/minizinc-2.10.1-globals.txt:127` carries the name.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:140` reads, verbatim:

> none

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only; there is no `value_precede.md` in it. **No published rule shape is stated in
this entry, from memory or otherwise.** No web access was used and no paper was fetched.

## Solver support

| | |
|---|---|
| Chuffed | native (`value-precede.cpp`) |
| Geas | **`[G]`** present |
| Choco LCG | **`[C]`** present |

Source: `CHRISTMAS_LIST.md:140`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. One
solver cell covers this name and `value_precede_chain`.

**Stub field corrected:** the auto-stub's Chuffed cell read bare `native`; the row names the
file. **This is the only constraint in this session's fourteen with all three solver columns
filled** — a native explaining propagator in Chuffed and natives in both Geas and Choco LCG —
which is worth stating beside a status of `nothing generated`: the three solvers explain this
constraint and this method does not.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes `value_precede`, and
none of the fifteen `explainall` calls (lines 879-893) mentions it.
**Emitted by:** nothing.
**Spec:** `decomps/value_precede.md` (40 lines, complete: signature, maths, schema mapping,
E-code, auxiliaries, and the roadmap correction above). Shape **B** in
`decomps/_shapes-seq.md:31-62`, renumbered **S5** in `decomps/_shapes.md:155-174`.

From `decomps/value_precede.md:8-10`:

```
b_1 = false                                       base: nothing precedes position 1
b_{i+1} ⇔ b_i ∨ (X_i = s)       i ∈ [1,n_x-1]     rule4, fixed shift by 1
X_i = t → b_i                   i ∈ [1,n_x]       rule3 (or its rule4 contrapositive), AC
```

Mapped onto the seven schemas, per `decomps/value_precede.md:12-18`:

1. the `X_i = s` channel is the shared `rule1` **AC** grid that `among`/`count`/`gcc` already
   use — no new channel;
2. `b_{i+1} ⇔ b_i ∨ (X_i = s)` is `rule4` with a fixed shift `i→i±1`, mechanically the same as
   `incr`'s `rule4` **except that the disjunct is `b_{i-1}` itself, not a re-indexed copy of
   the same reified predicate**;
3. `X_i = t → b_i` is `rule3`-style, AC.

**Nothing in that list is missing from the engine.** What is missing is a way to get `b_i` back
out of a finished rule.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No `explainall` call names this
constraint, so there is no `cata/value_precede.tex` and no `%% generator diagnostics (W1-T3)`
footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` (would be, from `xac`, `explenation generator.ml:869`) | — | **0** | not run: the decomposition has not been encoded |

**What would happen if it were, and what is *not* established.** `decomps/value_precede.md:28-31`
left this open in 2020's terms — "whether the generated `cata/value_precede.tex` would show a
real premise or the literal text `\"ERROR B \"` depends on whether `find`'s AND/OR walk fully
unfolds the recursion to a base case before it gives up; **not run, so not known**". W1-T10
changed the third outcome's observable and nothing else. The three possibilities, unchanged
from [`lex_less`](lex_less.md#scope-of-this-entry) and **not established**, because nobody can
run what nobody has encoded:

1. `find`'s AND/OR walk unfolds the recursion to an `X`-only base case and a rule prints — with
   `b_i` gone, which would be the good case;
2. the walk meets the recursion as a cycle and cuts it (`R`), which `filter_branches`
   (`explenation generator.ml:622-630`) warns about and drops, losing the candidate;
3. a bare `b_i` reaches a printer and the generator **raises** — `printevent_var` (`:488`) and
   `printvartex` (`:517`) both raise `Generator_failure` since W1-T10, rather than emitting the
   old literal string `"ERROR B "`. `docs/ROADMAP.md:54` records that task `DONE`, with the
   probe: the old generator exited 0 and wrote a broken `.tex`; the new one exits non-zero,
   names the failure and **writes no file**.

**Generation would therefore fail loudly rather than silently** — which is the one thing about
this constraint's future that *is* established, and it is established by reading the two
printer lines, not by running them.

## Generated rules

**None.** There is no `cata/value_precede.tex` (`ls cata/` → 16 files, none of this name;
2026-09-21). Nothing is rendered here and nothing is claimed.

## Status

**`nothing generated — blocked on G17`**

The gap number is `G17`, not `G3`, and the difference is the whole entry.
`docs/DECOMP_FORMAT_NOTES.md:85` defines G17 as "no pivot-elimination pass, so an auxiliary
cannot be removed from a finished rule. This is *why* D-0004 currently costs coverage rather
than only rule length", and scopes it to "every shape with a genuine auxiliary" — S5 is that
shape, by `decomps/_shapes.md:155-160`'s definition of it.

Three things are established and one is not:

- **Established: the schemas exist.** `rule1` AC, `rule4` with a fixed shift, `rule3` — all
  three are in the generator and all three are exercised by shipped decompositions.
- **Established: the auxiliary is genuine.** `b_i` has no `Global_devent` standing for it, so
  nothing substitutes it back, and D-0004 (`docs/DECISIONS.md:78`) says an auxiliary leaks into
  the explanation. G17 says nothing can remove it afterwards.
- **Established: the failure, if it comes, is loud.** W1-T10, above.
- **Not established: which of the three outcomes occurs.** It cannot be, without encoding the
  decomposition and running the generator, and this session owns neither file.

Nothing here is validated, flagged or refuted. **What can be said, and is unusual in this
catalog, is that this entry is blocked on a gap that costs rule *quality*, not
expressiveness** — every other `nothing generated` entry this session reviewed is blocked on
something that stops the input being written at all.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:140` records no explanation for this constraint, which is the condition
`catalog/TEMPLATE.md` attaches to this verdict. Two qualifications:

- **It is a statement about the repo's literature index, not about the literature.** That index
  cost one session of web research over all 118 MiniZinc globals (`CLAUDE.md`, "Context
  budget") and is the source this catalog is required to use; this session did not search the
  web and has no access.
- **Three solvers implement a native propagator for this constraint** (`value-precede.cpp`,
  plus Geas and Choco LCG). A propagator is not a published rule shape, and this catalog does
  not read source it has not got; the solver row is recorded under Solver support and is not
  evidence for or against the calibration verdict.

There are in any case **0** generated rules on this side, so no implication order could be
stated even if a shape were sourced. **Not compared on minimality**, per `catalog/README.md`:
none of the three papers sourced so far proves any explanation minimal.

## Gaps

| gap | what it blocks here |
|---|---|
| `G17` | **the binding one.** No pivot-elimination pass, so `b_i` cannot be removed from a finished rule. D-0004's cost in coverage, not just in rule length (`docs/DECOMP_FORMAT_NOTES.md:85`) |
| — (W1-T10, not a `G` number) | the accumulated-state auxiliary meets the two printers that now **raise** (`explenation generator.ml:488`, `:517`). `docs/DECOMP_FORMAT_NOTES.md:115-117` explains why this is a bug and not a format gap, and names this constraint in doing so |
| — | **`G3` is NOT this entry's.** The guarded literal is `X_i = t` against a parameter (D-0003), not `X_i = Y_i`. This is the distinction `decomps/_shapes.md:165-166` draws inside S5's own instance list, and it is what separates this entry from every `lex_*` one |
| — | **`G7` is NOT this entry's** — a single `value_precede` is one chain of fixed length. It is [`value_precede_chain`](value_precede_chain.md)'s and [`seq_precede_chain`](seq_precede_chain.md)'s |

Extensions: **E0** (`CHRISTMAS_LIST.md:140`), and here — unlike in the `lex_*` entries — E0 is
not qualified: `decomps/value_precede.md:20-22` says "mechanically nothing new is required to
*encode* this decomposition", and reading the schemas today agrees.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `ls cata/` → 16 `.tex` files, none named `value_precede.tex`.
- `python3 tools/mzn_coverage.py --rank` → `value_precede` under
  `B no-literature + solver-native`, ecode `E0`,
  `§3. Value ordering, precedence, symmetry:140`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:488`, `:517` (the two printers that raise on a
  bare `B`), `:622-630` (`filter_branches` and the `R` cut), `:830-831` (`incr` — the `rule1`
  BC channel and the `rule4` shift, the auxiliary that *does* wash out), `:869` (`xac`),
  `:879-893` (the fifteen `explainall` calls — none is this name). **Every line number was
  checked against the current file today** (W1-T14).
- `CHRISTMAS_LIST.md:140`, `:193`, `:106-108` read → the literature, solver and route cells,
  the `increasing` row, and the legend.
- `decomps/value_precede.md` (all 40 lines), `decomps/_shapes-seq.md:31-62`,
  `decomps/_shapes.md:155-174, 165-166, 337-341` read → the decomposition, the schema mapping,
  the roadmap correction, S5, and the declared S1-vs-S5 distinction.
- `docs/DECOMP_FORMAT_NOTES.md:85, 115-117` and `docs/DECISIONS.md:52, 78` read → G17, the
  W1-T10 note, D-0003 and D-0004.
- `docs/ROADMAP.md:54` read → W1-T10 `DONE`, with the probe showing a named failure and no file.
- `tools/data/minizinc-2.10.1-globals.txt:127` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
- The three-outcome analysis under "Scope of this entry" is **reasoning, labelled as such in
  place**, from the printer lines and `filter_branches`. Nothing about it was run.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`decomps/value_precede.md:15` cites `incr`'s `rule4` at "generator line 689".** It is at
   `:831` (the value spans `:830-831`); the file moved in W1-T3/W1-T7.
   [`increasing`](increasing.md) records the same rot for `decomps/increasing.md`'s "688-691".
2. **`decomps/value_precede.md:27-28` says `var_name`'s catch-all is `B i -> "ERROR B "` at
   "generator lines 399, 427" and is "live" for `b_i`.** Both printers **raise** instead, at
   `:488` and `:517`, since W1-T10 (`docs/ROADMAP.md:54`, `DONE`). The risk it describes is
   real and unchanged; its observable is now an exception and no output file. The same stale
   sentence appears in `decomps/_shapes-seq.md:48-57`, `decomps/_gaps-seq.md:9-24` and
   `decomps/_shapes.md:161-162`.
3. **`CHRISTMAS_LIST.md:140`'s route cell says the `increasing` entry "already works".**
   `catalog/README.md` bans that word for a catalog entry. The equivalent wording on
   `CHRISTMAS_LIST.md:193` was fixed on 2026-09-18; this row was not swept with it.
