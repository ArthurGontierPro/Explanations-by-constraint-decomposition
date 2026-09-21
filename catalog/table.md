# `table`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `table`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **D** — `D literature + solver-native`, ecodes `['E2']` (`python3 tools/mzn_coverage.py --rank --json`) |
| **Status** | `nothing generated — blocked on G6` |
| **Generated** | **0** rules in `cata/table.tex` |
| **Validator** | **0 rules to check.** `table` is *in* the validator's 11 in-scope entries — it is not reported out of scope — and contributes nothing: `---- cata/table.tex  (0 rules) ----` |
| **Calibration** | **pending sourcing (C2)** — two papers are cited at `CHRISTMAS_LIST.md:158` and neither is in `catalog/_literature/` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/table.tex \| wc -l`, `python3 tools/mzn_coverage.py --rank --json` |

**Why this entry was late.** It was skipped in an earlier review wave by an orchestrator
error — a session was told `table` had already been reviewed and it had not. Nothing about
the constraint caused the delay; the record is kept here so the gap in the wave log has a
cause attached to it.

## Constraint

`table(array[int] of var int: x, array[int,int] of int: t)`

The tuple `x[1..n]` is one of the rows of the constant matrix `t`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:125` carries the *name* only. The signature above is
transcribed from `decomps/table.md` ("Signature"), which records it without a citation of
its own; treat it as recall. `CHRISTMAS_LIST.md:158` files the name under
`5. Extensional — table, regular, MDD`.

## Published explanation

**Citation:** `CHRISTMAS_LIST.md:158` cites two —

- **Gange, Stuckey, Szymanek 2011**, *MDD propagators with explanation*, Constraints
  16:407–429 (the row notes MDDs subsume table, regular, set/multiset);
- **McIlree & McCreesh, CP 2023** (best paper), *Proof logging for smart extensional
  constraints*, which the row describes as certified justifications for Smart Table.

**Rule shape:** **pending sourcing (C2).** There is no `catalog/_literature/table.md`; that
directory holds `alldifferent`, `cumulative` and `gcc` only. **No published rule shape is
stated in this entry, from memory or otherwise**, and no web access was used.

**One in-repo sentence about those papers' content is UNSOURCED and is flagged here rather
than repeated.** `decomps/table.md` ends "the derived rules are the smart-table
justifications of McIlree & McCreesh, CP 2023", and `decomps/_shapes-ext.md` (EXT-1,
"Auxiliaries") says the intended printed form "is the shape of the justification McIlree &
McCreesh certify for smart tables". Neither file cites a reading. They are predictions about
an unread paper. This entry does not adopt them, and the Calibration section below says so
as a prior, not a verdict. (Those two files are not this session's to edit.)

What *is* quotable in-repo is this repo's own routing, and only that: `CHRISTMAS_LIST.md:158`
prices `table` at **E2** and adds, verbatim, "MiniZinc's `fzn_table_int` introduces a var
row-index into a constant matrix — an `element`. The repo's own `table` entry uses a
different encoding and currently emits an **unsound empty-premise rule**; that is a bug, not
a missing extension." **The second half of that sentence is now stale in the artifact and
true in the decomposition** — see "Scope of this entry".

## Solver support

| | |
|---|---|
| Chuffed | native (`table.cpp`) |
| Geas | `[G]` present |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:158`, solver-column legend at `CHRISTMAS_LIST.md:106-109`. The row
reads, verbatim: **native** (`table.cpp`) **[G] [C]**. All three explaining implementations
exist; none is vendored here, so none can be calibrated against from this repo.

## Decomposition used here

**Generator value:** `table`, `explenation generator.ml:862-864`
**Emitted by:** `explainall [x3ac] table "cata/table.tex"`, line **893**
**Spec:** `decomps/table.md`; shape **EXT-1** in `decomps/_shapes-ext.md`, which
`decomps/_shapes.md` renumbers to **S7** ("candidate-set selector over a constant relation",
the corpus's only instance).

```ocaml
let table  = [Decomp (1, rule1, [Global_devent (true , X   , id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule3, [Decomp_devent (true , (B 1), id, oni); Reified_devent (true, (B 2), id, imap [i_out])]);
              Decomp (4, rule4, [Decomp_devent (true , (B 2), id, onr)])]
```

with `oni = OpOn (FI, D 1)` (l.763), `i_out = OpOut FI` (l.771) and
`onr = OpOn (FR, D 4)` (l.766). The global event is
`x3ac = Global_event (true, X, [Ind (I 1,[]); Ind (T 1,[]); Ind (R 1,[])], AC)`, line **875**.

- **step 1, `rule1`** — `B1 ⇔ X = …`, arc consistency, `id`/`id` on both sides.
- **step 2, `rule3`** — the row conjunction: `B2 ⇔ ⋀_i B1`, with `i` dropped on the way up.
- **step 3, `rule4`** — the row selector: a disjunction over `r ∈ D_4`, with **no
  `Reified_devent`**, so `reified_devent` falls back to the placeholder
  `Reified_devent (true, T, id, id)` (l.245-246) that no real variable matches.

**The shipped decomposition is not EXT-1/S7, and that is the first thing to say about it.**
EXT-1 is `R_r ⇔ ⋀_{i∈[1,n]} (X_i = T[r,i])` selected by `⋁_r R_r`. The shipped value carries
the row index `r` on the **`X` literal itself** (`x3ac`'s third `Ind (R 1,[])`) and uses
`id`/`id` in step 1, so `r` is introduced on a literal that does not depend on it and is
never eliminated. **Nothing anywhere states the side condition `t = T[r,i]`.** So step 1 says
`B1_{i,t,r} ⇔ X_i = t` — `r`-indexed on the left, `r`-independent on the right — and steps 2
and 3 then quantify over an `r` that constrains nothing. This diagnosis is `decomps/table.md`'s
and `decomps/_shapes-ext.md`'s; it is re-read off the source here and it holds, but **both
files cite it at generator `l.720–722` / `l.734`, which no longer resolve** — the value is at
862-864 and `x3ac` at 875 (W1-T14).

## Scope of this entry

**Events the generator was asked to explain:** two — `X_i = t` and `X_i ≠ t`, from the single
global event `x3ac` (l.875). `x3ac` differs from the `xac` every other entry uses only by the
extra `Ind (R 1,[])`, which is the defect above.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **0** | `dropped F 0, cycle 0, duplicate 0, undefined index set 1` (`D4`) |
| `X_{i} \neq t` | 1 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |

Verbatim from the artifact — this is the whole file, there is nothing above it:

```
%% generator diagnostics (W1-T3)
%% X_{i}=t : 1 candidate(s) -> 0 rule(s); dropped F 0, cycle 0, duplicate 0, undefined index set 1
%%   ** REFUSED for X_{i}=t: 1 branch(es) reference undefined index set(s) D4; emitting them would state a rule over a set the artifact never defines (W1-T2) **
%%   ** NO RULE EMITTED for X_{i}=t: 1 candidate(s), all blocked **
%% X_{i} \neq t : 1 candidate(s) -> 0 rule(s); dropped F 1, cycle 0, duplicate 0, undefined index set 0
%%   ** NO RULE EMITTED for X_{i} \neq t: 1 candidate(s), all blocked **
```

**The two events are blocked by two different things, and only one of them is W1-T2.**
`X_i = t` loses its single candidate to the refusal over `D_4` — the row set, which
`onr = OpOn (FR, D 4)` names and `ind_set_defined` (l.459) does not admit. `X_i ≠ t` loses
its single candidate to an `F` drop, the legitimate kind (CLAUDE.md, W1-T3): the branch
reaches a constraint that is not reified. Step 3's missing `Reified_devent` is what puts it
there — `rule4`'s `fnre` on the `T` placeholder yields `Lit F`.

**What the artifact used to ship, and why the count moved.** Before W1-T2, `cata/table.tex`
carried **three** rules and `docs/VALIDATOR.md:287` measures all three as `UNSOUND` — "under
every reading", per `docs/ROADMAP.md:50`. One of them concluded `X_i = t` **from an empty
premise**. That rule is gone from the file; the decomposition that produced it is untouched.
`docs/ROADMAP.md:50` (W1-T4) is explicit and is quoted here rather than paraphrased:
"**MASKED, NOT FIXED** … do not close this row. The generator census now reports 0
empty-premise rules, but only because W1-T2 refused the whole branch … The decomposition
that produced an empty premise is untouched and will produce it again the moment G6 lands."
So `table` is the one entry in the catalog whose 0 is *worse* news than a 0 elsewhere: the
other empty entries are blocked, this one is also masked.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/table.tex`.

## Generated rules

**None.** `grep -o '\\frac' cata/table.tex | wc -l` → `0`. The file is the diagnostics footer
and nothing else (and it has no trailing newline, so `wc -l` reports 0 for a different
reason — CLAUDE.md, "Traps").

## The two propagations this decomposition means, and why neither is expressible

This section is the substance of the entry. Both propagations are the right ones; the
encoding can state neither, and they fail for *different* reasons.

**1. Row elimination forces a value.** If every row but `r` has been ruled out at some
position, then position `i` must carry row `r`'s entry:

```
∀r' ≠ r, ∃i : X_i ≠ T[r',i]
------------------------------ ⊢
X_i = T[r,i]
```

This needs **G6**, and nothing smaller.

**2. A ruled-out row forbids its own value.** If row `r` is dead, `X_i` need not take
`T[r,i]` — but the decomposition cannot supply "row `r` is dead" as a premise. The only thing
in the encoding that says what `R_r` means is `R_r`'s own defining conjunction, so an
explanation of `¬R_r` would be justified by the definition of `R_r`: **circular**. This is
not G6 and no gap on the consolidated list fixes it; it is why `X_i ≠ t`'s branch dies at an
`F` leaf rather than at the `D_4` refusal. Stating it would need a premise about a row's
status that is derivable from something other than the row's definition, and the
decomposition has no such thing.

### G6, stated precisely

> **The value in `X_i = t` should be `T[r,i]` — a function of row *and* position.** The
> language relates index **names** (`Rel : ind_name*ind_symbols*ind_name`, l.10) and, for a
> **1-D** constant array, `Addcst : ind_name*ind_name*ind_symbols*ind_const*ind_name` (l.12,
> printing as `i' = i - d_{j}`, l.504). It has **no term for a 2-D lookup.** So one anonymous
> `t` has to stand for two different values — `T[r',i]` in the premise and `T[r,i]` in the
> conclusion.

**That is why the rule is both unsound and unreadable, and the legibility half is not a
side-effect.** The unsoundness is the shared `t`: the premise's value and the conclusion's
value are forced to be the same symbol when the constraint requires them to differ. The
illegibility is the same fact seen from the page: a reader of the `.tex` cannot tell which
row a `t` came from, because the notation has nowhere to put the row. **A rule its own author
cannot read is not an explanation**, which is the project's own standard, and it means G6 is
not a rendering improvement that could wait for a printer patch. This statement of G6 is the
author's and the orchestrator's, recorded here because it is sharper than
`docs/DECOMP_FORMAT_NOTES.md:74`'s one-line table row ("2-D constant table read as a
function, `t = T[r,i]`. `Addcst` is 1-D") without contradicting it.

### The candidate cheap fix: `D2`, and what it does and does not buy

`docs/DECOMP_FORMAT_NOTES.md` records `ind_set`'s second constructor,
`D2 of ind_name list` (l.6), as the right hook for **G7** and notes that no decomposition
uses it. **Read against G6 it is a candidate here too, and it is cheaper than it looks in
one respect and not a solution in another.** All of the following is read off the source,
**not tested — nothing was run to check it**, and no decomposition was written.

What is already in place today:

- `ontin (D2 [R 1; I 1])` is **constructible**: `ontin d = OpOn (FT, d)` (l.768) takes any
  `ind_set`, and `D2` is one.
- `apply_op` **handles it** without change: `OpOn (f,d) -> Ind (fam_ind f, Set (fam_ind f, IN, d)::[])`
  (l.102) carries `d` opaquely. Nothing in the interpreter inspects the set.
- It would produce the modification `Set (T 1, IN, D2 [R 1; I 1])` — syntactically, "`t` is
  in the set named by `r` and `i`", i.e. `t ∈ D(r,i)`, and a singleton `D(r,i) = {T[r,i]}`
  makes membership and equality the same statement.

What is missing, in increasing order of cost:

1. **A printer.** `printind_set` (l.462-464) *raises* on `D2`: "the D2 (index-list) set
   variant has no printer; it used to emit the literal string `"setfils"`". (The `"setfils"`
   phrasing in older notes is stale — W1-T2 turned it into a raise, l.463-464.)
2. **Admission by the filter.** `ind_set_defined` (l.459) returns `false` for `D2 _`, so any
   branch using it is refused and counted exactly as `D_4` is now. One line, but it must not
   be flipped before (1) and (3).
3. **A stated meaning.** Nothing says what the `ind_name list` *is*. Is `[R 1; I 1]` an
   argument list of a 2-D lookup, a union over two families, a pair? The type admits all
   three and the repo states none. This is the part that belongs to the format freeze (W2-T1)
   rather than to a patch, and it is the same objection W1-T2 makes to simply defining `D_4`
   in the printer: the artifact would name a thing it does not define.
4. **A second, unconstrained value index — and this one `D2` does not supply.** G6's rule
   needs `T[r',i]` in the premise *and* `T[r,i]` in the conclusion: two value indices, free
   to be equal or not. The three ops that can put a `t` anywhere are `OpOn` (l.102), which
   **discards the index list and installs one fresh `T 1`**, `OpForall`/`OpPoint` (l.103-104),
   which prepend another index **also named `T 1`** because `fam_ind FT = T 1` (l.85), and
   `OpPrim`/`OpSum` (l.106-107), which are the only ones that prime — and both build
   `prim_node`/`sum_node`, which attach `Rel (t', NEQ, t)` unconditionally (l.96-97). So the
   only way to get a distinct `t'` today also asserts `t' ≠ t`, which for `table` is simply
   false: two rows may agree at a position.

**Assessment.** `D2` is a real hook for the *side condition* half of G6 and is worth two of
the three things it needs being cheap. It does **not** reach the anonymous-`t` problem, which
is the half that makes the rule unsound and unreadable. Anyone landing G6 through `D2`
should expect the printer and the meaning to be the easy part and the second value index —
either a way to prime without `≠`, or rule-level binder scope (roadmap W1-T1, the same
blocker `element` has) — to be the work. **Untested**; the read above is of
`explenation generator.ml` lines 6, 85, 96-97, 102-107, 459, 462-464, 768.

## Status

**`nothing generated — blocked on G6`**

Two events, one candidate branch each, zero rules: one refused over the undefined row set
`D_4` (W1-T2), one dropped at an `F` leaf. Nothing in this entry is validated or flagged,
because there is nothing to validate. The content of the entry is the negative result, the
statement of G6 above, and the fact recorded in `docs/ROADMAP.md:50` that the empty-premise
defect is **masked, not fixed** — the decomposition that produced it is unchanged and will
produce it again the moment the row set becomes printable without the `T[r,i]` side
condition landing alongside. **The order matters: G6 must land before, or with, any
definition of `D_4`, never after it.**

## Calibration (W3-T5, D-0013)

**Verdict: pending sourcing (C2).**

Both conditions for a calibration fail, independently:

1. **No published shape is in the repo.** Two papers are cited at `CHRISTMAS_LIST.md:158`
   and `catalog/_literature/` holds neither. `catalog/README.md` step 2 and
   `catalog/_literature/README.md` forbid writing a shape from memory; this session has no
   web access and searched nothing.
2. **No generated rule exists on this side.** With **0** rules there is no premise to place
   in an implication order even if the shape were sourced.

**`table` is a tier-D calibration target and it is currently the emptiest one.** It is one of
the four constraints `docs/ROADMAP.md:55` names as tier D — "`table`, `regular`,
`alldifferent`, `cumulative` are tier D, calibration targets" — and unlike `alldifferent` and
`cumulative` it has no rule at all to compare.

**A prior, recorded as a prior.** Two in-repo files predict that the G6-repaired rules would
*be* McIlree & McCreesh's smart-table justifications (quoted under "Published explanation"
above). If that prediction is right the verdict would be `agrees` or `weaker`; if the
published premise turns out to be indexed by a run-time object — an MDD node set, as Gange et
al.'s would be — the verdict would be `out of reach`, as it is for `alldifferent` §5/§6 and
`gcc`. **Which of those holds is unknown here and is not being scored.** The prediction is
written down so C2 can falsify it in one reading rather than re-derive it.

## Gaps

| gap | what it blocks here |
|---|---|
| `G6` | **the binding one.** 2-D constant table read as a function, `t = T[r,i]`. `Addcst` (l.12) is 1-D; `Rel` (l.10) relates index names only. Without it the same anonymous `t` stands for `T[r',i]` and `T[r,i]`, which is both the unsoundness and the illegibility |
| — | **"row `r` is dead" has no non-circular premise.** The second intended propagation is blocked by the decomposition's own structure, not by a numbered gap. It is what the `F` drop on `X_i ≠ t` is |
| `G7`'s hook, `D2` | shared with G6 as the candidate cheap fix above: constructible, interpreted, unprintable, undefined in meaning, and insufficient for the second value index |
| — (roadmap **W1-T4**) | `TODO`, and explicitly **masked not fixed**. The empty-premise rule returns with G6 unless the decomposition is re-authored to EXT-1/S7 at the same time |
| — (roadmap **W1-T1**) | rule-level binder scope. Not usually filed against `table`, but item 4 of the `D2` reading above lands on it: `element`'s blocker and `table`'s second value index are the same missing thing |

Extensions: **E2** (`CHRISTMAS_LIST.md:158`, ecode parsed by `tools/mzn_coverage.py`).
Roadmap: **W2-T3** (E2, "2-D constant tables", `TODO`) then **W3-T3** (the extensional
family, `TODO`).
Source: `docs/DECOMP_FORMAT_NOTES.md:74`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, output redirected to a file then grepped, per CLAUDE.md)
  → `---- cata/table.tex  (0 rules) ----` at line 326 of the run, **in the per-entry section,
  not in the out-of-scope block** (which lists `among`, `cumulative`, `range`, `regular`,
  `roots` and not `table`). Run totals: **34 rules checked in 11 entries: 13 SOUND and
  MINIMAL, 21 flagged; 2 rules in 5 entries out of scope.** Exit 0.
- `grep -o '\\frac' cata/table.tex | wc -l` → `0`.
- `python3 tools/mzn_coverage.py --rank --json` → `table` in `D literature + solver-native`,
  `ecodes: ['E2']`, `CHRISTMAS_LIST.md` line 158, section
  `5. Extensional — table, regular, MDD`.
- `cata/table.tex` read, not run → the diagnostics footer, quoted in full above.
- `explenation generator.ml` read, not run → `table` at **862-864**, `x3ac` at **875**,
  `explainall` at **893**; `oni` 763, `onr` 766, `i_out` 771, `ontin` 768; the
  `Reified_devent (true, T, id, id)` placeholder at **245-246**; `ind_set` at 6, `Rel` at 10,
  `Addcst` at 12; `fam_ind` at 85; `sum_node`/`prim_node` at 96-97; `apply_op` at 100-108;
  `ind_set_defined` at **459**; `printind_set` at **462-464**; `printioptex`'s `Addcst`
  rendering at 504; `rule3`/`rule4` at **307-341**.
- `CHRISTMAS_LIST.md:158` and `:106-109` read → the two citations, the solver cells, the E2
  routing sentence, the legend.
- `docs/ROADMAP.md:48, 50, 55, 71, 91` read **before reporting** (CLAUDE.md, "Verify before
  you report") → W1-T2 `DONE` with `table 1→0` booked as intended cost; W1-T4 `TODO` and
  **masked, not fixed**; W1-T11 (tier-D calibration targets); W2-T3 and W3-T3 `TODO`.
- `docs/VALIDATOR.md:60, 118-125, 187, 287, 336-343` read → the hand-encoded semantics row,
  the `D_4`-as-row-set latitude, the enumeration sizes, the pre-W1-T2 verdict table, the
  "`D_4` means two different things" note.
- `docs/DECOMP_FORMAT_NOTES.md:74, 75` read → G6 and G7 as consolidated.
- `decomps/table.md` and `decomps/_shapes-ext.md` (EXT-1), `decomps/_shapes.md` (S7) read →
  the intended shape, the free-index diagnosis, the S7 renumbering.
- **The precise statement of G6, and the `D2` assessment, are reasoning over the source,
  labelled as such in place.** Nothing in either was run. In particular items 1-4 of the
  `D2` reading are a code reading and **no `D2` decomposition was written or compiled**.
- **Not fetched, not written:** no paper. No rule shape from any paper appears anywhere in
  this entry.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **Stale generator line numbers, two documents.** `decomps/table.md` cites the shipped
   decomposition at "l.720–722" and `x3ac` at "l.734"; `decomps/_shapes-ext.md` cites
   "generator l.720–722". Measured today: **862-864** and **875**. This is W1-T14.
2. **`docs/VALIDATOR.md:287`'s per-entry table still reads `table | 3 | 3 UNSOUND`.** The
   artifact has held 0 rules since W1-T2. `docs/ROADMAP.md:55` (W1-T11, fourth item) already
   records that table as stale for `allequal`, `nvalues`, `atleastnvalues`, `atmostnvalues`
   and `gcc` — **`table` is a sixth stale row and is not on that list.** Also
   `docs/VALIDATOR.md:60` cites `table`'s ground semantics at generator "l.429–431"; the
   value is at 862-864.
3. **`docs/DECOMP_FORMAT_NOTES.md:40` (G1) cites the empty-`Decomp` reified placeholder at
   "generator line 111".** Measured today: `reified_devent`'s default is at **245-246**;
   line 111 is `op_set`. The gap it states is unaffected — the placeholder is real and is
   what puts `table`'s `X_i \neq t` branch on an `F` leaf — only the citation has rotted.
4. **`CHRISTMAS_LIST.md:158` says the repo "currently emits an unsound empty-premise rule".**
   As of W1-T2 it emits no rule. The underlying defect is still there (W1-T4 is `MASKED, NOT
   FIXED`), so the sentence is right about the decomposition and wrong about the artifact.
5. **Two files state a paper's content with no in-repo source** — `decomps/table.md`'s
   closing sentence and `decomps/_shapes-ext.md`'s EXT-1 "Auxiliaries" paragraph, both about
   McIlree & McCreesh 2023. Flagged UNSOURCED above; they are C2's to source or delete.
