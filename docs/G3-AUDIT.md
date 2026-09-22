# G3 re-audit — the 25 entries that name G3 as their blocker

**Task:** `docs/ROADMAP.md` W1-T20. **Session:** A-2, 2026-09-22. **Branch:** `explanation-catalog`.

**What this file is.** One row per catalog entry that currently carries the string
`blocked on G3`, with a verdict under the factoring test that session X-max produced when
`maximum` turned out to be authorable. It is an audit of *one question* — is G3 the blocker? —
and not a re-specification of any constraint.

**What this file is not.** It is not an authoring result. **Nothing here was run.** A sibling
session owns `explenation generator.ml` and was editing it throughout; this audit is reasoning
from the types, the rule schemas, the printers and the shipped decomposition values, read
today. Every generator line number below was re-checked by `grep -n` against the working copy
at **md5 `5d4045f45e686c784cceebaae5a289a0`**; if the file has moved on, re-check before
quoting. **No `catalog/*.md` and no `decomps/*.md` was edited** — where this audit contradicts
one, it says so by name and leaves the file alone.

**Read vs inferred.** Claims about what a type, schema or printer *is* are read off the source
and cited. Claims about what a decomposition *would* do are inference, and are marked as such.
No verdict below is a soundness claim about any rule, and the word "correct" appears nowhere.

---

## The test

From `docs/DECOMP_FORMAT_NOTES.md:51-61` (G3, sharpened by X-max on 2026-09-22):

> A variable-vs-variable comparison blocks a decomposition **only when it does not factor
> through a shared threshold.**

`m ≥ x_i` factors: `BC` events already *are* the order encoding, so `m ≥ t ⇔ ⋁_i (x_i ≥ t)` has
no var-var atom anywhere. `x_i = y_{p_i}` does not: the obstruction is a variable-valued
*index*, and no single `t` states both sides separately.

## The headline

| verdict | count | entries |
|---|---|---|
| **FACTORS** | **24** | the 13 lex-family entries, `var_perm_sym`, `var_sqr_sym`, `diffn`×4, `maximum`, `minimum`, `span`, `member`, `alternative` |
| **DOES NOT FACTOR** | **0** | — |
| **UNCERTAIN** | **1** | `arg_sort` |

**Of the 25 entries that name G3, none is confirmed to be blocked by G3.** That is a much
larger collapse than W1-T20 anticipated, and it needs the qualification in the next section
before anyone quotes it: *factors* is a claim about the **atom**, not a claim that the entry
can be generated today. Twenty of the twenty-four have a different, real blocker, and four of
them have a blocker this audit believes has never been written down.

**Two entries are counted here only because `grep` found the string.** `catalog/maximum.md:195`
and `catalog/minimum.md:140` contain `nothing generated — blocked on G3` inside a sentence that
*disowns* it. Both constraints ship (`maxi`, `explenation generator.ml:1059`; `minim`, emitted
at `:1178`). They are rows in the table for completeness and are already settled.

### The distinction this audit insists on

> **"Factors" means G3 is not the blocker. It does not mean "authorable today."**

This is the exact error `maximum` made in the other direction — `decomps/maximum.md` reported a
negative result about one encoding as a negative result about the constraint. The symmetric
error would be to report a positive result about one atom as a positive result about the
entry. So every row carries two columns: the G3 verdict, and the blocker that is actually left.

---

## The two shipped precedents that decide most of this

Neither is new work; both are in `cata/` today, and between them they settle the lex family and
`member` without any appeal to `maximum`.

**1. `increasing` is already a variable-vs-variable `≤`, factored through a threshold.**
`incr` (`explenation generator.ml:912-913`) is

```
Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true, (B 1), imoin 1, iplus 1)])
```

— i.e. `B1_{i,t} ⇔ X_i ≥ t`, then the clause `¬B1_{i,t} ∨ B1_{i+1,t}`. Quantified over `t`,
that clause **is** `X_i ≤ X_{i+1}`: a comparison of two decision variables, with no var-var
atom anywhere, joined at `t` by the order encoding. `docs/VALIDATOR.md` records it as 2/2 sound
and minimal. So "`X_i ≤ Y_i` cannot be written" is refuted by a shipped, validated entry, and
has been since 2020 — this is not a consequence of the `maximum` result, it *predates* it.

**2. `element` is already a variable-vs-variable `=`, factored through a threshold.**
`elem` (`:916-920`) reifies three globals — `X` (`:916`), `I` (`:917`), `V` (`:918`) — and joins
them with two `rule4` clauses (`:919-920`) whose signs expand a biconditional. `V` is a decision
variable and `X_I = V` is a var-var equality; it is expressed as `∀i,t: (I = i ∧ V = t) → X_i = t`,
every side a variable against a threshold. This is `decomps/_shapes.md`'s S6, and it also shows
that a variable in *index* position is not by itself fatal — see `arg_sort` below, where it is
the reason the verdict is UNCERTAIN rather than DOES NOT FACTOR.

A third, weaker precedent matters for `diffn`: `cumul` (`:892-894`) carries
`tplusci (C 1)` / `tmoinci (C 1)`, i.e. `OpShiftC` (`:92`), a **constant offset on the value
index**. So `x_i + w_i ≤ x_j` for parameter `w` has a shipped mechanism, not only a plausible
one.

---

## The audit table

`factors?` is the W1-T20 verdict. `real blocker` is what is left once G3 is set aside; **`—`
means this audit found nothing left**, i.e. the entry is authoring work, not engine work.

| # | entry | the comparison | factors? | real blocker |
|---|---|---|---|---|
| 1 | `lex_less` | `X_i ≤ Y_i`, `X_i = Y_i`, two arrays | **FACTORS** (via `increasing`) | **S5 accumulated state** (`tied_i`) + G2 (second array name) |
| 2 | `lex_lesseq` | as 1 | **FACTORS** | as 1 |
| 3 | `lex_greater` | as 1, signs swapped | **FACTORS** | as 1 |
| 4 | `lex_greatereq` | as 1, signs swapped | **FACTORS** | as 1 |
| 5 | `lex2` | `X_{r,i}` vs `X_{r+1,i}` — **one matrix** | **FACTORS** (no second variable exists) | S5 + **two-index literals do not print** (below) |
| 6 | `lex2_strict` | as 5 | **FACTORS** | as 5 |
| 7 | `strict_lex2` | as 5 | **FACTORS** | as 5 |
| 8 | `lex_chain_less` | as 5 | **FACTORS** | as 5 + G7/`D2` (chain length) |
| 9 | `lex_chain_lesseq` | as 5 | **FACTORS** | as 8 |
| 10 | `lex_chain_greater` | as 5 | **FACTORS** | as 8 |
| 11 | `lex_chain_greatereq` | as 5 | **FACTORS** | as 8 |
| 12 | `lex_chain_lesseq_orbitope` | as 5, rows **and** columns | **FACTORS** | as 8 |
| 13 | `lex_chain_greatereq_orbitope` | as 5, rows **and** columns | **FACTORS** | as 8 |
| 14 | `var_perm_sym` | `X_i` vs `X_{σ(i)}`, σ **constant** | **FACTORS** (no second variable) | **no `ind_op` for a data-given permutation** — unnumbered gap + S5 |
| 15 | `var_sqr_sym` | `X_{r,i}` vs `X_{r+1,i}` | **FACTORS** | as 5 + no `ind_op` for the transpose family swap |
| 16 | `diffn` | `s_i + w_i ≤ s_j`, `w` a **parameter** | **FACTORS** (via `OpShiftC`) | **G15** (offset prints `UNPARSED`) + unproven pairwise 4-way clause |
| 17 | `diffn_k` | as 16, k dimensions | **FACTORS** | as 16 + two-index literals do not print |
| 18 | `diffn_nonstrict` | as 16 | **FACTORS** | as 16 |
| 19 | `diffn_nonstrict_k` | as 17 | **FACTORS** | as 17 |
| 20 | `maximum` | `m ≥ x_i` | **FACTORS** — *settled, shipped* | — |
| 21 | `minimum` | `m ≤ x_i` | **FACTORS** — *settled, shipped* | — |
| 22 | `span` | `S = min_i(start_i)`, `E = max_i(end_i)` | **FACTORS** (it **is** `minimum`/`maximum`) | — (G15 only if `end_i` is derived as `start_i + d_i`) |
| 23 | `member` | `X_i = y`, `y` a variable | **FACTORS** (via `element`) | — |
| 24 | `alternative` | `start = start_k` | **FACTORS** either way the signature falls | **the signature**, which nobody here has |
| 25 | `arg_sort` | `x_{p_j} ≤ x_{p_{j+1}}` | **UNCERTAIN** | variable-valued index; see below |

---

## The lex family, worked properly

This is the family W1-T20 said was the one that mattered, and it splits in two — a split no
file in the repo currently makes.

### (a) `lex_less`/`lex_lesseq`/`lex_greater`/`lex_greatereq` — two distinct arrays

`decomps/lex_less.md`'s step 2 says, in full: "`X_i = Y_i` itself → **blocked by
`DECOMP_FORMAT_NOTES.md`'s G3**: `Global_event`/`ind_modifs` express `X_i = t` for a domain
value `t`, never `X_i = Y_i` for two decision variables." The reading of the types is accurate.
The inference is the one `maximum` already refuted, and here it is refuted by an entry that
predates the whole question:

- `tied_i → X_i ≤ Y_i` is `increasing`'s clause (`:913`) with a guard literal added and the
  second `Decomp_devent` pointing at `Y`'s reification instead of `X`'s. The `≤` is not
  represented; it is *derived* from `∀t: (X_i ≥ t) → (Y_i ≥ t)`, exactly as `incr` derives its
  own.
- `X_i = Y_i` is that clause in both directions — `¬B^X_{i,t} ∨ B^Y_{i,t}` and
  `¬B^Y_{i,t} ∨ B^X_{i,t}`. Both signs are free: `Decomp_devent` carries a `bool` (`:97`), and
  `elem` (`:919-920`) and `alleq` (`:887-888`) both use `false` summands in shipped code.

So **the comparison is not the blocker**. What *is* left is two things, and W1-T20 asked which
of the two is real. They are not equally serious.

**The second array is a legibility cost, not a wall.** `printvartex` (`:588-595`) has seven
cases, and exactly two — `X` (`:589`) and `O` (`:595`) — route through `printglobal_eventtex`
(`:584`), which is the only printer that renders an array subscript together with a threshold.
`I`, `V`, `N` (`:592-594`) print `hd (index_list v)` and are scalars. So a second array can be
written today by borrowing `O`, which is precisely what `maximum` did for its scalar bound
(`catalog/maximum.md`'s G2 row). Cost: `Y_i` prints as `O_i`. That is G2, and G2 has never
stopped an entry shipping.

**The accumulated state is the real blocker, and it is worse than the specs say.** `tied_i` is
`decomps/_shapes.md`'s S5, and S5 is the one shape in the corpus with **no instance anywhere in
the generator**: `grep -n -i 'precede\|lex\|tied' 'explenation generator.ml'` returns exactly
one hit, a comment at `:481`. Zero of S5's twelve listed instances have ever been encoded, so
every claim about S5 in this repo — including "E0", which `decomps/lex2.md` and
`decomps/orbitope.md` both assert — is untested. Three mechanisms stand between `tied` and a
printed rule, and each is read off today's source:

1. `printvartex`'s `B` case (`:590`) **raises** `Generator_failure` if any auxiliary reaches the
   printer. It no longer prints `"ERROR B "` — W1-T10 landed. So if `tied_i` survives into a
   premise, the run aborts; it does not degrade.
2. `tied` has no `Global_devent` behind it, so the only way it leaves a premise is by being
   re-expanded through its own defining `rule3` — which is recursive in `i`. `filter_branches`
   (`:695-715`) maps a cycle-cut branch to `BR` and **discards it** (`:702`, `kept` unchanged).
   A recursion that must be cut therefore yields no rule at all, which is how `regular` reached
   zero rules by a different route.
3. If the base case `tied_1 = true` has no constraint standing for it, the descent hits `IM`,
   and `filter_branches` (`:701`) **raises** on `IM`. There is no `Lit T` injection mechanism in
   any shipped decomposition that would supply it.

**Verdict for (a): G3 is not the blocker; S5 is, and S5 is unmeasured.** Both
`decomps/lex_less.md` and `catalog/lex_less.md` name G3 first and the auxiliary second, as a
"same status as `value_precede`'s `b_i`" aside. That ordering is backwards and this audit says
so. The honest status for these four is not `blocked on G3` and not `encodable today` either —
it is *the comparison is expressible, the auxiliary has never been tried*.

### (b) `lex2`, `lex2_strict`, `strict_lex2`, the six `lex_chain*`, `var_sqr_sym` — one matrix

**These nine compare two rows of the same matrix, so there is no second variable and G3 is not
even engaged.** `decomps/lex2.md` applies `lex_lesseq` "to every pair of adjacent rows";
`catalog/var_sqr_sym.md`'s own decomposition block writes the atom as `X_{r,i} = X_{r+1,i}`.
Both sides are the same `Global_devent X` at two index tuples — the `incr` construct with the
shift in the `FR` family (`:82`) instead of `FI`. `decomps/lex2.md` closes with "Still blocked
by G3 (var-vs-var `X_i=Y_i`), same as `lex_less` itself"; `decomps/orbitope.md` and
`decomps/lex_chain.md` inherit that sentence. **All three are contradicted by this audit**, and
not only under the sharpened G3 — the atom they name (`X_i = Y_i`, two arrays) is not the atom
their own decomposition writes.

**But this half has a blocker the four in (a) do not, and this audit believes it is
unrecorded.** A matrix literal `X_{r,i} ≥ t` carries two position indices. In
`printglobal_eventtex` (`:584-587`), `right` is the value index and `left = subi right
(index_list e)` (`:586`) — `subi` (`:300-301`) removes only the value index, so `left` has
**both** position indices. Line 587 then renders it with `printind_name_list`, and
`printind_name_list` (`:553`) is

```
let rec printind_name_list il = match il with []->""|i::tl->printind_name (ind_name i)
```

— `tl` is bound and never used. **It prints the first index and drops the rest, in the LaTeX
path.** There is no `printind_name_listtex`; `grep -n 'printind_name_list'` gives three hits
(`:553`, `:558`, `:587`) and `:587` is the tex printer. So `X_{r,i} ≥ t` would emit
`X_{r} \geq t`, silently losing `i`.

**This contradicts `CLAUDE.md:204` and `docs/ROADMAP.md:59`**, which both state the
`printind_name_list`/`printiopl_list` tail bug affects "the plain-text path only". That is
right for `printiopl_list` — `:587` calls the recursive `printiopl_listtex` — and **wrong for
`printind_name_list`**, which has no tex sibling and is called directly by the tex printer. The
reason it has never shown up is stated, unknowingly, in `catalog/var_sqr_sym.md`: "**no
generated artifact has ever contained an `r` index**", because `table` — the only shipped
decomposition with two position indices (`x3ac`, `:1098`) — has held 0 rules since W1-T2. The
first matrix entry to generate anything will hit it. It deserves its own roadmap row; this
audit does not own `docs/ROADMAP.md` and has not added one.

`var_perm_sym` (row 14) is in this half by structure but has its own obstruction: `σ` is
*instance data*, so the atom is two cells of one array and factors trivially, but no `ind_op`
(`:83-93`) applies a data-given permutation to an index. `catalog/var_perm_sym.md` already says
this and already says no gap number covers it. This audit agrees and adds only that the G3
attribution beside it is wrong.

---

## `diffn` — does a constant offset factor?

**Yes, and the mechanism is shipped.** `x_i + w_i ≤ x_j` for `w` a parameter is, for each `t`,
`x_i ≥ t → x_j ≥ t + w_i`: both sides are `BC` literals on the same array, related by a
constant offset **on the value index**. `OpShiftC` (`:92`) is exactly that —
`OpShiftC of ind_fam * ind_symbols * ind_const * ind_fam`, "`t' = t +/- c_i`" — and `cumul`
(`:892-894`) uses it in shipped code as `tplusci (C 1)` / `tmoinci (C 1)`. `invert_op`
(`:210-211`) inverts it. So the atom `s_i + w_i ≤ s_j` is `increasing`'s clause with a shifted
value index, and `catalog/diffn.md`'s "G3 — `diffn`'s non-overlap disjunction is exactly this
wall" is **contradicted**: the wall is elsewhere.

Two things are left, and neither is G3:

- **G15.** `print_op` (`:182`) renders `OpShiftC` as `t'=t-d_i`, and `docs/VALIDATOR.md:330`
  measures the consequence on the one shipped instance: `UNPARSED: index equation offset:
  t'=t-d_{i}`. So `diffn` would generate rules the validator cannot read. That is a real cost
  and it is the reason to hesitate, but "unvalidatable" is a different status from "blocked".
- **The 4-way pairwise clause is unproven.** Non-overlap is a `rule4` over four disjuncts
  relating boxes `i` and `j` — two indices of the same family, which `OpSum`/`OpPrim`
  (`:89-90`, the "primed sibling constrained to differ" ops) supply. Inference, not measured: no shipped decomposition
  puts four `Decomp_devent`s in one `rule4`, and `rule4`'s multi-summand branches (`:388-399`)
  have only ever been exercised by `elem`'s three.

`diffn_k` and `diffn_nonstrict_k` add the k-dimension and therefore also hit the two-index
printing defect above. `CHRISTMAS_LIST.md:177`'s route cell for `diffn` reads `E2 … reachable
once E2 lands`; on this evidence the atom needs no extension, and the routing should be
re-examined the way `catalog/maximum.md` asks for its own E2 row. Not edited; reported.

---

## `span`, `member`, `alternative`

**`span` — FACTORS, and it is now the cheapest entry in the audit.** `decomps/_shapes.md`'s
"Contradictions between sessions" §1 resolved a disagreement by ruling that "`span` has no
shape and is blocked by G3, exactly as `maximum` is", and `catalog/span.md` adopted that
resolution. **The premise has since been refuted and the conclusion inherits the refutation.**
`span`'s halves are `minimum` and `maximum`, both of which ship (`minim` at `:1178`, `maxi` at
`:1059`); `S = min_i(start_i)` is `minim` with `X` the start array and `O` the span start. The
only residue is whether `end_i` arrives as its own variable array (then nothing is left) or as
`start_i + d_i` (then `OpShiftC` and G15, as for `diffn`). `decomps/_shapes.md`'s "Not covered
by any shape" table lists all five of `maximum`, `minimum`, `arg_max`, `arg_min`, `span` against
G3; `catalog/maximum.md` already reported the first, and this audit reports that **the table is
now wrong in all five rows** — `arg_max`/`arg_min` are outside the 25 and were not audited, but
they are named there on the same refuted premise.

**`member` — FACTORS, and the var-target reading is *cheaper* than the parameter reading.**
`catalog/member.md` gives `member` two statuses: `encodable today, not encoded` for `y` a
parameter, and `nothing generated — blocked on G3` for MiniZinc's var-target signature. The
second is contradicted. With `y` a variable, `∃i: X_i = y` factors as `∀t: (y = t) → ⋁_i (X_i = t)`,
and every piece is shipped:

- `y = t ⇔ B3_t` is `rule1` on a scalar, which is `elem`'s `V` channel (`:918`) with the seed
  `v = Global_event (true, V, [Ind (T 1, [])], AC)` (`:1096`);
- `B2_t ⇔ ⋁_i B1_{i,t}` is `maxi`'s constraint 2 (`:1060`) with `AC` for `BC` — the same step
  `nvalues` uses (`:923`);
- the link `¬B3_t ∨ B2_t` is a two-literal `rule4`, the degenerate form `alleq` closes with
  (`:889`).

So the var-target `member` is `maxi`'s shape with an `AC` reification and a `V` channel. That is
an authoring job of about four lines and no new machinery — the same claim `catalog/member.md`
already makes for the *parameter* reading, now extending to the reading it called blocked. It
is inference: nothing was run, and the entry's own caveat that the `var int: y` signature is
recall still stands.

**`alternative` — FACTORS whichever way the signature falls, so G3 is not what is unresolved.**
`catalog/alternative.md` makes its G3 status conditional on whether an option's start and
duration are parameters or variables. If parameters, there is no var-var atom at all and the
entry says so. If variables, `start = start_k` factors through `t` exactly as `member` does, by
`element`'s channel. If the option index `k` is itself a decision variable, that is `element`'s
`I` channel (`:917`), which is shipped. **In all three readings G3 is not the blocker.** What is
genuinely unresolved is the signature, which no file in this checkout carries and which
`decomps/alternative.md` calls a placeholder. The entry's hedge is right; its attribution is not.

---

## `arg_sort` — UNCERTAIN, and the single check that settles it

`arg_sort`'s sortedness obligation is `x_{p_j} ≤ x_{p_{j+1}}`. The sharpened G3 names
`x_i = y_{p_i}` as the canonical non-factoring case, so the reflex answer is DOES NOT FACTOR.
**This audit does not make that call**, for a reason `catalog/arg_sort.md` half-states already:
`element` ships a variable in index position and handles it by channelling, `∀i,t: (I = i ∧ V = t)
→ X_i = t`. The same move for `arg_sort` is `∀j,p,t: (P_j = p ∧ X_p ≥ t) → Y_j ≥ t`, which has
no var-var atom either. Whether that is writable turns on one thing.

> **The check:** can a `Global_devent` for the permutation array carry a value index that
> ranges over *positions*? `printglobal_eventtex` (`:585`) selects the value index as
> `hd (isppp (index_list e) @ isttt (index_list e))` — the first `P`-family index, else the
> first `T`-family one. A literal `P_j = i` wants its value in the `I` family, and there is no
> case for that; `hd` on an empty list is `Failure "hd"`, the W1-T17 defect class. Relabelling
> the permutation's values into the `FP` family avoids it on paper. Writing that one channel
> and seeing whether it prints settles `arg_sort` either way, and it is half a day's work.

Two further notes. `arg_sort` needs three index families (`FI`, `FP`, `FT`) out of the four at
`:82`, so G16 is not reached. And `catalog/arg_sort.md` is **not** in fact an entry that claims
G3 — its `blocked on G3` hit is in a sentence correcting a task brief, and it files the
constraint under G9/G10 per `decomps/_shapes.md`'s S6. This audit agrees with that filing and
adds only that G9/G10 should be re-audited on the same evidence, since `element` is a shipped
counterexample to the widest reading of both.

---

## What survives as genuinely G3-blocked

**Zero of the twenty-five, with one open.** `arg_sort` is the only entry whose G3 status this
audit could not settle, and the repo does not attribute it to G3 anyway.

The sharpened G3 in `docs/DECOMP_FORMAT_NOTES.md:59-60` names its honest blocked set as
"`sort` / `arg_sort` / `symmetric_all_different`". Of those, **only `arg_sort` carries the
string, and only to disown it.** So after this audit G3's blocked set and G3's *claimants* are
disjoint, which is the shape of a gap that should probably be retired in favour of G8/G10 —
a call for whoever owns `docs/DECOMP_FORMAT_NOTES.md`, not for this file.

**Where the work actually is**, from the `real blocker` column:

| blocker | entries | status |
|---|---|---|
| **S5 accumulated state** | 15 (the whole lex family + both `var_*_sym`) | **never once instantiated in the generator.** The largest untested claim in the corpus |
| two-index literals print only the first index | 9 matrix entries + `diffn_k`, `diffn_nonstrict_k` | **believed unrecorded**; `CLAUDE.md:204` and `ROADMAP:59` say plain-text only, and `:587` says otherwise |
| G15 (`OpShiftC` prints `UNPARSED`) | `diffn`×4, `span` conditionally | recorded, measured at `docs/VALIDATOR.md:330` |
| no `ind_op` for a data-given permutation | `var_perm_sym`, `var_sqr_sym` (transpose) | recorded in `catalog/var_perm_sym.md`, **no gap number** |
| signature unknown | `alternative` | recorded |
| **nothing** | `maximum`, `minimum` (shipped), `member`, `span` | **authoring work, available now** |

## Specs and entries this audit contradicts, by name

1. **`decomps/lex_less.md`**, step 2 — "`X_i = Y_i` → blocked by G3". The comparison factors;
   `increasing` (`:912-913`) is the shipped counterexample. `decomps/lex_lesseq.md` inherits it.
2. **`decomps/lex2.md`** — "Still blocked by G3 (var-vs-var `X_i=Y_i`)". `lex2` compares two
   rows of **one** matrix; there is no second array and no var-var atom in the sense named.
3. **`decomps/orbitope.md`** — "same G3 blocker as `lex_less`". As 2.
4. **`decomps/lex_chain.md`** — inherits 2 via `lex2`. (Its `D2` claim was already corrected in
   its own header; the G3 inheritance was not.)
5. **`catalog/span.md`**, Decomposition §1 — "`S = min_i(start_i)` compares two decision
   variables … G3". The premise it cites, `decomps/maximum.md`'s "missing primitive", is
   retracted; `minimum` ships.
6. **`decomps/_shapes.md`**, "Not covered by any shape" — all five rows rest on the retracted
   premise, and `span`'s is reached through "Contradictions between sessions" §1, whose
   *conclusion* was right about Shape D and wrong about G3.
7. **`catalog/member.md`** — the var-target status. It factors through `element`'s channel.
8. **`catalog/diffn.md`**, Scope — "The concrete blocker in this generator is G3". The blocker
   is G15 plus an unproven clause arrangement; `OpShiftC` exists and ships in `cumul`.
9. **`catalog/alternative.md`** — G3 is not the conditional; the signature is.
10. **`CLAUDE.md:204` and `docs/ROADMAP.md:59`** — the `printind_name_list` tail bug is **not**
    plain-text only. `:587`, the LaTeX printer, calls the non-recursing `:553`.
11. **`CHRISTMAS_LIST.md:177`** routes `diffn` through E2; on this evidence the atom is E0, the
    same re-examination `catalog/maximum.md` asks for its own row.

Items 1–9 are `catalog/` and `decomps/` files this session was told not to edit, and did not.
Items 10–11 are outside its ownership too. All eleven are reported, not fixed.

## How this audit was produced

- `grep -l 'blocked on G3' catalog/*.md` → 25 files; then `grep -n` per file to read the
  context of each hit, which is how `maximum`, `minimum` and `arg_sort` were identified as
  string matches inside retractions or corrections rather than live claims.
- `explenation generator.ml` read at md5 `5d4045f45e686c784cceebaae5a289a0`, **not run and not
  edited**: types `:3`, `:5`, `:82`, `:83-93`, `:94-97`; schemas `rule1` `:357`, `rule3` `:366`,
  `rule4` `:384`; printers `:300-301`, `:553`, `:584-595`; `filter_branches` `:695-715`;
  decompositions `:886-953` and `:1059`; seeds `:1091-1106`; `explainall` calls `:1110-1178`.
  Every line number re-checked by `grep -n` after the last read, per W1-T14.
- `docs/DECOMP_FORMAT_NOTES.md:51-68` and `:115-117` read → the sharpened G3 and the
  "reinforced by three families" note.
- `decomps/_shapes.md` read → S5's instance list, the "Not covered by any shape" table, the
  contradictions section.
- `decomps/{lex_less,lex_lesseq,lex2,orbitope,lex_chain}.md` read in full;
  `catalog/{maximum,diffn,member,alternative,span,var_perm_sym,var_sqr_sym,arg_sort}.md` read
  in the Constraint / Decomposition / Scope / Gaps sections.
- `docs/VALIDATOR.md:330` read → the measured `UNPARSED` for `OpShiftC`.
- **Nothing was executed.** No `make check`, no `make validate`, no generator run. Every
  soundness figure quoted above is quoted from the file that measured it, with that file named.
