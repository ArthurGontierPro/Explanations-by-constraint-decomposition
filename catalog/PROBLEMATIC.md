# Problematic constraints — the register

> **This is a register of where *this method* has trouble, grouped by **kind of trouble**, not
> by constraint family. Nothing here says a constraint is hard in general.** Several of the
> constraints below have excellent published explanations; what is recorded is that a rule
> schema derived from a static decomposition cannot reach them. Where that distinction
> matters, the entry says so in its own words.

**Nothing in this file was re-derived or re-measured.** Every number is carried from the file
that measured it, and that file is cited beside it. Where a source says "reasoning, not
measurement", the tag travels with the claim. Written 2026-09-21 (session S-C) from
`catalog/*.md` (the 15 written entries), `catalog/_literature/*.md`,
`docs/DECOMP_FORMAT_NOTES.md`, `docs/ROADMAP.md`, `docs/DECISIONS.md` and `WORKLOG.md`.

**Vocabulary.** `catalog/README.md`'s status legend and `docs/VALIDATOR.md`'s verdict
vocabulary apply unchanged. A rule is never "correct". `SOUND and MINIMAL` is a floor, not
strength, and three of the seven categories below exist precisely because the floor is not
the ceiling.

---

## The seven categories, and what each touches

| # | kind of trouble | constraints touched | worst case |
|---|---|---:|---|
| **P1** | **Structurally out of reach** — the published premise is indexed by a run-time object | **3 of 3** sourced; ~8 more predicted | no fix exists; E4 is necessary but not sufficient |
| **P2** | **Blocked on a named format gap** (G1–G18) | **34 of 118** globals route through E2 alone; **5 of 16** shipped entries emit zero rules today | `among`, `range`, `regular`, `roots`, `table` — 0 rules each |
| **P3** | **Generates rules that cannot fire** | 6 entries; **13 of 34** validated rules `VACUOUS`, +1 dead-but-unflagged | `nvalue` — no rule that both fires and is sound |
| **P4** | **Generates rules that say nothing** | 3 entries, 4 rules | `all_equal` — premise literal *is* conclusion literal |
| **P5** | **Encoded twice, indistinguishably** | 2 constraints, 8 rules, 1 byte-identical file | `atleast_nvalue` ≡ `atmost_nvalue` |
| **P6** | **Out of scope by decision** | **35 of 118** globals | nothing; decided, and cheap |
| **P7** | **Not a MiniZinc global at all** | 3 of the 15 written entries | `sum` — orphan, no producer in `main` |

Categories overlap on purpose: `nvalue` appears in P3, `atmost_nvalue` in P3 and P5, `regular`
in P1 (predicted) and P2. The axis is the *kind of trouble*, and one constraint can have more
than one.

**Ranked by consequence, the order is P2 > P3/P4 (one shared root cause) > P1 > P5 > P7 > P6.**
The ranking is argued in "Blast radius" at the end.

---

## P1 — Structurally out of reach

**The defining property:** the published explanation quantifies its premises over an object
that exists only at propagation time — a Hall set, a strongly connected component, a flow cut,
a compulsory-part set. This method emits a *schema* over declared index sets. There is no
index-set expression for the output of Tarjan's algorithm, so **no implication comparison in
either direction is statable**, which is why `catalog/README.md` makes `out of reach` a
first-class calibration verdict rather than scoring it as `weaker`.

**This is the category that bounds the method**, and it is the one where the "hard for this
method, not hard in general" distinction has to be made loudest: every constraint below has a
published, implemented, explaining propagator. What is out of reach is the *derivation of its
rule from a decomposition*, not the rule.

### P1.1 — `all_different`, §5 (Hall interval) and §6 (SCC)

| | |
|---|---|
| **Evidence** | `catalog/_literature/alldifferent.md`, rules 2 and 3 — both classified **per-propagation**, `QUOTED` from Downing, Feydy, Stuckey, *Explaining alldifferent*, ACSC 2012. §5's `H` comes from a union-find sweep; §6's `H`, `V` are node sets of an SCC of the residual graph of a bipartite matching |
| | `catalog/alldifferent.md`, Calibration: "Both quantify their premises over an object that exists only at propagation time … The printer quantifies over declared index sets and has no expression for either" |
| **What it would take** | **Nothing on the gap list.** `catalog/alldifferent.md` and `catalog/_literature/gcc.md` independently reach the same conclusion: **E4 is necessary but not sufficient.** Counting across sums supplies the counting argument; it does not supply a run-time set to quantify over |
| **Scoped?** | **W4-T2**, `TODO` — and scoped as an *experiment whose expected result is a clean negative*, not as a fix. The roadmap row says so in those words |
| **Near miss worth keeping** | §7, the Feydy–Stuckey decomposition, *is* reachable in principle: it needs **E1** (integer auxiliaries `c[i]`, `s[i]`) **plus E4**. Even reaching §7 would not reach §5 — the paper states §7's reach as value consistency plus Hall intervals aligned to the ends of `min(E)..max(E)` (`QUOTED`) |

### P1.2 — `global_cardinality`, the flow-cut rule

| | |
|---|---|
| **Evidence** | `catalog/_literature/gcc.md`: **there is no `gcc`-specific explanation rule in the paper.** `gcc` is encoded as a flow network and the *generic* propagator is explained. Cut `C` is "the set of nodes searched for an augmenting path" (Ford-Fulkerson) or an SCC of the residual graph (Tarjan). `QUOTED` |
| | `catalog/gcc.md`, Calibration, gives three independently fatal obstacles: no index-set expression for "the arcs crossing `C`"; premise *polarity* depends on arc direction in a graph that flips arcs as flows hit bounds; and the rule is an explanation *of an explanation* (equation (2) synthesised per propagation, then explained as a linear constraint) |
| **What it would take** | Same answer, same wording: E4 necessary, not sufficient. `catalog/_literature/gcc.md` calls it "a negative result worth recording rather than a gap to close" |
| **Scoped?** | **No row.** W4-T2 is `alldifferent`'s; there is no `gcc` equivalent |
| **Not a vocabulary gap** | `catalog/gcc.md` is careful about this and it should not be flattened: this entry *does* carry occurrence atoms `O_t ≥ p`, and the published worked instance's premises (`[x3 ≠ 4] ∧ [c2 ≤ 1] ∧ [c3 ≤ 1]`) are exactly of that kind. **What is out of reach is the quantification, not the literals** |

### P1.3 — `cumulative`, the *global* time-table rule (§6.1, §6.2)

| | |
|---|---|
| **Evidence** | `catalog/_literature/cumulative.md`: B4 pointwise is the one the paper uses, and its `B` is "the set of tasks with a compulsory part at `t`" — a run-time predicate on current bounds. The profile sequence `[D1..Dp]` and the chosen time points `[t1..tm]` are likewise computed at propagation time. `QUOTED` |
| **What it would take** | For the *global* rule: E4 on top of everything else, and then the run-time set problem remains. **But this constraint splits, and the split is the best news in the catalog** — see P2.5 |
| **Scoped?** | **W4-T3**, `TODO`, promoted 2026-09-21 as "the better target of the two, by a distance" |

### P1.4 — predicted, not sourced: the decision-diagram family

`catalog/regular.md`, Calibration, records a **prior and labels it as one**: both papers cited
for `regular` (Gange, Stuckey, Szymanek 2011; McIlree & McCreesh, CP 2023) explain a
decision-diagram propagator, "whose premises are indexed by nodes, edges or layers of an MDD
built for the instance. That is the same kind of object as the Hall sets and flow cuts." The
predicted verdict is `out of reach` even after G7 lands.

**Neither paper has been sourced.** `catalog/_literature/` holds three files only. This
prediction touches `regular`, `regular_nfa`, `regular_regexp`, `mdd`, `mdd_nondet`, `cost_mdd`,
`cost_regular` and `table` — **8 globals, all tier C or D** — and is written down so the next
session can falsify it cheaply rather than re-derive it. **Scoped?** C2-shaped sourcing work;
no roadmap ID.

### The P1 headline

**All three constraints for which this repo has sourced a published explanation have at least
one published rule that is out of reach.** Three of three. That is the measured bound on the
method, and it is why `out of reach` had to become a verdict.

---

## P2 — Blocked on a named format gap

`docs/DECOMP_FORMAT_NOTES.md` carries the consolidated wave-two numbering, G1–G18. This
section lists the gaps that are *biting now* — the ones that cost a shipped entry its rules or
block a constraint from having a decomposition at all. The gap list converged before the
corpus ran out (§11, the last family, produced exactly one new gap, G18), which is itself the
useful result.

### P2.1 — Five shipped entries emit zero rules (G6, G7, G8)

W1-T2 made the generator **refuse** to state a rule over an index set the artifact never
defines, rather than print an undefined `D_k`. `docs/ROADMAP.md:48` books the cost as intended:

| entry | rules before → after | blocking gap | what `D_k` actually is |
|---|---|---|---|
| `among` | 2 → **0** | **G8** | `D_4` is the constraint's own parameter set `v` — a named value subset (`catalog/among.md`) |
| `range` | 3 → **0** | **G8** | `D_5`, `D_6` — named value subsets, the sets "eliminated by hand" per `docs/GCCAT.md:143-146` (`catalog/range.md`) |
| `roots` | 4 → **0** | **G8** | same; four candidates, four refusals, zero `F` — "the cleanest case" (`catalog/roots.md`) |
| `regular` | 2 → **0** | **G7** | `D_8`, `D_9` are the transition relation — a value set indexed by another index (`catalog/regular.md`) |
| `table` | 1 → **0** | **G6** | 2-D constant table read as a function, `t = T[r,i]`; `Addcst` is 1-D. No `catalog/table.md` exists yet |

**The orchestrator's brief was overruled here and the correction stands** (`WORKLOG.md`, E1
handoff): `among`/`range`/`roots` are **G8**, not G6/G7 — their sets are named value subsets,
not sets indexed by another index. Only `regular` is G7.

**What it would take.** Not a printer patch. `explenation generator.ml:440-446` states why: the
`D_k` counter is chosen *per decomposition*, so `D_4` is the row set in `table.tex` and the
value set in `among.tex`; one printer definition would name two different sets alike. Naming
sets properly is a property of the input format → **W2-T1 / E2**.

**Scoped?** **W2-T1** (`TODO`, its input complete) and **W2-T3 / E2** (`TODO`). `table`'s
route is additionally **W1-T4**, which is **`MASKED, NOT FIXED`** — the unsound empty-premise
rule is gone only because the whole branch was refused; the decomposition that produced it is
untouched and will produce it again the moment G6 lands.

### P2.2 — The `D2` printer emits the literal string `"setfils"`

`ind_set`'s `D2 of ind_name list` is the right hook for G7 and **is used by nothing**;
`printind_set` (`explenation generator.ml:375`) prints `"setfils"` and would put garbage into
the `.tex` if used. W2-B and W2-C found this independently, and it **withdrew a checked
negative**: `docs/DECOMP_FORMAT_NOTES.md:96-104` retracts W2-A's "variable-length chains are
fine" and routes `lex_chain_*`, `value_precede_chain` and `seq_precede_chain` to the same
missing printer.

**Touches:** G7's whole route plus 3+ chain constraints. **Scoped?** **No row.** It appears
only as one of "two things the freeze must settle that are not gaps" under W2-T1.

### P2.3 — Gaps with no shipped entry yet, by constraint

Read off `docs/DECOMP_FORMAT_NOTES.md`'s table; every gap names the constraint that hit it.

| gap | blocks | scoped? |
|---|---|---|
| **G1** | every counting constraint's own threshold: `at_least`, `at_most`, `exactly`, `count`, and the capacity `b` in `cumulative`. `alldifferent`'s implicit "at most 1" already never prints | W2-T1 |
| **G2** | `count`'s `c`, `range`/`roots`' `S`/`T`, `sum`'s total — `var_name` is a closed variant and every constraint borrows another's letter | **W2-T2 / E1**, `TODO` |
| **G3** | `maximum`, `minimum`, `arg_max`, `arg_min`, `lex_less`, plus `count`/`among` in their general MiniZinc signatures. **Three independent families make it load-bearing** (`docs/DECOMP_FORMAT_NOTES.md`) | W2-T3 / E2 |
| **G4** | `failwith "sommes multiples pas encore implémentés"` — one Boolean-sum family per rule. Blocks `global_cardinality`'s per-value sums | **W3-T4 / E3**, `TODO` |
| **G5** | not a format gap — a **decomposition-authoring mistake** in the shipped `among`: it uses the single-`Decomp_devent` shape for its own count variable where `nvalues` shows the correct two-step `N`-channel. Fixable today with no engine change | no row |
| **G9** | `inverse`, `sort`, `arg_sort` — no `Global ⇔ Global` channel, so each re-derives `element`'s five-`Decomp` detour | W2-T1 |
| **G10** | `symmetric_all_different`, `sort` — no variable in index position, `X_{X_i}` | W2-T1 |
| **G11** | `cumulative` (the weights), `knapsack`, `bin_packing*` — no weighted Boolean sum (**E8** under D-0011) | W2-T1 |
| **G12/G13** | `sliding_sum`, `sum_pred` — no schema sums integer *values*; **a fourth kind of schema, not a generalisation** (**E9** under D-0011) | W2-T1 |
| **G14** | `cumulatives`; and `range`/`roots` *proper*, because a set variable determines the sum's extent | W2-T1 |
| **G15** | `cumulative` with variable durations, `cost_regular`. **This is the measured** `UNPARSED: t'=t-d_i` | W2-T1 |
| **G16** | general `regular` — `ind_fam` is a closed 4-element enum and EXT-2b alone needs `i, t, q, q'`. `edit_distance` hits it independently, from two *position* families | W2-T1 |
| **G17** | every shape with a genuine auxiliary — no pivot-elimination pass, so an auxiliary cannot be removed from a finished rule. **This is *why* D-0004 costs coverage rather than only rule length** | W2-T1 |
| **G18** | `write`, `writes`, `writes_seq` — quantification over an index set with a *variable-determined exclusion*, `∀j ≠ I` for `I` a decision variable | **no row.** Added last, in the §11 addendum |

### P2.4 — Two entries whose decomposition cannot be matched to its name

**`range` and `roots` are the register's most uncomfortable finding**, because the gap is not
the binding problem. `catalog/range.md` and `catalog/roots.md` each give four reasons, and
none of them is a printer issue: neither set variable has a channel; both sums are restricted
on the *value* family when `roots`'s `i ∈ S` is a predicate on an *index*; neither sum's
threshold reaches the page (G1); and `D_5`/`D_6` are parameters, so the shipped object is a
parameterised special case.

> `catalog/roots.md`: "restoring the four pre-W1-T2 rules would produce four checkable
> statements about something, and nobody can currently say about what."

`docs/VALIDATOR.md:335-338` puts the same judgement in general terms. **Three separate sessions
have now read these two values and none could make them mean what the filename says**
(`decomps/_shapes.md:355-365` withdrew `span`'s "reusing `range`/`roots`" claim on the same
evidence).

**What it would take:** for the *artifact*, G8. For the *constraints*, **E5** (set → Boolean
channelling, `docs/DECISIONS.md:122`) + **G14** + **G2**. And before either, somebody has to
write `decomps/range.md` and `decomps/roots.md` — **the only two shipped decompositions in the
repo with no spec at all, and they are exactly the two that cannot be identified.**
**Scoped?** W2-T5 closed without them; **no row**.

### P2.5 — `cumulative`: the one entry where the gaps are the whole distance

**`cata/cumulative.tex` is really `disjunctive`.** `catalog/cumulative.md` leads with it: the
final step is a single *unweighted* Boolean sum with an implicit bound of 1 (`rule5`,
`explenation generator.ml:812`); there are no resource requirements and no capacity anywhere.
"The file name is the only thing in the artifact that says `cumulative`." It is filed here as
the catalog's most misleading artifact, and a future `catalog/disjunctive.md` should cite it
rather than re-render the same `.tex`.

And then the good news, which is the strongest positive statement anywhere in this repo:

> Schutt et al.'s own **TimeD** decomposition (§5.1) is `rule1` → `rule3` → `rule5` over
> exactly this generator's pair of auxiliaries, and the paper states (`QUOTED`, §6.2) that
> "the global cumulative using time-table filtering and the TimeD decomposition have the same
> propagation strength."

The shipped `cumul` chain is **TimeD at `r_i = 1`, `c = 1`** (`catalog/cumulative.md`, C3's
reading of two texts side by side, labelled as such). What separates the artifact from TimeD is
exactly **two gaps**: **G11** (the sum is unweighted) and **G15** (`t − d_i` is arithmetic on a
variable's value, which the validator reports mechanically as
`UNPARSED: index equation offset: t'=t-d_{i}`).

**So this constraint has two routes with two different blockers, and they must not be merged.**
The *global* §6.2 rule is structurally out of reach (P1.3, needs E4 and then still fails). The
*decomposition* route is two numbered gaps away from a shape whose propagation strength the
paper equates with the global propagator's. `catalog/cumulative.md` flags this as a correction
to `decomps/cumulative.md`, which says "E4 makes it good" — on the sourced evidence, **it is
not established that this method needs E4 to be good at `cumulative`.**
**Scoped?** W4-T3 (`TODO`) for the experiment; G11/G15 under W2-T1.

---

## P3 — Generates rules that cannot fire

**Measured, `make validate` 2026-09-21** (quoted identically by every entry): *34 rules checked
in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope.*

Of the 21 flagged: **13 `VACUOUS`**, 3 `UNSOUND(firing)`, 4 `SOUND but NOT MINIMAL`,
1 `AMBIGUOUS`. So **13 of 34 validated rules can never fire**, and a 14th — `alldifferent`'s —
is dead and escapes the flag.

### P3.1 — `element`: 4 of 6 `VACUOUS`, and the working half is the half nobody needs

| | |
|---|---|
| **Evidence** | `catalog/element.md`. Rules 1–2 `SOUND and MINIMAL`; rules 3–6 `VACUOUS`, each annotated `(premises never hold)`. `I = i` emits **no rule at all** — both candidates blocked |
| **Diagnosis** | `Decomp 4` composes `foralli` onto the **`V`** channel and `forallt` onto the **`I`** channel. `V` and `I` are *scalars* needing no binder; each got the other variable's quantifier. The premises print `∀t: V = t` and `∀i: I = i`, which no store satisfies |
| **What it would take** | **Not the obvious fix — that has been tried.** W3-S attempted the two principled remedies and **both made the verdict worse, 4 `VACUOUS` → 4 `UNSOUND`**, then stopped; `docs/ROADMAP.md:47` records that as the right call. The correct rule needs **one binder scoping both premises jointly** (`∃t. V = t ∧ X_i ≠ t`), and the printer scopes per literal while `validator.ml:333-336` binds such an index as a per-literal `∃`. No parser change rescues it |
| **Scoped?** | **W1-T1**, `TODO`, promoted — "once binders have scope the fix is two tokens in `elem`'s `Decomp 4`" |
| **The sting** | `catalog/element.md`: "the working half of `element` is the half a solver needs least … The pruning a solver actually wants — narrowing `I` from the array, or `V` from `I` — is exactly the part that is `VACUOUS` or absent" |
| **A `CLAUDE.md` claim this refutes** | `CLAUDE.md`'s Traps prices `element`'s missing `I=i` at **E4** by analogy with `alldifferent`. Measured: `elem` (l.834-838) is `rule1`×3 + `rule4`×2 with **no Boolean sum anywhere**, so "counting across sums" cannot be its route |

### P3.2 — `nvalue`: no rule that both fires and is sound

The weakest rule-bearing entry in the catalog, and it is worth stating flatly.

| | |
|---|---|
| **Evidence** | `catalog/nvalues.md`: 0 `SOUND and MINIMAL`; 4 `VACUOUS`, 1 `UNSOUND` of the firing kind, counterexample `n=2 m=2 X=(1,2) N=2 [nvalue] p=2`. Three of the five also carry the generator's D-0009 flag |
| **What it would take** | Unknown, and the entry says so. `CHRISTMAS_LIST.md:130` and `docs/ROADMAP.md:47` both say index hygiene (W1-T1); **nobody has run the experiment.** The near relative `gccn` — same three-layer shape, 4/4 `SOUND and MINIMAL` — needed a change to the *ascending operator* (`forallp` → `pointp`), not to binder names. `nvalues` step 4 still carries `forallp`. Recorded in the entry as "the obvious next experiment, not a diagnosis" |
| **Scoped?** | W1-T1 covers the binder half. The `pointp` transplant has **no row** |
| **Also** | `rule7` is the one schema the original author marked doubtful — `(*incohérent?*)` on both arms, generator l.377-378. `nvalues` is one of only two decompositions using it (the other is `among`, which emits nothing) |

### P3.3 — `atleast_nvalue` / `atmost_nvalue`: 0 of 4 sound each

Both entries: `1 NOT MINIMAL, 1 UNSOUND, 1 AMBIGUOUS, 1 VACUOUS` (at-least) and
`1 NOT MINIMAL, 1 UNSOUND, 2 VACUOUS` (at-most). See also P5, which is the same two files.

- **Rule 1 fires and is constraint-independent.** Drop the two droppable premises and what
  remains is `∀t' ≠ t: X_i ≠ t' ⊢ X_i = t` — **domain exhaustion**, sound for *any* constraint
  over `[1,m]`. `catalog/atleastnvalues.md`: "the `NOT MINIMAL` flag understates the problem".
- **Rule 3 bounds `N` from the wrong side**, and **gccat predicted it without running
  anything**: `atleast_nvalue` is monotone with `NVAL` decreasable, so `X` literals can only
  tighten `N`'s *upper* bound, and the rule concludes a lower one (`docs/GCCAT.md:126-128`).
- **A heuristic refined, not applied blindly** (`WORKLOG.md`, E2 handoff): rule 1's `∀i' ≠ i`
  premise *does* fire, because its polarity is `X_{i'} ≠ t`, where `alldifferent`'s is
  `X_{i'} = t`. **The `∀i' ≠ i` shape is not dead by itself; the polarity decides.**

### P3.4 — `alldifferent`: sound, minimal, and dead for every `n ≥ 3`

**The clearest example in the repo of the floor/strength distinction**, and the one the
validator cannot see.

| | |
|---|---|
| **Evidence** | `catalog/alldifferent.md`. The single rule's premise is `∀i' ≠ i: X_{i'} = t` — *every* other variable takes `t`, which **contradicts `alldifferent` itself** as soon as `n ≥ 3`. Verdict: `SOUND and MINIMAL`. It escapes `VACUOUS` because that flag asks whether *any* store in the enumerated scope satisfies the premises, and `n = 2` is in scope |
| **Calibration** | **strictly weaker than published** (Downing §4, `[x_h = v] → [x_i ≠ v]`, a *single* literal) for every `n ≥ 3`; coincident at `n = 2`. Settled at every arity, not sampled |
| **What it would take** | The strictly stronger `∃i' ≠ i: X_{i'} = t` is also sound, **and the validator cannot prefer it, because minimality is premise-droppability, not strength.** Nothing in the method generates or ranks by strength |
| **Scoped?** | **No row.** W3-T5 *compares* against a published rule; nothing *produces* the stronger one. This is the most important unscoped item in the register — see the closing list |
| **Correction already in the record** | An earlier `CLAUDE.md` said this entry "has one rule where it should have two". It should have one: `alldiff` is `rule1` + `rule5` alone and `X_i = t` is not derivable from a `≤` direction. W1-S retired the claim at `b93644a` after measuring that all 22 historically dropped branches were `F` |

### P3.5 — `sum`: 2 `VACUOUS`, 2 `NOT MINIMAL`, one cause

All four verdicts follow from `p` printing as a **universally bound** index, `∀p, p ∈ [1,n]`:
`∀p: N ≥ p` means `N ≥ n` (always true in scope, hence droppable) and `∀p: N < p` means
`N < 1` (never true, hence vacuous). **This is the exact defect W1-T9 fixed for `gcc` with
`OpPoint`/`pointp`**, which took all four `gcc` rules from flagged to sound and minimal.

`cata/sum.tex` has no producer, so the fix could not reach it: it is **the last place in the
tree where the pre-W1-T9 rendering survives**, and the only catalog artifact that predates the
2020 index-propagation rewrite (`e973e1e`). See P7.3.

---

## P4 — Generates rules that say nothing

Distinct from P3, and `catalog/nvalues.md` puts the three failure modes side by side:

| entry | verdict | why it is not useful |
|---|---|---|
| `alldifferent` | `SOUND and MINIMAL` | premise contradicts the constraint for `n ≥ 3`; **dead**, flag misses it |
| `all_equal` | `SOUND and MINIMAL` | premise *is* the conclusion; **alive and empty** |
| `nvalue` | `VACUOUS` ×4, `UNSOUND` ×1 | premises unsatisfiable in any store; the flag catches it |

**Dead and empty are different failures, and the same verdict covers both.**

### P4.1 — `all_equal`: the premise literal is the conclusion literal

| | |
|---|---|
| **Evidence** | `catalog/allequal.md`. Both rules read `X_i ≥ t, ∃i, i ∈ [1,n] ⊢ X_i ≥ t`. The `.tex` admits two readings — `(no binder)`, a **tautology**, and `exists i`, the intended dichotomy rule. Both are sound, so the validator returns `SOUND and MINIMAL` rather than `AMBIGUOUS` (which is reserved for sound-under-some, unsound-under-others) |
| **Root cause, read off source** | `addexists` (l.202) and `addforall` (l.203) **do not rename** the index they bind; `addprim` (l.204) does, which is why `alldifferent`'s and `gcc`'s premises print `X_{i'}` with `i' ≠ i`. When the conclusion's own index is `i`, the premise's `∃i` lands on top of it |
| **The generator's own detector misses it** | `branch_ambig` (l.613-617) counts repeated binders *within a single premise literal*; here `i` is bound once and the collision is with the **conclusion**, which `branch_ambig` never looks at. So `cata/allequal.tex` carries **no** D-0009 line while the validator reports two readings. **Two checks, two answers, and the weaker one is the generator's** |
| **What it would take** | **W1-T1**, rule-level binder scope. Not a printer patch |
| **Scoped?** | W1-T1, `TODO` |
| **The generator says it plainly** | `explenation generator.ml:291`: "`allequal` honestly has no non-trivial rule under this decomposition." The validator's `2 SOUND and MINIMAL` does not contradict that — it just cannot see it |

### P4.2 — Constraint-independent rules

`atleast_nvalue` / `atmost_nvalue` rule 1 (P3.3): strip the droppable premises and the content
is domain exhaustion, which holds for any constraint over `[1,m]`. Two more rules that pass a
check and say nothing about their constraint.

---

## P5 — Encoded twice, indistinguishably

### `atleast_nvalue` ≡ `atmost_nvalue`

| | |
|---|---|
| **Measured** | `cmp cata/atleastnvalues.tex cata/atmostnvalues.tex` silent; both md5 `82aa49d8a547f1a9df196c2eed408aa1`. All four rules and both diagnostics footers coincide exactly (`catalog/atleastnvalues.md`, measured 2026-09-21) |
| **The two decompositions differ in exactly two tokens** | `rule6` vs `rule5`, and `B4`'s reified sign `true` vs `false` (generator l.846 vs l.850) |
| **Diagnosed 2026-09-21** | `rule5` (l.343-355) and `rule6` (l.357-369) are the **same four-branch body** with the positive and negative calls interchanged (`ap`↔`nap`, `fre`↔`fnre`); `ap`/`nap` take their sign from the devent, so negating `B4`'s sign undoes the swap on **both** descent paths. Two interchanges compose to the identity. **As encoded, these are the same decomposition written twice** — not a printer bug, not a coincidence |
| **Independent evidence it must be wrong** | `docs/GCCAT.md:120-124`: the two constraints have **opposite closure properties** (`atleast_nvalue` extensible and monotone-decreasing in `NVAL`; `atmost_nvalue` contractible). Two constraints with opposite closure properties cannot have the same explanation rules. Both properties are machine-checked and hold |
| **Preserved on purpose** | `explenation generator.ml:712-715`: `write_footer` deliberately does not name its own file, so the collision stays visible as W1-T5's evidence |
| **Candidate root cause, recorded, untested** | Step 2's channel is `rule1`, a reified **equivalence**: `B4_p ⇔ N ≥ p` pins `N` from both sides, so the `≤`/`≥` distinction has nowhere to live but the sum schema. `catalog/atleastnvalues.md` records this as a reading of the source, and **explicitly does not propose it as a new G-number** |
| **What it would take** | An asymmetric channel schema — or a decomposition of `atmost_nvalue` that is not the polarity-dual of `atleast_nvalue`. **Nothing measured says which of the two files is wrong** |
| **Scoped?** | **W1-T5**, `TODO`, now `DIAGNOSED` but not fixed. The "no way to record an asymmetric channel" observation has **no G-number and no row** — recorded for W2-T1 |

**The same relation, handled correctly, is one file away.** gccat's `comparison swapped` link
(`docs/GCCAT.md:105`) is "the only near-mechanical relation" between constraints' explanations,
"and it is a renaming, not a derivation". Its other instance in this catalog is
`increasing`/`decreasing`: two separately authored, sign-swapped decompositions producing two
**different, mirror-image** files, each 2/2 `SOUND and MINIMAL` and **both firing**
(`catalog/decreasing.md`). Same relation, opposite outcome.

---

## P6 — Out of scope by decision

**35 of 118 globals**, measured: `python3 tools/mzn_coverage.py --rank --json`, tier
`- out of scope`. Cheap to state, so it is stated once here and not re-litigated per entry.

| group | code | globals carrying that code |
|---|---|---:|
| set variables unless channelled to Booleans first | **E5** | 10 |
| graph and reachability | **E6** | 12 |
| floats / non-linear | **E7** | 5 |

(Counts are per E-code over the 118 release globals and overlap where a row carries two codes;
the tier total is 35.) The tier list: `all_disjoint`, `arg_max`, `arg_min`, `at_most1`,
`bin_packing`, `bin_packing_capa`, `bin_packing_load`, `bounded_path`, `circuit`,
`circuit_opt`, `connected`, `dag`, `diffn`, `diffn_k`, `diffn_nonstrict`, `diffn_nonstrict_k`,
`disjoint`, `geost`, `int_set_channel`, `inverse_set`, `link_set_to_booleans`, `network_flow`,
`neural_net`, `partition_set`, `piecewise_linear`, `piecewise_linear_non_continuous`, `range`,
`reachable`, `roots`, `steiner`, `subcircuit`, `subgraph`, `sum_set`, `tree`,
`weighted_spanning_tree` (`catalog/INDEX.md`, generated).

**Sources:** D-0006 (E5, E6, E7), `docs/ROADMAP.md` "Explicitly out of scope",
`docs/DECISIONS.md:122` (E5's route). **Scoped?** Decided; nothing to do.

**Two wrinkles worth keeping.**

1. **`range` and `roots` are in this tier *and* have catalog entries** (P2.4). Out of scope for
   the *ranking*, in scope for the catalog, which requires an entry for all 118.
2. **The geometry/packing group has no E-code of its own.** `docs/ROADMAP.md` names it
   ("geometry and packing"), the coverage tool sorts it into the tier, but there is no letter
   for it the way E5/E6/E7 exist. Minor, and worth noticing before someone prices a `diffn`.

---

## P7 — Not a MiniZinc global at all

`python3 tools/catalog_index.py` reports three `UNMATCHED` warnings, and they are the three
entry files with no corresponding release global. **`catalog/INDEX.md`'s denominator is the 118
MiniZinc globals, so these three do not count towards the coverage claim.**

### P7.1 / P7.2 — `atleastnvalues`, `atmostnvalues`

gccat constraints, not MiniZinc globals. MiniZinc states the same thing through `nvalue(n, x)`
with an inequality on `n`. Consequences recorded in `catalog/atleastnvalues.md`:

- `tools/mzn_coverage.py --rank` assigns **no tier** (checked against all six; `missing_from_list`
  is empty, so it is genuinely not a release global rather than an indexing error);
- `CHRISTMAS_LIST.md` has **no row** — `grep -n 'nvalue' CHRISTMAS_LIST.md` gives three hits
  (l.96, 130, 217), none of them these constraints;
- so calibration is **`pending`**, not `no published rule`. **A silence that comes from not
  having looked is not a finding**, and the catalog distinguishes the two.

**What it would take:** a `CHRISTMAS_LIST.md` row for both — a citation, a searched-and-empty
finding, or an explicit "outside this index's scope". **Scoped?** C2-shaped; **no roadmap ID**.
And calibration should not be attempted before W1-T5 closes, whatever the literature says.

### P7.3 — `sum`: the orphan, and it is recoverable

| | |
|---|---|
| **Not a global** | `grep -x -E 'sum' tools/data/minizinc-2.10.1-globals.txt` → nothing. The file has `sliding_sum`, `sum_pred`, `sum_set` and no bare `sum`. Ambiguous between the two |
| **Orphaned** | No `sum` value and no `explainall … "cata/sum.tex"` in the generator. `Makefile:19-29` excludes it from the golden diff; `make check-orphans` fails if that set changes |
| **But the producer is in git — this is E1's find, verified by the orchestrator** | `3e4f17d` (2020-08-10, "tests sum and regular") carries the decomposition at l.361-363 and its `explainall` at l.388. `e973e1e` (2020-08-19, the `table` index-propagation rewrite) deleted both while keeping the `sumi`/`sumt` helpers, and rewrote every *other* `cata` file |
| **So W1-T6 is port-it-forward, not delete-or-regenerate** | And `docs/VALIDATOR.md:55-63` and `validator.ml:439`, which assert "no source in this repo", are **wrong** |
| **The recovered decomposition is an order encoding over a BC channel** | `Σ_t [X_i ≥ t] = X_i`, so `rule6`'s one-directionality is not a weakness — the equality comes from quantifying over all thresholds. `validator.ml:503`'s `nv_range Sum = (n, n·m)`, written from gccat alone with no access to the deleted code, **independently agrees** |
| **Scoped?** | **W1-T6**, `TODO`, rescoped 2026-09-21. Also **W1-T11**, third item, for the two stale "no source" assertions |
| **One thing to settle first** | The recovered decomposition sums **two index families** (`sumi ∘ sumt`) and passes G4's `dee::[]` guard only because both are composed into one `Decomp_devent`'s index modification. Whether that is intended or a hole in G4's wall is **unresolved, and `catalog/sum.md` says it should be resolved before W1-T6 closes by regeneration.** No row |

---

## Blast radius — the ranking, and the argument for it

**Widest: the index-set and side-condition family (E2; concretely G6, G7, G8, G15, G16, plus
the `D2` printer).**

- **34 of 118 release globals route through E2** (measured from
  `tools/mzn_coverage.py --rank --json`, summing every ecode list containing `E2`: 19 alone,
  plus `E0+E2` 4, `E1+E2` 3, `E1+E2+E9` 2, `E2+E4` 4, `E2+E7` 2).
- **5 of 16 shipped `cata/` entries emit zero rules because of it today** (P2.1), and those
  five include three of the repo's tier-C/D calibration targets.
- It is what W2-T1 and W2-T3 exist for, and D-0006 already calls E2 "the biggest single
  unlock".

**Runner-up, and widest by *rule* count among what ships: per-literal binder scope
(W1-T1 / D-0009).**

- **13 of the 36 rules in `cata/` carry the generator's own D-0009 flag** (measured:
  `grep -o 'DEFECT: [0-9]* emitted rule' cata/*.tex`, summing → 13; `atleastnvalues` 4,
  `atmostnvalues` 4, `gcc` 2, `nvalues` 2 — plus one footer line covering two `nvalues` rules,
  which is why the entry reports 3).
- **13 is a floor, not a ceiling**: `all_equal`'s two rules are ambiguous and are **not**
  flagged, because `branch_ambig` never inspects the conclusion (P4.1). So at least 15 of 36.
- It is the diagnosed cause of `element`'s 4 `VACUOUS` rules, and the suspected cause of
  `nvalue`'s five.

**Third: structural out-of-reach (P1).** Fewer constraints — 3 sourced, ~8 predicted — but it
is the only category with **no fix at any price**, and it is what bounds the method. A reader
who takes one thing from this file should take that E4 is necessary but not sufficient for
`alldifferent`'s §5/§6 and `gcc`'s flow rule.

**Then: E4 itself** — 9 of 118 globals carry it. D-0006 already says it "buys few constraints",
and P1 sharpens that: for two of the three sourced explanations it does not buy the target
either.

**Then P5** (2 constraints, but one of them must be wrong and nobody knows which), **P7** (3
entries, all bookkeeping), and **P6** (35 globals, but decided and costless).

---

## Contradictions in the evidence

Collected because a register is the right place for them; **none is fixed here** (S-C owns
this file only). Several are already open as roadmap rows, which is noted where true.

1. **`CLAUDE.md` contradicts itself on the validator totals.** Its table says "34 rules in 11
   entries: 13 sound and minimal, 21 flagged; 2 rules in 5 entries still out of scope"; the
   blockquote three paragraphs later says "11 of 42 rules are sound and minimal … and 31 are
   flagged" and "14 rules unmeasurable". The first matches every 2026-09-21 `make validate` run
   quoted in `catalog/`; the second is the pre-W1-T2 measurement left in place.
2. **`CLAUDE.md` prices `element`'s missing `I=i` rule at E4.** Measured by E2: `elem`
   (l.834-838) contains **no Boolean-sum schema at all**, so counting across sums is not its
   route (P3.1).
3. **Pre-W1-T2 rule count for `among`.** `docs/VALIDATOR.md:329` says 3; `docs/ROADMAP.md:48`
   books `among 2→0`. `range`/`regular`/`roots` agree between the two documents. Open as
   W1-T11. Today's count is 0 either way.
4. **Historic dropped-branch count.** `CLAUDE.md:156`, `docs/ROADMAP.md:49` and
   `WORKLOG.md:337` say **22**; `explenation generator.ml:549` says **25**. Today's shipped
   catalog drops **21** (measured 2026-09-21 by summing the `dropped F` fields). The all-`F`
   finding, which is the load-bearing part, is the same in every version.
5. **`cata/sum.tex` "has no source in this repo"** — `docs/VALIDATOR.md:55-63`,
   `validator.ml:439`. It has one, in git history (P7.3). Open as W1-T11, third item.
6. **`docs/VALIDATOR.md:279-288`'s per-entry table is stale for five entries** — `allequal`,
   `nvalues`, `atleastnvalues`, `atmostnvalues`, `gcc`. It predates W1-T9 and W1-T2. Open as
   W1-T11, fourth item.
7. **`explenation generator.ml:283-288` says the `EXAND` repair left 35 rules; the current run
   reports 34.** Reconciled in `catalog/allequal.md`: `576c718` (W1-T2) then took `table` from
   one rule to none. 35 − 1 = 34. Quote the run, not the comment.
8. **`decomps/sum_pred.md` prices an integer sum at G11 + G12 + G13**; the recovered `sum`
   order encoding needs none of the three, only G4's two-family sum (P7.3). `catalog/sum.md`
   does not claim the spec is wrong — it claims the spec was written without the orphan's
   decomposition in view.
9. **`decomps/all_different.md` states the shipped rule as `∃i' ≠ i`**; the shipped premise is
   `∀i'` (measured), and the whole calibration verdict turns on that quantifier.
10. **`CHRISTMAS_LIST.md:129` says `among` is "already in `cata/among.tex`"** — true of the
    decomposition, false of the output since W1-T2. The `increasing`/`decreasing` row's
    "already correct in the repo" was fixed at `45d1974`; this one was not in that scope.
11. **The E3 code collided with itself** — D-0006's *multi-family cardinality* versus
    `CHRISTMAS_LIST.md` §6's *weighted sums*. **Resolved by D-0011** (weighted = E8,
    integer-valued = E9), but `validator.ml`'s reason strings still carry the old meaning
    (W1-T11 (a), still open).
12. **`cata/gcc.tex` is produced by `gccn`, not by `gcc`.** The `gcc` value at l.813-814 is dead
    code and anyone reading it to understand the entry reads the wrong decomposition. Open as
    **W1-T12**. There is no `decomps/global_cardinality.md` either.
13. **Stale generator line numbers, everywhere.** `decomps/{all_equal,increasing,element,nvalue,
    among,regular}.md`, `decomps/_shapes*.md`, `docs/GCCAT.md`, `CHRISTMAS_LIST.md:206`,
    `validator.ml:439-453` and `CLAUDE.md` all cite pre-W1 line numbers. The *values* they name
    are still right; only the numbers rotted. This is why `catalog/README.md` step 4 says to
    record the value name as well as the line.

---

## Problems with no fix scoped anywhere

A roadmap row, a G-number, or an E-code counts as scoped. These have none.

1. **Nothing generates, or prefers, the *strongest* sound rule.** `alldifferent`'s `∀i' ≠ i`
   where `∃i' ≠ i` is also sound and strictly stronger; `all_equal`'s tautology reading
   alongside the intended one. Minimality is premise-droppability and **cannot see either**.
   W3-T5 *compares* against a published rule; nothing *produces* the stronger one, and D-0008
   (what "complete" means per entry) is open and does not cover strength. **This is the most
   consequential unscoped item in the register** — it is what separates "sound and minimal" from
   "useful", in the two entries the catalog itself nominates as its standing proofs.
2. **`element`'s `I = i` has no route stated at all.** E4 is ruled out (measured); W1-T1 fixes
   the *vacuity* of rules 3–6 but the entry does not claim it delivers `I = i`, which "would
   have to say every other index is excluded" and has no schema that says it.
3. **`G18`** (`write`, `writes`, `writes_seq`) — added in the §11 addendum, in no roadmap row.
4. **The `D2` printer** (`"setfils"`) — blocks G7's route and every variable-length chain
   (`lex_chain_*`, `value_precede_chain`, `seq_precede_chain`). Appears only as a note under
   W2-T1, with no row and no number.
5. **`ext X3`: `OpPrim` introduces `t'` without binding it** — so even after G7 lands,
   `regular`'s premise would print `t' ∈ D_9, t' ≠ t` with no quantifier, and "for some `t'`"
   and "for every `t'`" are different rules with different soundness. It received **no
   consolidated G-number**; `catalog/regular.md` warns that "anyone who lands G7 and reads two
   rules out of this file has not finished".
6. **No way to record an asymmetric channel.** `rule1` is a reified *equivalence*, so
   `B4_p ⇔ N ≥ p` pins `N` from both sides — the candidate root cause of P5.
   `catalog/atleastnvalues.md` deliberately does **not** propose it as a G-number; it is
   recorded for W2-T1 and nowhere else.
7. **No `decomps/range.md`, no `decomps/roots.md`** — the two shipped decompositions nobody can
   identify (P2.4). W2-T5 is `DONE` without them.
8. **No `CHRISTMAS_LIST.md` row for `atleast_nvalue` / `atmost_nvalue`** — so their calibration
   is `pending` rather than a finding (P7.1).
9. **G5 — the `among` decomposition-authoring mistake.** Fixable today with no engine change
   (`nvalues` shows the correct shape), and in no row.
10. **The `pointp` transplant from `gccn` to `nvalues`** — the "obvious next experiment" for the
    catalog's weakest entry, with no row and nobody assigned.
11. **`gcc`'s flow rule has no W4 row**, where `alldifferent` has W4-T2 and `cumulative` has
    W4-T3. Its `out of reach` verdict is recorded and then unowned.
12. **Whether `sum`'s two-family sum is legal under G4** — `catalog/sum.md` says resolve it
    before W1-T6 closes by regeneration; no row says who.

---

## How this register was produced

- **Nothing was run except two read-only measurements**, both on files this session does not
  own: `grep -o 'DEFECT: [0-9]* emitted rule' cata/*.tex` summed to **13**, and
  `grep -o '\frac' cata/*.tex | wc -l` per file summed to **36** emitted rules across the 16
  artifacts. Both are stated as measurements above; everything else is carried.
- **`make validate` was not re-run.** Every verdict here is quoted from the entry that ran it —
  all fifteen `catalog/*.md` files quote the same 2026-09-21 run totals (*34 rules in 11
  entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope*), which is the
  cross-check that they are one run and not several.
- **Constraint counts** from `python3 tools/mzn_coverage.py --rank --json` (tier counts:
  A 36, B 8, C 9, D 19, unclassified 11, out of scope 35) and from summing its `ecode_globals`
  map over every list containing a given code: **E0 45, E1 7, E2 34, E3 7, E4 9, E5 10, E6 12,
  E7 5, E8 4, E9 8**, plus 12 globals with no code given.
- **Entry counts** from `catalog/INDEX.md` (generated): 12 of 118 globals have an entry,
  8 have a generated rule, 6 have a validated one; 15 entry files exist, three matching no
  release global.
- **No web search, no paper fetched, no claim about any paper** beyond what
  `catalog/_literature/` already records with its own provenance tags. Where a `COMPARISON` tag
  travels with a statement in the source, it travels with it here.
- **Read, scoped:** `docs/DECOMP_FORMAT_NOTES.md` (whole — 132 lines, it is the gap list),
  `docs/ROADMAP.md` (whole), `docs/DECISIONS.md` via `grep -n '^## D-'` then D-0006,
  `WORKLOG.md` via `grep -n '^### '` then the four 2026-09-21 handoffs. `CHRISTMAS_LIST.md` was
  **not** read; every citation of it here is quoted through a `catalog/` entry that read the
  line.
