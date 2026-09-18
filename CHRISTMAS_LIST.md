# Christmas list — explanations for every MiniZinc global

For each global constraint in MiniZinc's `globals.mzn` (118 canonical entries):

1. **Lit.** — is there explanation literature for it?
2. **Solver** — does a solver implement an *explaining* propagator, or does it decompose?
3. **Decomposition route** — can we derive the explanation with the method in this repo, and if
   not, which extension is needed?

Compiled 2026-09-18. The literature column cites only papers that were checked, and says **none**
where none was found — most of the list is *none*, which is the point of a wish list. The solver
columns come from source inspection on that date (see below).

---

## Solvers that can consume these explanations

Explanations are not a Chuffed-only currency. Every solver below either learns from them or
certifies with them.

| solver | mechanism | explanation status | pointer |
|---|---|---|---|
| **Chuffed** | LCG, C++ | ~24 native explaining propagators in `chuffed/globals/`; everything else decomposed | [github.com/chuffed/chuffed](https://github.com/chuffed/chuffed) |
| **Geas** | LCG, C++ (Gange) | 8 native propagators, visible as `fzn_*` redefinitions shipped in MiniZinc's own `share/minizinc/geas/` | [github.com/gkgange/geas](https://github.com/gkgange/geas) |
| **Huub** | LCG, Rust (Dekker & Stuckey, Monash) — built on IPASIR-UP with CaDiCaL as the SAT back end | **only `all_different` and `disjunctive` natively; every other global is decomposed using MiniZinc's own decompositions.** Forward *and* backward explanation, with configurable eager/lazy thresholds | [github.com/huub-solver/huub](https://github.com/huub-solver/huub) |
| **Choco** | LCG since **5.0.0-beta.1** (17 Feb 2025), *replacing* the previous explanation framework; inspired by Chuffed and Feydy & Stuckey 2009. Opt-in: `new Model(SettingsBuilder.init().setLCG(true))` | ~20 n-ary propagators use the `Reason` API; **12 constraints throw `SolverException` in LCG mode** | [github.com/chocoteam/choco-solver](https://github.com/chocoteam/choco-solver) |
| **OR-Tools CP-SAT** | CDCL + CP propagators | every propagator supplies a reason for each bound it pushes; nogoods learned by conflict analysis | [github.com/google/or-tools](https://github.com/google/or-tools/tree/stable/ortools/sat) |
| **Pumpkin** | LCG, Rust (ConSol Lab, TU Delft — Demirović) | produces certificates of infeasibility/optimality checkable by a *formally verified* checker; CP 2024 multi-stage proof logging framework | [github.com/ConSol-Lab/Pumpkin](https://github.com/consol-lab/pumpkin) |
| **Glasgow Constraint Solver** | C++20 (McCreesh) | proof logs for *any* problem it solves; propagators justify their inferences for VeriPB | [github.com/ciaranm/glasgow-constraint-solver](https://github.com/ciaranm/glasgow-constraint-solver) |
| **CPMpy** | Python modelling layer (Guns' group) | the user-facing side: MUS/MCS, step-wise and contrastive explanations; drives OR-Tools, CP Optimizer, Choco, Glasgow GCS, Pumpkin, MiniZinc | [XCP-explain tutorial](https://cpmpy.github.io/XCP-explain/) |
| **Gecode** | propagation only | no explanations — the baseline that shows what they buy | [gecode.org](https://www.gecode.org/) |
| **PaLM** | historic (Jussien & Barichard 2000) | the original explanation-based CP solver | — |

## The structural observation

Chuffed ships native explaining propagators for about **24** constraints, Geas for **8**, Choco
for roughly **20**. For everything else they **decompose and let the primitive propagators explain
themselves**.

**Huub is the limiting case, and it is the project's best argument.** It implements exactly *two*
global propagators natively — `all_different` and `disjunctive` — and decomposes every other global
using **MiniZinc's own decompositions**, requiring each propagator to "explain the propagation by
computing a clause which is a consequence of the CP model" (Dekker & Stuckey, *Towards Modern and
Modular SAT for LCG*, CP 2025).

In other words: a competitive modern LCG solver already derives explanations for ~116 of the 118
globals *by constraint decomposition*. That is this repo's method, shipped as a solver. What it
does not have is a schema — it re-derives the clauses at flattening and conflict-analysis time,
per instance, with nothing recorded and nothing reusable.

And the paper reports where Huub loses: precisely on **`diffn`, `cumulative`** and global
difference constraints, the constraints needing specialised propagators. That is a *measured*
confirmation of the quality ceiling argued throughout this list — decomposition-derived
explanations are sound but weak, and they are weakest exactly where the hand-written literature
explanations (Schutt on `cumulative`) exist.

So the catalog is not a documentation exercise. It is the missing schema layer under something
four solvers already do at runtime.

## The immediately actionable target: Choco's LCG gap

Choco's own release notes state the position exactly:

> some constraints are explained with dedicated functions and others are decomposed into
> explained ones. More importantly, others are **neither explained nor decomposed** (for the
> moment). In the latter case, **an exception is raised** to inform the user of the situation.

That exception list, grepped from `IIntConstraintFactory.java`, *is* a wish list with a customer:

| Choco constraint | throws in LCG mode | this repo |
|---|---|---|
| `regular` | yes | **a decomposition already exists in `cata/regular.tex`** — needs `D_8`/`D_9` defined and **E2** |
| `costRegular`, `multiCostRegular` | yes | **E1 + E2 + E3** |
| `mddc` | yes | **E1 + E2** |
| `tree` | yes | **E6** — out of scope |
| `allDifferent` under condition, `allDiffPrec` | yes | **E0**/**E2** — plausibly easy wins |
| `clausesIntChanneling` | yes | **E0** |
| `keySort` | yes | **E2** |
| `distance`, `power`, `multiplication` | yes | arithmetic, not decomposition — see the AAAI 2025 certified-multiplication work |

Also note `AlgoAllDiffAC.java:329` carries `assert !isLCG() : "not implemented yet for LCG"` — so
**domain-consistent `alldifferent` is not fully LCG-ready in Choco either**, which is the exact gap
Downing et al. 2012 addresses and the one **E4** targets.

`regular` is the standout: it is on Choco's unsupported list, the repo already has a decomposition
for it, and that decomposition deliberately avoids state variables so the explanation stays in the
user's own vocabulary. That is a complete, small, publishable contribution.

## Legend

**Extensions needed** (cumulative wish list, cheapest first):

| code | extension | why |
|---|---|---|
| **E0** | none — works today | |
| **E1** | open `var_name` | admit new auxiliary integer families; the `rule1` channelling mechanism already exists (`N` in `nvalues`, `O` in `gccn`), it just isn't openable |
| **E2** | richer side conditions | `Rel` relates two index *names*; `Addcst` does `i₃ = i₂ ± c·i` over a 1-D constant array. Need inequalities against *expressions* (`u − t`) and 2-D constant tables (`d[q,s]`) |
| **E3** | multi-family cardinality | `rule5/6/7` handle one Boolean family and `failwith "sommes multiples"` otherwise |
| **E4** | counting / pigeonhole rule | Hall-type arguments: inference *across* several cardinality constraints, not within one |
| **E5** | set → Boolean channelling | membership matrix `b[i,v] ↔ v ∈ S_i`; MiniZinc's `link_set_to_booleans` is literally this |
| **E6** | graph reasoning | reachability/connectivity arguments have no finite Boolean decomposition that preserves the propagation-relevant reasoning |
| **E7** | floats / non-linear | out of scope |

**Solver column below:** `native` = explaining propagator in Chuffed; `decomp` = solved by
decomposition, explanations come from the primitive propagators. Geas natives are marked **[G]**,
Choco LCG natives **[C]**, Choco LCG *failures* **[C✗]**.

---

## 1. AllDifferent family

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `all_different` | **Downing, Feydy, Stuckey 2012**, *Explaining alldifferent* — compares value-, bounds- and domain-consistent propagators and their explanations; finds no single one is best | native (`alldiff.cpp`) **[G] [C]** | **E0** for the weak rule: pairwise `≠` gives `X_i ≠ t ← ∀i'. X_i' = t`, i.e. forward-checking level. The Hall-set explanation needs **E4** — decompose via occurrence cardinalities `Σ_i [x_i=v] ≤ 1` and reason across them. *This is the single best test case for the whole project.* |
| `all_different_except`, `all_different_except_0` | none | decomp **[G]** | **E0**, same shape with a guard on the excepted value |
| `symmetric_all_different` | none | decomp | **E0** + `inverse` channelling |
| `all_disjoint` | none | decomp | **E5** (set variables) |
| `alldifferent_except_0` (alias) | — | — | as above |

## 2. Counting and cardinality

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `global_cardinality`, `_closed`, `_low_up`, `_low_up_closed` | **Downing, Feydy, Stuckey 2012**, *Explaining flow-based propagation* (CPAIOR, LNCS 7298:146–162) — generic explaining flow propagator, explicitly replaces specialised **gcc** | decomp **[G]** | `_low_up` is **E0**. Full `global_cardinality` needs **E3**: `fzn_global_cardinality` is `forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)` and that trailing `sum(count)` is over *integer* variables. The flow explanation needs **E4**. |
| `count`, `at_least`, `at_most`, `exactly` | none specific | decomp | **E0** — this is `rule5/6/7` exactly as built |
| `among` | none | decomp | **E0** — already in `cata/among.tex` |
| `nvalue` | none | decomp | **E0** — already in `cata/nvalues.tex`, but the generated rule repeats binders (`∀i` twice); fix is index hygiene, not an extension |
| `at_most1` | none | decomp | **E5** |
| `distribute` | none | decomp | **E0** + **E3** |
| `sliding_among` | none | decomp | **E0** |
| `arg_val` | none | decomp | **E1** |

## 3. Value ordering, precedence, symmetry

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `value_precede`, `value_precede_chain` | none | **native** (`value-precede.cpp`) **[G] [C]** | **E0** — MiniZinc's decomposition is a Boolean state chain (`b[i]` with `xis -> b[i+1]`, `not xis -> b[i]==b[i+1]`), structurally identical to the `increasing` entry that already works. **Good early win.** |
| `seq_precede_chain` | none | decomp | **E0** |
| `lex_less`, `lex_lesseq`, `lex2`, `strict_lex2`, `lex2_strict` | Chu & Stuckey, *Symmetries and lazy clause generation* (IJCAI 2011) — static symmetry breaking is LCG-compatible provided the added constraints have explaining propagators; no dedicated `lex` explanation paper found | **native** (`lex.cpp`) **[C]** | **E0** — lex is a Boolean carry chain, same shape as `value_precede` |
| `lex_chain_*`, `*_orbitope` | none | decomp | **E0**, but MiniZinc's decomposition branches on instance data — one entry per variant |
| `var_perm_sym`, `var_sqr_sym` | Chu & Stuckey 2011 (above) | **native** (`sym-break.cpp`) | **E0**/**E2** |

## 4. Sequencing and sliding

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `sliding_sum` | none directly; the **sequence** family is covered by Downing et al. 2012 *Explaining flow-based propagation* | decomp | **E1 + E2**. MiniZinc uses prefix-sum *integer* auxiliaries `S[i] = xs[i] + S[i-1]`, then `S[i] <= S[i+w] - low`. Needs a new integer family (**E1**) and threshold arithmetic `u − t` (**E2**). |
| `span`, `alternative` | none | decomp | **E0** |

## 5. Extensional — table, regular, MDD

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `table` | **Gange, Stuckey, Szymanek 2011**, *MDD propagators with explanation* (Constraints 16:407–429) — MDDs subsume table, regular, set/multiset. Also **McIlree & McCreesh, CP 2023** (best paper), *Proof logging for smart extensional constraints* — certified justifications for Smart Table | **native** (`table.cpp`) **[G] [C]** | **E2**. MiniZinc's `fzn_table_int` introduces a var row-index into a constant matrix — an `element`. The repo's own `table` entry uses a different encoding and currently emits an **unsound empty-premise rule**; that is a bug, not a missing extension. |
| `regular`, `regular_nfa`, `regular_regexp` | Gange et al. 2011 (above); **McIlree & McCreesh CP 2023** covers Regular Language Membership | **native** (`regular.cpp`) **[C✗]** | **E2**. Note the repo already has a *different and legitimate* decomposition — transitions directly on consecutive `X` via value sets, no state variables, so explanations stay in the user's vocabulary. It only needs `D_8`/`D_9` defined in the printer and 2-D table side conditions. |
| `mdd`, `mdd_nondet` | **Gange, Stuckey, Szymanek 2011** | **native** (`mddglobals.cpp`) **[C✗]** | **E1 + E2** |
| `cost_regular`, `cost_mdd` | **Gange, Stuckey, Van Hentenryck, CP 2013**, *Explaining propagators for edge-valued decision diagrams* | decomp **[C✗]** | **E1 + E2 + E3** (costs accumulate) |

## 6. Scheduling

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `cumulative` | **Schutt, Feydy, Stuckey, Wallace 2011**, *Explaining the cumulative propagator* (Constraints 16(3):250–282) — time-table filtering with window-based explanations. **Schutt, Feydy, Stuckey, CPAIOR 2013**, *Explaining time-table-edge-finding propagation* (arXiv:1208.3015) | **native** (`cumulative.cpp`, `cumulativeCalendar.cpp`) **[G] [C]** | The repo's entry is the **unary-resource special case** and names all *n* tasks; Schutt names a small window with a capacity argument. Needs **E2** (variable durations/resources: `s_i + d_i ≤ s_j` with `d_i` a var) and **E4** (the capacity/counting argument). *The other key test case.* |
| `cumulatives`, `cumulative_opt` | as above | decomp | **E2 + E4** |
| `disjunctive`, `_strict`, `_opt` | implied by the cumulative papers (unary is the special case) | **native** (`disjunctive.cpp`) **[G]** | **E2** — `fzn_disjunctive` is `d_i=0 \/ d_j=0 \/ s_i+d_i<=s_j \/ s_j+d_j<=s_i`, i.e. var-var linear atoms |
| `knapsack` | none found | decomp **[C]** | **E1 + E3** (weighted sums over integer vars) |

## 7. Packing and geometry

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `bin_packing`, `_capa`, `_load` | none found | decomp | **E3** (weighted sums); `_load` is the most tractable |
| `diffn`, `diffn_k`, `diffn_nonstrict`, `diffn_nonstrict_k` | none found | decomp **[C]** | **E2** — pairwise non-overlap is a 4-way disjunction of var-var linear atoms, so actually reachable once E2 lands |
| `geost` | none found | decomp | **out** — no schema-expressible decomposition |

## 8. Graph and reachability

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `circuit`, `circuit_opt` | **Francis & Stuckey**, *Explaining circuit propagation* (Constraints, doi 10.1007/s10601-013-9148-0) — covers circuit and variants. **McIlree & McCreesh, CPAIOR 2024**, *Proof logging for the circuit constraint* | **native** (`circuit.cpp`) **[C]** | **E6**. The `alldifferent` + no-subtour decomposition is expressible, but the *useful* explanation is a reachability argument. |
| `subcircuit` | Francis & Stuckey (above) | **native** (`subcircuit.cpp`) **[C]** | **E6** |
| `tree`, `dag`, `connected`, `reachable`, `subgraph`, `bounded_path`, `steiner` | none found beyond the circuit line of work | **native** (`tree.cpp`, `dtree.cpp`, `dag.cpp`, `dconnected.cpp`, `bounded_path.cpp`, `well-founded.cpp`, `EdExplFinder.cpp`) **[C✗ for `tree`]** | **E6** — Chuffed has a dedicated *edge explanation finder*, which tells you how far this is from clause unfolding |
| `weighted_spanning_tree`, `network_flow` | flow: Downing et al. 2012 (above) | **native** (`mst.cpp`, `minimum_weight_tree.cpp`) | **E6 + E3** |

## 9. Ordering, sorting, channelling

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `increasing`, `decreasing`, `strictly_*` | none specific | decomp | **E0** — **already correct in the repo**; `cata/increasing.tex` and `cata/decreasing.tex` are cleanly dual |
| `element` | none found | decomp **[C]** | **E0** — already in `cata/element.tex`, 6 rules |
| `member` | none | decomp | **E0** — `exists(i)(x[i]=y)` |
| `maximum`, `minimum` | none found | **native** (`minimum.cpp`) **[C]** | **E2** (var-var atoms) |
| `arg_max`, `arg_min` | none | native for bool (`bool_arg_max.cpp`) | **E2**; float variants **E7** |
| `sort`, `arg_sort` | none | decomp | **E2** (composes `element`) |
| `inverse`, `inverse_in_range` | none | native (`inverse` per Chuffed docs) **[G] [C]** | **E2** — channelling `x[i]=j <-> y[j]=i` is two reified families, close to **E0** |
| `int_set_channel`, `link_set_to_booleans` | none | decomp | **E5** — and `link_set_to_booleans` *is* the E5 mechanism |

## 10. Set constraints

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `range`, `roots` | none | decomp | **E5**. Note: MiniZinc's `range`/`roots` take `var set of int` and have **no library decomposition** (declared solver-native). The repo's `cata/range.tex` and `cata/roots.tex` are a *different formulation* — worth reconciling or renaming. |
| `partition_set`, `disjoint`, `sum_set`, `inverse_set` | none | decomp | **E5** |

## 11. Maths and misc

| constraint | Lit. | Solver | Decomposition route |
|---|---|---|---|
| `sum_pred` | none | decomp | **E3** |
| `piecewise_linear`, `piecewise_linear_non_continuous` | none | decomp | **E7** |
| `neural_net` | none | decomp | **E7** |
| `write`, `writes`, `writes_seq` | none | decomp | **E2** (array update = `element` family) |
| `*_fn` functional variants (`among_fn`, `count_fn`, `nvalue_fn`, `range_fn`, `roots_fn`, `sort_fn`, `inverse_fn`, `distribute_fn`, `global_cardinality_fn`, `global_cardinality_closed_fn`, `bin_packing_load_fn`) | — | — | not separate constraints; they call the predicate form |
| `cost_mdd`, `edit_distance` | Gange et al. 2013 | native (`edit_distance.cpp`) | **E1 + E2** |

---

## What to actually ask for

Ranked by constraints unlocked per unit of work:

1. **E0 hygiene — no new features.** Fix index-binder scoping, define index sets above `D_3` in
   `printind_set_int`, stop `removeimp` silently swallowing failures, and kill the unsound
   empty-premise `table` rule. This alone makes ~25 constraints correct rather than
   plausible-looking: the whole counting family, `value_precede`, `lex*`, `member`, `among`,
   `seq_precede_chain`, `all_different_except*`.
2. **E2 — richer side conditions.** Biggest single unlock: `disjunctive`, `diffn`, `maximum`,
   `minimum`, `inverse`, `sort`, `regular` (finishes the existing entry), `table`, `write*`.
   ~12 constraints.
3. **E1 — open `var_name`.** `sliding_sum`, `mdd`, `cost_*`, `knapsack`. The mechanism already
   exists via `rule1`; it only needs to stop being a closed enum. ~6 constraints.
4. **E3 — multi-family cardinality.** Removes the `failwith`. `global_cardinality`,
   `bin_packing*`, `sum_pred`, `knapsack`. ~6 constraints.
5. **E4 — counting / pigeonhole.** Few constraints, but it is the only route to explanations that
   match **Downing** on `alldifferent` and **Schutt** on `cumulative`. This is the research, not
   the engineering.
6. **E5 — set channelling.** ~10 constraints, mechanical once the membership matrix exists.
7. **E6 / E7 — graph and float.** Declare out of scope.

**And there is a customer.** The ranking above is by constraints-unlocked; ranked instead by
*someone is waiting for this*, **E2 applied to `regular`** goes first — it is on Choco's
LCG-unsupported list, the decomposition already exists in this repo, and it avoids state variables
so the explanation stays in the user's own vocabulary. `clausesIntChanneling` (**E0**) and
conditional `allDifferent` / `allDiffPrec` (**E0**/**E2**) are the next cheapest items on that same
list.

Two constraints are worth singling out as the experiments that decide whether the method is
competitive rather than merely sound: **`alldifferent`** (can we reach the Hall-set explanation?)
and **`cumulative`** (can we reach the window/capacity explanation?). Both need **E4**, and both
have a published hand-written baseline to be measured against.

---

## References

- Ohrimenko, Stuckey, Codish. *Propagation via lazy clause generation.* Constraints 14(3):357–391, 2009.
- Feydy, Stuckey. *Lazy clause generation reengineered.* CP 2009.
- Schutt, Feydy, Stuckey, Wallace. *Explaining the cumulative propagator.* Constraints 16(3):250–282, 2011.
- Schutt, Feydy, Stuckey. *Explaining time-table-edge-finding propagation for the cumulative resource constraint.* CPAIOR 2013. <https://arxiv.org/pdf/1208.3015>
- Downing, Feydy, Stuckey. *Explaining alldifferent.* ACSC 2012. <https://people.eng.unimelb.edu.au/pstuckey/papers/alldiff.pdf>
- Downing, Feydy, Stuckey. *Explaining flow-based propagation.* CPAIOR 2012, LNCS 7298:146–162.
- Gange, Stuckey, Szymanek. *MDD propagators with explanation.* Constraints 16:407–429, 2011.
- Gange, Stuckey, Van Hentenryck. *Explaining propagators for edge-valued decision diagrams.* CP 2013.
- Francis, Stuckey. *Explaining circuit propagation.* Constraints, doi 10.1007/s10601-013-9148-0.
- Chu, Stuckey. *Symmetries and lazy clause generation.* IJCAI 2011.
- McIlree, McCreesh. *Proof logging for smart extensional constraints.* CP 2023 (best paper).
- McIlree, McCreesh. *Proof logging for the circuit constraint.* CPAIOR 2024.
- Dekker, Stuckey et al. *Towards Modern and Modular SAT for LCG.* CP 2025, LIPIcs vol. 340, paper 42.
- Flippo, Sidorov, Marijnissen, Smits, Demirović. *A multi-stage proof logging framework to certify the correctness of CP solvers.* CP 2024.
- Gupta, Genc, O'Sullivan. *Explanation in constraint satisfaction: a survey.* IJCAI 2021.
- Gontier, Truchet, Prud'homme. *Conflict analysis in CP solving: explanation generation from constraint decomposition.* CPTAI @ CP 2020. <https://hal.science/hal-03179630>
