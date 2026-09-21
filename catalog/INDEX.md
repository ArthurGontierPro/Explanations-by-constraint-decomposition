<!--
  catalog/INDEX.md -- GENERATED. Do not hand-edit.
  Regenerate with: python3 tools/catalog_index.py
  Generated: 2026-09-21
  Source: tools/catalog_index.py (reads tools/mzn_coverage.py --json,
  catalog/*.md, cata/*.tex, and `make validate`'s output; see that
  script's ALIAS table for the cata/catalog basename <-> MiniZinc
  global-name mapping).
-->

# Catalog index

One row per MiniZinc release global (118 total, from `tools/mzn_coverage.py`, release 2.10.1). Every count below is computed on
every regeneration, never hand-typed -- see the header comment for how.

## Summary

- catalog entries: **118 / 118** (12 reviewed, 106 stubs)
  A **stub** is a file `tools/catalog_stub.py` generated: it carries a
  machine-derived tier, citation line, solver class and rule count, and
  the words `not reviewed` in every field that would be a judgement.
  A **reviewed** entry is one a person wrote against `catalog/TEMPLATE.md`.
  **The entry count is never printed without this split** -- 118 / 118 with
  106 of them stubs is a claim about filenames, not about work done.
- have any generated rule (`cata/*.tex`, `\frac` count > 0): **8 / 118**
- have any validated (SOUND and MINIMAL) rule: **6 / 118**

| tier | globals | entries | reviewed | stubs | generated rules | validated |
|---|---:|---:|---:|---:|---:|---:|
| A | 36 | 36 | 6 | 30 | 5 | 4 |
| B | 8 | 8 | 0 | 8 | 0 | 0 |
| C | 9 | 9 | 1 | 8 | 1 | 1 |
| D | 19 | 19 | 3 | 16 | 2 | 1 |
| unclassified | 11 | 11 | 0 | 11 | 0 | 0 |
| out of scope | 35 | 35 | 2 | 33 | 0 | 0 |

## Warnings from this run

- UNMATCHED: 'atleastnvalues' has no corresponding release global (see ALIAS comment for why)
- UNMATCHED: 'atmostnvalues' has no corresponding release global (see ALIAS comment for why)
- UNMATCHED: 'sum' has no corresponding release global (see ALIAS comment for why)

## All 118 globals

| constraint | tier | catalog entry | kind | generated rules | validated | blocking gap |
|---|---|---|---|---:|---:|---|
| `all_different_except` | A | [all_different_except](all_different_except.md) | **stub** | — | — | — |
| `all_different_except_0` | A | [all_different_except_0](all_different_except_0.md) | **stub** | — | — | — |
| `all_equal` | A | [allequal](allequal.md) | reviewed | 2 | 2 | — |
| `alternative` | A | [alternative](alternative.md) | **stub** | — | — | — |
| `among` | A | [among](among.md) | reviewed | 0 | out of scope: index set D_4 is never defined by the printer (W1-T2), AND among's ... | G8 |
| `arg_sort` | A | [arg_sort](arg_sort.md) | **stub** | — | — | — |
| `arg_val` | A | [arg_val](arg_val.md) | **stub** | — | — | — |
| `at_least` | A | [at_least](at_least.md) | **stub** | — | — | — |
| `at_most` | A | [at_most](at_most.md) | **stub** | — | — | — |
| `count` | A | [count](count.md) | **stub** | — | — | — |
| `decreasing` | A | [decreasing](decreasing.md) | reviewed | 2 | 2 | — |
| `distribute` | A | [distribute](distribute.md) | **stub** | — | — | — |
| `element` | A | [element](element.md) | reviewed | 6 | 2 | — |
| `exactly` | A | [exactly](exactly.md) | **stub** | — | — | — |
| `increasing` | A | [increasing](increasing.md) | reviewed | 2 | 2 | — |
| `knapsack` | A | [knapsack](knapsack.md) | **stub** | — | — | — |
| `lex_chain_greater` | A | [lex_chain_greater](lex_chain_greater.md) | **stub** | — | — | — |
| `lex_chain_greatereq` | A | [lex_chain_greatereq](lex_chain_greatereq.md) | **stub** | — | — | — |
| `lex_chain_greatereq_orbitope` | A | [lex_chain_greatereq_orbitope](lex_chain_greatereq_orbitope.md) | **stub** | — | — | — |
| `lex_chain_less` | A | [lex_chain_less](lex_chain_less.md) | **stub** | — | — | — |
| `lex_chain_lesseq` | A | [lex_chain_lesseq](lex_chain_lesseq.md) | **stub** | — | — | — |
| `lex_chain_lesseq_orbitope` | A | [lex_chain_lesseq_orbitope](lex_chain_lesseq_orbitope.md) | **stub** | — | — | — |
| `member` | A | [member](member.md) | **stub** | — | — | — |
| `nvalue` | A | [nvalues](nvalues.md) | reviewed | 5 | 0 | — |
| `seq_precede_chain` | A | [seq_precede_chain](seq_precede_chain.md) | **stub** | — | — | — |
| `sliding_among` | A | [sliding_among](sliding_among.md) | **stub** | — | — | — |
| `sliding_sum` | A | [sliding_sum](sliding_sum.md) | **stub** | — | — | — |
| `sort` | A | [sort](sort.md) | **stub** | — | — | — |
| `span` | A | [span](span.md) | **stub** | — | — | — |
| `strictly_decreasing` | A | [strictly_decreasing](strictly_decreasing.md) | **stub** | — | — | — |
| `strictly_increasing` | A | [strictly_increasing](strictly_increasing.md) | **stub** | — | — | — |
| `sum_pred` | A | [sum_pred](sum_pred.md) | **stub** | — | — | — |
| `symmetric_all_different` | A | [symmetric_all_different](symmetric_all_different.md) | **stub** | — | — | — |
| `write` | A | [write](write.md) | **stub** | — | — | — |
| `writes` | A | [writes](writes.md) | **stub** | — | — | — |
| `writes_seq` | A | [writes_seq](writes_seq.md) | **stub** | — | — | — |
| `inverse` | B | [inverse](inverse.md) | **stub** | — | — | — |
| `inverse_in_range` | B | [inverse_in_range](inverse_in_range.md) | **stub** | — | — | — |
| `lex_greater` | B | [lex_greater](lex_greater.md) | **stub** | — | — | — |
| `lex_greatereq` | B | [lex_greatereq](lex_greatereq.md) | **stub** | — | — | — |
| `maximum` | B | [maximum](maximum.md) | **stub** | — | — | — |
| `minimum` | B | [minimum](minimum.md) | **stub** | — | — | — |
| `value_precede` | B | [value_precede](value_precede.md) | **stub** | — | — | — |
| `value_precede_chain` | B | [value_precede_chain](value_precede_chain.md) | **stub** | — | — | — |
| `cost_mdd` | C | [cost_mdd](cost_mdd.md) | **stub** | — | — | — |
| `cost_regular` | C | [cost_regular](cost_regular.md) | **stub** | — | — | — |
| `cumulative_opt` | C | [cumulative_opt](cumulative_opt.md) | **stub** | — | — | — |
| `cumulatives` | C | [cumulatives](cumulatives.md) | **stub** | — | — | — |
| `cumulatives_opt` | C | [cumulatives_opt](cumulatives_opt.md) | **stub** | — | — | — |
| `global_cardinality` | C | [gcc](gcc.md) | reviewed | 4 | 4 | — |
| `global_cardinality_closed` | C | [global_cardinality_closed](global_cardinality_closed.md) | **stub** | — | — | — |
| `global_cardinality_low_up` | C | [global_cardinality_low_up](global_cardinality_low_up.md) | **stub** | — | — | — |
| `global_cardinality_low_up_closed` | C | [global_cardinality_low_up_closed](global_cardinality_low_up_closed.md) | **stub** | — | — | — |
| `all_different` | D | [alldifferent](alldifferent.md) | reviewed | 1 | 1 | — |
| `cumulative` | D | [cumulative](cumulative.md) | reviewed | 2 | out of scope: the durations d_i appear as uninterpreted symbols inside index equa... | — |
| `disjunctive` | D | [disjunctive](disjunctive.md) | **stub** | — | — | — |
| `disjunctive_opt` | D | [disjunctive_opt](disjunctive_opt.md) | **stub** | — | — | — |
| `disjunctive_strict` | D | [disjunctive_strict](disjunctive_strict.md) | **stub** | — | — | — |
| `disjunctive_strict_opt` | D | [disjunctive_strict_opt](disjunctive_strict_opt.md) | **stub** | — | — | — |
| `lex2` | D | [lex2](lex2.md) | **stub** | — | — | — |
| `lex2_strict` | D | [lex2_strict](lex2_strict.md) | **stub** | — | — | — |
| `lex_less` | D | [lex_less](lex_less.md) | **stub** | — | — | — |
| `lex_lesseq` | D | [lex_lesseq](lex_lesseq.md) | **stub** | — | — | — |
| `mdd` | D | [mdd](mdd.md) | **stub** | — | — | — |
| `mdd_nondet` | D | [mdd_nondet](mdd_nondet.md) | **stub** | — | — | — |
| `regular` | D | [regular](regular.md) | reviewed | 0 | out of scope: index sets D_8, D_9 — the transition relation — are never defined b... | G7 |
| `regular_nfa` | D | [regular_nfa](regular_nfa.md) | **stub** | — | — | — |
| `regular_regexp` | D | [regular_regexp](regular_regexp.md) | **stub** | — | — | — |
| `strict_lex2` | D | [strict_lex2](strict_lex2.md) | **stub** | — | — | — |
| `table` | D | [table](table.md) | **stub** | 0 | 0 | — |
| `var_perm_sym` | D | [var_perm_sym](var_perm_sym.md) | **stub** | — | — | — |
| `var_sqr_sym` | D | [var_sqr_sym](var_sqr_sym.md) | **stub** | — | — | — |
| `among_fn` | unclassified | [among_fn](among_fn.md) | **stub** | — | — | — |
| `bin_packing_load_fn` | unclassified | [bin_packing_load_fn](bin_packing_load_fn.md) | **stub** | — | — | — |
| `count_fn` | unclassified | [count_fn](count_fn.md) | **stub** | — | — | — |
| `distribute_fn` | unclassified | [distribute_fn](distribute_fn.md) | **stub** | — | — | — |
| `global_cardinality_closed_fn` | unclassified | [global_cardinality_closed_fn](global_cardinality_closed_fn.md) | **stub** | — | — | — |
| `global_cardinality_fn` | unclassified | [global_cardinality_fn](global_cardinality_fn.md) | **stub** | — | — | — |
| `inverse_fn` | unclassified | [inverse_fn](inverse_fn.md) | **stub** | — | — | — |
| `nvalue_fn` | unclassified | [nvalue_fn](nvalue_fn.md) | **stub** | — | — | — |
| `range_fn` | unclassified | [range_fn](range_fn.md) | **stub** | — | — | — |
| `roots_fn` | unclassified | [roots_fn](roots_fn.md) | **stub** | — | — | — |
| `sort_fn` | unclassified | [sort_fn](sort_fn.md) | **stub** | — | — | — |
| `all_disjoint` | out of scope | [all_disjoint](all_disjoint.md) | **stub** | — | — | — |
| `arg_max` | out of scope | [arg_max](arg_max.md) | **stub** | — | — | — |
| `arg_min` | out of scope | [arg_min](arg_min.md) | **stub** | — | — | — |
| `at_most1` | out of scope | [at_most1](at_most1.md) | **stub** | — | — | — |
| `bin_packing` | out of scope | [bin_packing](bin_packing.md) | **stub** | — | — | — |
| `bin_packing_capa` | out of scope | [bin_packing_capa](bin_packing_capa.md) | **stub** | — | — | — |
| `bin_packing_load` | out of scope | [bin_packing_load](bin_packing_load.md) | **stub** | — | — | — |
| `bounded_path` | out of scope | [bounded_path](bounded_path.md) | **stub** | — | — | — |
| `circuit` | out of scope | [circuit](circuit.md) | **stub** | — | — | — |
| `circuit_opt` | out of scope | [circuit_opt](circuit_opt.md) | **stub** | — | — | — |
| `connected` | out of scope | [connected](connected.md) | **stub** | — | — | — |
| `dag` | out of scope | [dag](dag.md) | **stub** | — | — | — |
| `diffn` | out of scope | [diffn](diffn.md) | **stub** | — | — | — |
| `diffn_k` | out of scope | [diffn_k](diffn_k.md) | **stub** | — | — | — |
| `diffn_nonstrict` | out of scope | [diffn_nonstrict](diffn_nonstrict.md) | **stub** | — | — | — |
| `diffn_nonstrict_k` | out of scope | [diffn_nonstrict_k](diffn_nonstrict_k.md) | **stub** | — | — | — |
| `disjoint` | out of scope | [disjoint](disjoint.md) | **stub** | — | — | — |
| `geost` | out of scope | [geost](geost.md) | **stub** | — | — | — |
| `int_set_channel` | out of scope | [int_set_channel](int_set_channel.md) | **stub** | — | — | — |
| `inverse_set` | out of scope | [inverse_set](inverse_set.md) | **stub** | — | — | — |
| `link_set_to_booleans` | out of scope | [link_set_to_booleans](link_set_to_booleans.md) | **stub** | — | — | — |
| `network_flow` | out of scope | [network_flow](network_flow.md) | **stub** | — | — | — |
| `neural_net` | out of scope | [neural_net](neural_net.md) | **stub** | — | — | — |
| `partition_set` | out of scope | [partition_set](partition_set.md) | **stub** | — | — | — |
| `piecewise_linear` | out of scope | [piecewise_linear](piecewise_linear.md) | **stub** | — | — | — |
| `piecewise_linear_non_continuous` | out of scope | [piecewise_linear_non_continuous](piecewise_linear_non_continuous.md) | **stub** | — | — | — |
| `range` | out of scope | [range](range.md) | reviewed | 0 | out of scope: index sets D_5, D_6 are never defined by the printer (W1-T2); this ... | G8 |
| `reachable` | out of scope | [reachable](reachable.md) | **stub** | — | — | — |
| `roots` | out of scope | [roots](roots.md) | reviewed | 0 | out of scope: index sets D_5, D_6 are never defined by the printer (W1-T2); the s... | G8 |
| `steiner` | out of scope | [steiner](steiner.md) | **stub** | — | — | — |
| `subcircuit` | out of scope | [subcircuit](subcircuit.md) | **stub** | — | — | — |
| `subgraph` | out of scope | [subgraph](subgraph.md) | **stub** | — | — | — |
| `sum_set` | out of scope | [sum_set](sum_set.md) | **stub** | — | — | — |
| `tree` | out of scope | [tree](tree.md) | **stub** | — | — | — |
| `weighted_spanning_tree` | out of scope | [weighted_spanning_tree](weighted_spanning_tree.md) | **stub** | — | — | — |

## What this index cannot show

- **Whether a rule is right**, only whether the validator called it SOUND
  and MINIMAL at n,m <= 4 (`docs/VALIDATOR.md`). Sound and minimal is a
  floor, not strength -- see CLAUDE.md.
- **Calibration against a published rule** (agrees/weaker/stronger/
  incomparable/out of reach) -- that verdict lives in each entry's own
  "Calibration" field and is not re-derived here.
- **Anything about a stub beyond the machine-derived fields it
  carries.** A `**stub**` row means a file exists holding a tier, a
  `CHRISTMAS_LIST.md` line number, a solver class and a `\frac` count.
  It also means nobody has read the constraint. The entry column is not
  progress unless the kind column beside it says `reviewed`.
- **Entries that exist only as a claim.** This script trusts the
  filesystem (`catalog/*.md` existing) and `make validate`'s own output;
  it does not read entry prose for correctness.
- **A blocking gap for an entry that has no catalog/*.md yet.** The
  "blocking gap" column is only populated by grepping an *existing*
  entry for the phrase "blocked on G<n>"; a missing entry always shows
  — in that column even if a gap is already known informally.
  **And a stub never states one**, by design -- attributing a gap is a
  judgement -- so the column is empty for every one of them, whatever
  may already be known informally.
