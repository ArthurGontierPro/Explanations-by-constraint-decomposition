<!--
  catalog/INDEX.md -- GENERATED. Do not hand-edit.
  Regenerate with: python3 tools/catalog_index.py
  Generated: 2026-09-22
  Source: tools/catalog_index.py (reads tools/mzn_coverage.py --json,
  catalog/*.md, cata/*.tex, and `make validate`'s output; see that
  script's ALIAS table for the cata/catalog basename <-> MiniZinc
  global-name mapping).
-->

# Catalog index

One row per MiniZinc release global (118 total, from `tools/mzn_coverage.py`, release 2.10.1). Every count below is computed on
every regeneration, never hand-typed -- see the header comment for how.

## Summary

- catalog entries: **118 / 118** (118 reviewed, 0 stubs)
  A **stub** is a file `tools/catalog_stub.py` generated: it carries a
  machine-derived tier, citation line, solver class and rule count, and
  the words `not reviewed` in every field that would be a judgement.
  A **reviewed** entry is one a person wrote against `catalog/TEMPLATE.md`.
  **The entry count is never printed without this split** -- 118 / 118 with
  0 of them stubs is a claim about filenames, not about work done.
- have any generated rule (`cata/*.tex`, `\frac` count > 0): **11 / 118**
- have any validated (SOUND and MINIMAL) rule: **6 / 118**

| tier | globals | entries | reviewed | stubs | generated rules | validated |
|---|---:|---:|---:|---:|---:|---:|
| A | 43 | 43 | 43 | 0 | 8 | 4 |
| B | 8 | 8 | 8 | 0 | 0 | 0 |
| C | 9 | 9 | 9 | 0 | 1 | 1 |
| D | 19 | 19 | 19 | 0 | 2 | 1 |
| unclassified | 11 | 11 | 11 | 0 | 0 | 0 |
| out of scope | 28 | 28 | 28 | 0 | 0 | 0 |

## Warnings from this run

- no alias entry at all for basename 'alldifferent_except' (add it to ALIAS in tools/catalog_index.py)
- UNMATCHED: 'atleastnvalues' has no corresponding release global (see ALIAS comment for why)
- UNMATCHED: 'atmostnvalues' has no corresponding release global (see ALIAS comment for why)
- UNMATCHED: 'sum' has no corresponding release global (see ALIAS comment for why)

## All 118 globals

| constraint | tier | catalog entry | kind | generated rules | validated | blocking gap |
|---|---|---|---|---:|---:|---|
| `all_different_except` | A | [all_different_except](all_different_except.md) | reviewed | 1 | — | G8 |
| `all_different_except_0` | A | [all_different_except_0](all_different_except_0.md) | reviewed | — | — | G8 |
| `all_equal` | A | [allequal](allequal.md) | reviewed | 2 | 2 | — |
| `alternative` | A | [alternative](alternative.md) | reviewed | — | — | G3 |
| `among` | A | [among](among.md) | reviewed | 2 | out of scope | G8 |
| `arg_sort` | A | [arg_sort](arg_sort.md) | reviewed | — | — | G10 |
| `arg_val` | A | [arg_val](arg_val.md) | reviewed | — | — | — |
| `at_least` | A | [at_least](at_least.md) | reviewed | — | — | G1 |
| `at_most` | A | [at_most](at_most.md) | reviewed | 1 | — | G1 |
| `bin_packing` | A | [bin_packing](bin_packing.md) | reviewed | — | — | G11 |
| `bin_packing_capa` | A | [bin_packing_capa](bin_packing_capa.md) | reviewed | — | — | G11 |
| `bin_packing_load` | A | [bin_packing_load](bin_packing_load.md) | reviewed | — | — | G11 |
| `count` | A | [count](count.md) | reviewed | — | — | G8 |
| `decreasing` | A | [decreasing](decreasing.md) | reviewed | 2 | 2 | — |
| `diffn` | A | [diffn](diffn.md) | reviewed | — | — | G3 |
| `diffn_k` | A | [diffn_k](diffn_k.md) | reviewed | — | — | G3 |
| `diffn_nonstrict` | A | [diffn_nonstrict](diffn_nonstrict.md) | reviewed | — | — | G3 |
| `diffn_nonstrict_k` | A | [diffn_nonstrict_k](diffn_nonstrict_k.md) | reviewed | — | — | G3 |
| `distribute` | A | [distribute](distribute.md) | reviewed | — | — | G4 |
| `element` | A | [element](element.md) | reviewed | 6 | 2 | — |
| `exactly` | A | [exactly](exactly.md) | reviewed | — | — | G1 |
| `increasing` | A | [increasing](increasing.md) | reviewed | 2 | 2 | — |
| `knapsack` | A | [knapsack](knapsack.md) | reviewed | — | — | G11 |
| `lex_chain_greater` | A | [lex_chain_greater](lex_chain_greater.md) | reviewed | — | — | G3 |
| `lex_chain_greatereq` | A | [lex_chain_greatereq](lex_chain_greatereq.md) | reviewed | — | — | G3 |
| `lex_chain_greatereq_orbitope` | A | [lex_chain_greatereq_orbitope](lex_chain_greatereq_orbitope.md) | reviewed | — | — | G3 |
| `lex_chain_less` | A | [lex_chain_less](lex_chain_less.md) | reviewed | — | — | G3 |
| `lex_chain_lesseq` | A | [lex_chain_lesseq](lex_chain_lesseq.md) | reviewed | — | — | G3 |
| `lex_chain_lesseq_orbitope` | A | [lex_chain_lesseq_orbitope](lex_chain_lesseq_orbitope.md) | reviewed | — | — | G3 |
| `member` | A | [member](member.md) | reviewed | — | — | G3 |
| `nvalue` | A | [nvalues](nvalues.md) | reviewed | 5 | 0 | — |
| `seq_precede_chain` | A | [seq_precede_chain](seq_precede_chain.md) | reviewed | — | — | G17 |
| `sliding_among` | A | [sliding_among](sliding_among.md) | reviewed | — | — | G8 |
| `sliding_sum` | A | [sliding_sum](sliding_sum.md) | reviewed | — | — | G12 |
| `sort` | A | [sort](sort.md) | reviewed | — | — | G10 |
| `span` | A | [span](span.md) | reviewed | — | — | G3 |
| `strictly_decreasing` | A | [strictly_decreasing](strictly_decreasing.md) | reviewed | — | — | — |
| `strictly_increasing` | A | [strictly_increasing](strictly_increasing.md) | reviewed | — | — | — |
| `sum_pred` | A | [sum_pred](sum_pred.md) | reviewed | — | — | G14 |
| `symmetric_all_different` | A | [symmetric_all_different](symmetric_all_different.md) | reviewed | — | — | G10 |
| `write` | A | [write](write.md) | reviewed | — | — | G18 |
| `writes` | A | [writes](writes.md) | reviewed | — | — | G18 |
| `writes_seq` | A | [writes_seq](writes_seq.md) | reviewed | — | — | G18 |
| `inverse` | B | [inverse](inverse.md) | reviewed | — | — | — |
| `inverse_in_range` | B | [inverse_in_range](inverse_in_range.md) | reviewed | — | — | — |
| `lex_greater` | B | [lex_greater](lex_greater.md) | reviewed | — | — | G3 |
| `lex_greatereq` | B | [lex_greatereq](lex_greatereq.md) | reviewed | — | — | G3 |
| `maximum` | B | [maximum](maximum.md) | reviewed | — | — | G3 |
| `minimum` | B | [minimum](minimum.md) | reviewed | — | — | G3 |
| `value_precede` | B | [value_precede](value_precede.md) | reviewed | — | — | G17 |
| `value_precede_chain` | B | [value_precede_chain](value_precede_chain.md) | reviewed | — | — | G7 |
| `cost_mdd` | C | [cost_mdd](cost_mdd.md) | reviewed | — | — | G15 |
| `cost_regular` | C | [cost_regular](cost_regular.md) | reviewed | — | — | G15 |
| `cumulative_opt` | C | [cumulative_opt](cumulative_opt.md) | reviewed | — | — | G2 |
| `cumulatives` | C | [cumulatives](cumulatives.md) | reviewed | — | — | G14 |
| `cumulatives_opt` | C | [cumulatives_opt](cumulatives_opt.md) | reviewed | — | — | G14 |
| `global_cardinality` | C | [gcc](gcc.md) | reviewed | 4 | 4 | — |
| `global_cardinality_closed` | C | [global_cardinality_closed](global_cardinality_closed.md) | reviewed | — | — | G8 |
| `global_cardinality_low_up` | C | [global_cardinality_low_up](global_cardinality_low_up.md) | reviewed | — | — | G1 |
| `global_cardinality_low_up_closed` | C | [global_cardinality_low_up_closed](global_cardinality_low_up_closed.md) | reviewed | — | — | G1 |
| `all_different` | D | [alldifferent](alldifferent.md) | reviewed | 1 | 1 | — |
| `cumulative` | D | [cumulative](cumulative.md) | reviewed | 2 | out of scope | — |
| `disjunctive` | D | [disjunctive](disjunctive.md) | reviewed | — | — | — |
| `disjunctive_opt` | D | [disjunctive_opt](disjunctive_opt.md) | reviewed | — | — | G2 |
| `disjunctive_strict` | D | [disjunctive_strict](disjunctive_strict.md) | reviewed | — | — | G1 |
| `disjunctive_strict_opt` | D | [disjunctive_strict_opt](disjunctive_strict_opt.md) | reviewed | — | — | G2 |
| `lex2` | D | [lex2](lex2.md) | reviewed | — | — | G3 |
| `lex2_strict` | D | [lex2_strict](lex2_strict.md) | reviewed | — | — | G3 |
| `lex_less` | D | [lex_less](lex_less.md) | reviewed | — | — | G3 |
| `lex_lesseq` | D | [lex_lesseq](lex_lesseq.md) | reviewed | — | — | G3 |
| `mdd` | D | [mdd](mdd.md) | reviewed | — | — | G7 |
| `mdd_nondet` | D | [mdd_nondet](mdd_nondet.md) | reviewed | — | — | G7 |
| `regular` | D | [regular](regular.md) | reviewed | 0 | out of scope | G7 |
| `regular_nfa` | D | [regular_nfa](regular_nfa.md) | reviewed | — | — | G7 |
| `regular_regexp` | D | [regular_regexp](regular_regexp.md) | reviewed | — | — | G7 |
| `strict_lex2` | D | [strict_lex2](strict_lex2.md) | reviewed | — | — | G3 |
| `table` | D | [table](table.md) | reviewed | 0 | 0 | G6 |
| `var_perm_sym` | D | [var_perm_sym](var_perm_sym.md) | reviewed | — | — | G3 |
| `var_sqr_sym` | D | [var_sqr_sym](var_sqr_sym.md) | reviewed | — | — | G3 |
| `among_fn` | unclassified | [among_fn](among_fn.md) | reviewed | — | — | G8 |
| `bin_packing_load_fn` | unclassified | [bin_packing_load_fn](bin_packing_load_fn.md) | reviewed | — | — | G11 |
| `count_fn` | unclassified | [count_fn](count_fn.md) | reviewed | — | — | G8 |
| `distribute_fn` | unclassified | [distribute_fn](distribute_fn.md) | reviewed | — | — | G4 |
| `global_cardinality_closed_fn` | unclassified | [global_cardinality_closed_fn](global_cardinality_closed_fn.md) | reviewed | — | — | G8 |
| `global_cardinality_fn` | unclassified | [global_cardinality_fn](global_cardinality_fn.md) | reviewed | — | — | — |
| `inverse_fn` | unclassified | [inverse_fn](inverse_fn.md) | reviewed | — | — | — |
| `nvalue_fn` | unclassified | [nvalue_fn](nvalue_fn.md) | reviewed | — | — | — |
| `range_fn` | unclassified | [range_fn](range_fn.md) | reviewed | — | — | G8 |
| `roots_fn` | unclassified | [roots_fn](roots_fn.md) | reviewed | — | — | G8 |
| `sort_fn` | unclassified | [sort_fn](sort_fn.md) | reviewed | — | — | — |
| `all_disjoint` | out of scope | [all_disjoint](all_disjoint.md) | reviewed | — | — | — |
| `arg_max` | out of scope | [arg_max](arg_max.md) | reviewed | — | — | — |
| `arg_min` | out of scope | [arg_min](arg_min.md) | reviewed | — | — | — |
| `at_most1` | out of scope | [at_most1](at_most1.md) | reviewed | — | — | — |
| `bounded_path` | out of scope | [bounded_path](bounded_path.md) | reviewed | — | — | — |
| `circuit` | out of scope | [circuit](circuit.md) | reviewed | — | — | — |
| `circuit_opt` | out of scope | [circuit_opt](circuit_opt.md) | reviewed | — | — | — |
| `connected` | out of scope | [connected](connected.md) | reviewed | — | — | — |
| `dag` | out of scope | [dag](dag.md) | reviewed | — | — | — |
| `disjoint` | out of scope | [disjoint](disjoint.md) | reviewed | — | — | — |
| `geost` | out of scope | [geost](geost.md) | reviewed | — | — | — |
| `int_set_channel` | out of scope | [int_set_channel](int_set_channel.md) | reviewed | — | — | — |
| `inverse_set` | out of scope | [inverse_set](inverse_set.md) | reviewed | — | — | — |
| `link_set_to_booleans` | out of scope | [link_set_to_booleans](link_set_to_booleans.md) | reviewed | — | — | — |
| `network_flow` | out of scope | [network_flow](network_flow.md) | reviewed | — | — | — |
| `neural_net` | out of scope | [neural_net](neural_net.md) | reviewed | — | — | — |
| `partition_set` | out of scope | [partition_set](partition_set.md) | reviewed | — | — | — |
| `piecewise_linear` | out of scope | [piecewise_linear](piecewise_linear.md) | reviewed | — | — | — |
| `piecewise_linear_non_continuous` | out of scope | [piecewise_linear_non_continuous](piecewise_linear_non_continuous.md) | reviewed | — | — | — |
| `range` | out of scope | [range](range.md) | reviewed | 0 | out of scope | G8 |
| `reachable` | out of scope | [reachable](reachable.md) | reviewed | — | — | — |
| `roots` | out of scope | [roots](roots.md) | reviewed | 0 | out of scope | G8 |
| `steiner` | out of scope | [steiner](steiner.md) | reviewed | — | — | — |
| `subcircuit` | out of scope | [subcircuit](subcircuit.md) | reviewed | — | — | — |
| `subgraph` | out of scope | [subgraph](subgraph.md) | reviewed | — | — | — |
| `sum_set` | out of scope | [sum_set](sum_set.md) | reviewed | — | — | — |
| `tree` | out of scope | [tree](tree.md) | reviewed | — | — | — |
| `weighted_spanning_tree` | out of scope | [weighted_spanning_tree](weighted_spanning_tree.md) | reviewed | — | — | — |

## What this index cannot show

- **Whether a rule is right**, only whether the validator called it SOUND
  and MINIMAL at n,m in {2,3,4} -- n=1 and m=1 are NOT checked
  (`docs/VALIDATOR.md`, W1-T19). Sound and minimal is a
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
