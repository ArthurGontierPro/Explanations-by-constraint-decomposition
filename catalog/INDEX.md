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

- catalog entries: **3 / 118**
- have any generated rule (`cata/*.tex`, `\frac` count > 0): **8 / 118**
- have any validated (SOUND and MINIMAL) rule: **6 / 118**

| tier | globals | catalog entry | generated rules | validated |
|---|---:|---:|---:|---:|
| A | 36 | 0 | 5 | 4 |
| B | 8 | 0 | 0 | 0 |
| C | 9 | 1 | 1 | 1 |
| D | 19 | 2 | 2 | 1 |
| unclassified | 11 | 0 | 0 | 0 |
| out of scope | 35 | 0 | 0 | 0 |

## Warnings from this run

- UNMATCHED: 'atleastnvalues' has no corresponding release global (see ALIAS comment for why)
- UNMATCHED: 'atmostnvalues' has no corresponding release global (see ALIAS comment for why)
- UNMATCHED: 'sum' has no corresponding release global (see ALIAS comment for why)

## All 118 globals

| constraint | tier | catalog entry | generated rules | validated | blocking gap |
|---|---|---|---:|---:|---|
| `all_different_except` | A | — | — | — | — |
| `all_different_except_0` | A | — | — | — | — |
| `all_equal` | A | — | 2 | 2 | — |
| `alternative` | A | — | — | — | — |
| `among` | A | — | 0 | out of scope: index set D_4 is never defined by the printer (W1-T2), AND among's ... | — |
| `arg_sort` | A | — | — | — | — |
| `arg_val` | A | — | — | — | — |
| `at_least` | A | — | — | — | — |
| `at_most` | A | — | — | — | — |
| `count` | A | — | — | — | — |
| `decreasing` | A | — | 2 | 2 | — |
| `distribute` | A | — | — | — | — |
| `element` | A | — | 6 | 2 | — |
| `exactly` | A | — | — | — | — |
| `increasing` | A | — | 2 | 2 | — |
| `knapsack` | A | — | — | — | — |
| `lex_chain_greater` | A | — | — | — | — |
| `lex_chain_greatereq` | A | — | — | — | — |
| `lex_chain_greatereq_orbitope` | A | — | — | — | — |
| `lex_chain_less` | A | — | — | — | — |
| `lex_chain_lesseq` | A | — | — | — | — |
| `lex_chain_lesseq_orbitope` | A | — | — | — | — |
| `member` | A | — | — | — | — |
| `nvalue` | A | — | 5 | 0 | — |
| `seq_precede_chain` | A | — | — | — | — |
| `sliding_among` | A | — | — | — | — |
| `sliding_sum` | A | — | — | — | — |
| `sort` | A | — | — | — | — |
| `span` | A | — | — | — | — |
| `strictly_decreasing` | A | — | — | — | — |
| `strictly_increasing` | A | — | — | — | — |
| `sum_pred` | A | — | — | — | — |
| `symmetric_all_different` | A | — | — | — | — |
| `write` | A | — | — | — | — |
| `writes` | A | — | — | — | — |
| `writes_seq` | A | — | — | — | — |
| `inverse` | B | — | — | — | — |
| `inverse_in_range` | B | — | — | — | — |
| `lex_greater` | B | — | — | — | — |
| `lex_greatereq` | B | — | — | — | — |
| `maximum` | B | — | — | — | — |
| `minimum` | B | — | — | — | — |
| `value_precede` | B | — | — | — | — |
| `value_precede_chain` | B | — | — | — | — |
| `cost_mdd` | C | — | — | — | — |
| `cost_regular` | C | — | — | — | — |
| `cumulative_opt` | C | — | — | — | — |
| `cumulatives` | C | — | — | — | — |
| `cumulatives_opt` | C | — | — | — | — |
| `global_cardinality` | C | [gcc](gcc.md) | 4 | 4 | — |
| `global_cardinality_closed` | C | — | — | — | — |
| `global_cardinality_low_up` | C | — | — | — | — |
| `global_cardinality_low_up_closed` | C | — | — | — | — |
| `all_different` | D | [alldifferent](alldifferent.md) | 1 | 1 | — |
| `cumulative` | D | [cumulative](cumulative.md) | 2 | out of scope: the durations d_i appear as uninterpreted symbols inside index equa... | — |
| `disjunctive` | D | — | — | — | — |
| `disjunctive_opt` | D | — | — | — | — |
| `disjunctive_strict` | D | — | — | — | — |
| `disjunctive_strict_opt` | D | — | — | — | — |
| `lex2` | D | — | — | — | — |
| `lex2_strict` | D | — | — | — | — |
| `lex_less` | D | — | — | — | — |
| `lex_lesseq` | D | — | — | — | — |
| `mdd` | D | — | — | — | — |
| `mdd_nondet` | D | — | — | — | — |
| `regular` | D | — | 0 | out of scope: index sets D_8, D_9 — the transition relation — are never defined b... | — |
| `regular_nfa` | D | — | — | — | — |
| `regular_regexp` | D | — | — | — | — |
| `strict_lex2` | D | — | — | — | — |
| `table` | D | — | 0 | 0 | — |
| `var_perm_sym` | D | — | — | — | — |
| `var_sqr_sym` | D | — | — | — | — |
| `among_fn` | unclassified | — | — | — | — |
| `bin_packing_load_fn` | unclassified | — | — | — | — |
| `count_fn` | unclassified | — | — | — | — |
| `distribute_fn` | unclassified | — | — | — | — |
| `global_cardinality_closed_fn` | unclassified | — | — | — | — |
| `global_cardinality_fn` | unclassified | — | — | — | — |
| `inverse_fn` | unclassified | — | — | — | — |
| `nvalue_fn` | unclassified | — | — | — | — |
| `range_fn` | unclassified | — | — | — | — |
| `roots_fn` | unclassified | — | — | — | — |
| `sort_fn` | unclassified | — | — | — | — |
| `all_disjoint` | out of scope | — | — | — | — |
| `arg_max` | out of scope | — | — | — | — |
| `arg_min` | out of scope | — | — | — | — |
| `at_most1` | out of scope | — | — | — | — |
| `bin_packing` | out of scope | — | — | — | — |
| `bin_packing_capa` | out of scope | — | — | — | — |
| `bin_packing_load` | out of scope | — | — | — | — |
| `bounded_path` | out of scope | — | — | — | — |
| `circuit` | out of scope | — | — | — | — |
| `circuit_opt` | out of scope | — | — | — | — |
| `connected` | out of scope | — | — | — | — |
| `dag` | out of scope | — | — | — | — |
| `diffn` | out of scope | — | — | — | — |
| `diffn_k` | out of scope | — | — | — | — |
| `diffn_nonstrict` | out of scope | — | — | — | — |
| `diffn_nonstrict_k` | out of scope | — | — | — | — |
| `disjoint` | out of scope | — | — | — | — |
| `geost` | out of scope | — | — | — | — |
| `int_set_channel` | out of scope | — | — | — | — |
| `inverse_set` | out of scope | — | — | — | — |
| `link_set_to_booleans` | out of scope | — | — | — | — |
| `network_flow` | out of scope | — | — | — | — |
| `neural_net` | out of scope | — | — | — | — |
| `partition_set` | out of scope | — | — | — | — |
| `piecewise_linear` | out of scope | — | — | — | — |
| `piecewise_linear_non_continuous` | out of scope | — | — | — | — |
| `range` | out of scope | — | 0 | out of scope: index sets D_5, D_6 are never defined by the printer (W1-T2); this ... | — |
| `reachable` | out of scope | — | — | — | — |
| `roots` | out of scope | — | 0 | out of scope: index sets D_5, D_6 are never defined by the printer (W1-T2); the s... | — |
| `steiner` | out of scope | — | — | — | — |
| `subcircuit` | out of scope | — | — | — | — |
| `subgraph` | out of scope | — | — | — | — |
| `sum_set` | out of scope | — | — | — | — |
| `tree` | out of scope | — | — | — | — |
| `weighted_spanning_tree` | out of scope | — | — | — | — |

## What this index cannot show

- **Whether a rule is right**, only whether the validator called it SOUND
  and MINIMAL at n,m <= 4 (`docs/VALIDATOR.md`). Sound and minimal is a
  floor, not strength -- see CLAUDE.md.
- **Calibration against a published rule** (agrees/weaker/stronger/
  incomparable/out of reach) -- that verdict lives in each entry's own
  "Calibration" field and is not re-derived here.
- **Entries that exist only as a claim.** This script trusts the
  filesystem (`catalog/*.md` existing) and `make validate`'s own output;
  it does not read entry prose for correctness.
- **A blocking gap for an entry that has no catalog/*.md yet.** The
  "blocking gap" column is only populated by grepping an *existing*
  entry for the phrase "blocked on G<n>"; a missing entry always shows
  — in that column even if a gap is already known informally.
