# Family index — maths and misc (`CHRISTMAS_LIST.md` §11)

The last in-scope family. In-scope constraints get a spec file; out-of-scope ones get one line
here and no spec, per the convention the earlier waves used.

## In scope — spec files in this directory

| constraint | shape (`_shapes.md`) | E-code | file |
|---|---|---|---|
| `sum_pred` | **S12** | **E9** (was E3 — D-0011) | `sum_pred.md` |
| `write`, `writes`, `writes_seq` | **S6** | **E2**, plus new gap **G18** | `write.md` |
| `edit_distance` | **S8 + S11** | **E1 + E2 + E9** | `edit_distance.md` |
| `cost_mdd` | **S8 + S11** | **E1 + E2 + E9** | `cost_mdd.md` (wave two, §5) |

`cost_mdd` is listed in §11 as well as §5 and already has its spec; it is not re-specified here.

## Out of scope — one line each, no spec

- `piecewise_linear`, `piecewise_linear_non_continuous` — float-valued breakpoints, **E7**.
  `CHRISTMAS_LIST.md`'s own ranking declares E6/E7 out of scope.
- `neural_net` — float weights and activations, **E7**. Same declaration.
- `*_fn` functional variants — `among_fn`, `count_fn`, `nvalue_fn`, `range_fn`, `roots_fn`,
  `sort_fn`, `inverse_fn`, `distribute_fn`, `global_cardinality_fn`,
  `global_cardinality_closed_fn`, `bin_packing_load_fn`. **Not separate constraints**: each
  calls its own predicate form, which is specified elsewhere in this directory (or, for
  `distribute`/`global_cardinality`/`bin_packing*`, is outside this wave's scope). No shape of
  their own, no gap of their own.

## What §11 added to the gap list

One new gap, **G18** (`docs/DECOMP_FORMAT_NOTES.md`), from `write`/`writes`/`writes_seq`:
a universally quantified array-to-array channel whose index set excludes a position named by a
*decision variable*. G8 covers a constant exclusion, G14 covers a variable-determined
*summation* extent; neither covers this. Nothing else in §11 produced a gap that the first ten
sections had not already produced — `sum_pred` lands on G11/G12/G13 (and G14 under one reading
of its signature) and `edit_distance` lands on G16/G12/G13/G17, all pre-existing.
