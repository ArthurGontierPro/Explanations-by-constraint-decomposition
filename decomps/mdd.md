# mdd

**Signature.** `mdd(array[int] of var int: x, int: N, array[int] of int: level,
int: E, array[int] of int: from, array[int] of set of int: label, array[int] of int: to)` —
`x` spells out a root-to-sink path of the given multi-valued decision diagram.

**Shape: `EXT-3`** (`_shapes-ext.md`) — layered DAG with edge flow. Mechanically EXT-3 collapses
into `EXT-2b`: an MDD is a layered automaton whose state set may differ per layer. It is kept
separate only because `label`, `from` and `to` are three constant tables rather than one
transition function.

**E-code: E1 + E2**, agreeing with `CHRISTMAS_LIST.md` §5. E1 for the node and edge families,
E2 (gap **X2**, the index-dependent set form) for `label`/`from`/`to`. Gap **X7** applies: the
index families needed are position, value, node and edge.

**Auxiliaries — and D-0004 licenses them explicitly.** D-0004 names `mdd` in its own exception
clause: "Some constraints (`sliding_sum`, `mdd`) have no known auxiliary-free decomposition.
Those entries record their auxiliaries' definitions alongside the rule." So this entry is
allowed to leak, and the obligation is to *print the definitions*:

- `N_{i,v}` — "node `v` at layer `i` lies on some surviving root-to-sink path prefix";
- `Ed_{i,e}` — "edge `e` out of layer `i` is still usable".

A reader of the catalog sees premises about `N_{i,v}` — a node they did not write, though one
they did draw, which is the honest difference from `regular`'s invented state.

**M-1's criterion.** Fails under the sharpened reading, for exactly `regular`'s reason: the
state predicate of a node is the set of prefixes reaching it, a DNF of conjunctions, not a
clause. It passes M-1's criterion *as written* only because "finite disjunction over user
literals" is vacuous over finite domains. See `_shapes-ext.md`.

**The gap that actually blocks this entry is not E1 or E2 (gap X8).** The published MDD
explanation — Gange, Stuckey & Szymanek 2011, *MDD propagators with explanation*, which
`CHRISTMAS_LIST.md` §5 records as subsuming `table`, `regular` and set/multiset constraints —
justifies a value removal by a **reachability** argument over the diagram and reports it as a set
of `X` literals. Deriving that from EXT-3 requires resolving away every `N`/`Ed` pivot along all
paths. The generator's pipeline is AND/OR traversal with cycle detection (`find`) plus DNF
flattening (`an`); it has no resolution or reachability pass. So `mdd` is *expressible* at
E1 + E2 and its good explanation is not *derivable*, which is closer in character to E4/E6 than
to E1/E2. Nothing in `CHRISTMAS_LIST.md`'s E1+E2 pricing reflects this.
