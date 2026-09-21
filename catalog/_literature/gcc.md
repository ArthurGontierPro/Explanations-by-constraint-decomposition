# `gcc` / `global_cardinality` — published explanation rules

## Citation

**Nicholas Downing, Thibaut Feydy, Peter J. Stuckey. *Explaining flow-based propagation.*
Proc. CPAIOR 2012, LNCS 7298:146-162, Springer.
DOI [10.1007/978-3-642-29828-8_10](https://doi.org/10.1007/978-3-642-29828-8_10).**

Read as the authors' preprint,
<https://people.eng.unimelb.edu.au/pstuckey/papers/explaining_flow.pdf> (fetched 2026-09-21;
2.4 MB, 19 pages). The preprint carries **no printed page numbers**, so every page pointer
below is a *preprint PDF page index*. LNCS pagination 146-162 not cross-checked.
Repo index: `CHRISTMAS_LIST.md:127`, `CHRISTMAS_LIST.md:267`.

**Headline, `QUOTED`, abstract (preprint p.1):** the paper presents "two new generic
flow-based propagators" with "the addition of explanation capability", and says these "can
efficiently replace specialized versions, in particular for gcc and sequence".

---

## The structural fact the catalog most needs

**There is no `gcc`-specific explanation rule in this paper.** `gcc` is handled by *encoding
it as a flow network* (Régin's encoding) and then explaining the **generic** network-flow
propagator. Everything below is therefore stated over flow variables `f_uv`, with `gcc`
appearing only through the identification of arc flows with domain literals. `QUOTED` — see
the encoding sentence next.

**The encoding.** `QUOTED`, §3 Example 1, preprint p.3:

> "This illustrates Régin's [18] encoding of the constraint `gcc([x, y], [1..2, 0..1])`, with
> `x, y = 1` (day) or `2` (night) being the shift worked by Xavier (`x`) and Yasmin (`y`).
> Using the coercion function `bool2int`, the 'working arc' flows are expressed directly as
> domain literals which are intrinsic in a Lazy Clause Generation solver, e.g.
> `f_xd = bool2int(⟦x = 1⟧)`, where `bool2int(false) = 0` and `bool2int(true) = 1`."

So: `f_{i,v} = bool2int([x_i = v])` for the variable-value arcs, and the `f_{v,t}` arcs carry
the cardinality counts `c_v`, bounded by the `gcc` cover bounds.

**Flow conservation for a cut.** `QUOTED`, §4.1, preprint p.6, **equation (2)**. Summing the
flow-conservation equations (1) over the nodes `n ∈ C` gives

```
Σ_{(u,v) leaves C} f_uv  −  Σ_{(u,v) enters C} f_uv  =  Σ_{n∈C} s_n                    (2)
```

---

## Rule 1 — failure

**Paper's form.** `QUOTED`, §4.1 "Explaining failure", preprint pp.4-6:

> "Suppose there is no feasible solution. Let `C`, the 'cut', be the set of nodes searched for
> an augmenting path. It contains node(s) in excess but none in deficit. Then according to the
> current flow bounds, more flow enters `C` than can leave it, taking into account the arcs
> crossing `C` and the net supply/demand of `C`."

and then, `QUOTED`, preprint p.6:

> "Given `C` that proves infeasibility, we explain equation (2) as a linear constraint, using
> a standard linear explanation for `LHS ≤ RHS` [16]. Even if outflows are at minimum for
> outgoing arcs and inflows are at maximum for incoming arcs, minimizing the net flow leaving
> the cut, the net flow is still greater than the net supply/demand of the cut. **The
> explanation of failure is the conjunction of literals `⟦f_uv ≥ l_uv⟧` for outflows and
> `⟦f_uv ≤ u_uv⟧` for inflows, using current `l`, `u`.** Similar explanations were proposed by
> Rochart [20]. For the special case of gcc they reduce to those proposed by Katsirelos [12].
> We can improve the base explanation by using lifting methods [1, 5, 16] to create a stronger
> explanation."

(Boldface added here; the emphasis is not the paper's.)

**As a rule:**

```
⟦f_uv ≥ l_uv⟧  for each arc (u,v) leaving C
⟦f_uv ≤ u_uv⟧  for each arc (u,v) entering C
----------------------------------------------- ⊢
false
```

**Worked instance**, §4.1 Example 3, preprint p.6, `QUOTED`. With `C = {x, n, y}`:
"Cut-conservation (2) requires `bool2int(⟦x = 1⟧) + bool2int(⟦y = 1⟧) + f_nt = 2`,
unachievable since both literals are false and `f_nt ≤ 1`. Hence the network flow propagator
fails with nogood"

```
[x ≠ 1] ∧ [y ≠ 1] ∧ [f_nt ≤ 1] → false
```

Note the nogood mixes **user-variable literals** (`[x ≠ 1]`) with **flow-variable literals**
(`[f_nt ≤ 1]`) — the latter is a cardinality-count literal in `gcc` terms.

---

## Rule 2 — pruning

**Paper's form.** `QUOTED`, §4.2 "Explaining pruning", preprint pp.6-7:

> "Régin describes a method based on Strongly Connected Components (SCCs) for gcc constraints
> [18], which we generalize to any flow network to find all arcs fixed at a bound, that is
> `f_uv = l_uv` (resp. `u_uv`) which cannot increase (resp. decrease). For Boolean flow
> variables, bound-tightening implies fixing at a bound and vice versa, giving
> bounds-consistency on Boolean-valued arcs."

> "An arc `u → v` with `u, v` in different SCCs can never be augmented since by definition `u`
> is not reachable again from `v`."

> "**The explanation for pruning is the same as for failure, except that an SCC is used as the
> cut-set `C` instead of an infeasible set.** Once again we treat equation (2) as a linear '≤'
> constraint. This relies on the SCC acting as a 'trap' for incoming flow, to prune an
> incoming flow the bounds on outgoing flows must be tight."

**As a rule:**

```
⟦f_uv ≥ l_uv⟧  for each arc (u,v) leaving the SCC C
⟦f_uv ≤ u_uv⟧  for each arc (u,v) entering C, other than the one being pruned
----------------------------------------------------------------------------- ⊢
the pruned bound on the arc being pruned
```

**Worked instance — and this is the one the catalog should quote**, §4.2 Example 4,
preprint p.7, `QUOTED`:

> "Consider `alldifferent(x1, x2, x3)`, expressed as the usual gcc network of
> `gcc([x1, x2, x3], [c1, c2, c3, c4])` where `ci ∈ 0..1`. If `x1 ∈ {1,2}`, `x2 ∈ {2,3}`,
> `x3 ∈ {2,3,4}`, then a solution is `x1 = 1, x2 = 2, x3 = 3` ... Due to the cycle
> `t → 1 → x1 → 2 → x2 → 3 → x3 → 4 → t` every node is reachable from each other, the entire
> graph is a single SCC, and no pruning is possible.
> Now suppose `x3 ≠ 4` ... Then the arc `x1 → 2` may be pruned due to cut-conservation (2) for
> SCC #1: `bool2int(⟦x3 = 4⟧) + c2 + c3 − bool2int(⟦x1 = 2⟧) = 2` and hence
> `bool2int(⟦x1 = 2⟧) = 0` since `⟦x3 = 4⟧ = false`, `c2 ≤ 1`, and `c3 ≤ 1`. The explanation is

```
[x3 ≠ 4] ∧ [c2 ≤ 1] ∧ [c3 ≤ 1] → [x1 ≠ 2]
```

> or after removing redundant bounds `[x3 ≠ 4] → [x1 ≠ 2]`. Having pruned all arcs leaving
> SCC #2, that SCC is closed, allowing the arc `x1 → 1` to be fixed to true using `[x1 ≠ 2]`
> as justification and so on."

This makes the vocabulary question concrete: the premises are **user-variable literals**
(`[x3 ≠ 4]`) **plus the cardinality variables of the `gcc` signature** (`[c2 ≤ 1]`,
`[c3 ≤ 1]`). The `c_j` are arguments of `gcc`, not encoding auxiliaries — but for the
`alldifferent` instance they are auxiliaries introduced by the reduction to `gcc`.
`COMPARISON`.

---

## Translation to this repo's notation

Rule 2 translates **only as an instance**, never as a schema:

```
X_3 ≠ 4,  C_2 ≤ 1,  C_3 ≤ 1
------------------------------- ⊢        (AC)
X_1 ≠ 2
```

The general rule does **not** translate. Its quantifier is "over the arcs crossing an SCC of
the residual graph of the current flow", and:

1. There is no index-set expression for "the arcs crossing SCC `C`". The repo's printer has
   `⟦1,n⟧`, `⟦1,m⟧` and an undefined `D_k` beyond (`CLAUDE.md`, "Traps"); `C` is not a
   subscript range, it is the output of Tarjan's algorithm on a graph that exists only at
   propagation time.
2. The premise *polarity* depends on arc direction relative to the cut (`≥ l` for outflows,
   `≤ u` for inflows). Direction is a property of the run-time residual graph, which flips
   arcs as flows hit their bounds (§3.1, preprint p.3). A schema over indices has no such
   notion.
3. The rule is derived by **treating equation (2) as a linear constraint and applying a linear
   propagator's explanation to it** — an explanation *of an explanation*. The repo's engine
   explains a fixed decomposition, not a linear constraint synthesised per propagation.

`COMPARISON` for all three.

---

## Answers to the four catalog questions

**What event is explained?** Both a failure (§4.1) and a bound change / value removal (§4.2,
which for Boolean arcs is the same thing — `QUOTED`: "For Boolean flow variables,
bound-tightening implies fixing at a bound and vice versa"). The min-cost extension (§6) also
explains **fathoming** against an objective bound, which has no analogue in this repo at all.
`QUOTED`, §6.2, preprint p.9.

**Premises' vocabulary?** **Flow variables `f_uv`.** These are *partly* user variables — the
paper identifies `f_{i,v}` with the LCG literal `[x_i = v]`, so those premises are genuinely
over `x` — and *partly* the cardinality counts `c_j`, which for `gcc` are signature arguments
and for `alldifferent` are introduced by the reduction. `QUOTED` (Example 1 for the
identification, Example 4 for both kinds appearing in one nogood).

**Minimal / strongest?** **No, and the paper says so directly.** The explanation it gives is
called "the base explanation", and, `QUOTED`, §4.1, preprint p.6: "We can improve the base
explanation by using lifting methods [1, 5, 16] to create a stronger explanation." Example 4
strips "redundant bounds" by hand (`QUOTED`) to get from a three-literal nogood to a
one-literal one — which is exactly the premise-droppability the repo's validator measures, and
the paper leaves it as an optional post-pass, not a property of the rule. The conclusions
reinforce that the raw explanations are large, `QUOTED`, §8 (Experiments), preprint p.13: "explanations from
flow networks can be large (usually hundreds of literals for nurse rostering, more for car
sequencing)".

**Schema or per-propagation?** **Per-propagation, unambiguously.** The cut `C` is "the set of
nodes searched for an augmenting path" (Ford-Fulkerson) or a strongly connected component of
the residual graph (Tarjan). Both are outputs of graph algorithms run at propagation time on a
structure the decomposition does not contain. `QUOTED`.

---

## Bearing on this repo

`COMPARISON` throughout.

`CHRISTMAS_LIST.md:127` routes `global_cardinality` through **E3/E9** for the MiniZinc
decomposition (`forall(i)(count(xs,cover[i],count[i])) /\ length(xs) >= sum(count)`, whose
trailing sum is over *integer* variables) and notes separately that "The flow explanation
needs **E4**". This file supports the second half of that and sharpens it: **E4 is necessary
but not sufficient.** Counting across sums would give access to the cardinality literals
`[c_j ≤ 1]`; it would not give access to a cut of a residual graph. The published `gcc`
explanation is **structurally out of reach** for any method that derives a rule schema from a
static decomposition, because its premise set is indexed by a run-time graph object with no
static counterpart.

That is a negative result worth recording rather than a gap to close.

---

## What was not sourced

- The typeset LNCS 7298:146-162 chapter (paywalled at Springer; not fetched). Content above is
  from the authors' preprint, same title and authors.
- Katsirelos (2008) and Rochart (2005), which the paper says its explanations reduce to /
  resemble for the `gcc` special case. `NOT SOURCED` — not fetched (budget). If the catalog
  wants the `gcc`-specific ancestor of this rule, Katsirelos's thesis is the place, and
  `alldifferent.md` records that Downing et al.'s ACSC paper also names Katsirelos as the
  source of its SCC explanation.
- The soft / min-cost flow explanations (§5, §6) beyond noting that fathoming is explained.
  `NOT SOURCED` by choice — no analogue in this repo.

---

## How this file was produced

- `WebSearch` for the preprint URL, then
  `WebFetch https://people.eng.unimelb.edu.au/pstuckey/papers/explaining_flow.pdf`
  (2026-09-21). The fetch tool's summariser could not read the PDF; it saved the binary, which
  was then run through `pdftotext -raw` locally. **Every quote above is transcribed from that
  local text.**
- Page pointers: `pdftotext -raw -f <p> -l <p> flow.pdf - | grep -n '<phrase>'`, one page at a
  time, for every phrase cited. The preprint has 19 pages (`pdfinfo`). Section headings
  enumerated with `grep -n '^[0-9] [A-Z]\|^[0-9]\.[0-9] '`: §1-§9 with §4.1, §4.2, §5.1,
  §6.1, §6.2.
- The minimality claim is a **measurement**: `grep -n -i 'minimal' <text>` over the whole
  preprint returns **1** hit, and it is about the magnitude of an arc value in the dual
  network simplex (§5.1), not about explanations. The paper's own words for its explanations
  are "the base explanation" and "can be large".
- `CHRISTMAS_LIST.md` line numbers from `grep -n -i 'Downing' CHRISTMAS_LIST.md`.
