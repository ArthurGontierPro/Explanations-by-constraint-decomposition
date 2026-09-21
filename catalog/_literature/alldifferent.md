# `alldifferent` — published explanation rules

## Citation

**Nicholas Downing, Thibaut Feydy, Peter J. Stuckey. *Explaining alldifferent.*
Proc. 35th Australasian Computer Science Conference (ACSC 2012), Melbourne, January-February
2012. CRPIT Vol. 122, Mark Reynolds and Bruce Thomas (eds.), Australian Computer Society.**

Read as the authors' preprint, <https://people.eng.unimelb.edu.au/pstuckey/papers/alldiff.pdf>
(fetched 2026-09-21; 819.7 KB; the venue line above is transcribed from its own copyright
footnote on preprint p.1). The preprint carries **no printed page numbers**, so every page
pointer below is a *preprint PDF page index*. CRPIT pagination not cross-checked.
Repo index: `CHRISTMAS_LIST.md:116`, `CHRISTMAS_LIST.md:266`.

> **Citation correction.** The task that commissioned this file attributed the Hall-set
> `alldifferent` explanation to *Explaining flow-based propagation* (CPAIOR 2012, LNCS
> 7298:146-162). The Hall-set explanations are in **this** paper, the ACSC 2012 one. The
> CPAIOR paper does discuss `alldifferent`, but only as an instance of a `gcc` flow network
> (its Example 4); see [`gcc.md`](gcc.md). `CHRISTMAS_LIST.md:116` cites the ACSC paper
> correctly under the title *Explaining alldifferent*, and `CHRISTMAS_LIST.md:266` gives the
> ACSC venue. `QUOTED` (both papers fetched and compared).

---

## The paper's own vocabulary

`QUOTED`, §3 "Hall Sets", preprint pp.2-3:

> "Given a constraint `alldifferent(x1, ..., xn)`, `H ⊆ {1,...,n}` is a Hall set if
> `|H| ≥ |V|` where `V = ∪_{h∈H} D(x_h)`. If the inequality holds strictly, that is
> `|H| > |V|`, then the constraint is unsatisfiable. If it holds as an equality, `|H| = |V|`,
> then no variable `x_i, i ∉ H` can take a value from `V`."

`QUOTED`, §3, preprint p.3, on what the explanations are in general:

> "The explanation clauses are essentially descriptions of the well-known conditions for
> pruning. Usually these clauses also suffice to describe failure (because they wake up
> implicit clauses requiring domains to be non-empty) but in some cases explicit failure
> nogoods can also be produced."

`E` is defined in §4 as `E = ∪_{i=1..n} D_orig(x_i)`, the union of the *original* domains.

---

## Rule 1 — value-consistent (forward-checking) propagator

**Paper's form.** `QUOTED`, §4 "Global value-consistent propagator", preprint p.3. The
propagator "wakes upon variable fixing, i.e. when `D(x_h) = {v}` for some `h, v`, it prunes
all `D(x_i), i ≠ v` with explanation"

```
[x_h = v] → [x_i ≠ v].
```

(The `i ≠ v` in that sentence is the paper's own typo for `i ≠ h`; the formula is unambiguous.
`COMPARISON`.)

**This repo's notation.** Faithful:

```
X_h = t
------------------------------- ⊢        (h ≠ i, h ∈ ⟦1,n⟧, i ∈ ⟦1,n⟧, AC)
X_i ≠ t
```

**Event explained.** A value removal, `[x_i ≠ v]`. `QUOTED`.

**Vocabulary.** User variables only. No auxiliaries. `QUOTED`.

**Minimal / strongest?** The paper does not claim minimality for this rule and does not need
to: it is a single literal, so nothing can be dropped. The paper's strength discussion is
empirical, not formal — §9 "Discussion", preprint p.7: "the strong domain propagator produces a weaker
nogood than value, since the nogood involves many variables and describes a situation that
might not recur often enough to pay" its cost. `QUOTED`. There is no formal minimality proof
anywhere in the paper. `QUOTED` (by absence — searched the preprint text for
"minimal"/"stronger"/"weaker"; the only "minimal" hit is "minimal change" to an algorithm,
preprint p.3).

**Schema or per-propagation?** **Schema.** It is a fixed two-literal pattern over indices
`h, i`, independent of any data structure. This is the one published `alldifferent`
explanation a decomposition-derived generator can reach. `COMPARISON`.

**Related.** §4 also records, `QUOTED`, that when `|E| = n` the propagator additionally
enforces the clauses `⋁_{i=1..n} [x_i = v]` for all `v ∈ E`, which the paper says is
"equivalent to changing the upper bound of 1 to equality with 1 in the above linear
constraints" — i.e. the counting-across-sums direction that this repo files under **E4**
(`CHRISTMAS_LIST.md:116`).

---

## Rule 2 — bounds-consistent propagator (Hall interval)

**Paper's form.** `QUOTED`, §5 "Global bounds-consistent propagator", preprint p.4, final
display of the section. Given Hall set `H` with `V = a..b`, the increased lower bound for a
variable `x_i ∉ H` is explained as

```
[x_i ≥ a] ∧ ⋀_{h∈H} ([x_h ≥ a] ∧ [x_h ≤ b]) → [x_i ≥ b + 1].
```

followed by, `QUOTED`: "This requires `O(n)` literals per explanation."

**This repo's notation.** The clause body translates, but **the translation is not faithful
as a schema**, and the reason matters:

```
X_i ≥ a,  X_h ≥ a,  X_h ≤ b,  ∀h ∈ H
------------------------------- ⊢        (BC)
X_i ≥ b+1
```

`H` here is **not** an index set the printer can name. It is a set discovered at run time by
the union-find pass of Lopez-Ortiz et al. (2003) — §5, preprint p.4: the paper's only change
to that algorithm was "(ii) to collect the set `H`, required for explanations" (`QUOTED`).
Likewise `a` and `b` are the discovered interval endpoints, not indices drawn from `⟦1,n⟧`.
The repo's printer quantifies over declared index sets (`⟦1,n⟧`, `⟦1,m⟧`) and has no way to
denote "a set `H` such that `|H| = |a..b|`". `COMPARISON`.

**Event explained.** A bound change, `[x_i ≥ b+1]`. `QUOTED`. (The paper notes, preprint p.4,
that the algorithm as described "will only prune lower bounds" and that a second pass
recomputes Hall intervals for upper bounds; the upper-bound rule is symmetric and is **not**
displayed in the paper. `QUOTED`.)

**Vocabulary.** User variables only, with run-time constants `a, b` and a run-time set `H`.
`QUOTED`.

**Minimal / strongest?** Not claimed. §9 does argue these nogoods are reusable, preprint p.9:
"These nogoods are also symmetric between variables, since they describe a Hall interval
rather than any specific pruning resulting from the existence of the Hall interval, which
further promotes reuse." `QUOTED`. That is a reuse argument, not a minimality claim.

**Schema or per-propagation?** **Per-propagation.** `H`, `a` and `b` come out of a union-find
data structure built during the sweep. `QUOTED` (§5's description of the algorithm).

---

## Rule 3 — domain-consistent propagator (Régin / SCC), pruning

**Paper's form.** `QUOTED`, §6 "Global domain-consistent propagator", preprint p.5,
**equation (1)**. Given `H` and `V`, "the explanation that we use for pruning values in
`j ∈ V` from `x_i ∉ H` is"

```
⋀_{h∈H, d∈E\V} [x_h ≠ d] → [x_i ≠ j]                                    (1)
```

with, `QUOTED`: "It requires `|H|(|E| − |V|)`, or `O(n|E|)` literals per explanation in the
worst case."

Note the *polarity*: the premises are the values **outside** `V` that each `x_h` has already
lost — the paper renders this as "the list of dotted arcs leaving the SCC" (§6, preprint p.5).
It is **not** `⋀_{h∈H} [x_h ∈ V]`; the paper tries that first and then says, `QUOTED`, of the
failure case: "Since we do not have literals to express that `x_h ∈ {2,3}`, we use an
equivalent clausal representation `x_h ≠ 1 ∧ x_h ≠ 4`."

**This repo's notation.** Body translates; schema does not:

```
X_h ≠ d,  ∀h ∈ H,  ∀d ∈ E\V
------------------------------- ⊢        (AC)
X_i ≠ j
```

`H` and `V` are the node sets of a strongly connected component of the residual graph of a
bipartite matching. There is no index-set expression for them. `COMPARISON`.

**Event explained.** A value removal. The same machinery also deduces **equalities** —
§6, Example 6.4, preprint p.5, `QUOTED`: "Pruning the arc from SCC #2 → #3 as described in
Example 6.3 gives the residual graph of Figure 5c. Further pruning is possible: `x1` may be
fixed to 1, using SCC #3 as evidence, yielding explanation `[x1 ≠ 2] → [x1 = 1]`." The paper
stresses this as its delta over prior work, §6, `QUOTED`: "Our explanations are the same as
Katsirelos's (2008) except that, our explanations based on the list of dotted arcs leaving an
SCC are quite general, so we naturally deduce and propagate equalities, rather than just
disequalities as Katsirelos does."

**Vocabulary.** User variables only. `QUOTED`.

**Minimal / strongest?** Not claimed. The paper says explanations are generated *lazily*
(§6, preprint p.4, `QUOTED`: "Note that we use SCC-splitting (Gent et al. 2008), and we
generate explanations lazily") and that redundant literals are stripped against the original
domains (Example 6.2, preprint p.5, `QUOTED`: "By removing the literals that are false in the
original domains, we obtain the nogood `[x1 ≠ 1] ∧ [x3 ≠ 4] → false`"). Stripping literals already
false in `D_orig` is a *correctness/compaction* step, not a minimality proof.

**Schema or per-propagation?** **Per-propagation.** Tarjan's SCC algorithm on the residual
graph of a Ford-Fulkerson matching produces `H` and `V`. `QUOTED`.

---

## Rule 4 — failure

**Paper's form.** `QUOTED`. §6, preprint p.4: "For infeasibility, the set of nodes searched
for an augmenting path (the cut) consists of `H ∪ V` and is a failure set as necessarily
`|H| > |V|`." The resulting nogood in the worked example (Example 6.2, spanning preprint
pp.4-5), after stripping:

```
[x1 ≠ 1] ∧ [x3 ≠ 4] → false
```

and, `QUOTED` (preprint p.5): "This final nogood is simply the list of dotted arcs leaving
the cut."

The general shape is equation (1) with `false` in place of `[x_i ≠ j]`, `H ∪ V` the searched
cut, and `|H| > |V|`. `DERIVED` — the paper states the cut/dotted-arc correspondence in prose
(§6, preprint p.4) and displays only the instance; the generalisation is one substitution and
matches the instance, but the paper does **not** display it. **Per-propagation**, same reason
as rule 3.

---

## Rule 5 — the `gcc`-style decomposition of `alldifferent` (Feydy & Stuckey 2009)

This is the one place the paper gives an explanation that arises from a *decomposition* and
is therefore directly comparable to this repo's method.

**Paper's form.** `QUOTED`, §7 "alldifferent by decomposition", preprint p.6. The
decomposition, quoted verbatim from the paper's MiniZinc listing:

```minizinc
predicate alldifferent_feydy_decomp(
    array[int] of var int: x) =
  let { int: L = lb_array(x),
        int: C = ub_array(x) + 1 - L,
        int: N = length(x),
        array[1..C] of var 0..1: c,
        array[0..C] of var 0..N: s } in
  s[0] = 0 /\ s[C] = N /\
  forall (i in 1..C) (
    s[i] = s[i - 1] + c[i] /\
    c[i] = sum (j in 1..N) (bool2int(x[j] = i)) /\
    s[i] = sum (j in 1..N) (bool2int(x[j] <= i)));
```

`QUOTED`: "The new decomposition is efficient because it uses the literals `[x_i = v]` and
`[x_i ≤ v]`, which are native in a lazy clause generation solver, as they are part of the
integer variable encoding."

**The explanation**, §7 Example 7.1, preprint p.6, for `x1 ∈ 1..2, x2 ∈ 1..3, x3 ∈ 2..3`
with `x2` narrowed to `2..3`:

```
[x2 ≥ 2] ∧ [x3 ≥ 2] → [x1 ≤ 1]
```

**This repo's notation.** Faithful for this instance:

```
X_2 ≥ 2,  X_3 ≥ 2
------------------------------- ⊢        (BC)
X_1 ≤ 1
```

**Event explained.** A bound change. `QUOTED`.

**Vocabulary.** The *conclusion and premises are over user variables*, but the derivation runs
through the auxiliaries `c[i]` (occurrence counts) and `s[i]` (prefix sums of occurrences) —
the paper's text works the example through `s1 = Σ_i bool2int([x_i ≤ 1])`. `QUOTED`.

**Minimal / strongest?** Not claimed. The paper's characterisation of the reach of this
decomposition is, `QUOTED`, §7, preprint p.6: it gives "the consistency level described in
Section 4, plus the detection of Hall intervals aligned to the start or end of the domain
interval `min(E)..max(E)`". So: strictly between value-consistency and bounds-consistency.

**Schema or per-propagation?** **Schema** — it is the explanation of a linear-sum propagator,
which is exactly the kind of thing this repo's `rule5/6/7` schemas produce. But the sum is
over *integer* auxiliaries `s[i]` chained by `s[i] = s[i-1] + c[i]`, and the counting step
`c[i] = Σ_j bool2int(x[j] = i)` reasons across two different sums of the same Booleans.
`COMPARISON`: that is this repo's **E1** (integer auxiliaries) plus **E4** (counting across
sums); see `CHRISTMAS_LIST.md:116`, which independently reaches the same conclusion.

---

## Answers to the four catalog questions, condensed

| | value-consistent (§4) | bounds-consistent (§5) | domain-consistent (§6) | Feydy decomp (§7) |
|---|---|---|---|---|
| **Event** | value removal | lower-bound increase | value removal; also equality fixing; also failure | bound change |
| **Premises' vocabulary** | user vars, 1 literal | user vars over run-time set `H`, interval `a..b` | user vars over run-time `H`, `E\V` | user vars; derivation via integer auxiliaries `c`, `s` |
| **Minimal / strongest?** | no formal claim anywhere in the paper; strength discussion is empirical (§9) | idem; reuse argued, not minimality | idem; literals false in `D_orig` are stripped, which is compaction not minimality | idem |
| **Schema or per-propagation?** | **schema** | **per-propagation** (union-find) | **per-propagation** (matching + SCC) | **schema**, needs E1+E4 |

---

## Comparison with this repo's generated entry

`COMPARISON` throughout this section — this is C2's reading, not a claim about the paper.

`cata/alldifferent.tex` emits one rule (measured: `grep -o '\\frac' cata/alldifferent.tex | wc -l`
→ 1, run 2026-09-21):

```
X_{i'} = t,  ∀i',  i' ≠ i,  i' ∈ ⟦1,n⟧,  i ∈ ⟦1,n⟧
------------------------------- ⊢
X_i ≠ t
```

The published counterpart is rule 1 above, `[x_h = v] → [x_i ≠ v]`. The two differ in the
quantifier on the premise: the paper's premise is a *single* literal for *one* witness `h`,
the generated premise is a conjunction over *all* `i' ≠ i`. The generated rule is therefore
**sound but strictly weaker** than §4's for every `n > 2`, and coincides with it only at
`n = 2`. That matches `CLAUDE.md`'s note that this rule "only ever fires at `n=2`", and it is
a **calibration result** in D-0013's sense, not a bug.

The second rule `CLAUDE.md` says `alldifferent` should *not* have (concluding `X_i = t`) does
exist in the literature — it is the equality deduction of §6, Example 6.4, and it is reached
there from an SCC, not from a sum. That is consistent with `CLAUDE.md`'s trap note that
getting it requires **E4**.

---

## What was not sourced

- The upper-bound form of the bounds-consistent explanation. The paper states the symmetric
  case is "analogous and omitted". `NOT SOURCED` (the paper does not give it).
- CRPIT Vol. 122 page range for this paper. `NOT SOURCED` — the preprint has no printed page
  numbers and the CRPIT table of contents was not fetched (fetch budget).

---

## How this file was produced

- `WebFetch https://people.eng.unimelb.edu.au/pstuckey/papers/alldiff.pdf` (2026-09-21). The
  fetch tool's summariser could not read the PDF; it saved the binary, which was then run
  through `pdftotext -raw` and `pdftotext -layout` locally. **Every quote above is transcribed
  from that local text, not from the summariser.** `curl` to the same URL is blocked by the
  host's WAF (Incapsula), which is why WebFetch was used.
- Page pointers: `pdftotext -raw -f <p> -l <p> alldiff.pdf - | grep -n '<phrase>'`, one page at
  a time, for every phrase cited. The preprint has 10 pages (`pdfinfo`).
- The minimality claim is a **measurement**: `grep -c -i 'minimal' <text>` over the whole
  preprint returns **1**, and that one hit is "the original algorithm with minimal change"
  (preprint p.3, about the union-find algorithm, not about an explanation). Section headings
  were enumerated with `grep -n '^[0-9] '`: §1-§9. (An earlier `grep -n '^[0-9] [A-Z]'` appeared
  to show no §7; that was the pattern's fault — §7's heading is "7 alldifferent by
  decomposition", which begins lowercase. Corrected before committing.)
- `grep -o '\\frac' cata/alldifferent.tex | wc -l` → **1** (run 2026-09-21), for the
  comparison section.
- `CHRISTMAS_LIST.md` line numbers from `grep -n -i 'Downing' CHRISTMAS_LIST.md`.
