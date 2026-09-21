# `cumulative` — published explanation rules

## Citation

**Andreas Schutt, Thibaut Feydy, Peter J. Stuckey, Mark G. Wallace. *Explaining the
cumulative propagator.* Constraints 16(3):250-282, 2011.
DOI [10.1007/s10601-010-9103-2](https://doi.org/10.1007/s10601-010-9103-2).**

Read as the authors' **Constraints manuscript preprint**,
<https://people.eng.unimelb.edu.au/pstuckey/papers/cumulative.pdf> (fetched 2026-09-21;
710.1 KB). Its first line is "Constraints manuscript No. (will be inserted by the editor)",
so it is the accepted manuscript, not the typeset article. The preprint **is** internally
paginated (its own running page numbers 1..n), and every page pointer below is a *preprint*
page number. **The journal pagination 250-282 was not cross-checked** — preprint p.12 is not
journal p.261.
Repo index: `CHRISTMAS_LIST.md:167`, `CHRISTMAS_LIST.md:264`.

Notation: the paper writes literals as `⟦·⟧` (double brackets), `s[i]` for the start-time
variable of task `i`, `d[i]` its duration, `r[i]` its resource requirement, `c` the capacity,
`lb`/`ub` for current bounds.

---

## The paper's definition of explanation strength

`QUOTED`, §3, preprint p.7:

> "Propagation can be explained by different set of clauses. In order to get maximum benefit
> from the explanation we desire a "strongest" explanation as possible. A set of clauses `C1`
> is stronger than a set of clauses `C2` if `C1` implies `C2`. In other words, `C1` restricts
> the search space at least as much as `C2`."

Example 4 (same page) shows three explanations of one propagation of which "The second and
third explanation are stronger than the first, but neither of the second or third explanation
is stronger than the other." `QUOTED`. **So the paper's ordering is a partial order and it
explicitly does not claim a unique strongest explanation.** This is the single most important
sentence in this file for the catalog: the paper's "stronger" is *logical implication between
explanation clause sets*, which is a different property from the validator's *minimality*
(no premise droppable).

---

## Part A — consistency check (failure), §6.1, preprint p.12

**The overload condition.** `QUOTED`, §6.1, preprint p.12. If an overload occurs on a
resource of capacity `c` in the time interval `[s .. e−1]` involving the task set `Ω`:

```
∀i ∈ Ω : ub(s[i]) ≤ s  ∧  e ≤ lb(s[i]) + d[i]
Σ_{i∈Ω} r[i] > c
```

### A1. Naïve explanation — `QUOTED`, §6.1, preprint p.12

```
⋀_{i∈Ω} ⟦lb(s[i]) ≤ s[i]⟧ ∧ ⟦s[i] ≤ ub(s[i])⟧ → false
```

> "The naïve explanation simply uses the current domains of all variables involved in the
> inconsistency, which is always a correct explanation for any constraint." `QUOTED`

### A2. Big-step explanation — `QUOTED`, §6.1, preprint p.12

```
∀i ∈ Ω : ⟦e − d[i] ≤ s[i]⟧ ∧ ⟦s[i] ≤ s⟧ → false
```

(The display's `∀i ∈ Ω` is the paper's own way of writing the conjunction over `Ω`.)
Motivation, `QUOTED`: "In some cases some task in `Ω` might have compulsory parts before or
after the overload. These parts are not related to the overload, and give us the possibility
to widen the bounds in the explanation."

### A3. Pointwise explanation — `DERIVED` from a substitution the paper states

The paper does **not** display this one. It says, `QUOTED`, §6.1, preprint p.12:

> "We can instead explain the overload by concentrating on a single time point `t` in
> `[s .. e−1]` rather than examining the whole time interval. ... The explanation has the same
> pattern as a maximal explanation except we use `t` for `s` and `t + 1` for `e`. We call
> these explanations pointwise explanations. The pointwise and big-step explanation coincide
> iff `s + 1 = e`."

Applying that substitution to A2 gives

```
∀i ∈ Ω : ⟦t + 1 − d[i] ≤ s[i]⟧ ∧ ⟦s[i] ≤ t⟧ → false
```

**Check against the paper's own Example 8** (preprint p.13, `QUOTED`): with `Ω = {b,e,f}`,
`t = 5`, and `d[b] = 6` (from Example 6, preprint p.9), the paper's minimal explanation is
`⟦−1 ≤ s_b⟧ ∧ ⟦s_b ≤ 5⟧ ∧ ⟦1 ≤ s_e⟧ ∧ ⟦s_e ≤ 5⟧ ∧ ⟦−1 ≤ s_f⟧ ∧ ⟦s_f ≤ 5⟧ → false`. For `b`:
`t+1−d[b] = 5+1−6 = −1` ✓ and `s[b] ≤ 5` ✓. The substitution reproduces the paper's instance.

**Terminology caveat.** The quoted sentence says "the same pattern as a **maximal**
explanation", but the displayed formula A2 is introduced as the **big-step** explanation and
the word "maximal" is not otherwise defined in §6.1. Example 8 then calls A2's instance "The
maximal explanation". So "maximal" = "big-step" in this paper. `QUOTED` (both usages
transcribed); the identification is `COMPARISON`.

### The task set `Ω` need not be minimal — `QUOTED`, §6.1, preprint p.13

> "Sometimes a resource overload is detected where the task set `Ω` of tasks which are
> compulsory at that time is not minimal with respect to the resource limit, i.e. there exists
> a proper subset of tasks `Ω′ ⊂ Ω` with `Σ_{i∈Ω′} r[i] > c`. ... we know the context of the
> tasks involved and can decide which subset `Ω′` is used in order to explain the
> inconsistency if there exists a choice. Here as well, it is an open question which subset is
> the best ... For our experiments the lexicographic least set of tasks is chosen".

**This is an explicit statement that the shipped explanation is not minimal and that
minimality is left open.** Directly relevant to the catalog's minimality column.

---

## Part B — time-table filtering (bound change), §6.2, preprint pp.14-15

**The profile.** `QUOTED`, §6.2, preprint p.14:

> "A profile is a triple `(A, B, C)` where `A = [s .. e−1]` is a time interval, `B` the set of
> all tasks `i` with `ub(s[i]) ≤ s` and `lb(s[i]) + d[i] ≥ e` (that is a compulsory part in the
> time interval `[s .. e−1]`), and `C` the sum of the resource requirements `r[i]` of all tasks
> `i` in `B`."

**The propagation.** `QUOTED`, same page: when `lb(s[j])` can be raised to `LB[j]`, "there
exist a sequence of profiles `[D1, ..., Dp]` where `Di = ([si .. ei−1], Bi, Ci)` where
`e0 = lb(s[j])` and `ep = LB[j]` such that"

```
∀1 ≤ i ≤ p : Ci + r[j] > c  ∧  si ≤ e_{i−1} + d[j]
```

"Hence each profile `Di` pushes the start time of task `j` to `ei`."

### B1. Naïve — `QUOTED`, §6.2, preprint p.14

```
( ⟦lb(s[j]) ≤ s[j]⟧ ∧ ⋀_{1≤i≤p, l∈Bi} ⟦lb(s[l]) ≤ s[l]⟧ ∧ ⟦s[l] ≤ ub(s[l])⟧ ) → ⟦LB[j] ≤ s[j]⟧
```

### B2. Big-step over the whole sequence — `QUOTED`, §6.2, preprint p.14

```
( ⟦s1 + 1 − d[j] ≤ s[j]⟧ ∧ ⋀_{1≤i≤p, l∈Bi} ⟦ei − d[l] ≤ s[l]⟧ ∧ ⟦s[l] ≤ si⟧ ) → ⟦LB[j] ≤ s[j]⟧
```

`QUOTED`, immediately after: "Both the above explanations are likely to be very large (they
involve all start times appearing in the sequence of profiles) and hence are not likely to be
very reusable."

### B3. Per-profile ("iterative profile") — `QUOTED`, §6.2, preprint p.14

An explanation for the single profile `Di = ([si .. ei−1], Bi, Ci)` forcing `s[j]` from
`e_{i−1}` to `ei`:

```
( ⟦si + 1 − d[j] ≤ s[j]⟧ ∧ ⋀_{l∈Bi} ⟦ei − d[l] ≤ s[l]⟧ ∧ ⟦s[l] ≤ si⟧ ) → ⟦ei ≤ s[j]⟧
```

`QUOTED`: "This corresponds to a big-step explanation of inconsistency over the time interval
`[si .. ei−1]`."

### B4. Pointwise — `QUOTED`, §6.2, preprint p.15. **This is the one the paper uses.**

`QUOTED`: "Let `[t1, ..., tm]` be a set of time points such that `t0 = lb(s[j])`,
`tm + 1 = LB[j]`, `∀1 ≤ j ≤ m : t_{j−1} + d[j] ≥ tj` and there exists a mapping `P(tl)` of
time points to profiles such that `∀1 ≤ l ≤ m : s_{P(tl)} ≤ tl < e_{P(tl)}`. Then we build a
pointwise explanation for each time point `tl`, `1 ≤ l ≤ m`"

```
( ⟦tl + 1 − d[j] ≤ s[j]⟧ ∧ ⋀_{k∈Bi} ⟦tl + 1 − d[l] ≤ s[k]⟧ ∧ ⟦s[k] ≤ tl⟧ ) → ⟦tl + 1 ≤ s[j]⟧
```

**Transcription note.** The index hygiene in this display is the paper's, and it is broken:
the conjunction binds `k ∈ Bi` (with `i` unbound at this point — it should be `B_{P(tl)}`) yet
writes `d[l]` where `l` is the *time-point* index, not a task; by the pattern of B3 and by
Example 9 it must be `d[k]`. Transcribed exactly as printed; the two corrections are
`COMPARISON`. The repo will recognise the failure mode — it is the binder collision of D-0009.

`QUOTED`, on the choice of points: "We use these pointwise explanations in our experiments,
by starting from `t0 = lb(s[j])` and for `j ∈ [1 .. m]` we choose `tj` as the greatest time
maintains the conditions above. The exception is that if we never entirely skip a profile `Di`
even if this is possible, but instead choose `ei − 1` as the next time point and continue the
process. Our experiments show this is slightly preferable to the skipping a profile entirely."

**Worked instance, Example 9, preprint p.15, `QUOTED`** (`lb(sf)=0`, `LB[f]=10`, profiles
`[D1,D2] = [([4..7],{b,e},4), ([9..10],{c},4)]`):

- naïve: `⟦2 ≤ sb⟧ ∧ ⟦sb ≤ 3⟧ ∧ ⟦2 ≤ se⟧ ∧ ⟦se ≤ 4⟧ ∧ ⟦8 ≤ sc⟧ ∧ ⟦sf ≤ 9⟧ → ⟦10 ≤ sf⟧`
- iterative profile: `⟦1 ≤ sb⟧ ∧ ⟦sb ≤ 4⟧ ∧ ⟦2 ≤ se⟧ ∧ ⟦se ≤ 4⟧ → ⟦7 ≤ sf⟧` and
  `⟦4 ≤ sf⟧ ∧ ⟦8 ≤ sc⟧ ∧ ⟦sc ≤ 9⟧ → ⟦10 ≤ sf⟧`
- iterative pointwise (points 5 and 9): `⟦sb ≤ 5⟧ ∧ ⟦1 ≤ se⟧ ∧ ⟦se ≤ 5⟧ → ⟦6 ≤ sf⟧` and
  `⟦4 ≤ sf⟧ ∧ ⟦8 ≤ sc⟧ ∧ ⟦sc ≤ 9⟧ → ⟦10 ≤ sf⟧`

and, `QUOTED`: "Note that this explanation is analogous to the explanation devised by the
decomposition in Example 6, and stronger than the iterative profile explanation."

---

## Translation to this repo's notation

The **body** of B4 translates; the **quantification** does not.

```
S_j ≥ t+1−d_j,   S_k ≥ t+1−d_k,   S_k ≤ t,   ∀k ∈ B
------------------------------------------------- ⊢        (BC)
S_j ≥ t+1
```

Faithful in shape. **Not faithful as a schema**, for three independent reasons:

1. `B` is the set of tasks with a compulsory part at `t`. Membership is a *run-time*
   predicate on current bounds (`ub(s[k]) ≤ t < lb(s[k]) + d[k]`), not an index set the
   printer can name. The repo's printer has `⟦1,n⟧`, `⟦1,m⟧` and an undefined `D_k` beyond
   that (`CLAUDE.md`, "Traps").
2. The premises carry **arithmetic on thresholds**, `t + 1 − d[k]`. The repo's event type is
   `(sign, variable, index list, AC|BC)` with no term arithmetic; `CHRISTMAS_LIST.md:167`
   calls this **E2**.
3. `d[i]` and `r[i]` are *variables* in the general `cumulative`, and the capacity argument
   `Σ_{i∈B} r[i] + r[j] > c` is a sum comparison across tasks — **E4** by the same line.

`COMPARISON` for all three; `CHRISTMAS_LIST.md:167` reaches the same conclusion independently
("Needs **E2** ... and **E4** ... *The other key test case.*").

---

## Answers to the four catalog questions

**What event is explained?** Both: failure (§6.1, the overload check) and a **bound change**
(§6.2, `⟦LB[j] ≤ s[j]⟧`, i.e. a lower-bound increase; the paper says "the case of decreasing
upper bounds in analogous and omitted", `QUOTED`, preprint p.14). `QUOTED`.

**Premises' vocabulary?** **User variables only** — start times `s[i]` with shifted
thresholds. No auxiliaries appear in the *global* propagator's explanations. `QUOTED`.

Contrast with the paper's own **TimeD decomposition** (§5.1, preprint p.9), which *does*
introduce auxiliaries, `QUOTED`:

```
∀t ∈ [0 .. tmax−1], ∀i ∈ [1 .. n] : B_it ↔ ⟦s[i] ≤ t⟧ ∧ ¬⟦s[i] ≤ t − d[i]⟧
∀t ∈ [0 .. tmax−1] : Σ_{i∈[1..n]} r[i] · B_it ≤ c
```

This is a `rule1`-style reified equivalence over a conjunction, feeding a Boolean-sum-`≤`
(`rule5`) — structurally *exactly* the shape this repo's generator consumes, except that the
sum is weighted by `r[i]` and the second conjunct is a negated literal at a shifted threshold.
`COMPARISON`. The paper's verdict on the two, `QUOTED`, §6.2, preprint p.15: "The global
cumulative using time-table filtering and the TimeD decomposition have the same propagation
strength. The advantages of the global approach is that we can control the times points we
propagate on ... The possible advantage of the decomposition is that it learns smaller nogoods
related to the decomposed variables, but since `B_it` simply represents a fixed conjunction of
bounds in practice the nogoods learned by the TimeD decomposition have no advantage."

**Minimal / strongest?** **No.** The paper gives a *ladder* of explanations ordered by its own
implication-strength relation (naïve < big-step < pointwise) and says pointwise is the
strongest it uses — but it explicitly leaves two minimality questions open (`QUOTED`,
preprint pp.13): which time point `t` to pick ("does it matter which time point is picked, if
so, which is the best one?") and which subset `Ω′` of an over-large task set to use ("it is an
open question which subset is the best"). Example 8 calls the pointwise instance "A minimal
explanation" (`QUOTED`, preprint p.13), but that is the label on one instance, not a theorem;
no minimality is proved anywhere in the paper.

**Schema or per-propagation?** **Per-propagation.** `B` (the compulsory-part set), the profile
sequence `[D1..Dp]` and the chosen time points `[t1..tm]` all come from scanning the resource
time-table profile built at propagation time. The *form* of B3/B4 is a fixed template, so it
is closer to a schema than `alldifferent`'s SCC explanation is — but the index set the
template quantifies over is computed, and a decomposition-derived generator would have to
name it. The paper's own TimeD decomposition dodges this by quantifying over *all* times `t`
and letting `B_it` be false where the task is not compulsory; that **is** a schema, and it is
the form this repo could in principle reach. `COMPARISON`.

---

## What was not sourced

- The typeset Constraints 16(3):250-282 article itself (paywalled at Springer; not fetched).
  Everything above is from the authors' accepted manuscript, which may differ in pagination
  and in copy-editing. `SECONDARY` **only** in that sense — the content is quoted from a
  document by the same authors bearing the same title, not from a third-party summary.
- The upper-bound (decreasing) form of B1-B4. The paper says it is "analogous and omitted".
  `NOT SOURCED` (the paper does not give it).
- The **task decomposition** (TaskD, §5.2) explanations were not transcribed; only TimeD,
  which is the one structurally comparable to this repo. Fetch budget, not availability — the
  section begins at preprint p.10 for anyone who needs it.

---

## How this file was produced

- `WebFetch https://people.eng.unimelb.edu.au/pstuckey/papers/cumulative.pdf` (2026-09-21).
  The URL was a guess from the naming pattern of the same group's other preprints; it
  resolved to the Constraints accepted manuscript. The fetch tool's summariser could not read
  the PDF; it saved the binary, which was then run through `pdftotext -raw` locally.
  **Every quote above is transcribed from that local text.**
- Page pointers: `pdftotext -raw -f <p> -l <p> cumu.pdf - | grep -n '<phrase>'`, one page at a
  time, for every phrase cited. Several first-draft page numbers in this file were wrong by
  one or two and were corrected this way before committing.
- The A3 pointwise consistency rule is `DERIVED`, and the derivation was **checked** against
  the paper's Example 8 arithmetic (`t=5`, `d[b]=6` from Example 6, preprint p.9 → `−1 ≤ s_b`),
  not just asserted.
- The minimality claim is a **measurement**: `grep -n -i 'minimal' <text>` over the whole
  preprint returns 5 hits, quoted or accounted for above; none of them is a theorem or a proof
  obligation, two of them are the open questions quoted in §6.1.
- `CHRISTMAS_LIST.md` line numbers from `grep -n -i 'Schutt' CHRISTMAS_LIST.md`.
