# The Global Constraint Catalog — what to take, what not to

Beldiceanu, Carlsson and Rampon, *Global Constraint Catalog*, `https://sofdem.github.io/gccat/`.
Session M-1, task M-1-T1, 2026-09-18. `CHRISTMAS_LIST.md` mentions it zero times
(measured: `grep -i -c 'beldiceanu\|gccat' CHRISTMAS_LIST.md` → 0); this file closes that hole
without editing it.

**Method and budget.** 22 pages fetched, no more: the index; the by-name list `sec5.html`; the
keyword index `sec3.7.html`; three keyword pages (`Kautomaton_with_counters`,
`KBerge-acyclic_constraint_network`, `Kcontractible`); and 16 entry pages — the 13 `cata/`
constraints that have catalog entries (`alldifferent`, `all_equal`, `among`, `atleast_nvalue`,
`atmost_nvalue`, `cumulative`, `element`, `global_cardinality`, `increasing`, `in_relation`,
`nvalue`, `range_ctr`, `roots`) plus `sliding_sum`, `int_value_precede`,
`int_value_precede_chain` from the W3 shortlist. Nothing is transcribed; everything is summary
plus URL. Numbers are **read off the catalog** unless marked *derived* or *measured*.

Nothing here is evidence that any `cata/*.tex` entry is correct: W0-T1's validator covers 3 of 16
entries and found **0 of 13 rules sound-and-minimal**; the rest are "generated, unvalidated".

---

## 1. What a catalog entry contains — and what D-0008 should want from it

An entry (read off `Calldifferent.html`) has, in order: Origin, Constraint, Synonyms, Argument,
Restriction, **Purpose**, Example, All solutions, Typical, Symmetries, **Arg. properties**,
Usage, Remark, Algorithm, **Reformulation**, Counting, Systems, Used in, **See also**,
**Keywords**, **Cond. implications**, Arc input(s)/generator/arity/constraint(s), Graph
property(ies), Graph class, Graph model, **Automaton**, Quiz. 423 entries (read off `sec5.html`).

A `cata/*.tex` entry here is one LaTeX fraction and nothing else. Four of those fields would make
one *checkable*, and they bear directly on **D-0008 (OPEN: what "complete" means for an entry)**:

| field | what it buys D-0008 |
|---|---|
| **Purpose** | one sentence of ground semantics. `validator.ml` hand-encodes exactly this, and `docs/VALIDATOR.md` names that hand-encoding as its exposure; an entry carrying its Purpose beside its rules is one whose validation is auditable. |
| **Arg. properties** | contractible / extensible / monotone / functional dependency — *machine-checkable invariants on the semantics encoding*. See §3; the single most actionable field. |
| **Restriction / Typical** | the arity and domain box a schema was validated over. D-0008 already says a schema validated at `n ≤ 6` must not be called proved; this is where that caveat lives. |
| **Keywords** | notably `Berge-acyclic constraint network` (§2) — the catalog's own answer to "is this decomposition lossless?" |

**Proposal for D-0008, not a decision:** an entry is *complete* only relative to a stated Purpose,
a stated arity box, and a per-entry `complete`/`partial` label — D-0008's prime-implicate candidate
plus the catalog's Restriction and Arg. properties fields — and, per D-0009, excluding `VACUOUS`
rules. Recorded here for whoever closes D-0008.

---

## 2. The counter-automata, in E-code terms

62 constraints carry the keyword `automaton with counters` (read off
`Kautomaton_with_counters.html`); `automaton without counters`, `automaton with array of counters`,
`non-deterministic automaton` and `reified automaton constraint` are separate keyword pages.

Automaton section present for `alldifferent`, `among`, `cumulative`, `element`,
`global_cardinality`, `increasing`, `nvalue`, `int_value_precede` (counter-free, 2 states) and
`int_value_precede_chain` (counter-free, `m+1` states); **absent** for `all_equal`,
`atleast_nvalue`, `atmost_nvalue`, `in_relation`, `range_ctr`, `roots`, `sliding_sum`.

**The layers of a catalog automaton, and what each costs here:**

1. **Signature layer** — `S_i ⇔ X_i ∈ VALUES`. This is *already* `rule1`, the reified
   equivalence. **E0.** Nothing to build.
2. **Transition table** `d[q,s]` — a 2-D constant array. **E2**, exactly as D-0006 already
   records for `regular`. `Addcst` is 1-D today.
3. **State variable** `Q_i` — a new integer family. **E1** (open `var_name`); the `rule1`
   channelling mechanism already exists for `N`/`O`.
4. **Counter** `C_i` with updates `C_{i+1} = C_i + [s_i ∈ …]` and an acceptance test against a
   user variable — **E1** for the family, **E2** for the inequality against an expression.
5. **Array of counters** (`nvalue`, `global_cardinality`) — a counter per value, plus a final
   aggregate across the whole array. That is **E3** (multi-family cardinality), i.e. the
   `failwith "sommes multiples"` site. Not narrow.

Layers 1–2 are the cheap half D-0006 already priced; layers 3–5 carry the cost, and it is cost
*for auxiliaries*.

**What happens to the state variables — the D-0004 answer.** Taking an automaton as a
decomposition puts `Q_i = q` into premises: a variable the user never wrote, which a reader of
the catalog would not recognise. That is the same objection D-0004 raises against MiniZinc's
`a[i+1] = d[a[i], xs[i]]`, and this repo's own `regular` decomposition (generator l.421–422,
`rule4` over value sets `D_8`/`D_9` on consecutive `X`) already avoids it. **Do not import the
state layer.**

The workable middle, and the one rule to take away: **a state variable may be inlined when its
state predicate is a finite disjunction over user literals.** `int_value_precede` is the clean case
— its two states are "`S` occurred among `X_1..X_{i-1}`" and its negation, i.e. `⋁_{j<i} X_j = S`,
pure user vocabulary. `increasing` is the degenerate case, and the catalog's own decomposition for
it is the pairwise `X_i ≤ X_{i+1}` chain the repo already runs. Counter automata (layers 4–5) fail
the test: a counter's value is not a disjunction of user literals. That is the line.

**`Berge-acyclic constraint network`** (39 constraints, read off the keyword page) is the catalog's
own statement of when a decomposition loses nothing: no two constraints share more than one
variable, the hypergraph is acyclic, and AC on the parts gives AC on the whole. It contains `among`,
`int_value_precede`, `int_value_precede_chain`, `increasing_nvalue`, `stretch_path`,
`global_contiguity`, the `lex_*` family. For a Berge-acyclic decomposition, "the rules derived from
the parts are all the rules" becomes a *supportable* claim rather than a hopeful one — the strongest
thing D-0008 gets from this catalog.

---

## 3. The cross-constraint links — mostly one good thing, and it is not "See also"

`See also` is typed: generalisation, specialisation, implies, implied by, comparison swapped,
negation, soft variant, cost variant, common keyword, uses in reformulation.

**Explanation reuse between related constraints: not much.** `comparison swapped`
(`atleast_nvalue`/`atmost_nvalue`, `increasing`/`decreasing`) is the only near-mechanical relation,
and it is a renaming, not a derivation. Generalisation/specialisation transports no rule in either
direction — a rule for `alldifferent` is not a rule for `nvalue`.

**A validator cross-check: yes, and cheap.** `implies` and `specialisation` are ground facts: if
`C` specialises `D`, every assignment satisfying `C` satisfies `D`. `validator.ml` already
enumerates ground assignments at small `n` against hand-encoded semantics, so it can check these at
no new cost — and what it checks is *the hand-encoding*, precisely the exposure
`docs/VALIDATOR.md` names. Pairs available wholly inside `cata/`: `all_equal ⇒ increasing`, `all_equal ⇒ decreasing`,
`nvalue ⇒ atleast_nvalue`, `nvalue ⇒ atmost_nvalue`, `alldifferent` specialises `nvalue`,
`alldifferent` specialises `global_cardinality`.

**The most actionable single item in the whole catalog is `Arg. properties`,** and it lands on
W1-T5. The catalog states (read off the two entry pages):

- `atleast_nvalue`: **extensible** wrt VARIABLES, **monotone — `NVAL` can be decreased**.
- `atmost_nvalue`: **contractible** wrt VARIABLES.

Two constraints with *opposite* closure properties cannot have the same explanation rules, so
`cata/atleastnvalues.tex` and `cata/atmostnvalues.tex` being byte-identical is a defect on catalog
grounds alone — an argument independent of W0-A's validator run, which reached the same place.
*Derived* from the monotone property: the feasible set of `NVAL` for `atleast_nvalue` is downward
closed, so propagation from `X` literals can only ever tighten `NVAL`'s **upper** bound. W1-T5
already records that the at-least rule "bounds `N` from the wrong side" at `n=m=2, p=1`. The
catalog says which side is the wrong one, and says it without running anything.

Generalising: **contractible / extensible / monotone are machine-checkable invariants on
`validator.ml`'s hand-encoded semantics.** A few lines per entry, and they catch transcription
errors before any rule is judged. That is the recommendation.

---

## 4. What not to take — recorded so it is not rediscovered

- **Graph model, Arc generator, Arc constraint, Graph property (`NARC`, `NSCC`, `PATH`,
  `CLIQUE`).** The catalog's *primary* description language — most entries describe themselves
  this way and give no logical decomposition at all. **E6**, out of scope per D-0006. Reading an
  entry means skipping this section, which is most of it.
- **Set-variable constraints — E5.** `roots` is a set constraint here (`S`, `T` are sets;
  decomposition `i ∈ S ⇔ X_i ∈ T`). This repo's `roots` and `range` (generator l.423–428) already
  eliminated the sets by hand into index sets `D_5`/`D_6` — the same `D_k`'s W1-T2 flags as
  undefined in the printer. Do not re-import the set formulation.
- **Geometry and packing** (`geost`, `diffn`, `two_orth_*`, `cumulative_two_d`) — out of scope.
- **Counting** (solution counts) and **Quiz** — no use for explanation.
- **Systems** (which solver ships it) — `CHRISTMAS_LIST.md` already has a better version, targeted
  at explaining/LCG propagators rather than availability.
- **Wholesale import of the catalog's decompositions and automata.** D-0003's rejected MiniZinc
  proposal in different clothing; D-0004 gives the reason. §2 has the one narrow exception.

---

## 5. Reported, not edited: what this adds to or contradicts `CHRISTMAS_LIST.md`

`CHRISTMAS_LIST.md` is read-only for this session. Three items for whoever owns it:

1. **The catalog has no `regular`, no `table`, no `mdd`.** Measured twice: absent from the by-name
   list `sec5.html`, and `gccat/Cregular.html` returns HTTP 404. Its table-like entry is
   `in_relation`, which has *no* automaton section. **W3-T3 (the extensional family) gets nothing
   from this catalog** — `regular` stays this repo's own decomposition, which D-0003 already argues
   is the better one for explanation. The clearest boundary the exercise found.
2. **`range` is ambiguous across the two catalogs.** `cata/range.tex` is Bessiere et al.'s
   set-variable RANGE; the catalog's `range_ctr` is an unrelated arithmetic constraint on
   `max − min + 1`. Worth a note so the two are never conflated.
3. **`Berge-acyclic constraint network` (39 constraints) and `Arg. properties` are two per-constraint
   columns `CHRISTMAS_LIST.md` lacks** and this project can use — the first for completeness claims
   (§2), the second for validator invariants (§3).
