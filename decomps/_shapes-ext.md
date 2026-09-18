# Decomposition shapes — extensional (§5) and scheduling (§6)

Companion to the counting pilot. Each **shape** is written once, with its maths, its literals,
its rule schemas, its index families, its E-code and its auxiliaries (D-0004). Each
`decomps/<name>.md` then says which shape it instantiates and what differs. Gaps go to
`decomps/_gaps-ext.md`, not here.

Provenance conventions used below: **read off the source** = read in
`explenation generator.ml`; **read off the output** = read in `cata/*.tex`; **measured** =
`docs/VALIDATOR.md` reports a run. Nothing here is measured by this session; this session ran
no code.

Per D-0003 these decompositions are authored here for explanation quality. Where MiniZinc or
gccat is mentioned it is as a coverage remark, never as an argument. `docs/GCCAT.md` §5.1
records (measured there, twice) that gccat has **no `regular`, no `table`, no `mdd`** entry, so
§5 draws nothing from the catalog.

---

## Naming used throughout

`X_i` = the user's decision variables, `i ∈ [1,n]`. `t` ranges over the value/time domain
`[1,m]`. `B k` families are the generator's Boolean auxiliaries. Index *families* are the
generator's four: `FI`/`FT`/`FP`/`FR` printing as `i`/`t`/`p`/`r` (read off the source, l.38).

---

## EXT-1 — row selector over a constant relation

**Instantiated by:** `table` (and gccat's `in_relation`, out of this wave's file scope).

**Maths.** `T` is a constant `m_r × n` matrix of allowed tuples.

- `R_r ⇔ ⋀_{i∈[1,n]} (X_i = T[r,i])`, for `r ∈ [1,m_r]` — "row `r` is still a candidate".
- `⋁_{r∈[1,m_r]} R_r`.

**Literals.** Only `X_i = t` (AC). `T[r,i]` is a constant *lookup*, not a literal: the atom
`X_i = T[r,i]` is `X_i = t` together with the **side condition** `t = T[r,i]`.

**Rule schemas.** `rule1` for `B1_{i,t} ⇔ X_i = t`; `rule3` (∧) for `R_r`; `rule4` (∨) for the
selector. Index sets: `i ∈ [1,n]`, `t ∈ [1,m]`, `r ∈ [1,m_r]` — three families, `FI`/`FT`/`FR`.

**E-code: E2**, for the side condition `t = T[r,i]`, a **2-D constant table read as a
function of two indices**. `Addcst` is 1-D (`i₃ = i₂ ± c·i`, read off the source l.10) and
`OpShiftC` shifts one family by a constant named per index; neither can *determine* one index
from two others.

**Auxiliaries and what they look like printed (D-0004).** `R_r` is a per-row reification. It
washes out: with `rule3`/`rule4` the derived rules quantify it away, and the intended printed
form mentions only `X` literals plus the `T[r,i]` side conditions — e.g. to conclude
`X_i ≠ t`, "every row `r` with `T[r,i] = t` is already killed by some position `i'`". That is
the shape of the justification McIlree & McCreesh certify for smart tables
(`CHRISTMAS_LIST.md` §5), so the auxiliary is admissible under D-0004.

**Status of the shipped `table` (generator l.720–722, read off the source).** The shipped entry
does *not* implement EXT-1. It reifies `B1` over `(i,t,r)` while the global event `x3ac`
carries three indices `[I 1; T 1; R 1]` on `X` itself, with `id`/`id` on the `Global_devent`, so
`r` is introduced on the `X` literal and never eliminated, and the `t = T[r,i]` link is absent
entirely. `docs/VALIDATOR.md` l.287 **measures** its 3 rules as 3 UNSOUND, and `cata/table.tex`
carries the generator's own W1-T4 defect comment for the empty-premise rule. The missing piece
is exactly E2; the extra index is a decomposition-authoring error on top of it.

---

## EXT-2a — local transition chain on consecutive user variables (no state)

**Instantiated by:** the generator's shipped `regular` (l.712–713); `regular_regexp` whose
expression compiles into this class.

**Maths.** For each ordered value pair, a binary clause over consecutive positions:

- `B1_{i,t} ⇔ X_i = t`, `i ∈ [1,n]`, `t ∈ [1,m]` (AC).
- for each `i ∈ [2,n]`: `¬B1_{i-1,t'} ∨ B1_{i,t}` for the pairs `(t',t)` the transition
  relation admits — encoded by the value sets `D_8` (descending) and `D_9` (ascending).

**Rule schemas.** `rule1`, then a single `rule4` whose two `Decomp_devent`s are the same `B1`
family shifted by `±1` in `FI` and primed in `FT` (`OpShift`, `OpPrim`). Read off the source
l.713: `imap [imoin 1; tprimin (D 8)]` / `imap [iplus 1; tprimin (D 9)]`.

**Auxiliaries: none beyond the `rule1` reification.** This is the D-0003/D-0004 worked example
and the claim survives: `cata/regular.tex` (read off the output) contains only `X` literals and
index side conditions, no automaton state. Both its rules are in the user's vocabulary.

**E-code: E2**, and a *different* E2 from EXT-1's. What is needed is not a 2-D constant table but
**a value set that depends on another index**: `D_8` really means `pred(t)` and `D_9`
`succ⁻¹(t)`, i.e. `t' ∈ D(t)`. The type `ind_set = D of int | D2 of ind_name list` has a
constructor shaped for exactly this, but `D2` is **used nowhere** and prints as the literal
string `"setfils"` (read off the source l.6, l.111, l.375), which is not LaTeX. So the hook
exists and the implementation does not.

**What this shape does NOT cover — the coverage limit.** A conjunction of binary constraints on
consecutive positions can only express languages whose membership is decided by the *set* of
adjacent pairs occurring in the word (plus the permitted first and last values), i.e. the
**strictly 2-local** languages — equivalently, automata whose state is a
function of the last symbol read. "An even number of `a`s" is regular and is not of this form.
So EXT-2a is a complete decomposition of a *fragment* of `regular`, not of `regular`.

This is **not** a challenge to D-0003, which decides *where decompositions come from* and is
right that MiniZinc's state-variable encoding would put `a[i]` into premises. It is a statement
about what the shipped decomposition covers, derived by reading l.713 and asking which languages
a chain of binary constraints can define. `docs/VALIDATOR.md` l.332 independently records
`regular` as **not checkable** (`D_8`, `D_9` undefined), so nothing measured contradicts or
confirms it.

**Second reading hazard, read off the output.** `cata/regular.tex`'s premises name `t'` with
`t' ∈ D_8`/`D_9` and **no binder**: `OpPrim` is documented in the source (l.45) as "as `OpSum`
but the sibling is not bound here", and `prim_node` (l.94) indeed omits the `EXFORALL` that
`sum_node` adds. A reader cannot tell from the printed rule whether the premise is "for some
`t'`" or "for every `t'`", and the two differ in soundness unless the set is a singleton.

---

## EXT-2b — layered Boolean state matrix (general `regular`)

**Instantiated by:** `regular` in general, `regular_nfa`, `regular_regexp` in general.

**Maths.** `Q` states, `δ ⊆ Q × Σ × Q`, start `q₀`, accepting `F`.

- `B1_{i,t} ⇔ X_i = t`.
- `S_{i,q}` — "state `q` is reachable at layer `i`". `S_{1,q₀}`, `⋁_{q∈F} S_{n+1,q}`.
- `E_{i,q,t} ⇔ S_{i,q} ∧ B1_{i,t}` (`rule3`) — "transition taken".
- `S_{i+1,q'} ⇔ ⋁_{(q,t) : δ(q,t)=q'} E_{i,q,t}` (`rule4`).

For a DFA the `⋁` is over a single `(q,t)` per `q'` per symbol; the NFA case is the same
schema without that restriction, which is why `regular_nfa` is a pure instance here.

**Rule schemas.** `rule1`, `rule3`, `rule4` only — no sums. Mechanically the *schemas* are E0.

**Index families needed: `i`, `t`, `q`, `q'` — four, and `r`/`p` are then unavailable.**
`ind_fam` is the closed enum `FI | FT | FP | FR` (source l.38) with hardcoded printers
`i`/`t`/`p`/`r` (l.373). Two state families can only be squeezed in by borrowing `FP` and `FR`
and printing an automaton state as `p` or `r`.

**E-code: E1 + E2.** E1 for the `S`/`E` families (`var_name` is the closed enum
`X | B of int | T | I | V | N | O`, source l.3 — the `B of int` family can in principle absorb
them, but then every layer prints as `B`). E2 for `δ` as a 2-D relation on `(q,t)`.

**D-0004 cost, stated plainly because it is the whole question here.** `S_{i,q}` does **not**
wash out. It is the pivot of every derived rule: a conclusion `X_i ≠ t` is reached because no
state at layer `i` admits `t`, and the generator's DNF flattening (`an`, source l.~355) has no
resolution step that eliminates a pivot appearing on both sides. So a printed premise would read
`S_{i,q}` — "the automaton is in state `q` before position `i`" — a variable the user never
wrote. That is precisely the leak D-0004 forbids by default. **EXT-2b is therefore the shape
that is cheap for the engine and expensive for the catalog**, and EXT-2a is the reverse. There is
no third option in the current format; see `_gaps-ext.md`.

---

## EXT-2 addendum — M-1's inlining criterion, tested

`docs/GCCAT.md` proposes: *a state variable may be inlined when its state predicate is a finite
disjunction over user literals.* Tested against EXT-2a/EXT-2b/EXT-3, by writing out the state
predicate in each case:

| constraint | state predicate `S_{i,q}` as a formula over user literals | criterion as written | sharpened |
|---|---|---|---|
| `increasing` | `X_{i-1} ≤ v` — one literal | passes | passes |
| `int_value_precede` | `⋁_{j<i} X_j = S` — a clause, length `i-1` | passes | passes |
| `regular`, strictly 2-local | `X_{i-1} ∈ V_q` — a clause over one position | passes | passes |
| `regular`, general | a DNF whose disjuncts are conjunctions of length up to `i-1` | **passes vacuously** | fails |
| `mdd` / `mdd_nondet` | set of prefixes reaching the node — same DNF form | **passes vacuously** | fails |
| `cost_regular` / `cost_mdd` | an integer counter value | fails | fails |

**Verdict: the criterion is right in direction and wrong as written.** Over finite domains and a
fixed `n`, *every* predicate over `X_1..X_{i-1}` is a finite disjunction over user literals —
its full DNF. So "finite disjunction over user literals" is satisfied by general `regular` and by
`mdd`, and the criterion draws no line at all. M-1's own worked examples show what was meant: in
every passing case the state predicate is a disjunction **of literals** — a clause — not a
disjunction of conjunctions.

**Sharpened form, offered as a proposal and not as a decision:** *a state variable may be
inlined when its state predicate is equivalent to a **clause** over user literals — a disjunction
in which every disjunct is a single literal.* This is the right shape because a clause over user
literals is exactly what a premise set already is, so inlining is substitution and needs no new
machinery. Under the sharpened form the table above separates cleanly, `increasing` and
`int_value_precede` still pass (the second with an unbounded but width-1 clause, which is fine —
length is not the problem, disjunct width is), and it explains *why* EXT-2a works and where it
stops: EXT-2a is precisely the case where the state predicate collapses to a one-position clause.

M-1 also wrote that counter automata fail "because a counter's value is not a disjunction of user
literals". That part holds under both readings.

---

## EXT-3 — layered DAG with edge flow (MDD)

**Instantiated by:** `mdd`, `mdd_nondet`.

**Maths.** Layered DAG, nodes `N_{i,v}`, edges `e` labelled `lab(e) ∈ [1,m]` from layer `i` to
`i+1`.

- `B1_{i,t} ⇔ X_i = t`.
- `Ed_{i,e} ⇔ N_{i,tail(e)} ∧ B1_{i,lab(e)}` (`rule3`).
- `N_{i+1,v} ⇔ ⋁_{e : head(e)=v} Ed_{i,e}` (`rule4`); root asserted, `⋁` over sinks asserted.

**Rule schemas.** `rule1`, `rule3`, `rule4`. Same schema set as EXT-2b; an MDD is EXT-2b with the
state set allowed to differ per layer, so **EXT-3 collapses into EXT-2b mechanically** and is
kept separate only because `lab`/`head`/`tail` are three constant tables rather than one.

**E-code: E1 + E2** (`CHRISTMAS_LIST.md` §5 agrees).

**Auxiliaries: unavoidable, and D-0004 says so in as many words** — "Some constraints
(`sliding_sum`, `mdd`) have no known auxiliary-free decomposition. Those entries record their
auxiliaries' definitions alongside the rule." So `mdd`'s entry is licensed to leak `N_{i,v}` and
`Ed_{i,e}` into premises, and must print their definitions beside the rules.

**The gap that matters is not the auxiliaries.** The published MDD explanation (Gange, Stuckey,
Szymanek 2011, `CHRISTMAS_LIST.md` §5) is *not* the clausal unfolding above: it explains a value
removal by a **reachability** argument over the diagram — no path through that edge survives —
and reports it as a set of `X` literals. Deriving that from EXT-3 needs a pass that resolves away
every `N`/`Ed` pivot along all paths. The generator's pipeline is AND/OR traversal plus DNF
flattening with cycle detection; it has no resolution or reachability step. So EXT-3 is
*expressible* at E1+E2 while the explanation the literature considers the right one is not
derivable from it — closer in character to E4/E6 than to E1/E2.

---

## EXT-4 — EXT-2b/EXT-3 plus an integer accumulator

**Instantiated by:** `cost_regular`, `cost_mdd`.

Adds `C_{i+1} = C_i + c[q,t]` and a final `C_{n+1} ≤ K` (or a bound on a user variable).
`CHRISTMAS_LIST.md` §5 prices it E1+E2+E3; this session's reading adds that the accumulator is
the first thing in either section that needs **arithmetic on variable *values*** rather than on
*indices*. Every arithmetic construct in the format (`Addint`, `Addcst`, `OpShift`, `OpShiftC`)
operates on `ind_name`s inside an index list. Fails the sharpened inlining criterion, so the
accumulator is a genuine leaking auxiliary with no auxiliary-free alternative known here.

---

## SCH-1 — time-point overlap plus a Boolean sum per time point (unary resource)

**Instantiated by:** `disjunctive`, `disjunctive_strict`; and this is what the shipped
`cumul` entry (generator l.680–682) actually is.

**Maths.** `X_i` = start of task `i`, duration `d_i` a constant, `t` a time point.

- `B1_{i,t} ⇔ X_i ≥ t`, `i ∈ [1,n]`, `t ∈ [1,m]`, **BC** (not AC — this is the one shape in
  either section that is a bounds decomposition).
- `B2_{i,t} ⇔ B1_{i,t−d_i+1} ∧ ¬B1_{i,t+1}` — "task `i` is running at time `t`"; `rule3` with
  two `Decomp_devent`s of the same family and opposite signs, the first shifted in `FT` by the
  per-task constant `d_i` (`OpShiftC (FT,·,C 1,FI)`).
- `∑_{i∈[1,n]} B2_{i,t} ≤ 1` — `rule5`.

**E-code: E0 for the schemas** — this shape runs today and `cata/cumulative.tex` is its output.
The capacity `1` is implicit in the choice of `rule5` and is never printed; that is gap G1 from
`docs/DECOMP_FORMAT_NOTES.md`, and here it is not cosmetic, because it is the difference between
a unary and a cumulative resource.

**Auxiliaries.** `B1`, `B2` both wash out: `cata/cumulative.tex` (read off the output) prints
only `X_i ≥ t` / `X_i < t` literals plus index equations. D-0004 satisfied.

**Known weakness of the derived rule, read off the output.** Both emitted rules explain by
`∀i', i' ≠ i, i' ∈ [1,n]` — *all* other tasks. Schutt, Feydy, Stuckey & Wallace 2011 explain with
a **small window and a capacity argument** naming a subset. Getting from one to the other is
D-0006's E4 ("counting / pigeonhole reasoning across several cardinality constraints"), which
D-0006 labels the research. `rule5` reasons *within* one sum, and the window argument reasons
across time points.

**Measured status.** `docs/VALIDATOR.md` l.330 reports `cumulative` as **not checkable**: the
parser emits `UNPARSED: index equation offset: t'=t-d_{i}` and the capacity appears in no atom.
So this shape currently has no measurement at all, in either direction.

---

## SCH-2 — SCH-1 with weights and an explicit capacity (cumulative resource)

**Instantiated by:** `cumulative`, `cumulatives`, `cumulative_opt`.

Identical to SCH-1 except the last line: `∑_{i∈[1,n]} r_i · B2_{i,t} ≤ C`.

Three things are new against SCH-1, all of them format requirements rather than
decomposition choices:

1. **weights `r_i` on the summands** — `rule5`/`6`/`7` sum a Boolean family unweighted;
2. **the capacity `C` must appear in the printed rule** (G1 again, now load-bearing);
3. if `r_i` or `d_i` is a **variable**, the atom becomes variable-vs-variable
   (`X_i + D_i ≤ X_j`), which is G3.

`CHRISTMAS_LIST.md` §6 prices `cumulative` as E2 + E4. This session's reading is that the
weighting in (1) is a *third* requirement that neither E2 nor E4 as written in D-0006 covers;
see `_gaps-ext.md`, including a contradiction in how `E3` is used.

---

## SCH-3 — weighted sums over integer variables

**Instantiated by:** `knapsack`.

`∑_i w_i · X_i ≤ W` and `∑_i p_i · X_i ≥ P` over the *same* `X`. Two sums, weighted, over
integer-valued (not Boolean) summands. Every part of this is outside the Boolean-sum schemas:
two families in one reasoning step is the `failwith "sommes multiples pas encore implémentés"`
site (source l.320/334/348), the weights are SCH-2's (1), and integer summands have no encoding
at all. `CHRISTMAS_LIST.md` §6 gives E1 + E3.

---

## Modifiers (apply on top of a shape, not shapes of their own)

- **M-opt — optional tasks.** `disjunctive_opt`, `cumulative_opt`. Add a Boolean existence
  family `Ex_i` and conjoin it: `B2_{i,t} ⇔ Ex_i ∧ (overlap)`. `rule3` already takes a
  three-element `Decomp_devent` list, so the *schema* is E0; the family name is E1 (G2 — the
  `var_name` enum has no free letter that means "this constraint's own optionality flag";
  reusing `O` borrows `global_cardinality`'s printed letter). `Ex_i` is a user-visible variable
  in the MiniZinc signature, so it leaks *legitimately* under D-0004 — the user wrote it.
- **M-mach — machine assignment.** `cumulatives`. The sum at (machine `k`, time `t`) ranges over
  `{ i : M_i = k }` — an index set determined by a **decision variable**. Nothing in `ind_set`
  or `ind_op` is variable-dependent. See `_gaps-ext.md`.
