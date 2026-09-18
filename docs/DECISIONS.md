# Decision records

**Append-only.** Add new records at the bottom. Never reflow, reorder or rewrite an existing
one — a decision log records what was true when it was written. To amend, add a new record
that supersedes the old one by number and say so in both.

Records D-0001 … D-0008 were settled in a design session on 2026-09-18 between the author
and a Claude session that had surveyed the CP explanation literature. Two of them (D-0002,
D-0003) record a **correction the author made to a wrong proposal from that session**; the
wrong proposal is written out in full, because a future session that has not seen the
argument will otherwise re-propose it.

---

## D-0001 — Explanations derived from a correct decomposition are sound for the global constraint

**DECIDED.** If `D` is a correct decomposition of constraint `C`, then `sol(D)` projected onto
`C`'s variables equals `sol(C)`. Therefore a clause over `C`'s literals is entailed by `D`
**iff** it is entailed by `C`.

Two consequences, and the second is the one people get wrong:

1. Decomposition-derived explanations are sound *for the global constraint*. The decomposition
   is a proof device, not a semantic compromise.
2. **The decomposition imposes no ceiling on explanation quality.** Propagation strength and
   logical strength are different things. The pairwise-`≠` decomposition of `alldifferent`
   logically entails every Hall-set explanation. The reason the current generator does not
   find them is that its procedure mimics unfolding-style propagation rather than consequence
   finding — a limitation of the *procedure*, not of the decomposition.

The 2020 CPTAI paper does not state this theorem. It should be written up; it is the
foundation the whole programme rests on.

## D-0002 — Reification stays. It is the integer→Boolean interface, not an obstacle

**DECIDED**, as a correction.

**The wrong proposal, recorded so it is not made again:** that the architecture's assumption
"every atomic constraint in a decomposition has the shape *one reified Boolean ⇔ something*"
should be dropped, so that non-reified integer constraints like `S[i] = xs[i] + S[i-1]` could
be expressed directly.

**Why it is wrong.** The framework *already* handles auxiliary integer variables, through
reification: `gccn` channels the occurrence array `O` with `rule1`, and `nvalues` does the
same with `N`. `rule1` **is** the integer→Boolean interface, and it is the same move the LCG
literal vocabulary makes — `[x ≥ v]` is an order encoding, i.e. a reification.

So reification is the backbone and stays. The real gaps are narrower, and are recorded in
D-0006: `var_name` being a closed enum, and the side-condition language being too weak to
relate the thresholds of several reified atoms.

## D-0003 — Decompositions are authored here, for explanation quality. MiniZinc is a coverage map, not the input corpus

**DECIDED**, as a correction.

**The wrong proposal, recorded so it is not made again:** that MiniZinc's `fzn_*` predicate
bodies should be parsed and used as the project's input corpus, on the grounds that they are
free, maintained and machine-readable.

**Why it is wrong.** MiniZinc's decompositions are chosen for flattening and propagation
efficiency — **not** for explanation quality. Taking them imports someone else's optimisation
target.

The worked case is `regular`. MiniZinc introduces explicit state variables
(`a[i+1] = d[a[i], xs[i]]`). This repo's own decomposition encodes the transition directly on
consecutive `X` variables via value sets `D_8`/`D_9`, with **no state variables at all**. Those
are different decompositions of the same constraint, and this repo's is better *for
explanation*: its rules mention only `X` literals, i.e. the user's own variables, where
MiniZinc's would produce explanations about invented automaton states nobody wrote.

**The choice of decomposition is the modelling act, and it is ours.** The tool is a calculator
that derives and checks the explanations of a decomposition we chose; it is not a discovery
procedure over decompositions found in the wild.

MiniZinc keeps one role: a **coverage map** telling us which constraints are even in reach.
That map is `CHRISTMAS_LIST.md`.

## D-0004 — Prefer auxiliary-free decompositions; auxiliaries leak into the explanation

**DECIDED.** Where a decomposition can be designed without auxiliary variables, design it that
way, even at the cost of a longer rule.

An auxiliary in the decomposition appears in the explanation. A reader of the catalog — or a
user of a solver — gets a rule about `a[i]`, a variable they never wrote. `regular` (D-0003) is
the worked example: avoiding state variables keeps every premise in the user's vocabulary.

This **reverses** an earlier recommendation in the same session, which argued for admitting
auxiliaries because they make explanations shorter and because real LCG solvers explain over
them. That argument is correct *for a solver* and wrong *for a catalog*: the solver benefits
from short auxiliary-laden clauses, the reader does not. Where the two conflict, the catalog
is the customer.

Not absolute. Some constraints (`sliding_sum`, `mdd`) have no known auxiliary-free
decomposition. Those entries record their auxiliaries' definitions alongside the rule.

## D-0005 — The validator is written before any bug is fixed

**DECIDED.** W0-T1 builds the validator first. Only then are the generator's defects fixed.

The validator: for `n, m ≤ 4`, enumerate all domain stores; check that whenever the premises
hold, the decomposition entails the conclusion; and check that no premise is droppable.

**Its acceptance test is that it independently flags the two entries already known to be
wrong** — `cata/table.tex`'s empty-premise rule, and `atleastnvalues.tex` being byte-identical
to `atmostnvalues.tex`. If it does not flag them, the validator is wrong, not the catalog.

The ordering is the point. Writing the fixes first means grading your own homework: every
existing `.tex` renders, so nothing about the output distinguishes a correct rule from a
plausible one. This is also why no session may call an entry correct before W0-T1 lands.

## D-0006 — The extension taxonomy, and the two real gaps in the current encoding

**DECIDED** as shared vocabulary. Full per-constraint mapping in `CHRISTMAS_LIST.md`.

| code | extension |
|---|---|
| E0 | none — works today |
| E1 | open `var_name` so new auxiliary integer families can be added |
| E2 | richer side conditions: inequalities against expressions, 2-D constant tables |
| E3 | multi-family cardinality (removes `failwith "sommes multiples"`) |
| E4 | counting / pigeonhole reasoning across several cardinality constraints |
| E5 | set → Boolean channelling |
| E6 | graph reachability — out of scope |
| E7 | floats / non-linear — out of scope |

**E1 and E2 are the only two things standing between the current tool and the automaton /
sequence families.** Both are narrow:

- **E1**: the mechanism exists (D-0002) — `rule1` already channels `N` and `O`. `var_name` is
  simply a closed enum with hardcoded printers.
- **E2**: `Rel` relates two index *names*; `Addcst` does `i₃ = i₂ ± c·i` over a 1-D constant
  array. Needed: inequalities against expressions (`u − t`, for `sliding_sum`) and 2-D tables
  (`d[q,s]`, for `regular`).

**E4 is the research**, and it buys few constraints. It is the only route to explanations
matching the published hand-written ones (Downing on `alldifferent`, Schutt on `cumulative`).
The seed exists: `rule5/6/7` *are* cardinality rules. Strengthening them to reason **across**
several sums, rather than within one, is the path — not a generic "minimisation pass".

**E1 and E2 both land in the rule engine**, so they do not go out to concurrent sessions in
the same wave.

## D-0007 — OPEN: breadth or depth

**NOT DECIDED.** Roughly 50 constraints with sound-but-weak rules, versus a handful that match
the published hand-written explanations.

Deliberately deferred to the W2 gate, because W0 and W1 are prerequisites either way and the
decision is better made with validator output than with instinct. Whoever closes it: the
evidence to bring is what fraction of W1's entries survive validation, and how far the
`cumulative` and `alldifferent` rules sit from their published baselines.

## D-0008 — OPEN: what "complete" means for an entry

**NOT DECIDED.** "A complete catalog of all explanations" needs a definition that is checkable.

The candidate: for a fixed constraint, a fixed literal vocabulary and a fixed event, the set of
**prime implicates** that conclude that event — finite, canonical and checkable at fixed arity.

Two problems to settle with it. First, some entries' complete sets are exponential even at
small `n` (`alldifferent`'s is all Hall sets), so entries must be labelled `complete` or
`partial` individually rather than uniformly. Second, lifting from a fixed arity to a schema
valid for all `n` is a **conjecture** step; either prove it by induction or mark the entry
empirical. Do not let a schema validated at `n ≤ 6` be described as proved.

## D-0009 — OPEN: a shipped rule needs a `VACUOUS` verdict, and the `.tex` does not determine the rule

**NOT DECIDED.** Raised by W0-A's validator output on 2026-09-18; recorded here so it is not
rediscovered, not settled — this one is the author's to close.

Two findings, both from `make validate` over `table`, `atleastnvalues`, `atmostnvalues`:

1. **Three shipped rules are sound only because their premises can never hold.** The validator
   calls this `VACUOUS`. It is not the same property as soundness and it should not be reported
   as success: a rule that cannot fire explains nothing, and counting it as correct would
   inflate any future coverage claim. The proposal is a distinct verdict — `SOUND and MINIMAL`
   / `VACUOUS` / `AMBIGUOUS` / `UNSOUND` — and a rule that "passes" vacuously is a defect
   report, not a pass.

2. **The emitted LaTeX is lossy.** Repeated index composition prints self-contradictory binder
   prefixes (one premise carries `∃i, ∀i, ∀t, ∀i`), so the shipped artifact does not determine
   which rule was meant. W0-A's validator therefore enumerates *readings* of each rule and
   reports per-reading verdicts. That is the honest response to a lossy artifact, but it is a
   workaround: the real fix is W1-T7, and this raises W1-T7 from a refactor to a correctness
   prerequisite.

**Bearing on D-0008** (what "complete" means per entry): a prime-implicate definition has to
exclude vacuous implicates, or "complete" is satisfiable by rules that never fire.

**Bearing on W2-T4 / D-0007** (breadth or depth): the evidence D-0007 was waiting for has
started to arrive and it is bad — of 13 rules validated in 3 entries, **0 were sound and
minimal**. One wave of validation on the remaining 13 entries should precede that decision.

## D-0010 — CLOSES D-0007: breadth. All 118 MiniZinc globals is the goal

**DECIDED by the author, 2026-09-18**, in these words: *"we still want all minizinc constraints
this is our main goal."* D-0007 is closed; it was deferred to the W2 gate, and the author closed
it earlier and from the top instead.

Consequences, so this is not re-argued:

- **W4 is demoted, not cancelled.** Reaching Downing's Hall-set `alldifferent` or Schutt's
  `cumulative` explanation (W4-T2, W4-T3) is no longer the measure of success. A sound, weak,
  *user-vocabulary* rule for 118 constraints beats a publication-grade rule for two. E4 stays on
  the roadmap as research, off the critical path.
- **The critical path is E1 → E2 → E3**, in the rule engine, sequentially. That is what stands
  between the current tool and the automaton, sequence and cardinality families, which are most
  of the 118. D-0006 already says these do not share a wave.
- **The Global Constraint Catalog is an example, not a template** (author, same message). M-1
  read it for inspiration and it earned its keep — argument properties corroborated W1-T5 — but
  MiniZinc's 118 globals remain the target list, per D-0003. `docs/GCCAT.md` is reference, not a
  specification to conform to.
- **Coverage still means validated coverage.** Breadth does not relax W0-T1. An entry that is
  generated and unvalidated is not coverage; today that is 13 of 16 entries, and of the 3
  measured, 0 rules are sound and minimal.
