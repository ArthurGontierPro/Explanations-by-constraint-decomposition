# The validator (W0-T1)

`validator.ml`, run with `make validate`. Written before any generator bug is
fixed, per **D-0005**.

**This covers 3 of the 16 catalog entries. It is not a whole-catalog gate and
must not be cited as one.** The other 13 entries are untouched by it and remain
*generated, unvalidated*. `make check` is a different thing: it proves the
generator still reproduces the committed `.tex` byte-for-byte, which is a
reproducibility claim and says nothing about whether a rule is true.

| | |
|---|---|
| in scope | `cata/table.tex`, `cata/atleastnvalues.tex`, `cata/atmostnvalues.tex` |
| rules checked | 13 |
| flagged today | 13 |
| out of scope | the other 13 entries — generated, unvalidated |

---

## What is parsed and what is hand-encoded

This is the part that costs trust, so it is stated first.

**Parsed from the shipped artifact (good):** the *rule* — premises, conclusion,
quantifiers, index sets, disequalities — is read out of `cata/*.tex` by the
parser in `validator.ml`. Nothing about the rule is retyped. If the generator's
output changes, the validator is checking the new output.

**Hand-encoded in `validator.ml` (the cost):** the *ground semantics* — what the
decomposition under the rule actually means. Three predicates:

| entry | hand-encoded as | read off |
|---|---|---|
| `atleastnvalues` | number of distinct values in `X` is `>= N` | generator l.410–413 |
| `atmostnvalues` | number of distinct values in `X` is `<= N` | generator l.414–417 |
| `table` | the tuple `X` is one of the table's rows | generator l.429–431 |

**Why it could not be derived.** The decomposition in `explenation generator.ml`
carries its index modifications as two OCaml closures per `devent`
(`index_update`, `index_propagate`). A closure cannot be printed, compared or
inverted, so there is no way to read a decomposition's meaning out of the
program without executing it against a semantics it does not have. That is
exactly **W1-T7**, which the roadmap already names as a prerequisite for this
task. W1-T7 is not done and this session may not restructure the generator, so
the ground semantics was transcribed by hand instead.

**What that costs.** If a transcription is wrong, the verdicts are wrong. The
transcriptions are three one-line predicates over a complete assignment, and
they are the standard readings of `at_least_nvalue`, `at_most_nvalue` and
`table`, so the exposure is small — but it is real, and it is the single
weakest link in this validator. **Nobody should treat a `SOUND` verdict from
this tool as final until W1-T7 lands and the ground semantics can be derived
from the decomposition instead of typed next to it.**

There is a second, smaller cost: `cata/table.tex` refers to an index set `D_4`
that the printer never defines (it falls through to an undefined `D_k`; see
CLAUDE.md). The validator reads `D_4` as the table's row set, which is what the
decomposition means. That is an interpretation, not something the `.tex` says.

---

## What "sound" means here

A rule `P1, ..., Pk / C` is **sound** iff for every domain store `S` satisfying
every `Pj`, every solution of the decomposition inside `S` satisfies `C`.
Literals are read as store facts:

| literal | as a premise (store fact) | on a solution |
|---|---|---|
| `X_i = t` | `D(X_i)` is a subset of `{t}` | `x_i = t` |
| `X_i != t` | `t` is not in `D(X_i)` | `x_i != t` |
| `N >= p` | `lb(N) >= p` | `N >= p` |
| `N < p` | `ub(N) < p` | `N < p` |

A premise is **droppable** iff the rule stays sound without it; a rule with a
droppable premise is not minimal, and is flagged.

### The singleton reduction, and why the store sweep is still run

Every premise literal above is *anti-monotone* in the store: shrinking the store
preserves it. Universal and existential quantification preserve
anti-monotonicity, and "every solution in `S` satisfies `C`" is anti-monotone
too. So if any store `S` satisfies the premises and contains a solution `sigma`
violating `C`, then the singleton store `{sigma}` also satisfies the premises
and still violates `C`. Hence

> sound **iff** for every complete assignment satisfying the ground constraint,
> premises imply conclusion.

That replaces an enumeration over `2^(m*n)` stores with one over `m^n`
assignments, which is what makes `n, m <= 4` cheap.

D-0005 asks for the store enumeration in so many words, so **both** are
implemented. The full store sweep runs at the smaller sizes and every rule is
checked under both; a disagreement is a bug in `validator.ml` and the run says
so and exits 2. Today all 13 rules agree under both methods (`make validate`,
13 lines reading `cross-check: store sweep agrees with singleton reduction`).

### Sizes enumerated

| entry | sizes | ground instances |
|---|---|---|
| `atleastnvalues`, `atmostnvalues` | `n, m` in {2,3,4}, all 9 pairs; `N` in `[0,n]` | 1 each |
| `table` | `n, m` in {2,3}; store sweep at `n=m=2` | every table with 1 or 2 distinct rows over `[1,m]^n` |

A rule is schematic over tables, so `table` verdicts quantify over all those
tables: unsound means some table refutes it, droppable means no table needs it.

---

## Quantifier ambiguity: the shipped LaTeX does not always determine the rule

This was not anticipated and it is worth recording. Repeated index composition
in the generator emits prefixes that contradict themselves. `atleastnvalues`
rule 4 ships this premise:

```
X_{i}=t, ∃i, i∈[1,n], ∀i, i∈[1,n], ∀t, t∈[1,m], ∀i, i∈[1,n]
```

`i` is quantified three times, twice universally and once existentially. No
uniform parsing policy recovers the intent, because there is no intent in the
string — the prefix is an artifact of composing index functions that cannot be
inspected (W1-T7 again).

The validator therefore checks **every consistent reading**: each permutation of
the bound variables, each quantifier the variable is actually written with, and
— for a variable that is also free in the conclusion — both "reuse the
conclusion's copy" and "bind a fresh one". Verdicts:

- **UNSOUND** — fails under *every* reading. No better parser can overturn this.
- **AMBIGUOUS** — sound under some readings, unsound under others. This is a
  defect of the artifact, not a gap in the checker: the `.tex` does not say
  which rule it means.
- **VACUOUS** — sound, but no store in scope satisfies the premises, so the rule
  can never fire. Reporting these as `SOUND` would be an overclaim.
- **UNSOUND(firing)** — every reading that survives is vacuous, so the only
  reading under which the rule could ever fire is an unsound one.
- **NOT MINIMAL** — sound and it fires, but a premise is droppable.
- **SOUND and MINIMAL** — the only unflagged verdict. No catalog rule has it.

---

## The controls

A checker that flags everything proves nothing, so `make validate` runs four
hand-written control rules first, in the same LaTeX dialect, and asserts each
lands in its expected verdict: one genuinely sound and minimal, one sound with a
redundant premise, one flatly unsound, one vacuous. If a control regresses the
run says so and exits 2. `make validate-selftest` runs just the controls.

The sound+minimal control matters most: it is the evidence that the 13 catalog
flags are findings rather than a stuck checker.

---

## What it found (2026-09-18, `make validate`)

All 13 in-scope rules are flagged. **The two acceptance defects from D-0005 are
both flagged independently.**

### `cata/table.tex` — 3 rules, 3 unsound

| rule | verdict |
|---|---|
| 1. `(no premise) / X_i = t` | **UNSOUND under every reading** — the acceptance case. An empty premise concludes a fixing. Counterexample: `n=m=2`, table `{(1,1)}`, `i=1`, `t=2`. |
| 2. `X_i != t / X_i = t` | **UNSOUND under every reading** — premise and conclusion contradict each other, under both the shared-`i` and fresh-`i` readings. |
| 3. `∀i'!=i: X_i' = t / X_i != t` | **UNSOUND under every reading** — a table may contain a constant row. This rule is shaped like an `alldifferent` rule and does not belong here. |

Also worth recording: in rules 2 and 3 the row index `r` is quantified in the
premise but appears in no atom, so the rule cannot express "row `r` is
excluded". The row index is carried and then dropped.

### `cata/atleastnvalues.tex` and `cata/atmostnvalues.tex`

These two files are byte-identical (1025 bytes each) although their
decompositions differ — `rule6` vs `rule5`, and the reified event's sign flipped.
The verdicts are **not** identical, which is the point:

| rule | atleastnvalues | atmostnvalues |
|---|---|---|
| 1. `X_i != t' (∀t'!=t), N >= p (∀p) / X_i = t` | NOT MINIMAL — `N >= p` droppable | NOT MINIMAL — `N >= p` droppable |
| 2. `∀i'!=i: X_i' != t / X_i = t` | **UNSOUND** (`X=(2,2)`, `i=1`, `t=1`) | **UNSOUND** (same shape) |
| 3. `X_i = t' (∀t'!=t), N < p (∀p) / X_i != t` | **AMBIGUOUS** | **VACUOUS** |
| 4. `X_i = t / N >= p` | **UNSOUND(firing)** | **UNSOUND(firing)** |
| 5. `X_i != t (∀i, ∀t) / N < p` | VACUOUS | VACUOUS |

**Rule 3 is the discriminator.** The same premise string is ambiguous-but-
sometimes-sound against the at-least decomposition and unsatisfiable against the
at-most decomposition. One string cannot be the right rule for both, and the
validator says so without being told which file is the suspect one.

**Rule 4 is the sharper finding.** Of its four readings, three are vacuous and
the fourth — `∀t ∃i: X_i = t`, plainly the intended one — is unsound in both
files. The counterexamples differ in a way that tracks the real semantics:

- against at-least (`nvalue(X) >= N`), it fails at `n=m=2, p=1`. Information
  about `X` bounds `N` from *above* here, so concluding `N >= p` is the wrong
  direction outright.
- against at-most (`nvalue(X) <= N`), it fails only at `p > m` — first
  counterexample `n=3, m=2, p=3`. The direction is right; the bound is off.

So the shared rule is a boundary error for one constraint and a direction error
for the other. That is what the byte-identical output was concealing.

---

## Running it

```sh
make validate            # controls, then the 3 entries
make validate-selftest   # just the controls
./_build/validator .     # the binary directly, if you want its exit code
```

The **binary** exits `0` nothing flagged, `1` something flagged (today's
expected state), `2` the controls or the store-sweep cross-check failed — in
which case the verdicts mean nothing and `validator.ml` is what needs fixing.

`make validate` deliberately passes `1` through as success and only fails on
`2`: today every in-scope rule is flagged, and that is the finding, not a
breakage. What `make validate` fails on is the validator itself going wrong.

`make validate` is deliberately **not** part of `make check`. It exits 1 today
by design, and a gate that is red on purpose trains people to ignore it. It
turns green as W1 fixes the rules.

---

## Deliberately left out

- **The other 13 catalog entries.** Each needs its own hand-encoded ground
  semantics, and every hand-encoding adds exposure. Extending the scope is worth
  doing *after* W1-T7, when the semantics can be derived rather than typed.
- **Bounds vs arc consistency as distinct regimes.** `N` is treated as an
  interval (BC) and `X` by value removal (AC), matching how the entries are
  generated, but the validator does not check that a rule is *the* AC or BC
  explanation — only that it is sound and minimal.
- **Whether a rule is the strongest available explanation.** Minimality here
  means no premise is droppable; it does not mean no smaller premise set exists.
- **Any fix.** Per D-0005 the validator comes first. `validator.ml` changes no
  generator code and no `.tex`.
