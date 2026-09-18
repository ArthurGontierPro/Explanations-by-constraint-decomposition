# The validator (W0-T1, extended to the catalog by W1-T8)

`validator.ml`, run with `make validate`. Written before any generator bug is
fixed, per **D-0005**.

**This covers 11 of the 16 catalog entries. The other 5 are reported OUT OF
SCOPE with a machine-checked reason — they are not silently skipped, and they
are not "unvalidated" in the same sense: they *cannot* be validated as they
stand.** `make check` is a different thing: it proves the generator still
reproduces the committed `.tex` byte-for-byte, which is a reproducibility claim
and says nothing about whether a rule is true.

| | |
|---|---|
| entries in scope | 11 |
| rules checked | 42 |
| **SOUND and MINIMAL** | **11** (26%) |
| flagged | 31 |
| entries out of scope | 5 (`among`, `cumulative`, `range`, `regular`, `roots`) |
| rules out of scope | 14 |
| encoding invariants | 19, all holding |
| controls | 11, all behaving |
| runtime | 4.5 s (measured, `time ./_build/validator .`) |

W1-T8 measured the committed `cata/*.tex` **as they stand**, deliberately
without regenerating them: another session was changing the generator
concurrently, and the value of these numbers is that they predate the engine
fixes. Nothing in `cata/` or in the generator was touched.

Precisely: the rule text measured is byte-identical to `8d1ac98` for all 16
entries (verified per file by stripping `%%` comments and comparing the `\frac`
text). W1-T3 landed in between and appended `%% generator diagnostics` comment
lines to `cata/*.tex`; they contain no `\frac` and the parser ignores them.

---

## What is parsed and what is hand-encoded

This is the part that costs trust, so it is stated first.

**Parsed from the shipped artifact (good):** the *rule* — premises, conclusion,
quantifiers, index sets, disequalities, index equations — is read out of
`cata/*.tex` by the parser in `validator.ml`. Nothing about the rule is retyped.
If the generator's output changes, the validator is checking the new output.

**Hand-encoded in `validator.ml` (the cost):** the *ground semantics* — what the
decomposition under the rule actually means.

| entry | hand-encoded as | read off | gccat `Purpose` (fetched 2026-09-18) |
|---|---|---|---|
| `alldifferent` | all `X_i` distinct | generator l.387–388 | `Calldifferent` |
| `allequal` | all `X_i` equal | l.383–386 | `Call_equal` |
| `increasing` | `X_i <= X_{i+1}` | l.397–398 | `Cincreasing` |
| `decreasing` | `X_i >= X_{i+1}` | l.399–400 | `Cdecreasing` |
| `element` | `V = X_I` | l.401–405 | `Celement` |
| `nvalues` | `#distinct(X) = N` | l.406–409 | `Cnvalue` |
| `gcc` | `O_t = #{i : X_i = t}` | l.393–396 | `Cglobal_cardinality` |
| `atleastnvalues` | `#distinct(X) >= N` | l.410–413 | `Catleast_nvalue` |
| `atmostnvalues` | `#distinct(X) <= N` | l.414–417 | `Catmost_nvalue` |
| `table` | the tuple `X` is one of the rows | l.429–431 | none (gccat has no `table`) |
| `sum` | `sum(X) = N` | **no decomposition exists** | `Csum_ctr`, with `CTR` = `=` |

`cata/sum.tex` is the orphan the Makefile already tracks: nothing in the
generator produces it, so its semantics has **no source in this repo** and was
taken from gccat alone. That is a weaker provenance than the other ten and its
verdicts should be read accordingly.

**Why it was not derived — and what changed under this session.** The
decomposition in `explenation generator.ml` carried its index modifications as
two OCaml closures per `devent`. A closure cannot be printed, compared or
inverted, so there was no way to read a decomposition's meaning out of the
program without executing it against a semantics it does not have. That is
**W1-T7**, which the roadmap names as a prerequisite for this task, and it was
not done when W1-T8 began.

**W1-T7 landed while W1-T8 was running** (commit `463534f`, "index modifications
as data, not closures": the closures are now an `ind_op` datatype with an
explicit inverter). W1-T8 did not consume it — its brief was to measure the
committed artifact while the generator was moving, and it may not touch the
generator. So the hand-encoding stands, and **the follow-up is now unblocked**:
the ground semantics can be derived from the `ind_op` data instead of typed
beside it. Whoever picks that up should treat the eleven predicates here as the
thing to reproduce, not to trust.

### Two defences on the hand-encoding (W1-T8)

Hand-encoding eleven predicates is eleven chances to be wrong, so the encodings
are themselves checked before any rule is judged. This is M-1's proposal from
`docs/GCCAT.md` §3, implemented. **19 invariants, all holding**; a failure exits
2 and the rule verdicts are then worthless.

**(a) Closure properties** — gccat's `Arg. properties` field, quoted from the
entry pages fetched 2026-09-18:

| invariant | source |
|---|---|
| `atleast_nvalue` extensible wrt VARIABLES | `Catleast_nvalue` (M-1 verified) |
| `atleast_nvalue` monotone, `NVAL` can be decreased | `Catleast_nvalue` (M-1 verified) |
| `atmost_nvalue` contractible wrt VARIABLES | `Catmost_nvalue` (M-1 verified) |
| `alldifferent`, `all_equal`, `increasing`, `decreasing` contractible wrt VARIABLES | the four entry pages |
| `nvalue`: `NVAL` functionally determined by VARIABLES; contractible at `NVAL=1`; contractible at `NVAL=|VARIABLES|` | `Cnvalue` |
| `gcc`: `NOCCURRENCE` functionally determined by VARIABLES and VAL | `Cglobal_cardinality` |
| `element`: `VALUE` functionally determined by INDEX and TABLE | `Celement` |

One reading decision: gccat's "contractible when `NVAL=|VARIABLES|`" cannot mean
"keep `NVAL` and drop a variable" (that is false), so it is implemented with the
condition re-evaluated — `nvalue(X,n)` implies `nvalue(X',n-1)` — and labelled
as such in the output.

**(b) Implications between entries**, the pairs `docs/GCCAT.md` §3 identifies as
living wholly inside `cata/`: `all_equal => increasing`, `all_equal =>
decreasing`, `nvalue(X,k) => atleast_nvalue(X,k)`, `nvalue(X,k) =>
atmost_nvalue(X,k)`, `alldifferent <=> nvalue(X,n)`, `alldifferent =>` every gcc
count `<= 1`. These relate *different* hand-encodings to each other, so a
transcription error in one is caught by its neighbours.

**What is still exposed.** Both defences check the encodings against each other
and against the catalog; neither checks them against the generator's
decomposition. **Nobody should treat a `SOUND and MINIMAL` verdict from this
tool as final until the ground semantics is derived from the generator's now-
inspectable `ind_op` data rather than transcribed beside it.**

There is a second, smaller cost: `cata/table.tex` refers to an index set `D_4`
that the printer never defines. The validator reads `D_4` as the table's row set,
which is what the decomposition means. That is an interpretation, not something
the `.tex` says. The same latitude is **not** extended to `among`, `range`,
`regular` and `roots` — see "Out of scope" below.

---

## What "sound" means here

A rule `P1, ..., Pk / C` is **sound** iff for every domain store `S` satisfying
every `Pj`, every solution of the decomposition inside `S` satisfies `C`.
Literals are read as store facts:

| literal | as a premise (store fact) | on a solution |
|---|---|---|
| `X_i = t` | `D(X_i)` is a subset of `{t}` | `x_i = t` |
| `X_i != t` | `t` is not in `D(X_i)` | `x_i != t` |
| `X_i >= t` | no value below `t` is in `D(X_i)` | `x_i >= t` |
| `X_i < t` | no value from `t` up is in `D(X_i)` | `x_i < t` |
| `N >= p` / `N < p` | `lb(N) >= p` / `ub(N) < p` | likewise |
| `N = p` / `N != p` | `D(N) = {p}` / `p` not in `D(N)` | likewise |
| `O_t >= p`, `O_t < p` | as for `N`, on the occurrence variable | likewise |
| `I = i`, `I != i`, `V = t`, `V != t` | as for `X_i`, on `element`'s index and value | likewise |

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

D-0005 asks for the store enumeration in so many words, so **both** are
implemented. The store sweep now enumerates the auxiliary variables too — `N`'s
interval, each `O_t`'s interval, and `I`'s and `V`'s domains — but only for the
entries that have them, which is what keeps it affordable. Every rule is checked
under both methods and a disagreement exits 2. **All 42 rules agree under both**
(measured: `grep -c 'store sweep agrees' run.txt` → 42, `grep -c DISAGREE` → 0).

### Off-the-end indices: an interpretation, stated

`increasing` and `decreasing` carry index equations (`i'=i-1`). At `i=1` the
premise names `X_0`, which does not exist. The validator reads a premise about a
non-existent variable as **false** — the rule instance cannot fire. This is an
interpretation of the same kind as reading `table`'s `D_4` as the row set. It is
the only reading under which such a rule is not trivially unsound at the
boundary, and the four `SOUND and MINIMAL` verdicts for `increasing` and
`decreasing` depend on it.

### Sizes enumerated, and what was capped

| entry | assignment enumeration | store sweep |
|---|---|---|
| `alldifferent`, `allequal`, `increasing`, `decreasing` | `n, m` in {2,3,4}, all 9 pairs | `n, m <= 3` |
| `element`, `nvalues`, `gcc`, `sum` | `n, m` in {2,3,4}, all 9 pairs | `n = m = 2` |
| `atleastnvalues`, `atmostnvalues` | `n, m` in {2,3,4}; `N` in `[0,n]` | `n, m <= 3` |
| `table` | `n, m` in {2,3}; every table with 1 or 2 distinct rows | `n = m = 2` |

**What was capped:** the store sweep, not the assignment enumeration. Entries
with auxiliary variables multiply the store space (`gcc` at `n=m=2` already has
16 X-domain combinations × 36 occurrence-interval pairs), so their sweep is held
at `n=m=2`. The singleton reduction — which the sweep exists to corroborate —
runs at all sizes for every entry. Nothing was capped by dropping a rule: all 42
in-scope rules were checked under both methods.

**A scope artifact worth knowing.** Values are drawn from `[1,m]`, so `X_i >= 1`
always. For `sum` that means `N = sum(X) >= n >= p` for every `p` in the declared
`[1,n]`, which is *why* both of its `NOT MINIMAL` verdicts come out that way. A
validator with `0` in the domain might not flag those two rules. This is a
limitation of the enumeration, not a finding about the rules.

---

## Quantifier ambiguity: the shipped LaTeX does not always determine the rule

Repeated index composition in the generator emits prefixes that contradict
themselves. `atleastnvalues` rule 4 ships this premise:

```
X_{i}=t, ∃i, i∈[1,n], ∀i, i∈[1,n], ∀t, t∈[1,m], ∀i, i∈[1,n]
```

`i` is quantified three times, twice universally and once existentially. No
uniform parsing policy recovers the intent, because there is no intent in the
string — the prefix is an artifact of composing index functions that cannot be
inspected. W1-T7 makes them inspectable *inside the generator*; it does not
retro-fix the `.tex` already shipped, which is what is measured here.

The validator therefore checks **every consistent reading**: each permutation of
the bound variables, each quantifier the variable is actually written with, and
— for a variable that is also free in the conclusion — both "reuse the
conclusion's copy" and "bind a fresh one". Verdicts:

- **UNSOUND** — fails under *every* reading. No better parser can overturn this.
- **AMBIGUOUS** — sound under some readings, unsound under others. This is a
  defect of the artifact, not a gap in the checker.
- **VACUOUS** — sound, but no store in scope satisfies the premises, so the rule
  can never fire. Reporting these as `SOUND` would be an overclaim.
- **UNSOUND(firing)** — every reading that survives is vacuous, so the only
  reading under which the rule could ever fire is an unsound one.
- **NOT MINIMAL** — sound and it fires, but a premise is droppable.
- **SOUND and MINIMAL** — the only unflagged verdict.

---

## The controls

A checker that flags everything proves nothing, so `make validate` runs eleven
hand-written control rules first, in the same LaTeX dialect, and asserts each
lands in its expected verdict. W1-T8 added seven so that **every** new atom
shape and the new index-equation modification is covered by a control in both
the positive and the negative direction:

| control | ground | expected |
|---|---|---|
| sound+minimal | `atmost` | SOUND and MINIMAL |
| sound, redundant premise | `atmost` | NOT MINIMAL |
| unsound | `atmost` | UNSOUND |
| vacuous | `atmost` | VACUOUS |
| BC `>=` sound+minimal | `allequal` | SOUND and MINIMAL |
| index equation sound+minimal (offset 2) | `increasing` | SOUND and MINIMAL |
| index equation unsound | `decreasing` | UNSOUND |
| O-atom sound+minimal | `gcc` | SOUND and MINIMAL |
| O-atom redundant premise | `gcc` | NOT MINIMAL |
| V-atom sound+minimal | `element` | SOUND and MINIMAL |
| I-atom unsound | `element` | UNSOUND |

If a control regresses the run says so and exits 2. `make validate-selftest`
runs the controls and the encoding invariants and nothing else.

**One honest caveat.** The `gcc` constraint is simple enough that the O-atom
sound+minimal control says the same thing as `gcc.tex` rule 3. Its expected
verdict was written down from the semantics before the run, not copied from it,
and the "O-atom redundant premise" control is deliberately a shape no catalog
entry has — but the overlap is recorded rather than hidden.

---

## What it found (2026-09-18, `make validate`, commit `8d1ac98`)

**11 of 42 in-scope rules are sound and minimal.** That is the first non-zero
number this project has had, and every one of the eleven comes from an entry
W0-T1 never looked at.

| entry | rules | verdicts |
|---|---|---|
| `alldifferent` | 1 | 1 SOUND and MINIMAL |
| `allequal` | 4 | 2 SOUND and MINIMAL, 2 UNSOUND |
| `increasing` | 2 | 2 SOUND and MINIMAL |
| `decreasing` | 2 | 2 SOUND and MINIMAL |
| `element` | 6 | 2 SOUND and MINIMAL, 4 VACUOUS |
| `gcc` | 4 | 2 SOUND and MINIMAL, 2 VACUOUS |
| `nvalues` | 6 | 4 VACUOUS, 1 UNSOUND, 1 UNSOUND(firing) |
| `sum` | 4 | 2 NOT MINIMAL, 2 VACUOUS |
| `atleastnvalues` | 5 | 1 NOT MINIMAL, 1 UNSOUND, 1 AMBIGUOUS, 1 UNSOUND(firing), 1 VACUOUS |
| `atmostnvalues` | 5 | 1 NOT MINIMAL, 1 UNSOUND, 2 VACUOUS, 1 UNSOUND(firing) |
| `table` | 3 | 3 UNSOUND |

The three entries W0-T1 already covered reproduce their earlier verdicts
rule-for-rule, which is the regression check on the refactor.

### `sound and minimal` does not mean `good`

Minimality here means no premise is droppable. It does **not** mean the rule is
strong. `cata/alldifferent.tex`'s single rule is sound and minimal and almost
useless: its premise is `∀i' != i: X_{i'} = t`, which under `alldifferent`
requires `n-1` variables to share a value and is therefore unsatisfiable for
`n >= 3`. It fires only at `n = 2`. The `∀` is plainly a `∃` that the generator
lost, and CLAUDE.md already records that this file has one rule where it should
have two. **A `SOUND and MINIMAL` verdict is a floor, not a certificate.**

### The three new defects worth naming

1. **`allequal` rules 2 and 3 have the sign inverted.** Rule 2 concludes
   `X_i >= t` from `∀i' != i: X_{i'} < t`. Under all-equal, every other variable
   being below `t` forces `X_i` below `t` as well, so the conclusion is exactly
   backwards. Counterexample at `n=m=2`. Rule 3 is the mirror image.
2. **`element` loses four of its six rules to a quantifier.** Rules 3–6 each
   carry a premise of the form `∀t: V = t` or `∀i: I = i`, which no store with
   `m >= 2` (resp. `n >= 2`) can satisfy. The intended rules are the `∃`
   versions; as shipped they can never fire.
3. **`gcc` rules 1 and 2 are vacuous for the same reason on `p`.** `∀p ∈ [1,n]:
   O_t >= p` means `O_t >= n`, which contradicts the companion premise that the
   other `n-1` variables avoid `t`. Rules 3 and 4, which quantify `p` only in the
   conclusion, are the two that survive.

---

## Out of scope — and why that is a result

Five entries cannot be validated as they stand. Reporting them is the point:
this is direct evidence for **W1-T2** (the printer's undefined `D_k`).

| entry | rules | why not checkable |
|---|---|---|
| `among` | 3 | references `D_4`, which the printer never defines, **and** `among`'s count variable appears in no atom — so the rules constrain `X` alone while the constraint restricts `X` only jointly with that count |
| `cumulative` | 2 | the durations `d_i` appear as uninterpreted symbols inside index equations (`t'=t-d_i`), **and** the resource capacity appears in no atom, so the rule is schematic over a parameter the artifact never states. This one is caught mechanically: the parser reports `UNPARSED: index equation offset: t'=t-d_{i}` |
| `range` | 3 | `D_5`, `D_6` undefined; Bessiere's set RANGE, whose set variables appear in no atom (gccat's `range_ctr` is an unrelated constraint — `docs/GCCAT.md` §5.2) |
| `regular` | 2 | `D_8`, `D_9` — the transition relation — undefined; gccat has no `regular` entry at all (`docs/GCCAT.md` §5.1) |
| `roots` | 4 | `D_5`, `D_6` undefined; the set variables `S` and `T` appear in no atom |

The undefined index sets are printed by the run, read out of the `.tex` rather
than asserted here. A reading *could* have been invented for each — `D_4` as an
arbitrary value subset, a capacity pulled out of the air — and each would have
produced verdicts. None of them would have been about the shipped artifact.

Note also that **`D_4` means two different things**: the table's row set in
`table.tex` and the value set in `among.tex`. The printer's `D_k` counter is
per-decomposition, so the numbering carries no meaning across entries. That is
another item for W1-T2.

---

## Running it

```sh
make validate            # invariants, controls, then the 11 entries
make validate-selftest   # just the invariants and the controls
./_build/validator .     # the binary directly, if you want its exit code
```

The **binary** exits `0` nothing flagged, `1` something flagged (today's
expected state), `2` the controls, the encoding invariants or the store-sweep
cross-check failed — in which case the verdicts mean nothing and `validator.ml`
is what needs fixing.

`make validate` deliberately passes `1` through as success and only fails on
`2`. What it fails on is the validator itself going wrong.

`make validate` is deliberately **not** part of `make check`. It exits 1 today by
design, and a gate that is red on purpose trains people to ignore it. It turns
green as W1 fixes the rules.

---

## Deliberately left out

- **The five out-of-scope entries.** Not a gap to be closed by more validator
  work: it is closed by W1-T2 (define the `D_k`) and by the input format naming
  the arguments that currently appear in no atom.
- **Bounds vs arc consistency as distinct regimes.** `N` and `O_t` are treated as
  intervals (BC) and `X`, `I`, `V` by value removal (AC), matching how the
  entries are generated, but the validator does not check that a rule is *the*
  AC or BC explanation — only that it is sound and minimal.
- **Whether a rule is the strongest available explanation.** See the
  `alldifferent` case above: minimality does not mean strength, and the gap
  between them is where the real quality of a catalog entry lives. That is
  D-0008's question.
- **Any fix.** Per D-0005 the validator comes first. `validator.ml` changes no
  generator code and no `.tex`, and W1-T8 regenerated nothing — the numbers above
  measure the committed catalog, deliberately, because W1-S is changing the
  generator concurrently.
