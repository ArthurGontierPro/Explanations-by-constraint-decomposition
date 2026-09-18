# Explanations by constraint decomposition

Generate the **explanation rules** of a global constraint from one of its decompositions,
and publish them as a catalog.

- **Input**: a decomposition, written in this project's own format
- **Output**: guarded clause schemas over solver literals, with a derivation, plus a LaTeX
  rendering under `cata/`
- **Language**: OCaml (the generator) and Julia (the earlier prototypes). Both run.

```sh
eval $(opam env --switch=baguette --set-switch)   # OCaml 5.1.1 lives in this switch
ocaml 'explenation generator.ml'                  # regenerates cata/*.tex in cwd
```

`which ocaml` returns nothing in a non-interactive shell — the switch is not on the default
`PATH`. That is not the same as OCaml being absent, and an earlier draft of this file got it
wrong on exactly that evidence.

Contributors — including Claude sessions — read this file first, then `docs/DECISIONS.md`
for what is already settled. **Do not relitigate a decision record.** Six of them exist
because they were argued once already.

---

## Reality check — read this before you believe anything in the repo

This is a 2020 M2 internship prototype, not a maintained tool. As of 2026-09-18:

| | |
|---|---|
| `explenation generator.ml` | 460 lines, the current generator. **It builds and runs on OCaml 5.1.1 and regenerates all 15 `cata/*.tex` byte-identically** (verified 2026-09-18). No build system, but it needs none: `ocaml gen.ml` is enough. |
| `prototypes/moulinette2.jl` | Julia, also runs, also reproduces its documented output. The earlier baseline; the OCaml is the structured one. |
| `cata/*.tex` | 16 files, 15 generated. `sum.tex` is orphaned — nothing produces it. |
| tests | `make validate` — a validator covering **3 of 16 entries** (W0-T1, landed 2026-09-18). It flagged **all 13 rules it checked**; none earned "sound and minimal" |
| CI / gate | `make check` — golden-file byte-diff of every generated entry, plus a warning census (W0-T2/T3, landed 2026-09-18). **It proves reproducibility, not correctness.** No CI runner |

**`cata/table.tex` contains an unsound rule** — an empty premise concluding `X_i = t`.
`atleastnvalues.tex` and `atmostnvalues.tex` are byte-identical despite different
decompositions. These are not hypotheticals; they are shipped output. Treat every existing
entry as unverified until the validator says otherwise.

> **W0-T1 landed 2026-09-18, and it narrowed rather than lifted this rule.** The validator
> covers `table`, `atleastnvalues` and `atmostnvalues` only. It flagged all 13 rules in them
> and **not one rule in this repo has been shown sound and minimal.** For the other 13
> entries nothing has changed: a generated `.tex` that renders is not evidence of anything,
> and the honest phrasing is still "generated, unvalidated". Run `make validate` before
> calling any entry correct, and if it is not one of the three, you cannot.

---

## Context budget

This repo is small; the expensive context here is **the literature**, not the files.

**`CHRISTMAS_LIST.md` is the compressed literature index. Read it instead of searching.**
It covers all 118 MiniZinc globals with: the explanation literature (or "none", which is
most of them), which solvers implement an explaining propagator, and which extension this
method needs. It cost a full session of web research to build.

| Want | Do this |
|---|---|
| "is there a paper on explaining X?" | `grep -n -i 'X' CHRISTMAS_LIST.md` — do **not** web-search first |
| "what is already decided?" | `grep -n '^## D-' docs/DECISIONS.md`, then read that record |
| "what is my task?" | `grep -n -A6 'W1-T3' docs/ROADMAP.md` |
| "what is claimed?" | `sed -n '/^## Active claims/,/^## /p' WORKLOG.md` |
| the generator's shape | `head -30 'explenation generator.ml'` — the types are the design |

Never read `CHRISTMAS_LIST.md` or `docs/DECISIONS.md` whole "to be thorough". Scope the read.

---

## The protocol

Several Claude sessions may work this checkout at once.

1. **Claim before you edit.** Append a row to `## Active claims` in `WORKLOG.md`: task ID
   from `docs/ROADMAP.md`, the files you will touch, a session tag. Commit that claim first.
2. **Do not touch files another session claimed.** Write the request under
   `## Cross-session requests` and work on something else.
3. **Release when done.** Move your row to `## Completed`, add handoff notes.
4. **Append-only** on `WORKLOG.md` and `docs/DECISIONS.md`. Add at the bottom of the section;
   never reflow or reorder. That is what makes concurrent edits merge instead of conflict.
5. **Commit in small pieces.** An hour without committing is an hour another session can clobber.

### Two or three sessions, not more

The rule this project takes from `~/baguette`: **do not fabricate parallelism.** If one file
matters this round, one session works. Its orchestrator runs waves of one when there is no
honest disjoint task, and that is the right call, not laziness.

**Constraint families are NOT a parallel axis until the input format is frozen** (W2). Adding
`regular` needs E2; adding `sliding_sum` needs E1; both land in the rule engine. N family
agents before the freeze means N agents fighting over one file to add three lines each.
See D-0006.

---

## Verify before you report

Two failure modes have already happened in review of this project's sibling:

- **A finding taken from a document that predates the fix.** Two warnings written against
  `~/baguette` were stale because the roadmap had closed them. **Check the roadmap row before
  reporting a finding.**
- **A test that passed without running.** Redirect output, then `grep`; never pipe a full run
  into context and skim it.

If you report a number, say how you got it. "Read off the code" and "measured" are different
claims and this project writes down which one it is.

---

## Where things are

```
explenation generator.ml    the 2020 OCaml generator: event/decomposition/rule types,
                            7 rule schemas, AND/OR traversal, DNF flattening, LaTeX printer
prototypes/
  moulinette2.jl            Julia prototype that RUNS; the behavioural baseline
  moulinette.jl             single-constraint (cumulative) predecessor
  moulinette.ml             OCaml restructuring of moulinette2
cata/*.tex                  generated catalog entries, LaTeX \frac{premises}{conclusion}
CHRISTMAS_LIST.md           the literature + solver + extension map for 118 MiniZinc globals
docs/
  DECISIONS.md              append-only decision records. Read before proposing a design change.
  ROADMAP.md                waves and task IDs. Claims reference these.
WORKLOG.md                  claims, cross-session requests, handoff notes. Append-only.
```

### The generator's design, in one paragraph

An **event** is `(sign, variable, index list, AC|BC)` — a literal like `X_i = t` or `X_i ≥ t`.
A **decomposition** is a list of `Decomp (id, rule, devent list)`, each atomic constraint
tagged with one of 7 rule schemas (`rule1` reified equivalence, `rule3` ∧, `rule4` ∨,
`rule5/6/7` Boolean sum ≤/≥/=) and carrying two index functions, one for descending and one
for ascending. `find` walks the decomposition as an AND/OR graph with cycle detection; `an`
flattens to DNF; the printer emits LaTeX. **The ideas are sound.** The encoding is what
resists extension — see D-0006.

---

## Traps

- **`cata/*.tex` have no trailing newline**, so `wc -l` reports 0 for files with content.
  **`grep -c '\\frac'` is also wrong** — every entry is a *single line*, so it returns 1 for all
  16 regardless of content. Count rules with `grep -o '\\frac' f | wc -l` (measured 2026-09-18:
  `grep -c` gives 1 for `table`, `nvalues` and `increasing` alike; `grep -o` gives 3, 6 and 2).
- **FIXED 2026-09-18 (W1-T3), and the trap note it replaces was wrong.** `removeimp` used to
  discard any branch containing `F`/`IM`/`FE`/`R` in silence; it is now `filter_branches`, which
  raises on `FE`/`IM`, warns on `R` (cutting a cycle is a design choice), and counts legitimate
  `F` discards into a diagnostics block appended to every `cata/*.tex`.
  **The old note claimed `alldifferent.tex` "has one rule where it should have two". It should
  have one.** Measured: instrumenting the old filter over all 16 entries found 22 dropped
  branches, **all 22 of them `F`** — `IM`, `FE` and `R` never occurred, so nothing was ever lost
  to the silence. `alldiff`'s decomposition is `rule1` + `rule5` *alone* (a Boolean sum ≤), and
  `X_i = t` is simply not derivable from a ≤ direction. `element.tex`'s `I=i` is the same case.
  **Getting that second rule requires counting across sums — that is E4 (D-0006), the research
  item, not a bug in W1.**
- **The printer hardcodes index sets 1–3** (`[1,n]`, `[1,m]`, `[1,n]`) and falls through to
  an undefined `D_k` for everything else. That is why `regular`, `roots`, `range` and `table`
  reference `D_4`–`D_9` that appear nowhere.
- **Index functions are opaque closures**, so nothing can print, compare or invert them, and
  a wrong composition yields a plausible-looking wrong rule. This is D-0006's first item.
- **`!=` is used where structural inequality is meant** (physical equality in OCaml).
- **Warning counts move when the generator changes — re-measure, never quote.** On OCaml 5.1.1,
  before W1-T3/T7: default 0, `-w +27+39` 16, `+40+41+42` 42, `+a` 91. **After** (2026-09-18,
  from `make check`): default **0**, `-w +27+39` **8**, `-w +40+41+42` **31**, `-w +a` **57**. An earlier draft of this file said "16 default
  warnings"; 27 and 39 are off by default in 5.1.1, so the 16 only appear if you ask. The
  two warning-39s are the `printind_name_list` non-recursion bug below. `make check` keeps
  this census and fails if the counts move.
- **Constructor names are ambiguous across types, and OCaml resolves them silently.**
  `ocamlc -w +40+41+42` reports **31** warnings (was 42 before W1-T7), the sharp one being
  `I belongs to several types: ind_name var_name — The first one was selected.`
  `T` and `R` are likewise disambiguated by type. A site that means `var_name.I` (element's
  index variable) and gets `ind_name.I` is a silent semantic bug, not a compile error.
- **`printind_name_list` and `printiopl_list` (lines 263–264) ignore their tail** — they
  match `i::tl` and never use `tl`, so they print only the first index. The `…tex` siblings do
  recurse, so this affects the plain-text path only. Two of the warnings at `-w +27+39` point
  straight at it.
