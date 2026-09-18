# Worklog

**Append-only.** Add at the bottom of the relevant section. Never reflow or reorder what is
already there — that is what makes concurrent edits merge instead of conflict.

---

## Active claims

No task is claimed. The repo is at its 2020 internship state plus `CHRISTMAS_LIST.md`,
`CLAUDE.md`, `docs/DECISIONS.md` and `docs/ROADMAP.md`, all added 2026-09-18.

**Wave zero has not been dispatched.** When it is, it is W0-T1 (or W0-T1+W0-T2 together —
they are the same files) plus W0-T4, which is the only honestly disjoint task available:
it touches no generator code. Do not add a third.

| Task | Files being touched | Session | Since |
|---|---|---|---|
| — | — | — | — |
| W0-T1 + W0-T2 + W0-T3 | `validator.ml` (new), `Makefile` (new), `docs/VALIDATOR.md` (new). **Read-only** on `explenation generator.ml` and `cata/**` | W0-A (orchestrated, 2026-09-18) | 2026-09-18 |
| W0-T4 | `tools/` (new), `docs/COVERAGE.md` (new). **Read-only** on `CHRISTMAS_LIST.md` | W0-B (orchestrated, 2026-09-18) | 2026-09-18 |
| M-1-T1 | `docs/GCCAT.md` (new). **Read-only** on everything else | M-1 (orchestrated, 2026-09-18) | 2026-09-18 |
| W1-T3 + W1-T7 | `explenation generator.ml` — **the rule engine, sole owner this wave** | W1-S (spine, 2026-09-18) | 2026-09-18 |
| W1-T8 | `validator.ml`, `docs/VALIDATOR.md` | W1-V (2026-09-18) | 2026-09-18 |
| W2-T5 (pilot) | `decomps/**` (new dir), `docs/DECOMP_FORMAT_NOTES.md` (new) | W1-D (2026-09-18) | 2026-09-18 |

_Dispatched 2026-09-18 by the orchestrator session; supersedes the "wave zero has not been dispatched" note above. Two sessions, per CLAUDE.md. `WORKLOG.md` is owned by the orchestrator for this wave — W0-A and W0-B do not edit it, they report back and the orchestrator records._

_Both rows RELEASED 2026-09-18: W0-B at `ceb8627`, W0-A at `6f6204e`. Wave zero is closed. No task is claimed as of that commit._

_M-1-T1 RELEASED 2026-09-18. Nothing is claimed._

---

## Cross-session requests

Need a change in a file someone else has claimed? Write it here and move on. The owning
session picks it up.

| Request | For file | From | Status |
|---|---|---|---|
| **The rule engine is one file and one owner per wave.** W1-T7, W2-T2 (E1) and W2-T3 (E2) all land in it. They must not be dispatched concurrently — see D-0006 | `explenation generator.ml` (or its successor) | design session 2026-09-18 | standing |
| **No session may report a catalog entry as correct until W0-T1 lands.** There is no gate. A `.tex` that renders is not evidence. The honest phrasing is "generated, unvalidated" | `cata/**` | design session 2026-09-18 | standing, until W0-T1 |
| **Check the roadmap row before reporting a finding.** In review of `~/baguette` two warnings were written against defects the roadmap had already closed, taken from a document that predated the fixes. Stale context is confident | — | design session 2026-09-18 | standing |
| Add a `coverage` target running `python3 tools/mzn_coverage.py --check`. Keep it out of `make check`'s hard failure path — it exits 1 today on live drift, which is a fact about the catalog, not a broken build | `Makefile` | W0-B via orchestrator 2026-09-18 | routed to W0-A 2026-09-18 |
| **NARROWED, not lifted: the "no entry is correct" rule survives W0-T1.** The validator covers `table`, `atleastnvalues`, `atmostnvalues` only, and flagged every rule in them. The other 13 entries are still "generated, unvalidated", and **no rule in this repo has been shown sound and minimal** | `cata/**` | orchestrator 2026-09-18 | standing, supersedes the row above it |

---

## Completed

| Task | Session | Notes |
|---|---|---|
| — | — | — |
| W0-T4 | W0-B (2026-09-18) | `tools/mzn_coverage.py` + vendored `tools/data/minizinc-2.10.1-globals.txt` + `docs/COVERAGE.md`. Commits `e12ccce`, `80a89a6`. Classifier runs, exits 1 on drift. Coverage and defects verified independently by the orchestrator (see handoff note) |
| W0-T1 + W0-T2 + W0-T3 | W0-A (2026-09-18) | `Makefile`, `validator.ml`, `docs/VALIDATOR.md`, `.gitignore`. Commits `8a1a05b`, `2f42cde`, `49c826a`. `make check` exit 0, `make validate` runs, both re-run by the orchestrator. **Validator covers 3 of 16 entries; 13/13 rules flagged; 0 sound and minimal** |
| M-1-T1 | M-1 (2026-09-18) | `docs/GCCAT.md`, 170 lines. Commit `f82ada7`. 22 catalog pages fetched under the cap. Key claims re-verified by the orchestrator |

---

## Handoff notes

### 2026-09-18 — design session (with the author)

Set up `CLAUDE.md`, `docs/DECISIONS.md` (D-0001…D-0008), `docs/ROADMAP.md` (W0…W4) and this
file. Nothing under `cata/`, `prototypes/` or `explenation generator.ml` was touched.

Three things the next session should know, because they are not obvious from the code:

1. **Two decision records are corrections.** D-0002 (reification stays) and D-0003
   (decompositions are authored here, not imported from MiniZinc) each record a wrong proposal
   in full. Both wrong proposals are plausible and will be re-proposed by anyone who has not
   read them. The `regular` case in D-0003 is the one to understand: this repo's decomposition
   is *better than MiniZinc's for explanation* because it avoids state variables, which is the
   opposite of how it looks at first glance.

2. **`CHRISTMAS_LIST.md` cost a full session of web research.** It maps all 118 MiniZinc
   globals to their explanation literature, which solvers implement an explaining propagator,
   and which extension this method needs. Grep it before web-searching. Its most useful
   finding: **Huub implements exactly two global propagators natively and decomposes every
   other global using MiniZinc's decompositions** — so a competitive LCG solver already derives
   explanations by decomposition for ~116 of 118 globals, at runtime, with no schema. That is
   this project's argument, and it is stronger than "a catalog would be nice."

4. **Correction, same day: OCaml is installed and the generator works.** An earlier draft of
   `CLAUDE.md` and `docs/ROADMAP.md` said OCaml was not available and treated the Julia
   prototype as the only live baseline. That was wrong, and the evidence for it was
   `which ocaml` in a non-interactive shell — the compiler is in the opam switch `baguette`
   (OCaml 5.1.1), which is not on the default `PATH`. Verified since:

   - `ocaml 'explenation generator.ml'` runs clean and **regenerates all 15 `cata/*.tex`
     byte-identically**, `exp.tex` too. The only diff against the committed tree is the
     orphaned `sum.tex`, which confirms nothing produces it.
   - Default warnings: 16, all benign, but two of them point at a real bug —
     `printind_name_list`/`printiopl_list` (lines 263–264) match `i::tl` and never use `tl`,
     so the plain-text printer emits only the first index.
   - `-w +40+41+42`: **42 warnings.** The sharp one is
     `I belongs to several types: ind_name var_name — The first one was selected.`
     A site meaning `var_name.I` that silently gets `ind_name.I` is a semantic bug with no
     compile error. Worth a W1 row of its own.

   **Consequence: W0-T2 is no longer a language decision.** There is a working, reproducible
   OCaml baseline; the task is to wrap it in a gate, not to rewrite it. W0-T3 is nearly free
   for the same reason.

3. **The smallest complete contribution available is `regular`.** It is on Choco's
   LCG-unsupported list (Choco throws `SolverException` for it), this repo already has a
   decomposition, and that decomposition keeps explanations in the user's own vocabulary. It
   needs W1-T2 and W2-T3 and nothing else. See `CHRISTMAS_LIST.md` §"The immediately actionable
   target".

### 2026-09-18 — W0-B (W0-T4, coverage classifier) — CLOSED

`python3 tools/mzn_coverage.py [--share <minizinc share dir>] [--json f] [--check]`. Python 3
stdlib only, no network at runtime. Exit 1 on drift or defects — that is its gate use.

**Sourcing, and the caveat that matters.** There is no `minizinc` binary on this machine.
`/usr/local/share/minizinc` holds Gecode redefinitions only, no `std/`, so it is not usable as
a share dir. W0-B parsed a libminizinc source tree found in another session's *scratchpad*,
which is ephemeral, and therefore vendored a snapshot under `tools/data/` with a provenance
header (source path, sha256 of `globals.mzn`, date, and the words "NOT a live parse"). Live
parse and snapshot were diffed and produce identical report bodies. **Every run prints whether
it was a live parse.** The default run here is the snapshot — treat the release figure as
pinned to MiniZinc 2.10.1 (31 Aug 2026) until someone installs MiniZinc.

**Counts.** Measured by running the parser, not read off prose: 118 globals in the release,
which independently confirms `CHRISTMAS_LIST.md`'s "118" claim for 2.10.1; 113 of 118 covered
(95.8%); 5 uncovered; 2 listed names that are not 2.10.1 globals. Orchestrator re-ran
`--check` and reproduced exit 1, 118, 113/95.8%.

**Defects found in `CHRISTMAS_LIST.md` — reported, NOT fixed** (W0-B did not own the file):

- **No row for `all_equal`** — `grep -c 'all_equal' CHRISTMAS_LIST.md` → 0, confirmed by the
  orchestrator — yet `cata/allequal.tex` is a shipped catalog entry and `allequal` was touched
  by commit `16c45be`. A shipped entry with no line in the literature index is the sharpest
  single finding of this wave: it means the index and the catalog can disagree silently.
- No rows for `lex_greater`, `lex_greatereq` (section 3 has the `_less` duals only).
- `cost_mdd` appears twice with **conflicting routes**: line 157 `E1+E2+E3`, line 214 `E1+E2`.
  Both confirmed by the orchestrator.
- `edit_distance` (line 214) is not a MiniZinc 2.10.1 constraint under any spelling.
- `cumulatives_opt`, `disjunctive_strict_opt` uncovered; look like shorthand slips.
- Three rows carry no E-code, one of them the `*_fn` row covering 11 release globals.
  W0-B's suggestion, for whoever owns the list: give "out of scope" its own code so a machine
  can distinguish it from "unclassified".

**Deliberately not automated:** the literature column (not script-derivable; no web search was
done, per `CLAUDE.md`), the solver column beyond a coarse native/decomp split, and whether a
stated E-route is *correct* — the tool only extracts the codes.

### 2026-09-18 — W0-A (W0-T1/T2/T3, validator and gate) — CLOSED. Wave zero is closed.

`make check` (gate, exit 0), `make validate` (validator), `make validate-selftest`,
`make coverage` (advisory, never fails — it exits 1 on live drift and that is a fact about the
catalog, not a broken build). Orchestrator re-ran `check` and `validate` from a clean tree and
reproduced both.

**What the validator actually covers — read this before quoting it.** Three entries: `table`,
`atleastnvalues`, `atmostnvalues`. Rules are *parsed from the shipped `.tex`*, which is the
right call — the artifact under test is the one that ships. Only the ground semantics of the
three decompositions is hand-encoded, three one-line predicates read off the generator source
(l.410–417, l.429–431), because W1-T7 has not landed and closures cannot be inspected.
Soundness is computed two independent ways (D-0005's full store sweep, and a singleton-store
reduction justified by anti-monotonicity of every premise literal) and the run asserts the two
agree; they agreed on all 13 rules. Four hand-written controls run first — sound+minimal,
redundant premise, unsound, vacuous — and all four behave, so the flags are not a stuck checker
saying "no" to everything.

**Result: 13 rules checked, 13 flagged, 0 sound and minimal.** The acceptance test in D-0005 is
met, twice over:

- `table.tex` — **all three rules unsound under every reading**, not only the empty-premise one.
  That is worse than W1-T4 records.
- `atleast` / `atmost` — the byte-identical text gets **different verdicts** (rule 3: AMBIGUOUS
  vs VACUOUS). Sharper still: rule 4's only non-vacuous reading is unsound in both, but the
  counterexamples differ in kind — against at-least it fails at `n=m=2, p=1` (the bound runs the
  wrong way), against at-most only at `p > m` (right direction, wrong bound). **That asymmetry
  is what the byte-identity was hiding**, and it is where W1-T5 should start.

**Unanticipated, and it changes a roadmap row: the emitted `.tex` does not determine the rule.**
Repeated index composition prints self-contradictory binder prefixes (`∃i, ∀i, ∀t, ∀i` on a
single premise), so the validator must enumerate *readings*. Recorded as **D-0009 (OPEN)**,
together with the proposal that `VACUOUS` become a first-class verdict — three shipped rules are
sound only because their premises can never hold, and counting those as passes would inflate any
coverage claim. This promotes W1-T7 from refactor to correctness prerequisite.

**Corrections to this repo's own documents, all re-measured by the orchestrator before applying:**

- `grep -c '\frac'` **does not count rules** — every entry is a single line, so it returns 1 for
  all 16. Use `grep -o '\frac' f | wc -l`. `CLAUDE.md`'s Traps section said the wrong thing.
- Warnings on OCaml 5.1.1: default **0**, `-w +27+39` **16**, `-w +40+41+42` **42**, `-w +a`
  **91**. The "16 default warnings" figure in `CLAUDE.md` and in the design session's own
  handoff note was wrong — 27 and 39 are off by default in 5.1.1. `make check` now keeps the
  census and fails if it moves.

**Next wave, for whoever picks it up.** W1-T3 (make failure loud) and W1-T7 (indices as data)
are the two that unblock everything else, and both are the rule-engine file — so they are
**one session, not two**, and they do not share a wave with E1/E2. The honest disjoint partner
is W1-T6 (`sum.tex`) or extending the validator to a fourth entry. Do not dispatch a family
agent: W2-T1 has not happened.

### 2026-09-18 — M-1 (read the Global Constraint Catalog) — CLOSED

`docs/GCCAT.md`. Beldiceanu/Carlsson/Rampon, `https://sofdem.github.io/gccat/`. 22 pages
fetched, each mapped to an existing `cata/` entry or an open task. The by-name list is
`gccat/sec5.html` — note the path: plain `sec5.html` is a GitHub Pages 404 that still reads
like a page.

**Verified by the orchestrator, not taken on report:** 423 constraint entries (counted as
unique `C*.html` links in `gccat/sec5.html`, matching M-1's figure); `Cregular.html`,
`Ctable.html`, `Cmdd.html` all HTTP 404 while `Cin_relation.html` and `Catleast_nvalue.html`
are 200; `atleast_nvalue` carries **Extensible wrt** and `atmost_nvalue` **Contractible wrt**.

**The finding to act on — independent corroboration of W1-T5.** The catalog gives
`atleast_nvalue` and `atmost_nvalue` *opposite* closure properties. Two constraints with
opposite closure cannot have byte-identical explanation rules, so `atleastnvalues.tex` ≡
`atmostnvalues.tex` is a defect on catalog grounds alone — arrived at from a different
direction than W0-A's validator, which is worth more than either alone. M-1 derives further
that `atleast_nvalue`'s feasible `NVAL` set is downward closed, so propagation can only tighten
`NVAL`'s **upper** bound; that names the side W0-A's counterexample ("bounds `N` from the wrong
side", `n=m=2, p=1`) fails on. **Whoever takes W1-T5 starts here.** The generalisation is
cheap: extensible / contractible / monotone are machine-checkable invariants over
`validator.ml`'s hand-encoded semantics, and they check the hand-encoding itself, which
`docs/VALIDATOR.md` names as its own exposure.

**The finding that closes a door — and it is good news, not bad.** The catalog has **no
`regular`, no `table`, no `mdd`**; its table-like entry `in_relation` carries no automaton.
So **W3-T3 gets nothing from gccat.** That removes the temptation the brief was written
against: there is no catalog automaton to import for `regular`, and this repo's own
decomposition — which D-0003 argues is better *for explanation* because it invents no state
variables — stands unchallenged.

**Automata, within D-0004.** 62 catalog constraints are `automaton with counters`. M-1 layers
the cost honestly: the signature `S_i ⇔ X_i ∈ VALUES` is already `rule1` (**E0**); the
transition table `d[q,s]` is **E2**; the state variable is **E1**; counters and acceptance are
**E1+E2**; an array of counters (`nvalue`, `global_cardinality`) is **E3** — the existing
`failwith "sommes multiples"` site. Its proposed line, which respects D-0004 rather than
working around it: **inline a state only when its state predicate is a finite disjunction over
user literals.** `int_value_precede` passes that test; counter automata fail it. That is a
concrete criterion, and it is a proposal, not a decision — it belongs in a decision record
whenever someone takes E1/E2.

**For D-0008 (OPEN).** A gccat entry has ~30 fields. Four would make an entry here checkable:
**Purpose** (the ground semantics `validator.ml` hand-encodes today, which is its weakest
point), **Arg. properties**, **Restriction/Typical** (the arity box D-0008 needs), and
**Keywords**. Recorded in `docs/GCCAT.md` as a proposal against D-0008, not as a decision.

**Reported against `CHRISTMAS_LIST.md`, file untouched** (M-1 did not own it): the index lacks
two columns the catalog would supply — Berge-acyclicity (39 constraints) and argument
properties — and `cata/range.tex` is Bessiere's set RANGE while gccat's `range_ctr` is an
unrelated `max − min + 1` constraint. Add to the `all_equal` hole W0-B found: the index has
three known gaps now, and nobody owns it.

**Not read, deliberately:** the graph model / arc generators (E6, and it is the bulk of every
entry), set entries (E5), geometry, soft and cost variants, the Prolog/XML format pages.
