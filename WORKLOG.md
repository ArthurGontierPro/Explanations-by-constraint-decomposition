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

_W1-D RELEASED 2026-09-18. W1-S RELEASED 2026-09-18 at `b93644a`. W1-V RELEASED 2026-09-18 at `3578e05`. **Wave one is closed.** Wave two claimed 2026-09-18: three spec sessions, disjoint by constraint name, none touching engine code. Each writes its own `_shapes-*` and `_gaps-*` file so nothing merges by hand; the orchestrator consolidates into `docs/DECOMP_FORMAT_NOTES.md` at close._

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
| W2-T5 (pilot) | W1-D (2026-09-18) | `decomps/*.md` × 6 + `docs/DECOMP_FORMAT_NOTES.md`, 270 lines. Commit `c6a4247`. Five format gaps pinned to constraints — that list is the W2-T1 payload |
| W1-T3 + W1-T7 | W1-S (2026-09-18) | `1304386`, `463534f`. `make check` passes (orchestrator re-ran: exit 0). Goldens gained a diagnostics block and nothing else; W1-T7 changed zero goldens |
| W1-T8 | W1-V (2026-09-18) | `6be1f30`, `c3ce7d9`, `3ccaf97`. Validator now covers 11 entries. Orchestrator re-ran it: 42 rules, 11 sound and minimal, 31 flagged, 14 out of scope |
| W2-T5 §3+§4 | `decomps/` files for its own constraints + `decomps/_shapes-seq.md` + `decomps/_gaps-seq.md` | W2-A (2026-09-18) | 2026-09-18 |
| W2-T5 §5+§6 | `decomps/` files for its own constraints + `decomps/_shapes-ext.md` + `decomps/_gaps-ext.md` | W2-B (2026-09-18) | 2026-09-18 |
| W2-T5 §1+§9 | `decomps/` files for its own constraints + `decomps/_shapes-perm.md` + `decomps/_gaps-perm.md` | W2-C (2026-09-18) | 2026-09-18 |

_W2-C closed 2026-09-18 (`c0a704a`): 4 shapes, 3 new gaps, element's defect diagnosed. W2-A and W2-B still running._

_W2-A closed 2026-09-18: 5 shapes (`decomps/_shapes-seq.md`), 3 new gaps (`decomps/_gaps-seq.md`,
G6-G8 — numbered independently of W2-C's own G6-G8, reconciliation is the orchestrator's job at
consolidation), 17 constraint files across `CHRISTMAS_LIST.md` §3+§4. **Landed inside `b09b81c`
("Close W2-C..."), not a W2-A commit** — this session's own `git add`+working tree edits were
swept into that commit by the concurrent W2-C session committing from the same checkout (not a
worktree) while this session's files were staged but not yet committed. Content is exactly what
this session wrote; only the commit boundary/authorship line is wrong. Not fixed by amend/reset
per this session's standing instructions against destructive git ops on someone else's commit;
flagging for the orchestrator rather than rewriting history. See handoff note below for the
substance.

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

### 2026-09-18 — W1-D (W2-T5 pilot, counting family) — CLOSED

`decomps/{count,at_least,at_most,exactly,among,nvalue}.md` + `docs/DECOMP_FORMAT_NOTES.md`.
All six are **E0** — no engine extension needed — and `among` and `nvalue` already exist in the
generator. The pilot's value is not the six specs, it is the gap list.

**The five gaps, which are the input to W2-T1.** G1: no way to print a bare integer threshold,
so `at_least`/`at_most`/`exactly` would generate rules that never mention their own `n` — the
same silence as `alldifferent.tex`'s implicit "1". G2: `var_name` is a closed enum with no
letter for a constraint's own parameter, so `count`'s count variable has to borrow `N`/`O`.
G3: only variable-vs-domain-value comparisons exist, never variable-vs-variable, which blocks
treating `count`/`among`'s value argument as a decision variable. G4: `rule5/6/7` hard-fail on
more than one summed Boolean family — the `failwith "sommes multiples"` site, and the wall in
front of `global_cardinality`. G5 is a bug, not a gap, see below.

**G5, verified by the orchestrator with one correction.** `cata/among.tex` never explains its
own count variable: every conclusion is `X_i = t` or `X_i ≠ t`, none is about `N`. Confirmed.
**W1-D reported "all four rules"; there are three** (`grep -o '\frac' | wc -l` → 3). The
finding stands, the count did not. Note also that `among.tex` quantifies over `D_4`, an index
set defined nowhere — so it is caught by W1-T2 as well, which W1-D did not mention.

**The honest reading of "all six are buildable today with zero extension":** true of the
schemas, and misleading as a coverage claim. Three of the six would emit rules missing their
own threshold (G1) and `among`'s count-variable branch generates nothing at all (G5). E0 means
the engine will not refuse them; it does not mean the output would be right. Breadth means
validated breadth (D-0010).

**For whoever takes W2-T1:** the pilot did its job — one family, six constraints, five concrete
gaps, each pinned to the constraint that hit it. The same shape scales one family per session
*after* the freeze. Do not fan out families before it.

### 2026-09-18 — W1-S (W1-T3 + W1-T7, the engine spine) — CLOSED

Both landed. `make check` passes; the orchestrator re-ran it (exit 0) and inspected the diffs.

**W1-T3.** `removeimp`/`imp` → `filter_branches`: raises `Generator_failure` on `FE`/`IM`, warns
on `R` (cutting a cycle is a design choice, not a failure), counts legitimate `F` discards. Every
`cata/*.tex` now carries an appended diagnostics block — **the goldens' rule text is byte-identical
to before**, verified: the only diff is the appended `%%` comments. The footer deliberately omits
its own filename so `atleastnvalues.tex` and `atmostnvalues.tex` stay byte-identical, preserving
W1-T5's evidence. Census: 16 files, 43 events, 53 rules, 2 events with no rule, 1 empty premise,
13 ambiguous rules.

**W1-T7.** First-order `ind_op`, 9 constructors, replacing the two closures per `decomp_event`;
`apply_op` interprets, `print_op` prints, `(=)` compares, `invert_op` inverts what is invertible.
Modifications name an index *family* (`FI|FT|FP|FR`) because the numeral never mattered. Every
combinator kept its name, so the decomposition table itself is untouched. **Zero goldens changed** —
byte-for-byte reproduction across a re-encoding of the whole index machinery is the strongest
evidence available that the re-encoding is faithful, and it is worth more than any test this repo
has.

**The finding that corrects this project's own documentation, and it is the important one.**
`alldifferent.tex` has one rule **and should**. CLAUDE.md and the W1-T3 row both said it had one
where it should have two, and that was wrong. Two independent measurements: instrumenting the old
filter across all 16 entries found **22 dropped branches, all 22 of them `F`** — `IM`/`FE`/`R`
never occurred, so the silence never hid anything; and the decomposition is `rule1` + `rule5`
*alone*, a Boolean sum ≤, from which `X_i = t` is not derivable at all. The orchestrator confirmed
the decomposition by reading the table (generator l.678–679). `element.tex`'s `I=i` is the same
case. **The missing direction is E4 — counting across sums — so this belongs to W4-T2, not to W1.**
Corrected in `CLAUDE.md`, the W1-T3 row and the W4-T2 row at `b93644a`.

**Second finding: W1-T7 does not close D-0009.** Applying a modification *appends* to the index's
modifier list instead of rewriting it, so `OpShift`/`OpShiftC` fail to round-trip under
`invert_op` (`i'=i+1` then `i'=i-1` yields an `i''` carrying both `Addint` modifiers). That
accumulation is the mechanism behind the self-contradictory binder prefixes, and **13 of 53 rules
still bind an index name twice.** Recorded as a dated amendment to D-0009. The normalisation step
is separate work and nobody has claimed it.

**Warning census moved because the code moved:** default 0, `-w +27+39` **8** (was 16),
`+40+41+42` **31** (was 42), `+a` **57** (was 91). Both `CLAUDE.md` and the Makefile now say
re-measure rather than quote. `uniqueset`, the worst `!=`-for-structural-inequality site, is gone —
it was dead code, deleted rather than fixed. `printind_name_list`/`printiopl_list` still ignore
their tail.

**Left deliberately:** W1-T1, W1-T2, W1-T4, W1-T5, W1-T6, E1, E2.

**Outstanding, for the next session that owns `docs/VALIDATOR.md`:** it states that ground
semantics could not be derived because the index modifications are closures. **That blocker is
now removed** — they are data. The *rule schemas* are still closures, which is a different and
still-open item. W1-V owns that file right now, so this is recorded rather than applied.

### 2026-09-18 — W1-V (W1-T8, validator coverage) — CLOSED. Wave one is closed.

Re-run by the orchestrator: **42 rules in 11 entries — 11 SOUND and MINIMAL, 31 flagged — plus
14 rules in 5 entries out of scope.** Was 13 rules in 3 entries, 0 sound and minimal. Tree clean,
nothing outside `validator.ml` and `docs/VALIDATOR.md` touched.

**Why the verdicts are worth believing.** The trustworthiness machinery grew with the coverage
rather than being outgrown by it: controls 4 → 11, covering every new atom shape and the index
equation in both directions; both independent soundness computations ran on all 42 rules and
**agreed on all 42**; and 19 external invariants — 12 gccat closure properties from 8 fetched
`Purpose`/`Arg. properties` pages, plus 7 cross-entry implications from `docs/GCCAT.md` §3 — all
hold, with a failure exiting 2 rather than being reported as a verdict. That is M-1's catalog
read paying for itself a second time: it now guards the hand-encoding, which `docs/VALIDATOR.md`
names as its own weakest point.

**The eleven that pass.** `alldifferent` 1/1, `increasing` 2/2, `decreasing` 2/2, `allequal` 2/4,
`element` 2/6, `gcc` 2/4. **Every one of them is in an entry W0-T1 never looked at** — the first
three entries were chosen because they were already known to be broken, so 0/13 was never a fair
sample of the catalog. This is the first honest measurement of it.

**Three new defects, each with a counterexample — now W1-T9.** `allequal` rules 2–3 have the
inequality inverted (`n=m=2, X=(1,1)`); `element` loses 4 of 6 rules to unsatisfiable premises
(`∀t: V=t`, `∀i: I=i`); `gcc` rules 1–2 are vacuous because `∀p ∈ [1,n]: O_t ≥ p` means
`O_t ≥ n`, which contradicts its companion premise.

**Two caveats W1-V refused to let pass as findings, and they are the most valuable lines in its
report.** First, `sum`'s two NOT MINIMAL verdicts are an artifact of values being drawn from
`[1,m]`, so `N = ΣX ≥ n ≥ p` holds unconditionally — a validator whose domains included `0`
might not flag them. Second, **SOUND and MINIMAL is a floor, not strength**: `alldifferent`'s
rule passes and still only ever fires at `n=2`, because minimality is premise-droppability, not
power. Anyone quoting "11 of 42" as a quality figure needs both caveats attached.

**Evidence for W1-T2, which is now a measurement blocker and not a cosmetic one.** `among`,
`range`, `roots`, `regular` reference `D_4`–`D_9` that the printer never defines and their
non-`X` arguments appear in no atom; `cumulative` fails to parse on `t' = t - d_i` and its
capacity appears nowhere. And the `D_k` counter is **per-decomposition**: `D_4` is the row set in
`table.tex` and the value set in `among.tex`, so the numbering means nothing across entries.

**Provenance note, recorded because it is the kind of thing that rots.** `sum.tex` is the orphan
— no decomposition produces it — so its ground semantics came from gccat alone, which is weaker
provenance than the other ten, all read off the generator's decomposition table (l.383–434).

**Newly unblocked, nobody claimed it:** W1-T7 landed mid-session, so the ground semantics can now
be *derived* from the `ind_op` data instead of hand-typed. That would remove the hand-encoding
exposure entirely. The rule *schemas* are still closures — a separate, still-open item.

### 2026-09-18 — W2-C (W2-T5, §1 alldifferent + §9 ordering/sorting/channelling) — CLOSED

Four shapes in `decomps/_shapes-perm.md`: **P1** pairwise-sum guard (`alldifferent`, 1/1 sound);
**P2** monotone adjacent chain (`increasing`/`decreasing` 2/2, and `strictly_*` is a pure
parameter shift, not a new shape); **P3** three-way channel via cross-variable OR-clauses
(`element`, plus `inverse`/`inverse_in_range` newly derived onto the same detour); **P4**
existential disjunction (`member`, mirroring `nvalue`'s second step).

**Three new gaps, and they are structural rather than cosmetic.** G6: `ind_set` can only name a
whole predefined range — no subrange, no exclusion — which blocks `all_different_except*` and
`inverse_in_range`. G7: `rule1` only links `Global_devent ⇔ Reified_devent`, never
`Global ⇔ Global`, so **every array-to-array channel has to hand-reinvent `element`'s
five-`Decomp` detour** — `inverse` and `sort` both do. G8: no variable-valued index (`X_{X_i}`),
which blocks `symmetric_all_different`'s self-inverse half and `sort`'s permutation channel.
W2-C deliberately *reinforced* the existing G3 (variable-vs-variable comparison) rather than
opening a duplicate, noting `maximum`/`minimum`/`arg_max`/`arg_min` hit it independently — the
right instinct, and the gap numbering across the three sessions' files will need reconciling
when they are consolidated.

**`element`'s defect diagnosed, and it is a one-line error.** Read off the source, not run:
`Decomp 4` composes `foralli` onto `B3 ⇔ V=t` and `forallt` onto `B2 ⇔ I=i`, but `V` and `I` are
*scalars* — they need no quantifier at all. `B1` in the very same clause uses plain point
substitution. The orchestrator confirmed the structure at generator l.383–387. Recorded on the
W1-T9 row; that is where the fix belongs.

**Skipped, correctly:** `all_disjoint`, `int_set_channel`, `link_set_to_booleans` (E5), and the
float variants of `arg_max`/`arg_min` (E7) — one-liners, not specs.

**Noted for the `CHRISTMAS_LIST.md` owner:** §9's `element` row says "already in
`cata/element.tex`, 6 rules", which is accurate but reads as a coverage claim; the validated
figure is 2 of 6. Not a contradiction — an ambiguity worth closing when that file gets an owner.

### 2026-09-18 — W2-A (W2-T5, §3 value ordering/precedence/symmetry + §4 sequencing/sliding) — CLOSED

Five shapes in `decomps/_shapes-seq.md`. **A** threshold chain (`increasing`/`decreasing`,
already built, zero auxiliaries — the reified `B` *is* the explained literal). **B** Boolean
state chain with a genuine auxiliary (`value_precede`, `lex_less`/`lex_lesseq`) — mechanically
the same `rule4`/fixed-shift skeleton as A, but the chained Boolean is an accumulated fact with
no backing `Global_devent`, which matters (see G6 below). **C** Boolean-sum cardinality, reused
as-is from the counting-family pilot, tentatively for `alternative`. **D** min/max-over-index-set,
reused from `range`/`roots`, for `span`. **E** integer prefix-sum sliding window
(`sliding_sum`) — does not reduce to A-D, blocked outright (below).

**Checked the roadmap's own claim and it is half right.** "`value_precede` is structurally
identical to `increasing`" — true for the `rule4`+fixed-shift mechanics, false for the
auxiliary count: `increasing` needs none, `value_precede`'s `b_i` is a genuine accumulated-state
auxiliary, which is exactly the D-0004 concern `regular` was chosen to avoid. Recorded in
`decomps/value_precede.md` as a correction, not a rejection of the E0 rating.

**Three new gaps (`decomps/_gaps-seq.md`; G6-G8, numbered independently of W2-C's own G6-G8,
reconciliation is the consolidator's job).** G6: `var_name`'s `B` constructor prints as the
literal string `"ERROR B "`, unconditionally, in both printers (generator lines 399, 427) —
harmless today because every existing `B` washes out to a `Global_devent` before printing, but
live risk for Shape B's accumulated-state auxiliaries (`value_precede`, `lex_less`), which have
no `Global_devent` to resolve back to; whether the AND/OR walk fully unfolds the recursion
before printing is not established, not run. This sharpens D-0004 with a concrete broken-output
mechanism rather than a stylistic one. G7: no rule schema sums integer-valued expressions, only
Boolean occurrence counts (`rule5`-`rule7` are cardinality, not arithmetic) — blocks
`sliding_sum` outright; sharpens `CHRISTMAS_LIST.md`'s E1 line, which could be misread as "extend
the existing sum schemas" when it cannot be. G8: `var_name` has no constructor for an
integer-valued auxiliary at all (`sliding_sum`'s `S_i`). Two checked negatives also recorded:
matrix row-indexing (`lex2`, orbitopes) already has what it needs in the `R` index family used
by `table`, and instance-dependent chain length (`lex_chain_*`) already has what it needs in
`ind_set`'s `D2 of ind_name list` — neither is a gap, flagged only so nobody re-derives them as
one.

**`sliding_sum` gets a full spec but no rule derivation** — E1+E2 per `CHRISTMAS_LIST.md`,
confirmed by reading the generator rather than trusting the list entry; it is one of D-0004's
own named exceptions (auxiliary `S_i` recorded and justified, not eliminated), but the current
encoding has no schema for it at all, so `decomps/sliding_sum.md` stops at the maths rather than
forcing a fake `rule1`/`rule3` derivation that would silently drop the arithmetic.

**Two files carry an explicit low-confidence hedge:** `span.md` and `alternative.md`. Neither
constraint's predicate signature is given in `CHRISTMAS_LIST.md` §4, and this session's scoped
reading (§3-§4 only, no web search) cannot independently pin them down; both decompositions are
reconstructed from general knowledge of MiniZinc's scheduling globals and flagged as such rather
than asserted. `alternative.md` is flagged more strongly than `span.md` — "exactly one of several
options" has more than one standard encoding and this session cannot tell which one MiniZinc
picked without reading past its scope.

**Skipped, correctly:** none — §3 and §4 contain no sets/E5, graph/E6, float/E7 or geometry
constraints, so there was nothing to give a one-line-only treatment.

**Committed as:** every file above landed inside `b09b81c` ("Close W2-C..."), not a commit of
this session's own — see the note above this section. Re-verify the file list against that
commit's `--stat` if provenance matters.

### 2026-09-18 — orchestrator note on W2-A's commit boundary: the fault was mine

W2-A reported that its staged files were swept into `b09b81c`. That commit is **mine**, not
W2-C's: I ran `git add -A` while two sessions were still writing into a shared checkout. The
content is exactly as W2-A wrote it and nothing was lost, but the authorship and the commit
boundary are wrong, and no amend can fix that without rewriting a landed commit. **From here,
the orchestrator stages explicit paths, never `-A`, while any session is running.** W2-A also
appended to `WORKLOG.md`, which its brief marked read-only; it did so to document exactly this,
the append-only rule meant nothing merged badly, and the record is better for having it. Noted,
not held against it — but the ownership line stands for the next wave.

### 2026-09-18 — W2-A (W2-T5, §3 + §4) — CLOSED. Its own note is above; this is the verification.

Five shapes, and the collapse is the point: `value_precede_chain`, `seq_precede_chain`,
`lex_lesseq`, `lex2`/`strict_lex2`/`lex2_strict`, `lex_chain_*`, the orbitopes and both symmetry
constraints are all **three-liners** — instances of two shapes. The matrix variants reuse the
`R` row-index family the generator already has for `table`, and variable pair-counts are already
expressible through `ind_set`'s `D2` list variant, so neither needed new machinery. W2-A
recorded those two as **checked negatives** — "not a gap, here is why" — which is worth as much
as a gap and is rarer.

**G6 verified, with a correction: the literal `"ERROR B "` is at generator l.399 and l.428**,
not 427. It is *printed into the output*, not raised — the same disease W1-T3 cured in the
filter, still present in the printer. No shipped entry triggers it because their `B` always
resolves to a `Global_devent` first; `value_precede` and `lex_less` would trigger it on day one.
Now roadmap **W1-T10** and a `CLAUDE.md` trap.

**A roadmap claim corrected.** W3-T2 said `value_precede` is "a Boolean state chain, same shape
as the working `increasing`". Half true: same `rule4` chain mechanics, but it needs a genuine
accumulated-state auxiliary that `increasing` does not — the exact leak D-0004 flags. Corrected
in place. This is the second inherited claim this wave has overturned by checking it.

**`sliding_sum` is blocked outright** — no rule schema sums integer-valued expressions, only
Boolean occurrence counts (W2-A's G7), and `var_name` has no integer-valued auxiliary slot at
all (its G8). Its spec stops at the maths, correctly, rather than inventing a derivation.

**Nothing skipped:** §3 and §4 contain no set, graph, float or geometry constraints.

**Gap numbering now needs reconciling.** W2-A and W2-C both numbered from G6 into different
files and they mean different things. The consolidation into `docs/DECOMP_FORMAT_NOTES.md` is
the orchestrator's, after W2-B lands.
