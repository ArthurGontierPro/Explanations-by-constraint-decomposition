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
| **`catalog/inverse_fn.md` and `catalog/sort_fn.md` are now stale.** Both resolve to a parent entry and quote its Status row verbatim as `not reviewed`; `inverse.md` and `sort.md` were reviewed 2026-09-21 and their Status rows now read `nothing generated — blocked on G9` / `— blocked on G10`. The same will happen to every `*_fn` pointer whose parent gets reviewed | `catalog/*_fn.md` | R6 2026-09-21 | open |
| **`tools/catalog_stub.py` under-reports specs.** It tests `os.path.isfile("decomps/<name>.md")`, so any constraint covered by a multi-constraint spec file is stubbed as having none. **Seven of R6's twelve were wrong this way** — `inverse_in_range`, `sort`, `arg_sort`, `minimum`, `symmetric_all_different`, `writes`, `writes_seq` are covered by `decomps/inverse.md`, `decomps/maximum.md`, `decomps/all_different.md` and `decomps/write.md`, whose title lines list every name they cover. Other slices will have the same defect; a grep of `decomps/*.md` title lines would fix it generatively | `tools/catalog_stub.py` | R6 2026-09-21 | open |
| **The status legend has no value for "encodable today, unwritten".** `member`'s specified decomposition (`rule1` + `rule4`, shape S4) needs no gap at all — every schema it uses runs inside `nvalues` — and the six statuses cover only generated-and-judged, generated-and-unjudged, and blocked-on-a-gap. `catalog/member.md` uses `nothing generated — blocked on G3`, which is honest only because MiniZinc's `member` takes a var target; a par-only constraint in the same position would have no honest row. Raised, not decided — a legend change is `docs/DECISIONS.md`'s | `catalog/README.md`, `docs/DECISIONS.md` | R6 2026-09-21 | open |
| **`docs/VALIDATOR.md:287` is a sixth stale per-entry row and is not on W1-T11's list.** It reads `table \| 3 \| 3 UNSOUND`; `cata/table.tex` has held 0 rules since W1-T2. `docs/ROADMAP.md:55` (W1-T11, fourth item) names `allequal`, `nvalues`, `atleastnvalues`, `atmostnvalues` and `gcc` as stale there and not `table`. Also `docs/VALIDATOR.md:60` cites `table`'s ground semantics at generator `l.429–431`; the value is at **862-864** | `docs/VALIDATOR.md`, `docs/ROADMAP.md` | R6 2026-09-21 | open |
| **SUPERSEDES the legend-hole row above.** The orchestrator has defined **`encodable today, not encoded`** and R6 has adopted it for `catalog/member.md` and `catalog/inverse.md`. **As of commit `46719da` the value is in neither `catalog/README.md`'s status legend (still six values, ending at `nothing generated — blocked on G<n>`) nor `catalog/TEMPLATE.md`**, and `catalog/strictly_increasing.md`'s own Status row still reads `**nothing generated** — and **no status-legend value fits**`. Four entries now use a status the format does not define. Needs the legend entry landed and R5's two rows updated | `catalog/README.md`, `catalog/TEMPLATE.md`, `catalog/strictly_increasing.md`, `catalog/strictly_decreasing.md` | R6 2026-09-21 | open |
| **`decomps/write.md`'s G2 paragraph is wrong in both directions, and `decomps/inverse.md` omits G2 entirely.** It says a second user array "would print as a Boolean auxiliary": with `B of int` it does not print at all — `printvartex` **raises** (generator l.517, W1-T10) — and **`O` is a genuine second-array letter** that the paragraph does not mention (`printvartex` l.522, the same indexed-array path `X` uses; `gccn` already carries `O` as a real user global at l.829). Consequence for the catalog: a two-array constraint is **encodable today** with one array wearing `gcc`'s name, so G2 is a legibility cost, not a wall. R6 initially got this wrong in five entries and corrected them at `46719da` | `decomps/write.md`, `decomps/inverse.md` | R6 2026-09-21 | open |
| **Authorship defect, flagged not rewritten: `catalog/sum_pred.md` (255 lines) was swept into R6's commit `9bdcd69`** by a `git add -A` while a sibling session's edit sat unstaged in the shared checkout. Content is that session's and is intact; only the commit boundary and the `Co-Authored-By` line are wrong. Not amended — history is shared and three sessions are live, and the repo's precedent for this (the W2-A/W2-C sweep recorded in `## Completed`) is to flag rather than rewrite. **R6 has switched to explicit-path staging; the very next commit left six sibling-modified files correctly unstaged** | — | R6 2026-09-21 | flagged, do not rewrite |
| **PARTLY RESOLVED, re-measured after `19e0af1`.** The legend row for `encodable today, not encoded` has landed at `catalog/README.md:66` (the legend now has **seven** values), so R6's preceding row is stale in its first half. Still open: **`catalog/TEMPLATE.md` does not carry the value** (`grep -c 'encodable today' catalog/TEMPLATE.md` → 0), and `catalog/strictly_increasing.md` / `catalog/strictly_decreasing.md` still read `**nothing generated** — and **no status-legend value fits**`, which the legend has now overtaken. R6's `inverse.md` and `member.md` were updated to cite `README.md:66` | `catalog/TEMPLATE.md`, `catalog/strictly_increasing.md`, `catalog/strictly_decreasing.md` | R6 2026-09-21 | open |

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
| Catalog C1/C2/C3 | C1, C2, C3 (2026-09-21) | `catalog/**`. First three entries complete: `alldifferent` **weaker than published**, `gcc` **out of reach**, `cumulative` **out of reach by gaps, not by structure** |
| W2-T5 §3+§4 | `decomps/` files for its own constraints + `decomps/_shapes-seq.md` + `decomps/_gaps-seq.md` | W2-A (2026-09-18) | 2026-09-18 |
| W2-T5 §5+§6 | `decomps/` files for its own constraints + `decomps/_shapes-ext.md` + `decomps/_gaps-ext.md` | W2-B (2026-09-18) | 2026-09-18 |
| W2-T5 §1+§9 | `decomps/` files for its own constraints + `decomps/_shapes-perm.md` + `decomps/_gaps-perm.md` | W2-C (2026-09-18) | 2026-09-18 |
| W1-T2 + W1-T9 + W1-T10 | `explenation generator.ml` + the goldens it regenerates — **rule engine, sole owner** | W3-S (2026-09-18) | 2026-09-18 |
| W2-T5 §11 + shape consolidation + D-0011 relabelling | `decomps/**`, `docs/DECOMP_FORMAT_NOTES.md` | W3-D (2026-09-18) | 2026-09-18 |
| `CHRISTMAS_LIST.md` repairs (4 recorded issues) | `CHRISTMAS_LIST.md` | W3-C (2026-09-18) | 2026-09-18 |
| W1-T11(a) + priority ranking | `tools/mzn_coverage.py`, `docs/COVERAGE.md` | orchestrator (2026-09-21) | 2026-09-21 |
| Catalog: format + first entries | `catalog/**` (new) | C1 (2026-09-21) | 2026-09-21 |
| Catalog: sourcing the published explanations | `catalog/_literature/**` (new) | C2 (2026-09-21) | 2026-09-21 |
| Catalog: merge literature + write calibration verdicts (W3-T5) | `catalog/*.md` (not `_literature/`) | C3 (2026-09-21) | 2026-09-21 |
| Catalog: the five silent entries | `catalog/{among,range,regular,roots,sum}.md` | E1 (2026-09-21) | 2026-09-21 |
| Catalog: the seven rule-bearing entries | `catalog/{allequal,atleastnvalues,atmostnvalues,nvalues,increasing,decreasing,element}.md` | E2 (2026-09-21) | 2026-09-21 |
| Catalog: the 118-row index + its generator | `catalog/INDEX.md`, `tools/catalog_index.py` | E3 (2026-09-21) | 2026-09-21 |
| Catalog: stub every global that has no entry | `tools/catalog_stub.py`, the generated `catalog/<name>.md` stubs, `tools/catalog_index.py` | S-A (2026-09-21) | 2026-09-21 |
| Catalog: the problematic-constraints register | `catalog/PROBLEMATIC.md` | S-C (2026-09-21) | 2026-09-21 |
| Review the tier-D stubs | the tier-D `catalog/<name>.md` stubs only | R1 (2026-09-21) | 2026-09-21 |
| Review the tier-C and unclassified stubs | those `catalog/<name>.md` stubs only | R2 (2026-09-21) | 2026-09-21 |
| Review the out-of-scope stubs | those `catalog/<name>.md` stubs only | R3 (2026-09-21) | 2026-09-21 |
| Review the counting/cardinality stubs (13) | those `catalog/<name>.md` only | R4 (2026-09-21) | 2026-09-21 |
| Review the lex/sequencing stubs (14) | those `catalog/<name>.md` only | R5 (2026-09-21) | 2026-09-21 |
| Review the channelling/order stubs + `table` (12) | those `catalog/<name>.md` only | R6 (2026-09-21) | 2026-09-21 |

_**C1 RELEASED 2026-09-21.** `catalog/` created: `TEMPLATE.md`, `README.md`, and the first three entries (`alldifferent.md`, `cumulative.md`, `gcc.md`). Nothing outside `catalog/` was touched, and `catalog/_literature/**` was left untouched for C2. `make check` re-run: exit 0, gate passed. `make validate` re-run: **34 rules in 11 entries, 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**, 19/19 invariants, 11/11 controls. **C2 is still claimed.**_

_W3-C RELEASED (`1e7dc67`): index coverage 113/118 → **118/118**. W3-D RELEASED (`04d800a`, `1d25c45`, `b083974`): the corpus is complete — **12 shapes + 3 modifiers cover 55 constraints**. W3-S RELEASED (`790bfa7`, `fbb95c7`, `47bb4ef`, `576c718`). **Wave three is closed. Nothing is claimed.**_

_W2-C closed (`c0a704a`), W2-A closed (`fdf46ca`), W2-B closed (`c5a8352`). **Wave two is closed.** Gaps consolidated at `9774a62`. Wave three claimed 2026-09-18: engine fixes, spec consolidation, and the literature index — three files, three owners, no overlap._

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

_**S-A RELEASED 2026-09-21** (`c753045`, `021bcbd`, `b9a4bd0`). `tools/catalog_stub.py` (new), 106 generated `catalog/<name>.md` stubs, `tools/catalog_index.py`, `catalog/INDEX.md`, `catalog/README.md`, `.gitignore`. Index now reads **118 / 118 (12 reviewed, 106 stubs)** and cannot print the total without the split. The 12 reviewed entries and `catalog/_literature/**` were not touched: the generator refuses any `catalog/*.md` lacking the `AUTO-STUB — NOT REVIEWED` marker and reported all 12 skipped. `catalog/PROBLEMATIC.md` (S-C) was not created, read or written by this session, only added to the index's non-entry list so it is not counted as a constraint entry._

_**R6 RELEASED 2026-09-21.** 12 stubs upgraded to reviewed entries: `table`, `inverse`, `inverse_in_range`, `sort`, `arg_sort`, `maximum`, `minimum`, `member`, `symmetric_all_different`, `write`, `writes`, `writes_seq`. All twelve emit **0 rules**; none is in `explenation generator.ml`, and `cata/table.tex` holds only its diagnostics footer. `make validate` was run (totals **34 rules in 11 entries: 13 SOUND and MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**) and `table` is in the eleven in-scope entries with 0 rules, **not** in the out-of-scope block — the entry says so. Statuses: `table` G6; `inverse` G9 (recorded as a **cost**, not a wall — `element` proves the detour is writable); `inverse_in_range` G8 (a wall); `sort`/`arg_sort` G10; `maximum`/`minimum` G3; `member` G3 for the var-target signature only; `symmetric_all_different` G10; `write`/`writes`/`writes_seq` G18. Every calibration is `no published rule` except `table`, which is `pending sourcing (C2)`. Four findings are routed above under `## Cross-session requests`; two more are recorded in the entries themselves — **`arg_sort` is not one of `decomps/_shapes.md`'s five unshaped G3-blocked constraints** (those are `maximum`, `minimum`, `arg_max`, `arg_min`, `span`; `_shapes.md` lists `arg_sort` under S6), and **G2 is a hard stop rather than a legibility cost for any constraint with two user arrays**, because a second array encoded as `B 1` makes `printvartex` raise at generator l.517 rather than print badly. `decomps/inverse.md`, `decomps/maximum.md` and `decomps/all_different.md` all use pre-consolidation perm-local gap numbers (their G6/G7/G8 are G8/G9/G10); the entries translate them in place and flag the rot. No file outside the twelve `catalog/*.md` and this one was modified._

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

### 2026-09-18 — W2-B (W2-T5, §5 extensional + §6 scheduling) — CLOSED. Wave two is closed.

Eight shapes, 15 constraints, nothing out of scope in either family. The three findings below
are the most consequential of the whole wave, and none of them is a spec.

**1. The shipped `regular` is not a decomposition of `regular`.** Read off generator l.713 (not
measured): it is a complete, auxiliary-free decomposition of the **strictly 2-local** languages
— a consecutive-pair chain cannot express "an even number of `a`s". This does not challenge
D-0003, which decides where decompositions come from, and nothing measured bears on it because
`docs/VALIDATOR.md` puts `regular` out of scope. But it splits W3-T3 into two plans that the
roadmap's one line was hiding: G6+G7 buys a *complete method for the 2-local fragment*, which is
genuinely the smallest complete contribution available; `regular` entire additionally needs E1
and G17, and at that point `mdd` is nearly free and the contribution is no longer small.
**Either is defensible; claiming the first while describing the second is not.** Recorded on the
W3-T3 row.

**2. M-1's criterion survives in direction, not as written.** "Inline a state only when its state
predicate is a finite disjunction over user literals" draws no line at all: over finite domains
*every* predicate over `X_1..X_{i-1}` is a finite disjunction — its full DNF — so general
`regular` and `mdd` pass it. Sharpened to **"the state predicate must be a clause, every disjunct
a single literal"**, it separates cleanly: `increasing`, `int_value_precede` and strictly-2-local
`regular` pass; general `regular`, `mdd` and all counter automata fail. It then characterises
exactly the fragment this repo's decompositions cover, which is the best evidence it is the right
criterion. M-1's counter half needed no repair. **This is the wave checking the previous wave's
proposal instead of inheriting it.**

**3. E2 is two extensions, not one.** G6 (a 2-D constant table read as a *function*, `t = T[r,i]`)
and G7 (a value set *indexed by another index*, `t' ∈ D(t)`). D-0006's E2 line names only G6, and
cites `regular` as its constraint — but `regular` needs G7. Without G6 there is no correct
`table` at all: its three shipped rules are measured UNSOUND, and the cause is a free `r` index
on the `X` literal itself (l.720–722 plus `x3ac`).

**Also:** `cata/cumulative.tex` is `disjunctive` — `rule1` + `rule3` + `rule5` over one
unweighted family with an implicit bound of 1, confirmed by the orchestrator at l.680–682. Real
`cumulative` needs G11/G15 to be *expressible* and E4 to be *good*. §5's wall is expressiveness;
§6's is rule quality; **a frozen format solves only the first.**

**One stale finding, and it is the failure mode `CLAUDE.md` warns about.** W2-B reported that
`CLAUDE.md` still tells readers to count rules with `grep -c '\frac'`. It does not — that was
corrected at `b93644a`, before wave two was claimed (`CLAUDE.md` l.148–150 now gives the `grep -o`
form and the measured counts). A finding taken from a document state that predates the fix, which
is exactly the trap the "Verify before you report" section describes. No harm done; worth naming.

### 2026-09-18 — W3-C (`CHRISTMAS_LIST.md` repairs) — CLOSED

**The index now covers 118 of 118 globals** — re-run by the orchestrator: `covered 118 (100.0%)`,
`missing 0`, `no duplicate names`, against 113/118 with 5 missing and one duplicate before. Every
repaired row carries a `2026-09-18, W3-C` marker so a reader can tell a repair from the original
research session's work.

Fixed: the missing `all_equal` row (literature "none" — **not invented**, which is the right answer
for most of the 118); `lex_greater`/`lex_greatereq` added as argument-swapped `lex_less` instances
citing the wave-two shapes; the duplicate `cost_mdd` reconciled to §5's row under D-0011, with the
stale §11 row removed behind a comment marker rather than silently deleted; `cumulatives_opt` and
`disjunctive_strict_opt` named explicitly, since the `_strict`/`_opt` shorthand does not compose
past two suffixes and was silently dropping four-way combinations. The `element` row now states
**2 of 6 validated** instead of "6 rules", which read as coverage; the `range`/`roots` row now
disambiguates itself from gccat's unrelated `range_ctr`.

**W3-C corrected its own brief, and it was right.** I wrote that `decomps/` specs the `all_equal`
family. It does not — `ls decomps/ | grep equal` returns nothing, confirmed. Wave two's §1 session
wrote `all_different.md` and missed `all_equal` entirely, so a **shipped** catalog entry has no
spec in the corpus. W3-C said so in the row rather than citing a file that does not exist. Routed
to W3-D mid-task, because its headline is "N shapes covering M constraints" and M was short by one.

**Left flagged and correct as written:** `alldifferent_except_0` still reports as "named, not a
2.10.1 global" — it is marked `(alias)` and `docs/COVERAGE.md` already calls that defensible;
likewise the three rows with no E-code (`geost` is "out", the `*_fn` row covers 11 functional
variants). `--check` still exits 1 for these, which is the tool being honest, not a regression.

**New, small, unowned:** `tools/mzn_coverage.py` predates D-0011 and does not recognise **E8**/
**E9**, so it parses the `(was E3; …)` trailing text as a literal E3. The traceability text is
worth keeping; the classifier should learn the two new codes. Nobody owns `tools/`.

### 2026-09-18 — W3-D (§11, cross-family consolidation, D-0011 relabelling) — CLOSED

**The coverage story now has a number: `decomps/_shapes.md` — 12 shapes plus 3 modifiers cover
55 in-scope constraints**, per-shape counts tabulated so it is auditable. Five more (`maximum`,
`minimum`, `arg_max`, `arg_min`, `span`) have no shape at all: **G3 blocks them before one can be
written.** "118 globals" is a list; "12 shapes" is a claim that can be defended or refuted, and
it is the right unit for D-0010.

**The merge that matters most:** `all_different` and `at_least`/`at_most`/`exactly` are **one
shape**, differing only in the threshold and in whether the counted value is a parameter or an
index family. Consequence, and it is the kind of thing only consolidation finds: **G1 (no bare
integer threshold) is one defect, not two.** Also merged: the monotone chain across three
families (one generator construct, l.689 and l.713, differing only in `imap`s), EXT-3 into
EXT-2b, the two accumulator shapes into one, and `all_equal` into S4 rather than a 13th shape.

**Rejections are the better half of the work.** S7 vs S8 kept apart because S8 recurses with the
state as a pivot — *that difference is G17*. S9 vs S10 kept apart because a weighted sum is a
missing schema, not a parameter — the exact distinction D-0011 was written to protect. S1 vs S5
kept apart because S5's Boolean has no `Global_devent` behind it, which is the whole of W1-T10.
Two conventions were declared openly rather than assumed: `{rule3,rule4}` is one family by De
Morgan with free sign bits, and `{rule5,rule6,rule7}` is one comparator-parameterised family.

**Three contradictions between sessions, caught exactly as intended.** (1) `span.md` claimed a
min/max shape at E0 while `maximum.md` said the same thing is impossible — the second is right,
`span` is G3-blocked. (2) The cause is a **misreading of the generator**: `_shapes-seq.md` read
`rule6`/`rule7` as ∀/∃, but they are `∑ ≥ c` and `∑ = c` — confirmed by the orchestrator at the
definitions, l.339/353/367, which carry the comments `Bool sum<=c`, `Bool sum=>c`, `Bool sum=c`.
So `range`/`roots` are sum shapes and were never a precedent for min/max. (3) `lex_chain.md`
still asserted the `D2` escape hatch that the wave-two consolidation withdrew. Correction notes
added to the affected specs; **no wave-two prose was rewritten**, which is the right instinct.

**D-0011 applied per site, as judgement not sed:** `cumulative` → E8 (one sum per time point,
the `failwith` is never reached); `knapsack` → E1+E3+E8+E9, the only constraint in the corpus
needing all three sum codes; `cost_regular`/`cost_mdd` → E1+E2+E9; the ext shape and gap files
relabelled and their "contradiction to report" paragraphs marked resolved rather than left open.

**One new gap, G18** — `∀j ≠ I` where `I` is a *decision variable* (`write`, `writes`,
`writes_seq`). G8 covers a constant exclusion and G14 a variable-determined summation extent;
neither covers this. **Everything else in §11 landed on existing gaps: the gap list converged
before the corpus ran out**, which is the strongest sign so far that W2-T1 can freeze against
real requirements rather than guesses.

`all_equal` was added on the orchestrator's mid-task request and is S4 composed twice, E0 — the
decomposition is sound; it is the shipped rules 2–3 that invert the quantifier (W3-S is fixing
that in the generator now).

### 2026-09-18 — W3-S (W1-T2 + W1-T9 + W1-T10) — CLOSED. Wave three is closed.

Re-run by the orchestrator from a clean tree: `make check` exit 0, `make validate` exit 0.
**42 rules / 11 sound and minimal / 31 flagged / 14 unmeasurable → 34 rules / 13 sound and
minimal / 21 flagged / 2 unmeasurable.** No sound-and-minimal rule was lost at any step, and
`atleastnvalues.tex` ≡ `atmostnvalues.tex` was preserved at every commit — W1-T5's evidence is
intact.

**Read the headline correctly: the catalog got smaller and truer.** `among`, `range`, `regular`,
`roots` and `table` now emit **zero rules** (verified: `grep -o '\frac' | wc -l` → 0 for each).
They were previously emitting rules quantified over index sets the artifact never defines. The
honest position is that those five entries need G6/G7 — E2 — before they say anything at all,
and that is now a specified requirement rather than a mystery. Anyone quoting "34 rules" against
the earlier "53 rules" census should quote this paragraph with it.

**`allequal`'s defect was not local, which is why it cleared four other entries.** `rule3`/`rule4`
built their pair with `EXOR` where `EXAND` belongs, so each half of a conjunction shipped as a
rule on its own; the multi-conjunct branch two lines down, and `rule5/6/7`, already used `EXAND`.
One fix, and UNSOUND rules also disappeared from `atleast`, `atmost`, `nvalues` and `table`.
`allequal`'s rules 2–3 could not be *corrected* — `¬B2`/`¬B3` simply are not derivable from
`B2 ∨ B3` — so they now die as counted blocked branches instead of shipping.

**`gcc` is the first entry in this project to be fully sound and minimal: 4 of 4.** `forallp`
printed `∀p: O_t ≥ p`, i.e. `O_t ≥ n`; but `p` is quantified at the *constraint* level, so an
explanation drawn from it is a schema valid per `p`. W3-S added `OpPoint` — ranged but unbound —
which prints, compares and inverts under W1-T7's first-order operators.

**`element` was not fixed, and not forcing it is the best decision in this wave.** The diagnosis
(quantifying over scalars) was right; the prescribed remedy was not — plain `id` *crashes*, and
both principled alternatives made the verdict **worse**, 4 VACUOUS → 4 UNSOUND. Measured reason:
the correct rule needs one binder scoping *both* premises (`∃t. V=t ∧ X_i≠t`), and both the
printer and `validator.ml` (l.333–336) scope binders per literal. So `element` is blocked on
**W1-T1**, now promoted, and once binders have rule-level scope the fix is two tokens, because
`OpPoint` already exists.

**W1-T4 is masked, not fixed — the row stays open.** The census reports 0 empty-premise rules
only because W1-T2 refused that whole branch. The decomposition that produced an empty premise
is untouched and will produce it again the moment G6 lands. W3-S flagged this itself rather than
claiming the row.

**Demonstration over assertion, worth copying.** For W1-T10 the session built a probe
decomposition whose `B2` never resolves: the old generator exits 0 and writes
`$$\frac{ERROR B }{X_i=t}$$` into the catalog; the new one exits 2, names the failure and writes
no file. Zero goldens changed. `T` was fixed alongside `B` — same two lines, same defect.

**Routed, small, unowned:** `validator.ml`'s out-of-scope reason strings are now stale for four
entries (W1-T11 (a)); deriving ground semantics from `ind_op` instead of hand-typing it is
unblocked (W1-T11 (b)); `-w +27+39` went 8 → 6 and the Makefile's expectation is updated.
`ind_set`'s `D2` now raises rather than printing `"setfils"`, so **G7 is untouched** — refusing
is not implementing.

### 2026-09-21 — orchestrator: priority ranking in the coverage tool — CLOSED

`tools/mzn_coverage.py` + `docs/COVERAGE.md`. Claimed and released by the orchestrator; nothing
else was running.

Prompted by a question from the author: `table` has published explanations (Gange/Stuckey/
Szymanek 2011, McIlree/McCreesh 2023) **and** a native propagator, so why derive one? The right
answer is that `table` is a calibration target, not a contribution — and that the list already
holds the two columns needed to say that mechanically, for all 118.

**Measured, 2026-09-21:** tier A (no literature **and** solver only decomposes) = **36**;
B (no literature, native) = 8; C (literature, decomp) = 9; D (literature **and** native) = 19;
unclassified 11; out of scope 35.

**Tier A is this project's argument as a number:** for 36 constraints a generated schema would
be the only schema in existence. Tier D — `table`, `regular`, `alldifferent`, `cumulative` —
is where the interesting constraints are and where the method proves itself rather than pays
off. **This cuts against the current queue:** D-0012 puts `regular` first, and `regular` is
tier D.

Scope rules were wrong on the first run and are now aligned with `docs/ROADMAP.md`: geometry and
packing rows carry E2/E8, not E5/E6/E7, so a code-only filter ranked `diffn*`, `bin_packing*` and
`geost` as tier A. Section match added; tier A went 44 → 36.

Fixed in passing (W1-T11(a), the `tools/` half): the E-code regex stopped at `E7` and could not
see **E8**/**E9** from D-0011, and it read the `(was E3; …)` traceability notes as live routes.
**The validator's stale out-of-scope reason strings are a different file and still open.**

### 2026-09-21 — C1, the catalog's first three entries

`catalog/` now exists. `TEMPLATE.md` is the format and carries each field's rules as HTML
comments beside it; `README.md` states what the catalog claims and holds the status legend.
Three entries: `alldifferent.md` (tier D), `cumulative.md` (tier D), `gcc.md` (tier C) — the
only tier-D/C constraints the generator currently emits anything for (D-0013's documented-first
order).

**The wording decision that mattered.** D-0013's appended note says an entry listing some rules
must not read as if it lists all of them. Three devices in the format enforce it, and an entry
that drops any of them is wrong even if every rule in it is right: a **banner** at the top of
every entry; a mandatory **"Scope of this entry"** section that states the finite question the
generator was asked (which events, over which decomposition) and shows the *empty* answers
beside the non-empty ones; and a **status legend** with no value meaning "correct".
The Scope section is the load-bearing one — it is what turns "`alldifferent` has one rule" from
a suspicious-looking number into a stated result.

**Status lines, from this session's own `make validate` (2026-09-21):**
`alldifferent` validated sound and minimal at n,m ≤ 4 (1/1) · `gcc` validated sound and minimal
at n,m ≤ 4 (4/4, the only fully validated entry) · `cumulative` **not validatable** (out of
scope: `UNPARSED: index equation offset: t'=t-d_{i}`, and the capacity appears in no atom).
Run totals reproduce CLAUDE.md exactly: 34 rules in 11 entries, 13 sound and minimal, 21
flagged; 2 rules in 5 entries out of scope.

**Left for C2:** all three entries' *Published explanation → Rule shape* and *Calibration*
sections say `pending C2` and link to `catalog/_literature/<name>.md`. No published rule shape
is stated anywhere from memory. Each entry does record the in-repo prior (from
`CHRISTMAS_LIST.md`) for what the calibration is expected to find, written down *before* the
comparison so the eventual result confirms or contradicts something.

**Discrepancies found while reading, none fixed — they are in files C1 does not own:**

1. **Stale generator line numbers in three places.** `decomps/all_different.md` cites `alldiff`
   at "lines 678-679" (now 808-809); `decomps/cumulative.md` and `decomps/disjunctive.md` cite
   `cumul` at "l.680-682"/"l.682" (now 810-812); `CLAUDE.md` carries the same "generator
   l.680-682". The *claims* made at those sites are still true at the new lines; only the
   numbers rot. `explenation generator.ml` l.399/l.428 in CLAUDE.md's `var_name` trap is
   likewise worth re-checking.
2. **`decomps/all_different.md` misstates the shipped rule.** It gives it as
   `X_i ≠ t ← ∃i'≠i: X_i'=t`. The shipped premise is `∀i'` — and the ∀/∃ difference is the
   whole point of `docs/VALIDATOR.md`'s "sound and minimal does not mean good" passage, since
   the ∃ form is the strictly stronger rule the generator does *not* produce.
3. **22 vs 25 dropped branches.** `CLAUDE.md:156`, `docs/ROADMAP.md:49` and `WORKLOG.md:337`
   all say the old silent filter dropped **22** branches across 16 entries; the comment at
   `explenation generator.ml:549` says **25**. The all-`F` finding is identical in both and is
   the part anything depends on, so this is a bookkeeping conflict, not a result in doubt.
   (For reference: today's shipped catalog drops **21**, measured 2026-09-21 by summing the
   `dropped F` fields across `cata/*.tex` — a different generator, not comparable to either.)
4. **`make check`'s warning census has drifted from CLAUDE.md.** Measured this session:
   default 0, `-w +27+39` **6**, `-w +40+41+42` 31, `-w +a` **56**. CLAUDE.md says 8 and 57 for
   the first and last; the Makefile's own expected line says 6 and 57. The gate passes (the
   census is informational), but CLAUDE.md's "8" is stale and `+a` is off by one against the
   Makefile's own expectation.
5. **No `decomps/global_cardinality.md`.** `gcc` is the one entry of the three with no
   `decomps/` spec; its decomposition was read straight off the generator. Also worth knowing
   for anyone reading that source: the value named `gcc` at l.813-814 is **dead** — `cata/gcc.tex`
   is emitted from `gccn` at l.827-829.
6. **Convention drift in this file, pre-existing.** The 4-column claim rows (W2-A onward,
   including C1/C2 at `88d1c24`) are appended to the 3-column table under `## Completed`, not
   to the one under `## Active claims`. Left alone rather than reflowed, per the append-only
   rule.

### 2026-09-21 — C1 (catalog format + first three entries) — CLOSED

`catalog/{TEMPLATE,README,alldifferent,cumulative,gcc}.md` (`235323f`, `2d17538`, `9fde8db`).
C2 is still sourcing `catalog/_literature/`; every entry's *Rule shape* and *Calibration* field
is `pending C2`, and **no published rule shape was written from memory** — the one thing that
mattered most in that brief.

**The format decision worth keeping.** Beyond the field list I gave it, C1 added a mandatory
**Scope of this entry** section stating the finite question the entry answers — which events,
over which decomposition — and showing the *empty* answers beside the non-empty ones. Its
reasoning: the banner and the legend are boilerplate a reader skips, so the "these are not all
the explanations" guarantee has to be concrete per entry. That is right, and it is exactly the
distinction the D-0008 note draws between complete *coverage* and complete *enumeration*.
`catalog/README.md` says dropping that section makes an entry wrong. Keep it.

**Status lines, from C1's own `make validate` run** (reproducing the recorded figures): 
`alldifferent` validated 1/1 sound and minimal, with the entry stating in place that one rule is
*correct* and that it fires only at `n=2`; `gcc` validated 4/4, still the only fully validated
entry; `cumulative` **not validatable**, and its entry leads with "`cata/cumulative.tex` is
really `disjunctive`".

**Six contradictions found in other sessions' files. Orchestrator verified all six; four fixed
at `eef1d74`, two recorded as rows.**

1. Stale generator line numbers in `decomps/all_different.md`, `decomps/cumulative.md`,
   `decomps/disjunctive.md` and `CLAUDE.md` — the file grew in W1-T3/T7 and the references did
   not follow. Repointed: `alldiff` l.808–809, `cumul` l.810–812.
2. `decomps/all_different.md` states the shipped rule in the `∃i'` form; **it is `∀i'`**
   (verified against `cata/alldifferent.tex`). That difference is the whole floor-versus-strength
   point, so it is not cosmetic. Left for the spec's owner, flagged here.
3. **22 vs 25 dropped branches.** `CLAUDE.md`, `docs/ROADMAP.md` and this file say 22; the
   generator's own comment at l.549 says 25. Both come from W1-S, the instrumentation was a
   one-off, and neither is re-measurable. **Today's catalog drops 21**, measured and
   reproducible: `grep -ho 'dropped F [0-9]*' cata/*.tex | awk '{s+=$3} END{print s}'`. The
   *finding* — all dropped branches were `F`, nothing was lost to the silence — is identical in
   both accounts and is unaffected. Recorded as disputed rather than silently picking one.
4. Warning census drifted again: measured **6 / 31 / 56**; `CLAUDE.md` said 8/31/57 and the
   Makefile expected 57. Both corrected. Third movement in three days, which is why that bullet
   now says re-measure rather than quote.
5. **The `gcc` decomposition value (l.813–814) is dead code** — verified: `gcc` appears only at
   its own definition and in comments, and `cata/gcc.tex` is produced by **`gccn`** (l.827–829).
   Anyone reading `gcc` to understand that entry reads the wrong decomposition. Now **W1-T12**.
   There is also no `decomps/global_cardinality.md`.
6. `gcc` rules 3–4 carry the generator's D-0009 "binds an index name twice" flag *and* a
   `SOUND and MINIMAL` verdict. Both are reported in the entry, which is the honest treatment:
   the rule is sound under every reading the validator enumerated, and the LaTeX still does not
   determine which reading is meant.

### 2026-09-21 — C2 (source the published explanation rules) — CLOSED

`catalog/_literature/{README,alldifferent,cumulative,gcc}.md` (`3ba4139`). Nothing outside
`catalog/_literature/` was touched. **C1's `catalog/` entries can now replace their
`pending C2` fields**; each file is laid out to answer the template's *Published explanation*
and *Calibration* sections directly.

**Access note for whoever sources the next paper.** All three papers are on
`people.eng.unimelb.edu.au/pstuckey/papers/`, and `curl` to that host is blocked by a WAF
(Incapsula returns an HTML challenge with a `.pdf` name — check `file`, not the exit code).
`WebFetch` gets through; its summariser cannot read a PDF and says so, but it **saves the
binary** to the session's tool-results directory, and `pdftotext` in raw mode on that file
gives clean text. Six fetches sourced all three papers. `cumulative.pdf` was a URL guess from
the group's naming pattern and hit the Constraints accepted manuscript.

**Three results.**

1. **Citation correction.** The Hall-set `alldifferent` explanation is in Downing, Feydy,
   Stuckey, *Explaining alldifferent*, ACSC 2012 (CRPIT 122) — **not** the CPAIOR 2012
   *Explaining flow-based propagation*, which the brief named. `CHRISTMAS_LIST.md:116` had it
   right; the CPAIOR paper touches `alldifferent` only as a `gcc` flow network (its Example 4).
2. **Two of the three published explanations are structurally out of reach for this method,
   and that is a result, not a gap.** `alldifferent`'s bounds- and domain-consistent rules and
   the whole of the `gcc` flow rule are quantified over objects that exist only during a
   propagation — a union-find Hall interval, an SCC of the residual graph of a matching. There
   is no index-set expression for "the arcs crossing an SCC". **E4 is necessary but not
   sufficient** for the flow explanation: counting across sums buys the cardinality literals
   `[c_j <= 1]`, not the cut. `cumulative` is the *opposite* case and the better target — the
   paper's own TimeD decomposition (§5.1) is a `rule1` reified equivalence feeding a Boolean
   sum ≤, which is exactly this generator's shape, and the paper states that TimeD and the
   global propagator have **the same propagation strength**.
3. **None of the three papers proves any explanation minimal, and one says outright it does
   not.** Measured: the `alldifferent` paper contains the word "minimal" exactly once, about an
   algorithm. Schutt et al. leave two minimality questions explicitly open (which time point,
   which subset `Ω′`). Downing et al. 2012 call the flow rule "the base explanation" and point
   at lifting methods for a stronger one. So the catalog's *Calibration* verdicts should not
   expect the published rules to be minimal in the validator's sense — the comparison axis is
   the papers' own implication-strength order, which `cumulative.md` quotes.

**One thing a calibration entry can use immediately.** `cata/alldifferent.tex`'s single rule
has premise `X_{i'}=t` universally quantified over all `i' ≠ i`; Downing §4's is the single
literal `[x_h = v]`. Sound, strictly weaker for every `n > 2`, coincident at `n = 2`. That is
D-0013's "weaker than published", with a citable counterpart.

**Not sourced, deliberately:** the typeset Springer/CRPIT versions (all three read as author
preprints — noted in each file, with the pagination caveat); the upper-bound/symmetric forms
of the `alldifferent` bounds rule and the `cumulative` filtering rules, which the papers
themselves omit as "analogous"; Katsirelos 2008 and Rochart 2005, the `gcc`-specific
ancestors. Nothing was blocked — these were budget choices, and each file says so in its own
"What was not sourced".

### 2026-09-21 — C2 (sourcing the published explanations) — CLOSED

`catalog/_literature/{alldifferent,cumulative,gcc}.md` + README (`3ba4139`, `65983de`), 944
lines. **6 fetches of a 15 cap.** Every quote transcribed locally — `curl` to the author's host
is WAF-blocked, so it fetched the PDFs and read them with `pdftotext -raw` rather than trusting
a summariser — and page pointers were re-verified page by page, with several first-draft numbers
corrected before committing. That is the standard this directory should hold to.

**My brief named the wrong paper.** I attributed the Hall-set explanation to Downing, Feydy,
Stuckey 2012 *Explaining flow-based propagation* (CPAIOR). It is **Explaining alldifferent,
ACSC 2012 (CRPIT 122)**. `CHRISTMAS_LIST.md:116` already had it right and C2 caught it. Second
time this wave that a session has corrected a factual error in its own brief.

**Result 1 — two of the three published explanations are structurally out of reach, and that is
a finding, not a failure.** `alldifferent`'s bounds-consistent Hall-interval rule (§5) and
domain-consistent SCC rule (§6) and the whole `gcc` flow rule quantify over **run-time objects**:
a union-find interval, an SCC of a matching's residual graph, a Ford–Fulkerson cut. There is no
index-set expression for "the arcs crossing an SCC". **E4 is necessary but not sufficient** —
counting across sums buys `[c_j ≤ 1]`, it does not buy the cut. W4-T2 should be budgeted as a
clean negative and written up as one.

**Result 2 — `cumulative` is the opposite case and the better target by a distance.** Schutt et
al.'s own **TimeD** decomposition (§5.1) is a `rule1` reified equivalence feeding a Boolean sum
≤ — *this generator's exact shape* — and the paper states TimeD and the global propagator have
**the same propagation strength**. That is a published claim that a decomposition of this shape
loses nothing, and it is the strongest external support this method has. W4-T3 promoted.

**Result 3 — none of the three papers proves any explanation minimal.** Measured: "minimal"
occurs exactly once in the `alldifferent` paper, about an algorithm; Schutt et al. leave two
minimality questions explicitly open; Downing et al. call the flow rule "the base explanation".
**Calibration must therefore compare on the papers' own implication-strength order, not on the
validator's minimality.** W3-T5 corrected accordingly — this changes the method of the
deliverable, not just a number.

**First calibration verdict, available now.** `cata/alldifferent.tex`'s rule universally
quantifies its premise over all `i' ≠ i`; Downing §4's value-consistent rule uses a **single**
literal, `[x_h = v] → [x_i ≠ v]`. Ours is sound, **strictly weaker for n > 2**, and coincident
at `n = 2` — which is exactly the "fires only at `n=2`" observation, now with a citable
counterpart. This is D-0013's first real result: *weaker than published, and here is the
difference.*

**Not sourced, all budget choices rather than blocks:** the typeset Springer/CRPIT versions (all
three read as preprints, with a pagination caveat in each file), the symmetric upper-bound forms
the papers themselves omit, and Katsirelos 2008 / Rochart 2005.

### 2026-09-21 — C3 (merge + calibration) — CLOSED. The catalog's first three entries are done.

**The three verdicts, which are the first output of D-0013:**

1. **`alldifferent` — weaker than published.** Our premise `⋀_{i'≠i} X_{i'}=t` implies Downing
   §4's single literal `[x_h=v]`; the converse fails, so their rule fires strictly more often.
   Coincident at `n=2`; for `n≥3` our premise contradicts `alldifferent` itself, so the rule is
   sound and **can never fire — while `make validate` still calls it SOUND and MINIMAL**. That
   is the floor-versus-strength distinction, measured against a citation instead of asserted.
2. **`gcc` — out of reach.** No index-set expression exists for "the arcs crossing an SCC", so
   neither implication direction is even statable. C3 sharpened this correctly: it is a
   **quantification** gap, not a vocabulary one — the entry already carries occurrence-count
   atoms of the kind the paper's own nogood uses. The 4 validated rules are marked as answering
   a different question rather than scored against it.
3. **`cumulative` — out of reach by gaps, not by structure**, and that distinction is the
   valuable part. Schutt et al.'s TimeD is `rule1 → rule3 → rule5`, which *is* the shipped
   `cumul` chain (l.810–812) at `r_i = 1, c = 1`. Closing **G11** and **G15** puts the generator
   on the shape the paper says matches the global propagator's strength. Conditional, nothing
   measured, and the entry says so.

**C3 corrected two of C1's priors rather than inheriting them.** C1's `cumulative` entry said
"the honest comparison is against the unary special case of the same papers" — the paper gives
no unary special case; the comparable object is TimeD and the unary specialisation is *this
repo's*. And C1's `alldifferent` Scope attributes the missing `X_i=t` rule to E4, but the
published equality rule comes from an SCC, so E4 is not the route to it. Both recorded.

**Template changed, minimally and with a reason:** the verdict vocabulary lacked `out of reach`
(two of the three verdicts) and `stronger` (possible once you compare by implication). Six
verdicts now defined in `TEMPLATE.md`, with the "never compare on minimality" rule beside them,
and `README.md` matched.

**What a reader still cannot tell, recorded by C3 unprompted** — soundness beyond `n,m ≤ 4` and
beyond a hand-encoded ground semantics; whether the `cumulative` rules are sound at all (no
verdict exists); whether the TimeD correspondence survives contact with the generator, since the
shift direction cannot be read off the index operators; and what the CPAIOR 2013
time-table-edge-finding paper says (`NOT SOURCED`).

**One loose end it flagged and I fixed (`Makefile`, `catalog/README.md`): `make validate` exits
0, not 1.** The validator *binary* exits 1 when it flags rules, but the target maps only exit 2
— a broken validator — to a failure. The wrong claim was mine, written into the Makefile
comment earlier in this session and copied from there into the catalog README.

**Tension left open, deliberately:** `decomps/cumulative.md` says "E4 makes it good", while the
paper's TimeD statement says a decomposition of this shape already matches the global
propagator. One of those is wrong and the spec corpus is not the catalog's to edit.

### 2026-09-21 — branch `explanation-catalog` pushed

At the author's request. `git checkout -b explanation-catalog` from `master` at `c734f75`, then
`git push -u origin explanation-catalog`: **66 commits ahead of `origin/master`**, the whole of
this session's work. Git forbids spaces in ref names, so the author's "ecplanation catalog"
became `explanation-catalog`. **`master` is untouched and unpushed.** All catalog sessions from
here work on the branch; the orchestrator pushes, sessions commit locally.

### 2026-09-21 — E3 (catalog index) — CLOSED

`tools/catalog_index.py` + `catalog/INDEX.md` (`b2ac3f5`). Regenerate with
`python3 tools/catalog_index.py`; `--dry-run` prints, `--validate-log FILE` reuses a saved run.
Orchestrator re-ran it: numbers reproduce, warnings fire.

**The coverage claim is now measured, and the number is small on purpose:** 3 of 118 have
catalog entries, 8 of 118 have any generated rule, 6 of 118 have any validated one. By tier:
A 36 globals (0 entries, 5 generated, 4 validated), B 8 (0/0/0), C 9 (1/1/1), D 19 (2/2/1).
E1 and E2 are adding twelve more entries as this is written, so **regenerate before quoting.**

**The finding that came out of building it: three shipped catalog files correspond to no
MiniZinc 2.10.1 global at all.** `atleastnvalues` and `atmostnvalues` are **gccat** names
(`atleast_nvalue` / `atmost_nvalue`); MiniZinc says it with `nvalue`. `sum` is the orphan and is
ambiguous besides, between the release's `sum_pred` and `sum_set`. So of the 16 entries the 2020
prototype ships, **only 13 map onto the target list** — worth knowing before anyone writes "16 of
118". Routed to E2 so its two entries say so in place rather than looking like coverage.

**Built the way it should have been:** the alias map is an editable `ALIAS` dict at the top of
the script, every entry sourced to a specific `CHRISTMAS_LIST.md` row in a comment above it, and
unmatched files are **printed as warnings rather than silently dropped** — the one failure mode
that would have inflated coverage. `gcc → global_cardinality` maps the base form only;
`_low_up` and friends are a separate G4 gap and were deliberately not fanned out.

**Stated in its own footer, correctly:** the index cannot show whether a rule is right beyond
the validator's floor, cannot show calibration (that lives per entry), and shows `—` for the
blocking gap of any constraint that has no entry yet, since it greps the entries themselves.

### 2026-09-21 — E1 (the five silent catalog entries) — CLOSED

`catalog/{among,range,regular,roots,sum}.md`, six commits. All ten template headings kept, no
entry says "correct", every number from its own `make validate` run.

| entry | status | blocked on |
|---|---|---|
| `among` | nothing generated (2 candidates, 2 W1-T2 refusals over `D_4`) | **G8** |
| `range` | nothing generated (4 candidates → 3 refusals + 1 `F`) | **G8** |
| `regular` | nothing generated (4 candidates → 2 refusals on `D_8`/`D_9` + 2 `F`) | **G7** |
| `roots` | nothing generated (4 candidates, 4 refusals, no `F` — the cleanest case) | **G8** |
| `sum` | **flagged** — 4 rules: 2 sound but NOT minimal, 2 vacuous; orphaned; not a MiniZinc global | — |

**E1 overruled my brief on the gaps, and it is right.** I told it `regular` was G7+G16 and implied
the others were G6/G7 too. Only `regular` is: `among`'s `D_4` and `range`/`roots`' `D_5`/`D_6`
are **named value subsets**, not sets indexed by another index, so the binding gap is **G8**
(`ind_set` names only whole predefined ranges). For `range`/`roots` it splits the claim further:
G8 unblocks the *artifact*, while the constraints themselves need E5 + G14 (+G2). That split is
the kind of thing an entry is for.

**The find of this wave: `cata/sum.tex`'s producer is not lost.** Verified by the orchestrator —
`3e4f17d` (2020-08-10) has `let sum = [Decomp …]` at l.361 and its `explainall` at l.388;
`e973e1e` (2020-08-19, the `table` index-propagation rewrite) deleted both while keeping the
`sumi`/`sumt` helpers, and rewrote every other `cata` file in the same commit. **W1-T6 becomes
port-it-forward rather than delete-or-regenerate**, and two places that assert "no source in this
repo" (`docs/VALIDATOR.md:55–63`, `validator.ml:439`) are wrong. Both rows updated.

Two consequences E1 drew from the recovered decomposition, written as falsifiable predictions
rather than claims: all four `sum` verdicts follow from `∀p ∈ [1,n]` collapsing to `N ≥ n` /
`N < 1` — **the same rendering `pointp` fixed for `gcc` in W1-T9**, unreachable here only because
the entry is an orphan; and the recovered decomposition is an **order encoding over a BC
channel**, so it needs neither a weighted sum nor an integer-valued schema — contradicting
`decomps/sum_pred.md`'s G11+G12+G13 pricing. `validator.ml`'s `nv_range Sum = (n, n·m)`, written
from gccat alone, independently agrees with the recovered form.

**On `regular`'s fragment sentence** — E1 carried D-0012's "strictly 2-local" verbatim, labelled
it derived rather than measured, and sharpened it: the *shipped* value is narrower still than the
full 2-local fragment — two `Decomp`s, one uniform pair clause, no first/last-symbol condition,
nothing for `q₀`/`F`, and an unguarded `±1` shift. That sharpens W2-B rather than contradicting
it, and it is the honest version of the sentence D-0012 requires.

**Stale references reported, not fixed** (not E1's files): line numbers in `decomps/among.md`,
`decomps/regular.md`, `decomps/_shapes-ext.md`, `decomps/_shapes.md`, `docs/GCCAT.md`,
`CHRISTMAS_LIST.md:206`, `validator.ml:439–453`; and `decomps/_gaps-ext.md`'s X3 quotes a premise
"read off `cata/regular.tex`" that W1-T2 has since removed.

### 2026-09-21 — E2 (the seven rule-bearing catalog entries) — CLOSED. Catalog wave closed.

Seven entries, six commits, nothing outside its own files. **`catalog/INDEX.md` regenerated
after: 12 of 118 globals have entries** (15 entry files, three of which — `atleastnvalues`,
`atmostnvalues`, `sum` — match no MiniZinc global), 8 of 118 have a generated rule, 6 of 118
have a validated one.

| entry | verdict |
|---|---|
| `increasing`, `decreasing` | 2/2 sound and minimal each, **and both fire** |
| `allequal` | 2/2 sound and minimal — but **the premise literal is the conclusion literal** |
| `element` | 2 sound and minimal + **4 vacuous**; `I=i` emits nothing |
| `nvalues` | 4 vacuous + 1 unsound. **No rule that both fires and is sound** |
| `atleastnvalues`, `atmostnvalues` | **0 of 4 sound** each; byte-identity re-measured (`cmp` silent, md5 equal) |

**W1-T5 is diagnosed, and the orchestrator verified the reading at l.343–369.** `rule5` and
`rule6` are the *same four-branch body* with the positive and negative calls interchanged
(`ap`↔`nap`, `fre`↔`fnre`). `ap`/`nap` take their sign from the devent, so negating `B4`'s
reified sign in the decomposition undoes the swap on both descent paths: **as encoded,
`atleastnvalues` and `atmostnvalues` are the same decomposition written twice.** E2 also
recorded a candidate root cause rather than stopping at the mechanism — step 2's channel is
`rule1`, a reified *equivalence*, so `B4_p ⇔ N ≥ p` pins `N` from both sides and the `≤`/`≥`
distinction has nowhere left to live but the sum schema.

**A second CLAUDE.md claim of mine corrected, verified: `element`'s missing `I=i` rule is not an
E4 case.** `elem` (l.834–838) is `rule1`×3 + `rule4`×2 with **no Boolean sum anywhere**, so
"counting across sums" cannot be its route; `alldifferent`'s `rule5` made that analogy tempting
and wrong. Its cause is the scalar-quantifier defect plus per-literal binder scope — W1-T1.

**`allequal` is the opposite failure mode to `element`, and worth naming.** `element`'s rules
are sound and cannot fire; `allequal`'s fire and say nothing — its premise literal *is* its
conclusion literal, and the `.tex` admits two readings (a tautology, and the intended
dichotomy), both sound, so the verdict cannot separate them. Root cause read off source:
`addexists`/`addforall` (l.202–203) do not rename the index they bind, while `addprim` (l.204)
does. That is a sharper, cheaper statement of D-0009 than the one in the record.

**It refined my own heuristic rather than applying it blindly.** I told it to check every
`∀i' ≠ i` premise for whether it can fire, by analogy with `alldifferent`. `atleast`/`atmost`
rule 1 has that shape and *does* fire — its polarity is `X_{i'} ≠ t`, which is satisfiable,
where `alldifferent`'s is `X_{i'} = t`, which is not. Its real defect is different: dropping the
two droppable premises leaves pure domain exhaustion, sound for *any* constraint.

**Sourcing discipline held.** `atleast_nvalue`/`atmost_nvalue` got `pending`, not "no published
rule", because `CHRISTMAS_LIST.md` has **no row** for either — the silence is unsearched, not
empty. The other five got "no published rule" from their rows. Nothing written from memory.

**Reported, not fixed:** `docs/VALIDATOR.md:279–288`'s per-entry table is stale for five
entries (now on W1-T11); `docs/ROADMAP.md:51`'s rule numbering is off by one since `790bfa7`;
`CHRISTMAS_LIST.md` said `decomps/all_equal.md` does not exist (it does, written later that day)
and used "already correct in the repo", which `catalog/README.md` forbids — **both fixed at
`45d1974`**; and `decomps/{all_equal,increasing,element,nvalue}.md` cite pre-W1 line numbers.

### S-A (2026-09-21) — stubbing the remaining 106

**The number to quote is "118 / 118 (12 reviewed, 106 stubs)", never "118 / 118".** That is
enforced in code, not by convention: `tools/catalog_index.py` prints the split in the same
breath as the total and spends four lines saying that a file count is not work done. If a
later session finds a bare 118/118 anywhere, it is a regression.

**What a stub is allowed to know.** Five fields, each naming its own source in the file:
tier (`mzn_coverage.py --rank`), the literature/solver/E-route cells of the constraint's
`CHRISTMAS_LIST.md` row quoted verbatim with the line number, the name's line in the vendored
globals snapshot, a `decomps/<name>.md` link when the spec exists, and the `cata/<name>.tex`
`\frac` count when the file exists. Everything else reads `not reviewed`. No status value, no
blocking gap, no calibration verdict, no guessed extension — a guess and a finding are
indistinguishable six months later, which is the entire point of the exercise.

**Measured, not assumed:** 106 stubs written, 12 files skipped for lacking the marker, 0
existing entries modified (`git show --stat`). Of the 118 release globals, **43** have a
`decomps/<name>.md` under their exact release name, of which **35** fall to stubs; the other
3 spec files (`edit_distance`, `lex_chain`, `orbitope`) name no release global. **No stub
carries a rule count**, because every `cata/*.tex` already belongs to one of the 12 reviewed
entries.

**Idempotence is real and was tested three ways**, not asserted: a second run reports
`0 created / 0 refreshed / 106 already current` and the md5 of `catalog/**` is unchanged; a
run with `date.today()` monkeypatched to 2027-03-04 also changes nothing, because content is
compared with dates normalised out; and de-marking a stub by hand makes the next run skip it
and leave the bytes alone (13 skipped instead of 12).

**Two things a later session should know.** `tools/catalog_index.py` no longer needs an
`ALIAS` row for a basename that spells a release global exactly — identity resolution covers
the 106, and `ALIAS` is back to doing only the job a script cannot: `alldifferent →
all_different` and the three deliberate `None` rows. And `catalog/README.md`'s hand-typed
"entries written | 3 of 118" table is gone, replaced by a pointer to the generated index; it
was stale at 3 when the truth was 12, and a second copy of a generated number will always
rot.

### 2026-09-21 — S-A (stub every remaining global) and S-C (problematic register) — CLOSED

**The catalog's denominator is now honest: `118 / 118` entries — 12 reviewed, 106 stubs.** That
parenthesis is the deliverable, not the 118. `catalog/INDEX.md` carries a `kind` column on every
row, reviewed/stub columns per tier, and four lines saying a file count is not work done.
Regenerate with `python3 tools/catalog_stub.py` then `python3 tools/catalog_index.py` (the index
runs `make validate`, so it needs the opam switch).

**Idempotence was tested rather than asserted**, which is why this can be re-run safely: a second
run reports `0 created / 0 refreshed / 106 already current` with `catalog/**` byte-identical; a
run with the date monkeypatched to 2027 changes nothing, because dates are normalised out of the
comparison; and hand-removing a stub's marker makes the next run skip that file and leave its
bytes alone. **0 existing entries were modified** — `git show --stat 021bcbd` is 106 additions,
no modifications.

**A stub says nothing it cannot source.** Five machine-derived fields, each naming where it came
from, and `not reviewed` everywhere a judgement would go — with the banner stating that this
means *nobody has read this constraint*, not that there is nothing to say. No stub guesses a gap,
a status or an extension.

**A number in my brief was wrong again, and S-A measured the right one.** I said 55 constraints
have a `decomps/` spec; **43 of the 118 globals have one under their exact name**, 35 of those
now stubs. The 55 came from W3-D's shape consolidation, which counts constraints *covered* by the
specs, not files named after globals. Both are true of different things; the brief conflated them.

### The problematic register — `catalog/PROBLEMATIC.md`

Seven categories by kind of trouble, with counts: P1 structurally out of reach (**3 of 3** sourced
explanations, ~8 more predicted); P2 blocked on a named gap (**34 of 118** globals route through
E2); P3 rules that cannot fire (**13 of 34** validated rules vacuous); P4 rules that say nothing
(3 entries); P5 encoded twice indistinguishably (2 constraints); P6 out of scope by decision
(**35 of 118**); P7 not a MiniZinc global at all (3 of the 15 entry files).

**Widest blast radius: the index-set / side-condition family (E2 — G6/G7/G8/G15), 34 of 118.**
Runner-up by rule count is per-literal binder scope (W1-T1/D-0009) at 13 of 36 emitted rules, and
S-C flagged that as a *floor*, because the ambiguity check never inspects the conclusion, so
`all_equal`'s two go uncounted.

**12 problems have no fix scoped anywhere.** The consequential one is now **W1-T13**: nothing
generates or prefers the strongest sound rule — `alldifferent` emits `∀i'` where `∃i'` is sound
and strictly stronger, `all_equal` emits a tautology reading — and **minimality cannot see
either**, so the validator will go on certifying weak rules. **W4-T5** added for `gcc`'s flow rule,
which had an `out of reach` verdict and no write-up row where `alldifferent` and `cumulative`
both had one.

**Of S-C's 13 recorded contradictions the sharpest was mine:** `CLAUDE.md`'s reality table said
34/13/21 while the blockquote below it still said 42/11/31, pre-W1-T2. Fixed at `d430c57`, and
that blockquote now says to re-measure rather than quote either.

### 2026-09-21 — R3 (out-of-scope stubs) — CLOSED

33 entries upgraded, then 7 of them revised again under D-0014. Verified against the fixed tool:
tier A = 43, out of scope = 28, matching.

**Its finding changed a project decision, which is the point of reviewing a stub rather than
trusting it.** `diffn`×4 and `bin_packing`×3 were out of scope only because the ranking filtered
by *section*; their routes are E2 and E8. The decisive line was `CHRISTMAS_LIST.md:51` — the
Huub paper loses *precisely on `diffn` and `cumulative`* — which makes `diffn` a target. D-0014
now decides scope by mechanism, and the section filter was mine.

**On revision it sharpened the blockers past what I told it**, which is the better answer:
`diffn*` is `nothing generated — blocked on **G3**` (only variable-vs-value comparisons exist;
non-overlap needs variable-vs-variable atoms), not "E2" as a bare code; `bin_packing*` is
**G11**, the same gap tier-A `knapsack` carries. Each keeps a short *History* paragraph recording
that the classification was checked rather than assumed — the right instinct, since a reader who
sees only the corrected state cannot tell whether anyone looked.

**Correctly left out of scope, with reasons now recorded in the entries:** all 8 set constraints
(E5 — the event type has no set-membership literal), all 12 graph constraints (E6 — both
documents say *declare* out of scope, not schedule), the 3 float constraints (E7), `geost` (its
route cell names no E-code at all, a stronger ground than a closable extension), and
`arg_max`/`arg_min`, whose route is E2 **+** E7 — the int/bool variant is reachable and has a
native explaining propagator, only the float variant is out. The tooling classifies by name and
cannot split one, so the entry says so instead of the index pretending.

### 2026-09-21 — R2 (tier C + the eleven `*_fn`) — CLOSED

19 files, six commits, resumed cleanly after the session limit and redid nothing.

**The `*_fn` question is answered, and the answer is no: a functional variant does not change the
explanation.** Three steps, each checkable: the method explains *events* derived from a
*decomposition*; `CHRISTMAS_LIST.md:217` says the `_fn` forms "call the predicate form", so the
`Decomp` list and the available literals are identical; `find`/`an`/the printer are functions of
those, so the rules are the same object. R2 then found a **second, independent in-repo source** —
`docs/DECOMP_FORMAT_NOTES.md:129`, wave two's *format* survey, which had already recorded "the
`*_fn` variants — not separate constraints; no gap recorded". Two independent derivations
agreeing is the strongest evidence this catalog has produced without a citation. It settles why
those eleven rows carry no E-code: the route is the base's.

It chose one entry per name rather than a single shared note, for a reason I would not have
thought of: **the catalog's denominator and `tools/catalog_index.py` are both per release
global**, so collapsing eleven names would make the index undercount.

**It found a stub-generator data defect, in all eleven files.** The machine-derived solver cell
read row 217's `—` and rendered Geas and Choco as `absent`. **A solver never sees a `_fn` name**,
so the base's row is the right source. Corrected, and — the part worth copying — it described the
stub's derivation as *right for the cell it read*, rather than calling the generator wrong.

**Tier C's eight entries each name a different gap, which is more informative than the tier.**
`global_cardinality_closed` → G8, and R2's observation that if `cover` is the whole range the
constraint *is* `gcc`, "so G8 is the whole difference"; `global_cardinality_low_up` → G1, because
`gccn`'s `rule6` step with free `p` — the W1-T9 `pointp` repair — already *is* the low/up shape at
`p := lb_t`, and only printing `p = lb_t` is missing; `cumulatives` → G14, with the finding that
`decomps/cumulatives.md`'s workaround **trades G14 for G16** rather than avoiding it;
`cost_regular` → G15, and it "cannot use the shipped auxiliary-free EXT-2a", so it pays G16+G17
rather than `regular.md`'s G7; `cost_mdd` → G15 and pays G6 three or four times over.

**Calibration handled with the right asymmetry:** `out of reach` *inherited* from `gcc.md` for the
gcc trio, but `out of reach` *stated independently* for the cumulative trio — because
`CHRISTMAS_LIST.md:168` says "no new literature", so `cumulative.md`'s positive TimeD result does
**not** transfer to the optional and multi-machine forms. Both `cost_*` left `pending sourcing`.

**Reported, not fixed:** more stale line numbers (`failwith` is at 355/369/383, not the 177-219 in
`DECOMP_FORMAT_NOTES.md` nor the 320/334/348 in `_shapes-ext.md`; `_shapes-ext.md` still has
`cumul` at 680–682; `docs/COVERAGE.md:137–139` cites 118/174/213 for rows now at 120/178/217), and
`docs/COVERAGE.md` still calls `cost_mdd`'s duplicate row a defect that W3-C fixed on 2026-09-18.
I corrected the `failwith` citation and opened **W1-T14** for the pattern itself — six sessions
have now reported line-number rot, and the fix is to cite symbols or to check the citations in
`make check`, not to re-point them by hand a seventh time.

**Could not establish, correctly left open:** whether any individual `*_fn` library body does more
than declare a result and post the predicate. That needs the MiniZinc library, which is not
vendored here, and R2 had no web access. Marked as the one open item rather than assumed.

### 2026-09-21 — R1 (tier-D stubs) — CLOSED. Review wave closed: 79 of 118 reviewed.

Fifteen entries, nine commits, resumed after the session limit without redoing anything.
Index regenerated: **118 / 118 entries — 79 reviewed, 39 stubs** (was 12 reviewed this morning).

**The `disjunctive` finding is confirmed and sharper than my brief.** R1 verified it instead of
taking it: **`rule5` takes no capacity argument at all** (l.343, `rule5 e de c dec ch`), so
`cumul`'s "at most 1" is not a parameter set to 1 — there is no parameter, and `alldiff` uses the
same pair at l.808–809. The consequence is the best news in the wave: `catalog/cumulative.md`
lists G11+G15 between the artifact and Schutt's TimeD, but **for `disjunctive` G11 falls away** —
a unary resource *is* `r_i = 1`, so an unweighted sum is the target rather than an approximation.
Only G15 and G1 remain, making `disjunctive` **the corpus's closest approach to a published
shape**, and `cata/cumulative.tex` is its artifact, filed under the wrong name.

**No new shapes in fifteen constraints** — 7 collapse into S5 (lex/symmetry), 4 into S8, 3 into
S9 plus modifiers. And a rule worth keeping, which R1 derived rather than inherited: **a suffix
is free when it widens a clause** (`mdd_nondet`, `strict_lex2`), **G1 when it is a predicate on a
constant** (`disjunctive_strict`), **G2 when it is a new variable** (`disjunctive_opt`). Also:
`mdd`/`regular_nfa` need G16+G17 *as well as* G7, so unlike `regular` they are on W3-T3's plan
(b) — closing G7 alone produces nothing for them.

**It corrected a stale claim it had itself repeated.** "Index functions are opaque closures" has
been false since W1-T7; R1 wrote it into an entry, found the `ind_op` values, and fixed its own
entry at `974fe3b` — and the duration shift's direction *is* readable, at l.796–797. I have now
retired that trap in `CLAUDE.md` too, along with a second one of mine: the `grep -o '\frac'`
example quoted 3/6/2, and today measures **0/5/2**, because W1-T2 emptied `table` and the `EXAND`
repair took a rule off `nvalues`. A trap note with a stale number teaches the wrong lesson twice.

**New defect, apparently unrecorded anywhere until now — W1-T15:** `printevent_var` (l.493)
renders `var_name`'s `O` as the letter **`X`**, while `printvartex` (l.522) renders `O`.
Plain-text path only, so no shipped `.tex` is affected; it sits beside the
`printind_name_list`/`printiopl_list` tail bug in the same printer.

**`D2` no longer prints `"setfils"` — it raises** (l.463–464, the W1-T2 backstop). The gap is
unchanged, but `docs/DECOMP_FORMAT_NOTES.md` was describing a state that no longer exists;
corrected.

**Left open, correctly:** whether `strict_lex2` and `lex2_strict` are aliases — all three `lex2`
names are distinct exports in the globals snapshot and no `.mzn` is vendored here; every
signature in the fifteen is flagged as recall rather than sourced; and no published rule shape
for the lex, mdd or regular papers, since only three constraints have sourced literature.

### 2026-09-21 — orchestrator error: `catalog/table.md` was never reviewed

I told R1 that `table` was already reviewed and excluded it from the tier-D list. It was not —
C1 wrote `alldifferent`, `cumulative`, `gcc`; E1 wrote `among`, `range`, `regular`, `roots`,
`sum`. `table` has carried the AUTO-STUB banner the whole time. It goes to R6, and it matters
more than most: it is the constraint whose `T[r,i]` link the author and the orchestrator worked
through in detail, and G6 is named for it.

### 2026-09-21 — orchestrator error: `--amend` in a shared checkout

I ran `git commit --amend` while R4 was live. R4 committed between my `git add` and my amend, so
the amend rewrote **R4's** commit: `0c2b28f` now carries R4's `catalog/sum_pred.md` review
alongside my two doc edits, under my message. R4's earlier `2df823f` is untouched and nothing
was lost — the message and the boundary are wrong, the content is not. **I did not rewrite
history a second time to fix a label while a session was running.**

This is the stronger form of the `git add -A` hazard I hit this morning and then warned two
sessions about an hour before doing this. **Rule for the next orchestrator: with live sessions,
stage explicit paths and never amend.** The shared git index is the one piece of shared mutable
state this protocol does not otherwise have.

Also recorded: I told R4 and R6 by message that the status value `encodable today, not encoded`
was "now defined" in `catalog/TEMPLATE.md` before defining it, and it turned out to live in
`catalog/README.md` anyway. It is defined now (`bc64ca3`). Asserting a fact to a session before
making it true is the same failure as a stale document, with a shorter fuse.

### 2026-09-21 — R5 (lex, precedence, sliding: 14 entries) — CLOSED

All 14 reviewed, all `no published rule` — every row's literature cell reads `none`.
**11 of 14 are pure instances**: the two `lex_greater*` (argument swap), six `lex_chain*`
(S5 + row modifier), three precede entries. Three are genuinely distinct.

**`strictly_increasing`/`strictly_decreasing` are free — no gap.** R5 established it by reading:
`tplus`/`tmoin` exist (l.794–795), `imap`/`OpSeq` composes (l.799–801), the `Addint` printer case
is already exercised by `incr`/`decr` (l.471, l.503). Three qualifications stated in place:
`tplus`/`tmoin` appear in no shipped decomposition, nothing was run, and the boundary falls off
two index sets (a note, not a blocker — `increasing` already carries it).

**It found a hole in the status legend and refused to paper over it.** "Encodable today, not
encoded" had no legend value, and the only `nothing generated` form *requires* a gap number.
R5 declined to invent one and reported it. The value now exists (`bc64ca3`).

**`value_precede` is the only one of the fourteen the current format can express** — its guarded
literal is `X_i = t` against a *parameter*, so G3 does not apply; G17 and the W1-T10 raise are
what block it. That corrects the shape of the earlier claim that the whole family is G3-blocked.

**Wrong stub fields, fixed in 12 files:** `Spec: none` on 8, because the stub probes for
`decomps/<exact-name>.md` and misses family specs; bare `native` Chuffed cells on 4 where the row
names `lex.cpp` / `value-precede.cpp`; and a `Literature: absent` heading над a quote that names
Downing et al. 2012 for the sequence family.

### 2026-09-21 — R6 (channelling, order, and `table`: 12 entries) — CLOSED

**`table`** — artifact verified as 0 rules, diagnostics only. `X_i=t` loses its one candidate to
the W1-T2 refusal over `D_4`; `X_i≠t` loses its one to an `F`, because step 3 has no
`Reified_devent` and falls back to the `T` placeholder. Status `nothing generated — blocked on
G6`; calibration `pending sourcing`. The entry carries the precise G6 statement — one anonymous
`t` standing for both `T[r',i]` and `T[r,i]`, so **the unsoundness and the illegibility are the
same fact** — both intended propagations with the second's circularity, and W1-T4's
`MASKED, NOT FIXED`, from which it draws the operational conclusion: **G6 must land *with* any
definition of `D_4`, not after it**, or the empty-premise rule returns.

**On the `D2` route for G6: half viable, and the other half lands on W1-T1.** `ontin (D2 [R 1; I 1])`
is constructible and `apply_op` carries it; missing are a printer, admission by
`ind_set_defined`, and a stated meaning. But it does **not** reach the anonymous-`t` problem:
`OpOn` installs one fresh `T 1`, `OpForall`/`OpPoint` collide on that name, and the only primers
attach `Rel (t', NEQ, t)` unconditionally, which is false for `table`. **Printer and meaning are
the easy part; the second value index is the work, and it is W1-T1 — `element`'s blocker.** That
links the two biggest open items in the repo, which nothing had done before.

**New finding, now in the gap notes:** **G2 is a hard stop, not a legibility cost.** A second
*user array* taken as `B 1` makes `printvartex` **raise** (l.517), so `inverse`, `write` and
`sort` cannot be printed at all. `decomps/write.md` records G2 without the raise;
`decomps/inverse.md` records neither.

**It corrected my brief:** `arg_sort` is **not** one of `_shapes.md`'s five unshaped G3-blocked
constraints (those are `maximum`, `minimum`, `arg_max`, `arg_min`, `span`) — `_shapes.md` lists
it under S6. And it separated cost from wall throughout: `inverse` is G9 as a **cost** (the
`element` detour is writable, so its zero is "unwritten"), while `inverse_in_range` is G8 as a
**wall**. That distinction is worth more than the entries.

**Same wrong stub field as R5, independently:** 7 of 12 stubbed "no spec" while covered by a
family file. Now **W1-T16**.
