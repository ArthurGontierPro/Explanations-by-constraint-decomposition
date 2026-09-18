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

_Dispatched 2026-09-18 by the orchestrator session; supersedes the "wave zero has not been dispatched" note above. Two sessions, per CLAUDE.md. `WORKLOG.md` is owned by the orchestrator for this wave — W0-A and W0-B do not edit it, they report back and the orchestrator records._

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

---

## Completed

| Task | Session | Notes |
|---|---|---|
| — | — | — |
| W0-T4 | W0-B (2026-09-18) | `tools/mzn_coverage.py` + vendored `tools/data/minizinc-2.10.1-globals.txt` + `docs/COVERAGE.md`. Commits `e12ccce`, `80a89a6`. Classifier runs, exits 1 on drift. Coverage and defects verified independently by the orchestrator (see handoff note) |

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
