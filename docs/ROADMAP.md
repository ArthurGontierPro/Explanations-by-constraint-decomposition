# Roadmap

Task IDs here are what sessions claim in `WORKLOG.md`. **Keep IDs stable once published** —
they get referenced from commits and claims. A row whose work moved elsewhere stays, marked
`SUPERSEDED`, naming where it went.

Status: `TODO` / `WIP` / `DONE` / `BLOCKED`.

Waves are dispatch units. **A wave is one or two sessions, never more**, and the second
session exists only when there is an honestly disjoint task — see D-0006 and `CLAUDE.md`.

---

## W0 — a gate exists

Goal: it is possible to tell a correct rule from a plausible one. Nothing else matters until
this is true.

| ID | Task | Status | Notes |
|---|---|---|---|
| W0-T1 | **The validator, written before any fix.** For `n,m ≤ 4` enumerate all stores; check premises ⊨ conclusion, and that no premise is droppable | DONE | **DONE 2026-09-18 (W0-A).** `validator.ml`, `docs/VALIDATOR.md`. Scope is 3 entries, not 16 — rules are parsed from the shipped `.tex`, decomposition semantics hand-encoded, because W1-T7 has not landed. Acceptance test met: it flags `table.tex`'s empty premise and splits the `atleast`/`atmost` collision. **13/13 rules checked were flagged; 0 sound and minimal.** — was: **D-0005.** Acceptance test: it must independently flag `cata/table.tex`'s empty-premise rule and the `atleastnvalues ≡ atmostnvalues` collision. If it does not, the validator is wrong, not the catalog |
| W0-T2 | Stand up a build + `make check` around the **existing OCaml** | DONE | **DONE 2026-09-18 (W0-A).** `Makefile`, `make check`. Warning census corrected: default 0, `-w +27+39` 16, `+40+41+42` 42, `+a` 91. — was: **Corrected 2026-09-18: OCaml 5.1.1 is installed** (opam switch `baguette`) and `ocaml 'explenation generator.ml'` regenerates all 15 entries byte-identically. An earlier draft said OCaml was unavailable, on the evidence of `which ocaml` in a non-interactive shell, and proposed a Julia rewrite on that basis. **There is no longer a reason to rewrite.** The gate is the deliverable, not the language |
| W0-T3 | Golden files: regenerate every `cata/*.tex` and byte-diff against committed output | DONE | **DONE 2026-09-18 (W0-A).** All 15 entries plus `exp.tex` reproduce byte-for-byte; `sum.tex` excluded explicitly and `check-orphans` fails if that set changes. **Correction: `grep -c '\\frac'` does not count rules** — entries are single-line; use `grep -o '\\frac' f | wc -l`. — was: **Mostly already true** — verified 2026-09-18 that the generator reproduces all 15 files byte-for-byte, and `exp.tex` too. So this row is: wire `ocaml gen.ml && diff -r` into `make check`, and delete or regenerate the orphaned `sum.tex` (W1-T6), which is the only diff. Note the files have no trailing newline — count rules with `grep -c '\\frac'` |
| W0-T4 | Automate the `CHRISTMAS_LIST.md` coverage classification so it reruns per MiniZinc release | DONE | **DONE 2026-09-18 (W0-B).** `tools/mzn_coverage.py`, `docs/COVERAGE.md`, vendored 2.10.1 snapshot (no MiniZinc on this machine). Found: no `all_equal` row despite a shipped `cata/allequal.tex`; conflicting `cost_mdd` routes; 5 uncovered globals. — was: **Genuinely disjoint from W0-T1/T2** — touches no generator code. This is the honest parallel task for wave zero. A prototype classifier was written on 2026-09-18 and is not committed |

## M-1 — steal from the Global Constraint Catalog

Outside the W-numbering on purpose: it is prior art to read, not a wave of the build. Nothing
here blocks W1, and W1 does not block it. Requested by the author 2026-09-18.

Beldiceanu, Carlsson and Rampon's *Global Constraint Catalog* is the field's other catalog —
~400 constraints, each with a structured entry, and for many of them a **counter-automaton**.
`CHRISTMAS_LIST.md` does not mention it once (measured: `grep -i -c 'beldiceanu\|gccat'` → 0),
which is a real hole in the literature index. Online at `https://sofdem.github.io/gccat/`,
entry pages `gccat/C<name>.html`.

| ID | Task | Status | Notes |
|---|---|---|---|
| M-1-T1 | Read a bounded slice of the catalog and write `docs/GCCAT.md`: what this project should take, what it must not, mapped onto existing task IDs and E-codes | TODO | **Hard context cap — the catalog is thousands of pages and `CLAUDE.md` says the literature is the expensive context here.** Prioritise the 16 constraints already in `cata/` plus the W3 shortlist. **D-0003 applies in full: decompositions are authored here for explanation quality. A proposal to import the catalog's decompositions wholesale is the MiniZinc proposal again and was already rejected once** |

## W1 — the generator tells the truth

Goal: every existing entry is either validated or reported as failing. No new constraints yet.

| ID | Task | Status | Notes |
|---|---|---|---|
| W1-T1 | Fix index-binder hygiene | TODO | `nvalues.tex` repeats `∀i` twice. Scoping is not hygienic |
| W1-T2 | Define index sets above `D_3` in the printer, or refuse to emit an undefined one | TODO | `regular`, `roots`, `range`, `table` reference `D_4`–`D_9` that appear nowhere. **Refusing is better than printing** — see W1-T3 |
| W1-T3 | Make failure loud: stop `removeimp` silently discarding `F`/`IM`/`FE`/`R` | DONE | **DONE 2026-09-18 (W1-S).** `filter_branches` raises on `FE`/`IM`, warns on `R`, counts `F`; every entry now carries a diagnostics block. **Measured: of 22 branches the old filter dropped across all 16 entries, all 22 were `F` — `IM`/`FE`/`R` never occurred, so no rule was ever lost to the silence.** Census: 43 events, 53 rules, 2 events with no rule, 1 empty premise, 13 ambiguous rules — was: Today "no explanation exists" and "the generator failed" are indistinguishable, which is why `alldifferent.tex` has one rule instead of two. **Do this early** — every later task is debugged through it |
| W1-T4 | Remove the unsound `cata/table.tex` rule, or fix the decomposition that produces it | TODO | Empty premise concluding `X_i = t`. Currently shipped. **W0-A 2026-09-18: worse than recorded — the validator finds all 3 `table.tex` rules unsound under every reading, not just the empty-premise one** |
| W1-T5 | Diagnose `atleastnvalues.tex` ≡ `atmostnvalues.tex` | TODO | Different decompositions (`rule6` vs `rule5`, reified sign flipped) produce byte-identical output. One of them is wrong. **W0-A 2026-09-18 split them: the identical text gets different verdicts (AMBIGUOUS vs VACUOUS on rule 3), and rule 4's only firing reading is unsound in both — but for different reasons.** Against at-least it fails at `n=m=2, p=1` (bounds `N` from the wrong side); against at-most only at `p > m`. Start from that asymmetry |
| W1-T6 | Delete or regenerate the orphaned `cata/sum.tex` | TODO | Nothing in `main` produces it |
| W1-T7 | Structural: index modifications as data, not closures | DONE | **DONE 2026-09-18 (W1-S).** First-order `ind_op` (9 constructors) replaces the two closures per `decomp_event`; `apply_op`/`print_op`/`(=)`/`invert_op`. **Zero goldens changed — byte-identical reproduction is the evidence the re-encoding is faithful.** But it does not by itself make the `.tex` unambiguous: 13 rules still bind an index name twice. See the D-0009 amendment for the root cause W1-S measured — was: Prerequisite for printing, comparing and inverting them, and for W0-T1 to validate against anything. **Rule-engine file — does not share a wave with E1/E2**. **Strengthened by W0-A 2026-09-18: it is not only that the closures cannot be compared — the emitted `.tex` is itself lossy.** Repeated index composition prints self-contradictory binder prefixes (`∃i, ∀i, ∀t, ∀i` on one premise), so a shipped rule does not determine what it means; the validator has to check every reading. Until this lands, no validator can cover the catalog rather than three hand-encoded entries |
| W1-T8 | Extend `validator.ml` from 3 entries to all 16 | TODO | **Added 2026-09-18.** The measurement D-0007 wanted and D-0010 still needs: breadth means *validated* breadth, and 13 entries have never been checked. Separate file from the rule engine, so it runs concurrently with W1-T3/T7. Ground semantics is hand-encoded per entry — gccat's **Purpose** field is a cross-check source (`docs/GCCAT.md`) |

## W2 — freeze the input format

Goal: the decomposition format stops changing, so content work can fan out.

| ID | Task | Status | Notes |
|---|---|---|---|
| W2-T1 | Write down the decomposition format and freeze it | TODO | **This is the gate that makes family-per-agent honest.** Before it, every content session is blocked on machinery it also wants to change |
| W2-T2 | E1: open `var_name` for auxiliary integer families | TODO | **D-0006.** Mechanism already exists via `rule1` (`N`, `O`). Rule-engine file |
| W2-T3 | E2: richer side conditions — inequalities against expressions, 2-D constant tables | TODO | **D-0006.** Biggest single unlock. Finishes `regular` (W1-T2). Rule-engine file — **not** concurrent with W2-T2 |
| W2-T4 | Close D-0007 (breadth or depth) with validator output in hand | DONE | **CLOSED EARLY 2026-09-18 by the author, not by this row: D-0010 decides breadth.** W1-T8's measurement is still worth having, but it is no longer what gates the decision |
| W2-T5 | Decomposition spec corpus: one format-independent file per MiniZinc global, stating the decomposition as maths, the literals it needs and its E-code | TODO | **Added 2026-09-18, and it is the honest parallel axis before the freeze.** Writing a decomposition as maths touches no engine code, so it does not collide the way D-0006 warns about — and **it is the input to W2-T1**: you cannot freeze a format without knowing what it must express. Order families by E-code, E0 first. Per D-0003 these are authored here, not imported |

## W3 — fan out by constraint family

Goal: coverage. **Only after W2-T1.** Each session authors decompositions against a frozen
format and a working validator; each decomposition is its own file, so sessions do not collide.

| ID | Task | Status | Notes |
|---|---|---|---|
| W3-T1 | Counting family: `count`, `at_least`, `at_most`, `exactly`, `among`, `nvalue` | TODO | Mostly E0 |
| W3-T2 | Sequencing family: `value_precede`, `seq_precede_chain`, `sliding_among`, `lex*` | TODO | Mostly E0. `value_precede` is a Boolean state chain, same shape as the working `increasing` |
| W3-T3 | Extensional family: `regular`, `table`, `mdd` | TODO | Needs W2-T3. **`regular` is on Choco's LCG-unsupported list and this repo already has a decomposition for it** — smallest complete contribution available |
| W3-T4 | E3: multi-family cardinality | TODO | Removes `failwith "sommes multiples"`. Unblocks `global_cardinality`, `knapsack`, `bin_packing*` |

## W4 — the experiment

| ID | Task | Status | Notes |
|---|---|---|---|
| W4-T1 | **E4: counting / pigeonhole reasoning across cardinality constraints** | TODO | **D-0006.** The research, not the engineering. Strengthen `rule5/6/7` to reason *across* sums rather than within one |
| W4-T2 | Target `alldifferent`: can the method reach the Hall-set explanation? | TODO | Published baseline: Downing, Feydy, Stuckey 2012. **Budget this as an experiment, not as a constraint.** A clean negative is a result. **Sharpened 2026-09-18 (W1-S, verified): `alldifferent.tex`'s single rule is correct, not a dropped one.** `alldiff` is `rule1` + `rule5` alone, and `X_i = t` is not derivable from a Boolean sum's ≤ direction — so the missing rule *is* E4, counting across sums. W4-T2 is therefore "add pigeonhole reasoning", not "fix a silent discard" |
| W4-T3 | Target `cumulative`: can the method reach the window/capacity explanation? | TODO | Published baseline: Schutt et al. 2011. Current entry is the unary-resource special case and names all *n* tasks |
| W4-T4 | Close D-0008 (what "complete" means per entry) | TODO | Needs W4-T2's outcome |

## Explicitly out of scope

Stated here so it is not rediscovered at constraint 200. ~25 of the 118 MiniZinc globals:
graph and reachability (E6), geometry and packing, floats (E7), and set variables unless
channelled to Booleans first (E5). See `CHRISTMAS_LIST.md`.
