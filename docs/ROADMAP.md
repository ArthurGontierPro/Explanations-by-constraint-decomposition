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
| W0-T1 | **The validator, written before any fix.** For `n,m ≤ 4` enumerate all stores; check premises ⊨ conclusion, and that no premise is droppable | TODO | **D-0005.** Acceptance test: it must independently flag `cata/table.tex`'s empty-premise rule and the `atleastnvalues ≡ atmostnvalues` collision. If it does not, the validator is wrong, not the catalog |
| W0-T2 | Stand up a build + `make check` around the **existing OCaml** | TODO | **Corrected 2026-09-18: OCaml 5.1.1 is installed** (opam switch `baguette`) and `ocaml 'explenation generator.ml'` regenerates all 15 entries byte-identically. An earlier draft said OCaml was unavailable, on the evidence of `which ocaml` in a non-interactive shell, and proposed a Julia rewrite on that basis. **There is no longer a reason to rewrite.** The gate is the deliverable, not the language |
| W0-T3 | Golden files: regenerate every `cata/*.tex` and byte-diff against committed output | TODO | **Mostly already true** — verified 2026-09-18 that the generator reproduces all 15 files byte-for-byte, and `exp.tex` too. So this row is: wire `ocaml gen.ml && diff -r` into `make check`, and delete or regenerate the orphaned `sum.tex` (W1-T6), which is the only diff. Note the files have no trailing newline — count rules with `grep -c '\\frac'` |
| W0-T4 | Automate the `CHRISTMAS_LIST.md` coverage classification so it reruns per MiniZinc release | TODO | **Genuinely disjoint from W0-T1/T2** — touches no generator code. This is the honest parallel task for wave zero. A prototype classifier was written on 2026-09-18 and is not committed |

## W1 — the generator tells the truth

Goal: every existing entry is either validated or reported as failing. No new constraints yet.

| ID | Task | Status | Notes |
|---|---|---|---|
| W1-T1 | Fix index-binder hygiene | TODO | `nvalues.tex` repeats `∀i` twice. Scoping is not hygienic |
| W1-T2 | Define index sets above `D_3` in the printer, or refuse to emit an undefined one | TODO | `regular`, `roots`, `range`, `table` reference `D_4`–`D_9` that appear nowhere. **Refusing is better than printing** — see W1-T3 |
| W1-T3 | Make failure loud: stop `removeimp` silently discarding `F`/`IM`/`FE`/`R` | TODO | Today "no explanation exists" and "the generator failed" are indistinguishable, which is why `alldifferent.tex` has one rule instead of two. **Do this early** — every later task is debugged through it |
| W1-T4 | Remove the unsound `cata/table.tex` rule, or fix the decomposition that produces it | TODO | Empty premise concluding `X_i = t`. Currently shipped |
| W1-T5 | Diagnose `atleastnvalues.tex` ≡ `atmostnvalues.tex` | TODO | Different decompositions (`rule6` vs `rule5`, reified sign flipped) produce byte-identical output. One of them is wrong |
| W1-T6 | Delete or regenerate the orphaned `cata/sum.tex` | TODO | Nothing in `main` produces it |
| W1-T7 | Structural: index modifications as data, not closures | TODO | Prerequisite for printing, comparing and inverting them, and for W0-T1 to validate against anything. **Rule-engine file — does not share a wave with E1/E2** |

## W2 — freeze the input format

Goal: the decomposition format stops changing, so content work can fan out.

| ID | Task | Status | Notes |
|---|---|---|---|
| W2-T1 | Write down the decomposition format and freeze it | TODO | **This is the gate that makes family-per-agent honest.** Before it, every content session is blocked on machinery it also wants to change |
| W2-T2 | E1: open `var_name` for auxiliary integer families | TODO | **D-0006.** Mechanism already exists via `rule1` (`N`, `O`). Rule-engine file |
| W2-T3 | E2: richer side conditions — inequalities against expressions, 2-D constant tables | TODO | **D-0006.** Biggest single unlock. Finishes `regular` (W1-T2). Rule-engine file — **not** concurrent with W2-T2 |
| W2-T4 | Close D-0007 (breadth or depth) with validator output in hand | TODO | Evidence to bring: what fraction of W1's entries survive validation, and how far `cumulative`/`alldifferent` sit from their published baselines |

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
| W4-T2 | Target `alldifferent`: can the method reach the Hall-set explanation? | TODO | Published baseline: Downing, Feydy, Stuckey 2012. **Budget this as an experiment, not as a constraint.** A clean negative is a result |
| W4-T3 | Target `cumulative`: can the method reach the window/capacity explanation? | TODO | Published baseline: Schutt et al. 2011. Current entry is the unary-resource special case and names all *n* tasks |
| W4-T4 | Close D-0008 (what "complete" means per entry) | TODO | Needs W4-T2's outcome |

## Explicitly out of scope

Stated here so it is not rediscovered at constraint 200. ~25 of the 118 MiniZinc globals:
graph and reachability (E6), geometry and packing, floats (E7), and set variables unless
channelled to Booleans first (E5). See `CHRISTMAS_LIST.md`.
