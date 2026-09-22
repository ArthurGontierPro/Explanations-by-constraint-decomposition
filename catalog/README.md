# The catalog

One entry per MiniZinc global constraint, gathering three sources side by side:

1. **the published explanation**, if one exists (`CHRISTMAS_LIST.md`'s citation, with the
   rule shape sourced into `catalog/_literature/`);
2. **what solvers implement** — native explaining propagator, or decomposition;
3. **what this method generates** — the rules `explenation generator.ml` derives from a
   decomposition, with each rule's validator verdict.

`catalog/TEMPLATE.md` is the format. Every entry keeps every heading.

---

## What the catalog claims

**It claims complete *coverage*.** Every one of the 118 MiniZinc globals gets an entry with
an honest status — including `nothing generated, blocked on G6` and `encodable today, not
encoded`, both of which are complete entries,
not a hole. 118 of 118 entries with a known status is a checkable target and
`tools/mzn_coverage.py` measures the denominator.

**Today 118 files exist and 12 of them are that.** The other 106 are *stubs* (below): a file
per global, machine-filled, with `not reviewed` where the status would be. `not reviewed` is
not one of the six statuses and is not meant to look like one — it is the absence of a
status. So the coverage claim above is a **target**, and the number that measures progress
towards it is the *reviewed* count, never the file count. `catalog/INDEX.md` prints both and
refuses to print the file count on its own.

**It never claims complete *enumeration*.** An entry lists the rules this method generated
for the events the generator was asked to explain. It does **not** list every valid
explanation of the constraint. That set is exponential for some entries even at fixed arity,
and what "complete for this constraint" should mean is still **D-0008, open**.

So: *an entry listing some rules must not read as if it lists all of them.* Three things in
the format exist to enforce that, and an entry that drops them is wrong even if every rule in
it is right.

- The **banner** at the top of every entry says it in one sentence.
- The **Scope of this entry** section states the finite question that was asked — "explain
  these events of this decomposition" — and shows the empty answers alongside the non-empty
  ones. `alldifferent` was asked for two events and produced one rule; the entry says so.
- **Status** is never `correct`. See the legend below.

Both claims are recorded in `docs/DECISIONS.md`, under the 2026-09-21 note appended to D-0013.

## Never write "correct"

A rule in this catalog is `validated: sound and minimal at n,m <= 4`, or `flagged`, or
`generated, unvalidated`, or `not validatable`. It is never "correct" and never "works".

And **sound and minimal is a floor, not strength.** Minimality means no premise can be
dropped without losing soundness. It does not mean the rule is useful:
`cata/alldifferent.tex`'s one rule is sound and minimal and only ever fires at `n = 2`.

## Status legend

| status | means |
|---|---|
| `validated: sound and minimal at n,m <= 4` | every generated rule in the entry got `SOUND and MINIMAL` from `make validate`, at the sizes `docs/VALIDATOR.md` enumerates |
| `partly validated` | some rules `SOUND and MINIMAL`, some flagged. The per-rule verdicts are in the entry |
| `flagged` | every generated rule is flagged: `UNSOUND`, `AMBIGUOUS`, `VACUOUS`, `UNSOUND(firing)` or `NOT MINIMAL` |
| `not validatable` | rules exist in `cata/` but the validator reports the entry out of scope, with a machine-printed reason (an undefined `D_k`, an unparsed index equation, an argument that appears in no atom) |
| `generated, unvalidated` | rules exist and no verdict has been obtained. Distinct from `not validatable`: nobody has looked |
| `nothing generated — blocked on G<n>` | no decomposition is encodable, or the generator emits no rule. The gap number is required, not optional |
| `encodable today, not encoded` | **added 2026-09-21.** The current format can already express the decomposition, but nothing in the generator does it, so **there is no gap to name**. Use this rather than inventing a G-number to satisfy the row above. First cases, found by R5: `strictly_increasing` / `strictly_decreasing`, a pure parameter shift on the validated `increasing` / `decreasing` pair — `tplus`/`tmoin` already exist and the `Addint` printer case is already exercised |

The verdict vocabulary itself (`SOUND and MINIMAL`, `UNSOUND`, `AMBIGUOUS`, `VACUOUS`,
`UNSOUND(firing)`, `NOT MINIMAL`) is defined in `docs/VALIDATOR.md`, "Quantifier ambiguity".

## Calibration verdicts

A separate axis from the status legend, and a separate question: how the generated rule
compares to the **published** one (D-0013, W3-T5). One of `agrees`, `weaker`, `stronger`,
`incomparable`, `out of reach`, `no published rule`; `catalog/TEMPLATE.md` defines each.

Two rules about it, both learned the hard way in wave three:

- **Compare on implication strength, not on minimality.** Measured: none of the three papers
  sourced so far proves any explanation minimal. Sound-and-minimal is this repo's floor, and
  `alldifferent` — `SOUND and MINIMAL` and strictly weaker than Downing et al. §4 at every
  `n ≥ 3` — is the standing proof that the two axes are different.
- **`out of reach` is a first-class verdict.** When the published premise is indexed by a
  run-time object (a Hall set, an SCC, a flow cut), no implication either way is statable.
  Saying so is a result; scoring it as `weaker` would be a fabrication.

## How an entry is produced

1. **Tier** — `python3 tools/mzn_coverage.py --rank --json out.json`, read the constraint's
   tier out of `result.ranking`. Entries are written documented-first, tier D → C → B → A
   (**D-0013**).
2. **Citation** — `grep -n -i '<name>' CHRISTMAS_LIST.md`. Quote the row with its line number.
   Do **not** web-search, and do **not** write a published rule shape from memory: the shapes
   are sourced separately into `catalog/_literature/<name>.md`, which is not this session's to
   write. Until that file exists the entry says `pending C2`.
3. **Solver support** — the same row's solver column; legend at `CHRISTMAS_LIST.md:106-109`.
4. **Decomposition** — find the value in `explenation generator.ml` (the `(*Decompositions*)`
   block) and the `explainall` call that emits it. Record both the value name and the line
   numbers; the numbers rot, the name does not.
5. **Rules and scope** — read `cata/<name>.tex` and its `%% generator diagnostics` footer.
6. **Verdicts** — `make validate`, and quote *your own run*, dated.
7. **Gaps** — `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## Regenerating the generated parts

The rules themselves are not written by hand. `cata/*.tex` is the artifact; an entry renders it.

```sh
eval $(opam env --switch=baguette --set-switch)   # OCaml 5.1.1; `which ocaml` is empty without this
ocaml 'explenation generator.ml'                  # rewrites cata/*.tex in cwd
make check                                        # golden-file byte-diff + warning census
make validate                                     # verdicts; exits 0 (only a broken validator fails)
```

`make check` proves **reproducibility**, not correctness. `make validate` is the one that
judges rules, and it is deliberately not part of `make check` because it is red on purpose.

If a regeneration changes a rule, the entry's **Generated rules**, **Status**, **Validator**
and **Last measured** rows all change together. Re-run; do not patch one and leave the others.

## Files

```
TEMPLATE.md        the entry format, with each field's rules beside it
README.md          this file
<name>.md          one entry per MiniZinc global
_literature/       sourced published rule shapes (owned by the literature sessions)
```

## Stubs

A **stub** is a `catalog/<name>.md` that `python3 tools/catalog_stub.py` wrote, so that every
release global has a file and the catalog's denominator stops being a promise. It is not a
small entry; it is an entry with no findings in it, and it says so at the top:

```
> **AUTO-STUB — NOT REVIEWED.**
```

That banner is load-bearing three times over. It tells a reader the file is machine output;
`tools/catalog_index.py` greps for it to report e.g. `(12 reviewed, 106 stubs)` instead of a bare
`118 / 118`; and `tools/catalog_stub.py` refuses to write over any `catalog/*.md` that lacks
it, so a stub someone has reviewed and de-marked is safe from the next run.

**What a stub may state**, each field naming its own source: the priority tier from
`tools/mzn_coverage.py --rank`; the literature, solver and E-route cells of the constraint's
`CHRISTMAS_LIST.md` row, quoted verbatim with the line number; the name's line in
`tools/data/minizinc-*-globals.txt`; a link to `decomps/<name>.md` if that spec exists; and
the `cata/<name>.tex` rule count, from the literal `\frac` (never `grep -c` — CLAUDE.md,
"Traps"), or `no generator entry`.

**What a stub must never state:** a status, a blocking gap, a calibration verdict, an
extension it "probably" needs, or anything about a paper's content. All of those are review
work. A stub that guessed one would be indistinguishable, six months later, from a finding —
which is the whole reason the reviewed/stub distinction exists.

**Upgrading a stub** is editing it in place: the headings are already `TEMPLATE.md`'s, in
order, so a field gets replaced rather than the file restructured. Delete the banner when the
entry is genuinely reviewed — that is what moves it from the stub column to the reviewed one,
and what makes the generator leave it alone.

## Coverage so far

**See `catalog/INDEX.md`, which is generated.** This paragraph used to carry hand-typed
figures ("12 reviewed, 106 stubs"); they were stale within a day, which is the second time a
hand-typed count in this file has rotted. Do not quote the first number without the
split; see "Stubs" above for why.

`catalog/INDEX.md` is generated (`python3 tools/catalog_index.py`) and carries the current
split per tier and per constraint, alongside the generated-rule and validated counts. This
section deliberately keeps no second copy of those numbers: the one in the repo that is
recomputed on every run is the one to read.
