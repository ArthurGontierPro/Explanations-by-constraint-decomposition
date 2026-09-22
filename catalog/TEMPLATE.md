<!--
  catalog/TEMPLATE.md — the entry format. Copy this file, keep every heading,
  delete nothing. A field with nothing to say is filled with "none" or with the
  reason it is empty; an absent heading is a defect, because a reader cannot
  tell a missing field from a field that was never checked.

  Every rule below the "----" markers is part of the format. Read them once;
  they are the difference between a catalog and a pile of generated LaTeX.
-->

# `<constraint_name>`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `<constraint_name>`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | `<A/B/C/D/unclassified/out of scope>` — `tools/mzn_coverage.py --rank` |
| **Status** | `<one status-legend value, verbatim>` |
| **Generated** | `<k>` rules in `cata/<file>.tex` |
| **Validator** | `<k SOUND and MINIMAL, k flagged>` / `out of scope: <reason>` |
| **Calibration** | `<agrees / weaker / stronger / incomparable / out of reach / no published rule>` |
| **Last measured** | `<YYYY-MM-DD>`, `<the commands run>` |

<!--
  ---- the header table ----
  Tier            copied from the ranking tool, never guessed. Re-run it; do not
                  read the tier off docs/COVERAGE.md's counts table.
  Status          exactly one of the six strings in README.md's status legend.
                  Never "correct". Never "works".
  Validator       the verdict counts from YOUR OWN `make validate` run, for this
                  entry alone. If the entry is out of scope, say so and give the
                  machine-printed reason, not a paraphrase.
  Calibration     one verdict from the vocabulary below, expanded in the
                  Calibration section. The comparison is on **implication
                  strength**, never on minimality: no paper sourced so far
                  proves an explanation minimal (W3-T5, method corrected
                  2026-09-21). `out of reach` is a first-class verdict, not a
                  failure to compare.
  Last measured   the date and the literal commands. "Read off the source" and
                  "measured" are different claims (CLAUDE.md); this row says which.
-->

## Constraint

`<MiniZinc signature>`

`<one or two sentences: what it means>`

**Provenance of the signature:** `<a file and line in this repo, or an explicit
note that it is not vendored here>`

<!--
  ---- Constraint ----
  The signature is a factual claim like any other. If this repo does not carry
  it (tools/data/minizinc-*-globals.txt lists names only), say so in the
  provenance line rather than presenting recall as a citation.
-->

## Published explanation

**Citation:** `<author, year, title, venue>` — `CHRISTMAS_LIST.md:<line>`

**Rule shape:** <!-- C2: sourced rule shapes go in catalog/_literature/<name>.md -->
see [`catalog/_literature/<name>.md`](_literature/<name>.md).

`<If nothing is sourced yet: "pending C2 — not stated here." If you state
anything about the paper's content that you have not read in this repo, mark the
sentence UNSOURCED.>`

<!--
  ---- Published explanation ----
  **Do not write a published rule shape from memory.** The citation itself comes
  from CHRISTMAS_LIST.md and is quotable with a line number; the *content* of the
  paper is C2's to source into catalog/_literature/. Until that file exists, this
  section says "pending C2" and the Calibration section says "pending C2" too.
  A sentence about a paper with no in-repo source is marked UNSOURCED inline, so
  a later reader can find and either source or delete it.
-->

## Solver support

| | |
|---|---|
| Chuffed | `<native (file.cpp) / decomp>` |
| Geas | `<[G] present / absent>` |
| Choco LCG | `<[C] present / [C✗] failure / absent>` |

Source: `CHRISTMAS_LIST.md:<line>`, solver-column legend at `CHRISTMAS_LIST.md:106-109`.

## Decomposition used here

**Generator value:** `<name>`, `explenation generator.ml:<lines>`
**Emitted by:** `explainall [<events>] <name> "cata/<file>.tex"`, line `<n>`
**Spec:** `decomps/<name>.md` `<or: none — this constraint has no decomps/ spec>`

`<The schema chain in prose: which of the 7 rule schemas, in what order, over
which auxiliaries. Say what the decomposition actually encodes — if it is not
the constraint the file name claims, say so here, first, in plain words.>`

<!--
  ---- Decomposition used here ----
  Line numbers drift. Give them, and give the value name too, so a reader can
  re-find the code when the numbers rot (several decomps/*.md already cite
  pre-W1-S line numbers that no longer resolve).
  If the shipped decomposition is a special case of the named constraint, that
  belongs at the TOP of this section, not in a footnote.
-->

## Scope of this entry

**Events the generator was asked to explain:** `<list>`

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `<literal>` | `<k>` | `<k>` | `<the %% diagnostics line, verbatim-ish>` |

`<For any event with 0 rules: one sentence on why, and the gap or extension that
would change it.>`

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/<file>.tex`.

<!--
  ---- Scope of this entry ----
  This is the section that stops the entry reading as exhaustive. It states the
  finite question the generator was asked — "explain these events of this
  decomposition" — and shows what came back, including the empty answers. An
  entry without it would let a reader infer that k rules is all there is.
  It is also the only place the F/cycle/duplicate drop counts are surfaced.
-->

## Generated rules

Rendered from `cata/<file>.tex` (single line, no trailing newline; count with
`grep -o '\\frac' cata/<file>.tex | wc -l`).

### Rule `<k>` — `<conclusion literal>`

```
<premise>, <premise>
------------------------------- ⊢
<conclusion>
```

**Verdict:** `<VERDICT line, verbatim from make validate>`
**Reading(s) checked:** `<the validator's reading list>`
`<Any counterexample the validator printed, verbatim.>`

<!--
  ---- Generated rules ----
  Render premises above the line and the conclusion below, matching the LaTeX
  \frac. Keep the generator's own index names (i, i', t, t', p) — renaming them
  hides the binder collisions that D-0009 is about.
  The verdict is COPIED from a run, not judged here. If the generator's
  diagnostics flag a rule (e.g. "binds an index name twice", D-0009) and the
  validator still passes it, report BOTH; they are different checks and the
  disagreement is information.
-->

## Status

<!-- The status legend is in `catalog/README.md` (seven values as of 2026-09-21), not here.
     It includes `encodable today, not encoded`, for a constraint the format can already express
     but nothing generates — use it rather than inventing a G-number. -->

**`<status-legend value>`**

`<Two or three sentences. What is and is not established. If the status is
"validated: sound and minimal at n,m ∈ {2,3,4}", add two caveats. The floor
caveat: sound and minimal means no premise is droppable, not that the rule is
strong. And the range caveat: docs/VALIDATOR.md:184 enumerates the literal set
{2,3,4}, so n = 1 is unchecked (W1-T19). Write the range as a set, never as
"n,m <= 4" -- that phrasing was swept out of this catalog on 2026-09-22
because it claimed a size the validator never builds.>`

## Calibration (W3-T5, D-0013)

**Verdict:** `<agrees / weaker than published / stronger than published /
incomparable / out of reach / no published rule exists>`

`<The comparison against the shape sourced in catalog/_literature/<name>.md.
Compare on IMPLICATION STRENGTH — does our premise imply theirs, theirs ours,
or neither — and say at which arities the comparison holds. "Generated rule is
sound but strictly weaker than <author>'s" is a RESULT (D-0013), not a failure.>`

<!--
  ---- Calibration ----
  | verdict | means |
  |---|---|
  | `agrees`            | same rule up to renaming, at the stated arities |
  | `weaker`            | our premise implies theirs; theirs does not imply ours, so their rule fires in strictly more states |
  | `stronger`          | theirs implies ours and not conversely |
  | `incomparable`      | both expressible in a common vocabulary, neither premise implies the other |
  | `out of reach`      | no comparison is statable, because the published premise is not expressible here at all — typically indexed by a run-time object (a Hall set, an SCC, a graph cut). FIRST-CLASS, not a failure |
  | `no published rule` | CHRISTMAS_LIST.md records no explanation for this constraint |

  Do NOT compare on the validator's minimality. Measured 2026-09-21 (C2): none
  of the three papers sourced proves any explanation minimal — Downing et al.
  call theirs "the base explanation", Schutt et al. leave two minimality
  questions open. Minimality is a floor; the papers' own order is implication.
  Say WHICH arities the comparison holds at: `alldifferent` coincides with
  Downing §4 at n = 2 and is strictly weaker for every n >= 3.
  A verdict of `out of reach` still names what is out of reach and why, and
  says whether a numbered gap would change it (cumulative: G11 + G15) or
  nothing on the gap list would (gcc: E4 is necessary but not sufficient).
-->

## Gaps

| gap | what it blocks here |
|---|---|
| `G<n>` | `<one line>` |

Extensions: `<E-codes from CHRISTMAS_LIST.md's route column>`.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated numbering, wave two).

## How this entry was produced

- `<command>` → `<what it gave>`
- `<file:line>` read, not run → `<what was read off it>`

<!--
  ---- How this entry was produced ----
  CLAUDE.md: "If you report a number, say how you got it." Every number in the
  entry traces to a line here. A number with no line here should be deleted.
-->
