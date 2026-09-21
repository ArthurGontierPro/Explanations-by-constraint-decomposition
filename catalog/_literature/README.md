# `catalog/_literature/` — sourced explanation rules from the published work

One file per constraint. Each file records **the shape of the explanation that a published
paper actually gives**, so that a catalog entry in `catalog/` can be *calibrated* against it
(D-0013, W3-T5) instead of compared against a remembered rule.

Owned by session **C2**. `catalog/` proper is C1's; these files are linked from the
"Published explanation" section of each entry.

## What these files are, and are not

**These are summaries of other people's work, cited, not reproduced.** Short formulas are
quoted so the claim is checkable; nothing here replaces reading the paper, and no text here
is a licence to redistribute it. Every file names the exact document the quote came from,
including whether it was the author's preprint or the publisher's version, because the two
can differ in pagination and occasionally in wording.

## The provenance convention

Every claim about a paper carries exactly one tag:

| tag | means |
|---|---|
| `QUOTED` | The document was fetched in this session and the formula/sentence is transcribed from it. The pointer (section, figure, page) resolves in the fetched document. |
| `DERIVED` | Obtained by applying a substitution the paper states in prose to a formula the paper displays, and checked against the paper's own worked example. Not a memory reconstruction — the file shows the substitution and the check. |
| `SECONDARY` | Supported only by an abstract, a summary, or another author's description. The secondary source is named. |
| `NOT SOURCED` | Could not be obtained. The file says what was tried. |

There is no fifth tag. **A rule with no tag is a defect**, and so is a tag on a sentence
whose source is "the standard X explanation" — that is not a provenance.

`COMPARISON` marks a sentence that is *this session's reading* of how the published rule
relates to this repo's generated one. It is an opinion of C2's, not a claim about the paper,
and a catalog entry that repeats it should say so.

## Pagination caveat

Two of the three papers were read as author preprints with **no printed page numbers**
(`alldifferent`, `gcc`). For those, page pointers are *preprint PDF page indices*, stated as
such. The published pagination (CRPIT 122 / LNCS 7298:146-162 / Constraints 16(3):250-282)
is carried in the citation but was **not** cross-checked against the preprint layout.

## Files

- [`alldifferent.md`](alldifferent.md) — Downing, Feydy, Stuckey, ACSC 2012
- [`cumulative.md`](cumulative.md) — Schutt, Feydy, Stuckey, Wallace, Constraints 2011
- [`gcc.md`](gcc.md) — Downing, Feydy, Stuckey, CPAIOR 2012
