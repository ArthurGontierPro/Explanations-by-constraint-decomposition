#!/usr/bin/env python3
"""catalog_tex.py -- compile the catalog into one readable LaTeX document.

Produces `catalog/catalog.tex`: the whole catalog, end to end. It carries
rules of two kinds and never lets them be confused. A GENERATED rule is this
project's output, copied verbatim from `cata/*.tex` as the
`\\frac{premises}{conclusion}` the generator already emits. A PUBLISHED rule is
someone else's result, read from `catalog/_literature/*.md` and printed inside
a bar that says so on every page it spans. Where an entry has both, the
calibration relating them follows the pair; and the document leads with the
entries that have rules, with the status material behind them.

**Nothing in the output is hand-typed.** Every count, tier, status, verdict and
rule is read at generation time from the repo:

  - `tools/mzn_coverage.py --json`  -- the 118 release globals and their
    priority tier. Reached through `tools/catalog_index.py`'s `load_ranking`,
    so this script and the index agree by construction rather than by
    coincidence, and the basename <-> release-global mapping is that script's
    `ALIAS` table, not a second copy of it. Where a catalog entry and its
    artifact do not share a basename, `CATA_ALIAS` below maps the one to the
    other; that is a different question from `ALIAS`'s and is asked here.
  - `catalog/*.md`                  -- the uniform six-row header table at the
    top of every entry (Tier / Status / Generated / Validator / Calibration /
    Last measured). An entry whose table does not parse is REPORTED, never
    silently dropped: it lands in the document's "Entries that did not parse"
    section and on stderr.
  - `cata/*.tex`                    -- the rules, copied VERBATIM. This script
    never re-renders a rule. It splits the single content line from the
    trailing `%%` diagnostics block and presents the latter as a small italic
    note, because that block carries the dropped-branch counts and the D-0009
    ambiguity flags and they are part of the finding.
  - `catalog/_literature/*.md`      -- the PUBLISHED explanations: other
    people's results, sourced under citation, every claim carrying one of the
    four provenance tags `catalog/_literature/README.md` defines. Printed
    inside a bar that says whose they are, with the tags carried across
    unchanged and never upgraded, and typeset as a `\\frac` only where the
    source file says its translation into this notation is faithful. Where it
    says the translation is not faithful -- the premises are indexed by a Hall
    interval, an SCC, a flow cut, a compulsory-part set, none of them an index
    set this notation can name -- the paper's own form is printed instead.
  - `make validate`                 -- per-rule verdicts, parsed from its own
    output. Never piped into a reader's context: `--validate-log FILE` reuses a
    saved run.
  - `catalog/README.md`             -- the coverage/enumeration paragraphs, the
    status legend and the calibration vocabulary, lifted verbatim so the
    document cannot drift from the file that defines them.

Where a number this script computes disagrees with a number written in an
entry, the disagreement is printed to stderr AND to a section of the document.
It is never resolved in favour of either side.

Usage:
    python3 tools/catalog_tex.py                    # writes catalog/catalog.tex
    python3 tools/catalog_tex.py --dry-run          # print, don't write
    python3 tools/catalog_tex.py --validate-log F   # reuse a saved
                                                    # `make validate` log
    python3 tools/catalog_tex.py --out FILE         # write somewhere else

Then:
    /usr/local/texlive/2025/bin/x86_64-linux/pdflatex -halt-on-error \\
        -output-directory _build catalog/catalog.tex   # twice, for the ToC

No network access. Python 3 standard library only.
"""

from __future__ import annotations

import argparse
import datetime
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import catalog_index as ci  # noqa: E402  -- the ALIAS map and the tier loader

REPO = ci.REPO
CATALOG_DIR = ci.CATALOG_DIR
CATA_DIR = ci.CATA_DIR
OUT_PATH = os.path.join(CATALOG_DIR, "catalog.tex")
README_PATH = os.path.join(CATALOG_DIR, "README.md")

# The six header-table rows catalog/TEMPLATE.md mandates. A row missing from an
# entry is a parse failure for that row, reported per row rather than per file,
# so one absent field does not hide the five that are there.
HEADER_FIELDS = ["Tier", "Status", "Generated", "Validator", "Calibration",
                 "Last measured"]
HEADER_ROW_RE = re.compile(
    r"^\|\s*\*\*(%s)\*\*\s*\|\s*(.*?)\s*\|\s*$" % "|".join(
        re.escape(f) for f in HEADER_FIELDS),
    re.M)

# `nothing generated - blocked on G7`, `... on E6`, `... on E2 (int/bool ...)`.
# The FIRST code in the Status cell is the primary blocker; entries that name
# more than one say so in prose and that prose is reproduced in full, so the
# grouping key being the first code loses nothing.
BLOCK_RE = re.compile(r"blocked on\s+\**\s*(G\d+|E\d+)")
ENCODABLE = "encodable today, not encoded"

# catalog/<entry>.md  ->  cata/<artifact>.tex, where the two do NOT share a
# basename. `tools/catalog_index.py`'s ALIAS maps a cata basename to a RELEASE
# GLOBAL; this maps a CATALOG ENTRY basename to a cata basename, which is a
# different question and the one this script asks when it looks for an entry's
# rules. Without a row here the entry is reported as having no artifact at all,
# which is a false negative, not a missing feature.
#
# `all_different_except` is the release global's spelling and the entry is named
# for it; `explenation generator.ml:1071` writes the artifact as
# `cata/alldifferent_except.tex`, following the `alldifferent` file it is a
# one-line variation of. Both spellings are deliberate in their own file, so the
# mapping lives here rather than either being renamed. Added 2026-09-22 (U2),
# from U1's cross-session request in `WORKLOG.md`.
CATA_ALIAS = {
    "all_different_except": "alldifferent_except",
}

RULE_RE = re.compile(r"\$\$(.*?)\$\$", re.S)
DIAG_LINE_RE = re.compile(r"^%%\s?(.*)$", re.M)

# `make validate` per-rule lines.
V_ENTRY_RE = re.compile(r"^---- cata/(\S+)\.tex\s+\((\d+) rules?\) ----\s*$")
V_RULE_RE = re.compile(r"^\s{2}rule\s+(\d+)/(\d+)\s+(.*?)\s*$")
V_VERDICT_RE = re.compile(r"^\s+VERDICT\s*:\s*(.*?)\s*$")
V_CONT_RE = re.compile(r"^\s{12,}(\S.*?)\s*$")
V_COUNTER_RE = re.compile(r"^\s+counterexample:\s*(.*?)\s*$")

# Numbers written in an entry, for the cross-check against what we compute.
WRITTEN_GENERATED_RE = re.compile(r"\*{0,2}(\d+)\*{0,2}\s+rules?\b")
WRITTEN_SOUNDMIN_RE = re.compile(r"(\d+)\s+`?SOUND and MINIMAL`?")

# --------------------------------------------------------------------------
# Markdown-in-a-table-cell -> LaTeX.
#
# The header cells are prose with inline code, bold, italics and links. They
# are reproduced in full -- truncating a status cell would be exactly the kind
# of quiet edit this catalog exists to avoid -- so they need a converter.
# Anything it cannot map is reported, not dropped silently.
# --------------------------------------------------------------------------

UNICODE_TEX = {
    "\u2014": "---", "\u2013": "--", "\u2018": "`", "\u2019": "'",
    "\u201c": "``", "\u201d": "''", "\u2026": "\\ldots{}",
    "\u00a0": "~", "\u00a7": "\\S{}", "\u00b7": "$\\cdot$",
    "\u00d7": "$\\times$", "\u2264": "$\\leq$", "\u2265": "$\\geq$",
    "\u2260": "$\\neq$", "\u2208": "$\\in$", "\u2209": "$\\notin$",
    "\u2192": "$\\rightarrow$", "\u21d2": "$\\Rightarrow$",
    "\u21d4": "$\\Leftrightarrow$", "\u2194": "$\\leftrightarrow$",
    "\u2200": "$\\forall$", "\u2203": "$\\exists$", "\u22a2": "$\\vdash$",
    "\u2227": "$\\wedge$", "\u2228": "$\\vee$", "\u00ac": "$\\neg$",
    "\u2211": "$\\Sigma$", "\u2208\u0338": "$\\notin$",
    "\u03b1": "$\\alpha$", "\u03b2": "$\\beta$", "\u2205": "$\\emptyset$",
    "\u2286": "$\\subseteq$", "\u2229": "$\\cap$", "\u222a": "$\\cup$",
    "\u2248": "$\\approx$", "\u2261": "$\\equiv$", "\u00b1": "$\\pm$",
    "\u2032": "$'$", "\u2020": "\\dag{}", "\u00e9": "\\'e",
    "\u00e8": "\\`e", "\u00fc": '\\"u', "\u00f6": '\\"o', "\u00e4": '\\"a',
    # Added with the published rules: these occur in the quoted formulas and
    # in the prose of catalog/_literature/*.md, never in a catalog entry.
    "\u00ef": '\\"{\\i}', "\u03a3": "$\\Sigma$", "\u03a9": "$\\Omega$",
    "\u2212": "$-$", "\u2282": "$\\subset$", "\u22c0": "$\\bigwedge$",
    "\u22c1": "$\\bigvee$", "\u2713": "$\\checkmark$",
    "\u27e6": "$\\llbracket$", "\u27e7": "$\\rrbracket$",
    "\u2264\u0338": "$\\nleq$",
}

ESCAPE = {"\\": "\\textbackslash{}", "{": "\\{", "}": "\\}", "$": "\\$",
          "&": "\\&", "#": "\\#", "_": "\\_", "%": "\\%",
          "~": "\\textasciitilde{}", "^": "\\textasciicircum{}"}

_unmapped = set()


def tex_escape(s):
    out = []
    for ch in s:
        if ch in ESCAPE:
            out.append(ESCAPE[ch])
        elif ord(ch) < 127:
            out.append(ch)
        elif ch in UNICODE_TEX:
            out.append(UNICODE_TEX[ch])
        else:
            _unmapped.add(ch)
            out.append("[U+%04X]" % ord(ch))
    return "".join(out)


def md_to_tex(s):
    """One markdown table cell -> LaTeX, preserving every word of it.

    Single pass, no recursion: code spans become placeholders, emphasis
    becomes control bytes that survive escaping, then the whole string is
    escaped once and the markers are expanded. Recursing into the inner text
    of a bold run would re-escape a placeholder and lose it.
    """
    if s is None:
        return ""
    stash = []

    def keep(tex):
        stash.append(tex)
        return "\x00%d\x00" % (len(stash) - 1)

    # 1. code spans, before anything can chew on their contents. A code span
    #    that is exactly a provenance tag becomes a badge instead, so the tag
    #    travels with the claim wherever the claim is printed.
    def _code(m):
        inner = m.group(1)
        if inner in PROV_COLOR:
            return keep("\\provtag{%s}{%s}"
                        % (PROV_COLOR[inner], tex_escape(inner)))
        t = tex_escape(inner)
        if len(inner) > 24:
            # a long path or URL in a code span, given somewhere to break
            t = re.sub(r"(\\_|[/.-])", r"\1\\allowbreak{}", t)
        return keep("\\texttt{%s}" % t)

    s = re.sub(r"`([^`]*)`", _code, s)
    # 1b. a bare <https://...>: \url breaks it, \texttt does not
    s = re.sub(r"<((?:https?|ftp)://[^>\s]+)>",
               lambda m: keep("\\url{%s}" % m.group(1)), s)
    # 2. links: keep the text, drop the target (every target is a repo-local
    #    file already named elsewhere in the entry)
    s = re.sub(r"\[([^\]]*)\]\(([^)]*)\)", lambda m: m.group(1), s)
    # 3. paired straight quotes -> TeX quotes
    s = re.sub(r'"([^"]*)"', "``\\1''", s)
    # 4. bold then italic, as balanced control bytes
    s = re.sub(r"\*\*(.+?)\*\*", "\x01\\1\x02", s, flags=re.S)
    s = re.sub(r"(?<![\*\w])\*([^*]+?)\*(?!\*)", "\x03\\1\x04", s, flags=re.S)
    s = tex_escape(s)
    s = (s.replace("\x01", "\\textbf{").replace("\x02", "}")
          .replace("\x03", "\\emph{").replace("\x04", "}"))
    return re.sub(r"\x00(\d+)\x00", lambda m: stash[int(m.group(1))], s)


def md_strip(s):
    """Markdown cell -> plain text, for the places that must fit a column."""
    if s is None:
        return ""
    s = re.sub(r"`([^`]*)`", r"\1", s)
    s = re.sub(r"\[([^\]]*)\]\(([^)]*)\)", r"\1", s)
    s = s.replace("**", "").replace("*", "")
    return " ".join(s.split())


def tt(s):
    """Plain string -> \\texttt{}, with breakable underscores."""
    return "\\texttt{%s}" % tex_escape(s).replace("\\_", "\\_\\allowbreak{}")


# --------------------------------------------------------------------------
# catalog/_literature/ -- the PUBLISHED explanations.
#
# These are other people's results, summarised under citation by session C2,
# every claim carrying one of the four provenance tags that
# `catalog/_literature/README.md` defines. This script reads those files at
# generation time exactly as it reads `cata/*.tex`: it copies, tags and lays
# out; it never restates a paper, never re-sources one, and never promotes a
# `DERIVED` or `SECONDARY` claim to `QUOTED`.
#
# The one judgement it makes is a LAYOUT judgement, and it is made from the
# source file's own words: a published rule is typeset as a
# `\frac{premises}{conclusion}` only where the file says its translation into
# this repo's notation is *faithful*. Where the file says the translation is
# not faithful -- because the premises are indexed by a Hall set, an SCC of a
# residual graph, a flow cut or a compulsory-part set, none of which is an
# index set this notation can name -- the paper's own form is printed instead
# and the file's reasons are printed under it.
# --------------------------------------------------------------------------

LIT_DIR = os.path.join(CATALOG_DIR, "_literature")
LIT_README = os.path.join(LIT_DIR, "README.md")

# The four provenance tags, plus C2's `COMPARISON` marker, which is not a
# provenance tag at all: `catalog/_literature/README.md` says it marks "this
# session's reading", and a document repeating one must say so.
PROV_COLOR = {
    "QUOTED": "tagquoted",
    "DERIVED": "tagderived",
    "SECONDARY": "tagsecondary",
    "NOT SOURCED": "tagnotsourced",
    "COMPARISON": "tagcomparison",
}

# Sections of a literature file that belong next to the PAIR rather than
# inside the published block: they compare the two kinds of rule.
LIT_CALIBRATION_SECTIONS = ("Comparison with this repo's generated entry",
                            "Bearing on this repo")
LIT_METHOD_SECTION = "How this file was produced"
LIT_NOTSOURCED_SECTION = "What was not sourced"

# Unicode -> math mode, for the rule bodies only. Text-mode strings go through
# tex_escape/UNICODE_TEX instead.
MATH_UNI = {
    "≠": "\\neq ", "≥": "\\geq ", "≤": "\\leq ",
    "∈": "\\in ", "∉": "\\notin ", "⟦": "\\llbracket ",
    "⟧": "\\rrbracket ", "∀": "\\forall ", "∃": "\\exists ",
    "∧": "\\wedge ", "∨": "\\vee ", "⋀": "\\bigwedge ",
    "⋁": "\\bigvee ", "→": "\\rightarrow ",
    "↔": "\\leftrightarrow ", "⇒": "\\Rightarrow ",
    "⇔": "\\Leftrightarrow ", "−": "-", "·": "\\cdot ",
    "∑": "\\sum ", "∏": "\\prod ", "⊢": "\\vdash ",
    "∪": "\\cup ", "∩": "\\cap ", "⊆": "\\subseteq ",
    "⊂": "\\subset ", "′": "'", "…": "\\ldots ",
    "≡": "\\equiv ", "¬": "\\neg ", "\\": "\\setminus ",
    "×": "\\times ", "≈": "\\approx ", "∅": "\\emptyset ",
    "Ω": "\\Omega ", "ω": "\\omega ", "α": "\\alpha ",
    "β": "\\beta ", "—": "---", "–": "--",
    "‘": "`", "’": "'", "“": "``", "”": "''",
    " ": "~",
}

SEP_RE = re.compile(r"^\s*(-{4,})\s*(.*)$")
FENCE_RE = re.compile(r"^\s*```+\s*([A-Za-z0-9_+-]*)\s*$")
CLOSE_RE = re.compile(r"^\s*```+\s*$")
HEAD_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*$")
BULLET_RE = re.compile(r"^(\s*)[-*]\s+(.*)$")
# One or two digits only: a paragraph beginning "2012. CRPIT Vol. 122..." is a
# citation, not an ordered list, and it cost one to find that out.
NUMBER_RE = re.compile(r"^(\s*)\d{1,2}\.\s+(.*)$")
HRULE_RE = re.compile(r"^\s*(?:-{3,}|\*{3,}|_{3,})\s*$")


def to_math(s):
    """A rule body -> math mode. `X_i`, `t+1-d_j` and `E\\V` all mean what they
    look like; only the non-ASCII operators need a macro."""
    # A run of two or more spaces is layout in the source file -- a gap
    # between premises -- and becomes a thin space. Collapsing it BEFORE the
    # operators are mapped keeps a mapped operator's own trailing space out of
    # the count.
    s = re.sub(r"\s{2,}", "\x00", s)
    out = []
    for ch in s:
        if ch == "\x00":
            out.append("\\; ")
        elif ch in MATH_UNI:
            out.append(MATH_UNI[ch])
        elif ch in ("%", "#", "&"):
            out.append("\\" + ch)
        elif ch == "$":
            out.append("\\$")
        elif ord(ch) < 127:
            out.append(ch)
        else:
            _unmapped.add(ch)
            out.append("\\text{[U+%04X]}" % ord(ch))
    return "".join(out)


def ascii_rule_to_frac(lines):
    """The ASCII rule layout the literature files use ->
    `\\frac{premises}{conclusion}` with the side condition beside it.

    Returns None when the block is not rule-shaped, so the caller falls back
    to printing it as the source file wrote it.
    """
    sep = None
    side = ""
    for k, ln in enumerate(lines):
        m = SEP_RE.match(ln)
        if m:
            sep, side = k, m.group(2)
            break
    if sep is None:
        return None
    prem = [l.strip() for l in lines[:sep] if l.strip()]
    conc = [l.strip() for l in lines[sep + 1:] if l.strip()]
    if not prem or not conc:
        return None
    side = side.strip()
    if side.startswith("⊢"):
        side = side[1:].strip()
    body = "\\frac{%s}{%s}" % (
        ",\; ".join(to_math(p.rstrip(",")) for p in prem),
        ",\; ".join(to_math(c.rstrip(",")) for c in conc))
    if side:
        body += "\\qquad %s" % to_math(side)
    return body


def md_blocks(text):
    """A markdown body -> a list of typed blocks.

    Deliberately small: these files use fenced code, block quotes, pipe
    tables, `-` lists, `###` sub-headings and paragraphs, and nothing else.
    An unrecognised line becomes paragraph text rather than disappearing.
    """
    lines = text.split("\n")
    out = []
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if HRULE_RE.match(line):
            out.append(("hrule",))
            i += 1
            continue
        m = FENCE_RE.match(line)
        if m:
            lang, buf, j = m.group(1), [], i + 1
            while j < n and not CLOSE_RE.match(lines[j]):
                buf.append(lines[j])
                j += 1
            out.append(("code", lang, buf))
            i = j + 1
            continue
        m = HEAD_RE.match(line)
        if m:
            out.append(("head", len(m.group(1)), m.group(2)))
            i += 1
            continue
        if line.lstrip().startswith(">"):
            buf = []
            while i < n and lines[i].lstrip().startswith(">"):
                buf.append(re.sub(r"^\s*>\s?", "", lines[i]))
                i += 1
            out.append(("quote", " ".join(x.strip() for x in buf if x.strip())))
            continue
        if line.lstrip().startswith("|"):
            rows = []
            while i < n and lines[i].lstrip().startswith("|"):
                raw = lines[i].strip().strip("|")
                if not re.match(r"^[\s:|-]+$", raw):
                    rows.append([c.strip() for c in raw.split("|")])
                i += 1
            if rows:
                out.append(("table", rows))
            continue
        if BULLET_RE.match(line) or NUMBER_RE.match(line):
            ordered = bool(NUMBER_RE.match(line))
            items = []
            while i < n and lines[i].strip():
                m = BULLET_RE.match(lines[i]) or NUMBER_RE.match(lines[i])
                if m:
                    items.append(m.group(2))
                elif items:
                    items[-1] += " " + lines[i].strip()
                else:
                    break
                i += 1
            out.append(("list", ordered, items))
            continue
        buf = []
        while i < n and lines[i].strip() \
                and not FENCE_RE.match(lines[i]) \
                and not HEAD_RE.match(lines[i]) \
                and not lines[i].lstrip().startswith(">") \
                and not lines[i].lstrip().startswith("|") \
                and not BULLET_RE.match(lines[i]) \
                and not HRULE_RE.match(lines[i]):
            buf.append(lines[i].strip())
            i += 1
        if buf:
            out.append(("para", " ".join(buf)))
        else:
            i += 1
    return out


NEG_TRANSLATION_RE = re.compile(
    r"not faithful|does \*\*not\*\* translate|does not translate|"
    r"never as a schema|schema does not|not as a schema")


def block_kind(prev_par, section_title):
    """What a fenced block in a literature file IS, decided from the sentence
    the file puts in front of it. Never from this script's opinion of the
    rule.

    - `frac`      the file calls the translation faithful -> typeset as a rule
    - `attempt`   the file translates and then marks the translation unfaithful
    - `generated` the file is quoting THIS project's generated rule back
    - `paper`     the paper's own form, printed as the paper writes it
    """
    p = prev_par or ""
    if re.search(r"cata/[A-Za-z0-9_]+\.tex", p):
        return "generated"
    translating = ("This repo's notation" in p
                   or "Translation to this repo's notation" in (section_title or "")
                   or re.search(r"\btranslate[sd]?\b", p))
    if translating:
        if re.search(r"\bFaithful\b", p) and not NEG_TRANSLATION_RE.search(p):
            return "frac"
        return "attempt"
    return "paper"


BLOCK_LABEL = {
    "frac": "Published rule, translated into this repo's notation. The source "
            "file marks this translation faithful.",
    "attempt": "Published rule, in the source file's attempted translation --- "
               "which that file marks \\emph{not faithful}. Printed in the "
               "file's own layout, not as a rule of this catalog; the reasons "
               "follow.",
    "paper": "Published rule, in the paper's own form. Not translated: see the "
             "surrounding text for why a translation would misrepresent it.",
    "generated": "The \\emph{generated} rule, quoted back by the source file. "
                 "Its verbatim copy is under ``Generated rules'' above.",
    "listing": "Quoted from the paper: the paper's own listing, not a rule.",
}


def lit_code_display(buf):
    """A fenced block printed as the source file wrote it: monospace, one line
    per line, shrunk to the measure rather than rewrapped, so no token of a
    quoted formula is lost or moved."""
    out = ["{\\raggedright"]
    for ln in buf:
        if not ln.strip():
            out.append("\\smallskip")
            continue
        lead = len(ln) - len(ln.lstrip(" "))
        txt = tex_escape(ln.strip())
        txt = re.sub(r"\s{2,}", lambda m: "~" * len(m.group(0)), txt)
        out.append("\\litline{\\ttfamily\\small %s%s}" % ("~" * lead, txt))
    out.append("\\par}")
    return out


def render_md(text, section_title=None, small=False):
    """A markdown body -> LaTeX, block by block. Nothing is summarised or
    dropped; a block this renderer does not recognise comes out as its own
    text."""
    L = []
    prev_par = ""
    for blk in md_blocks(text):
        if blk[0] == "hrule":
            L.append("\\par\\smallskip")
        elif blk[0] == "para":
            L.append(md_to_tex(blk[1]))
            L.append("")
            prev_par = blk[1]
        elif blk[0] == "quote":
            L.append("\\begin{quotation}\\small\\itshape")
            L.append(md_to_tex(blk[1]))
            L.append("\\end{quotation}")
        elif blk[0] == "head":
            L.append("\\litsubsub{%s}" % md_to_tex(blk[2]))
            prev_par = blk[2]
        elif blk[0] == "list":
            env = "enumerate" if blk[1] else "itemize"
            L.append("\\begin{%s}\\setlength{\\itemsep}{0pt}" % env)
            for it in blk[2]:
                L.append("\\item %s" % md_to_tex(it))
            L.append("\\end{%s}" % env)
        elif blk[0] == "table":
            L.extend(lit_table(blk[1]))
        elif blk[0] == "code":
            lang, buf = blk[1], blk[2]
            kind = "listing" if lang else block_kind(prev_par, section_title)
            frac = ascii_rule_to_frac(buf) if kind == "frac" else None
            L.append("%s{%s}"
                     % ("\\genrulehead" if kind == "generated"
                        else "\\rulekind", BLOCK_LABEL[kind]))
            if frac:
                L.append("\\pubrulebox{%s}" % frac)
            else:
                L.extend(lit_code_display(buf))
            prev_par = ""
    return L


def lit_table(rows):
    """A pipe table -> a plain tabular. Not a longtable: these sit inside the
    framed published block, which cannot break one."""
    ncols = max(len(r) for r in rows)
    width = 0.86 / ncols
    spec = "".join(">{\\raggedright\\arraybackslash}p{%.3f\\linewidth}" % width
                   for _ in range(ncols))
    L = ["{\\small\\setlength{\\tabcolsep}{3pt}",
         "\\begin{tabular}{@{}%s@{}}" % spec, "\\hline"]
    for k, row in enumerate(rows):
        cells = [md_to_tex(c) for c in row] + [""] * (ncols - len(row))
        if k == 0:
            cells = ["\\textbf{%s}" % c if c else "" for c in cells]
        L.append(" & ".join(cells) + " \\\\")
        if k == 0:
            L.append("\\hline")
    L += ["\\hline", "\\end{tabular}\\par}"]
    return L


def top_sections(text):
    """A markdown file -> (preamble, [(title, body)]) split on `## ` only."""
    chunks = re.split(r"^##[ \t]+(.*?)[ \t]*$", text, flags=re.M)
    pre = chunks[0]
    secs = [(chunks[i], chunks[i + 1]) for i in range(1, len(chunks) - 1, 2)]
    return pre, secs


def parse_literature(base):
    """catalog/_literature/<base>.md -> its sections, or None."""
    path = os.path.join(LIT_DIR, base + ".md")
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    pre, secs = top_sections(text)
    m = re.match(r"^#\s+(.*?)\s*$", pre.strip().split("\n")[0])
    by = dict(secs)
    tags = sorted({t for t in PROV_COLOR if re.search(r"`%s`" % t, text)})
    return {
        "path": os.path.relpath(path, REPO),
        "title": m.group(1) if m else base,
        "sections": [(t, b) for t, b in secs
                     if t not in LIT_CALIBRATION_SECTIONS
                     and t != LIT_METHOD_SECTION],
        "calibration": [(t, b) for t, b in secs
                        if t in LIT_CALIBRATION_SECTIONS],
        "method": by.get(LIT_METHOD_SECTION),
        "tags": tags,
        "n_rules": len(re.findall(r"^##+\s+(?:Rule\s+\d+|[A-Z]\d+\.)", text,
                                  re.M)),
    }


def lit_readme_provenance():
    """The provenance convention, lifted from the file that defines it."""
    if not os.path.exists(LIT_README):
        return None
    with open(LIT_README, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    _, secs = top_sections(text)
    by = dict(secs)
    body = by.get("The provenance convention", "")
    return body or None


def entry_section(path, prefix):
    """The body of the `## <prefix>...` section of a catalog entry."""
    with open(path, encoding="utf-8", errors="replace") as fh:
        _, secs = top_sections(fh.read())
    for title, body in secs:
        if title.startswith(prefix):
            return title, body
    return None, None


# --------------------------------------------------------------------------
# Sources
# --------------------------------------------------------------------------

def parse_entry(path):
    """catalog/<name>.md -> {field: raw cell}, plus a list of missing fields."""
    with open(path, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    fields = {}
    for m in HEADER_ROW_RE.finditer(text):
        fields.setdefault(m.group(1), m.group(2))
    missing = [f for f in HEADER_FIELDS if f not in fields]
    return fields, missing


def read_cata(path):
    """cata/<name>.tex -> (list of rule bodies, list of diagnostics lines).

    The file is a SINGLE content line with no trailing newline followed by a
    `%%` diagnostics block (CLAUDE.md, "Traps"). Rule bodies are returned
    exactly as written -- this script does not re-render them.
    """
    with open(path, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    diag = [m.group(1).rstrip() for m in DIAG_LINE_RE.finditer(text)]
    body = DIAG_LINE_RE.sub("", text)
    rules = [m.group(1).strip() for m in RULE_RE.finditer(body)]
    frac = len(ci.FRAC_RE.findall(body))
    return rules, diag, frac


def parse_validate_rules(text):
    """cata basename -> [{n, label, verdict, counterexample}]."""
    out = {}
    lines = text.splitlines()
    i, n = 0, len(lines)
    base = None
    while i < n:
        m = V_ENTRY_RE.match(lines[i])
        if m:
            base = m.group(1)
            out.setdefault(base, [])
            i += 1
            continue
        if lines[i].startswith("=="):
            base = None
            i += 1
            continue
        if base is not None:
            rm = V_RULE_RE.match(lines[i])
            if rm:
                rule = {"n": int(rm.group(1)), "of": int(rm.group(2)),
                        "label": rm.group(3), "verdict": None,
                        "counterexample": None}
                out[base].append(rule)
                i += 1
                while i < n and not V_RULE_RE.match(lines[i]) \
                        and not V_ENTRY_RE.match(lines[i]) \
                        and not lines[i].startswith("=="):
                    vm = V_VERDICT_RE.match(lines[i])
                    cm = V_COUNTER_RE.match(lines[i])
                    if vm:
                        rule["verdict"] = vm.group(1)
                        i += 1
                        while i < n and V_CONT_RE.match(lines[i]) \
                                and not V_VERDICT_RE.match(lines[i]) \
                                and not V_COUNTER_RE.match(lines[i]):
                            rule["verdict"] += " " + V_CONT_RE.match(lines[i]).group(1)
                            i += 1
                        continue
                    if cm:
                        rule["counterexample"] = cm.group(1)
                    i += 1
                continue
        i += 1
    return out


def readme_blocks():
    """The paragraphs and tables catalog/README.md owns, lifted verbatim."""
    with open(README_PATH, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    out = {}

    def para(starts_with):
        for block in text.split("\n\n"):
            if block.lstrip().startswith(starts_with):
                return " ".join(block.split())
        return None

    out["coverage"] = para("**It claims complete *coverage*.**")
    out["enumeration"] = para("**It never claims complete *enumeration*.**")

    # The status legend and the calibration vocabulary, as markdown tables.
    def table_after(heading):
        m = re.search(r"^##\s+%s\s*$" % re.escape(heading), text, re.M)
        if not m:
            return []
        rows = []
        for line in text[m.end():].splitlines():
            if line.startswith("##"):
                break
            if line.startswith("|") and not re.match(r"^\|[\s:-]+\|", line):
                cells = [c.strip() for c in line.strip().strip("|").split("|")]
                if len(cells) == 2 and cells[0] not in ("status", "verdict"):
                    rows.append(cells)
        return rows

    out["status_legend"] = table_after("Status legend")
    # The calibration vocabulary lives in an HTML comment in TEMPLATE.md; the
    # README states the six values in prose. Take the prose sentence.
    m = re.search(r"One of ([^.]*?);\s*`catalog/TEMPLATE\.md`", text)
    out["calibration_values"] = m.group(1) if m else None
    return out


# --------------------------------------------------------------------------
# Assembly
# --------------------------------------------------------------------------

def collect(validate_log=None):
    tier_of, release_count, provenance = ci.load_ranking()
    entries = ci.list_catalog_entries()
    cata = ci.list_cata_files()
    vtext = ci.get_validate_output(validate_log)
    vrules = parse_validate_rules(vtext)
    voos = ci.parse_validate(vtext)
    readme = readme_blocks()

    # basename <-> release global, exactly as tools/catalog_index.py resolves it
    base_of_global = {g: b for b, g in ci.ALIAS.items() if g is not None}
    for base in sorted(set(cata) | set(entries)):
        if base not in ci.ALIAS and base in tier_of:
            base_of_global.setdefault(base, base)
    global_of_base = {b: g for g, b in base_of_global.items()}

    rows = []
    parse_failures = []
    disagreements = []
    for base, path in sorted(entries.items()):
        fields, missing = parse_entry(path)
        if missing:
            parse_failures.append((base, missing))
        global_name = global_of_base.get(base)
        tier_key = tier_of.get(global_name) if global_name else None
        status = fields.get("Status", "")

        cata_base = CATA_ALIAS.get(base, base)
        cata_path = cata.get(cata_base)
        rules, diag, frac = ([], [], None)
        if cata_path:
            rules, diag, frac = read_cata(cata_path)
            if frac != len(rules):
                disagreements.append(
                    "%s: cata/%s.tex has %d `\\frac` but %d `$$...$$` groups; "
                    "the rules printed here are the $$ groups"
                    % (base, cata_base, frac, len(rules)))

        # --- cross-check the entry's own numbers against the artifacts ------
        written = fields.get("Generated", "")
        wm = WRITTEN_GENERATED_RE.search(written)
        # An entry may legitimately report rules that live in a DIFFERENT
        # cata/*.tex (`disjunctive` points at cata/cumulative.tex and says so).
        # Only compare when the cell is talking about this entry's own file.
        named = set(re.findall(r"cata/([A-Za-z0-9_]+)\.tex", written))
        talks_about_self = (not named) or (cata_base in named)
        if wm and talks_about_self:
            n_written = int(wm.group(1))
            if frac is not None and n_written != frac:
                disagreements.append(
                    "%s: entry's Generated row says %d rules, "
                    "`grep -o '\\frac' cata/%s.tex | wc -l` gives %d"
                    % (base, n_written, cata_base, frac))
            if frac is None and n_written != 0:
                disagreements.append(
                    "%s: entry's Generated row says %d rules, but there is no "
                    "cata/%s.tex at all" % (base, n_written, cata_base))

        vr = vrules.get(base, [])
        sound = sum(1 for r in vr
                    if (r["verdict"] or "").startswith("SOUND and MINIMAL"))
        wv = WRITTEN_SOUNDMIN_RE.search(fields.get("Validator", ""))
        if wv and vr and int(wv.group(1)) != sound:
            disagreements.append(
                "%s: entry's Validator row says %s SOUND and MINIMAL, this "
                "run gives %d" % (base, wv.group(1), sound))

        # `<name>_fn` entries quote the base entry's Status row. Those quotes
        # are dated 2026-09-21 and some of them have gone stale; say so.
        qm = re.search(r"resolves to \[`([^`]+)\.md`\].*?Status row reads "
                       r"`([^`]+)`", status)
        if qm:
            other = ci.list_catalog_entries().get(qm.group(1))
            if other:
                ofields, _ = parse_entry(other)
                ostatus = ofields.get("Status", "")
                if not ostatus.startswith("`%s`" % qm.group(2)):
                    now = md_strip(ostatus)
                    if len(now) > 70:
                        now = now[:67].rstrip() + "..."
                    disagreements.append(
                        "%s: quotes %s.md's Status as \"%s\"; that row now "
                        "reads \"%s\"" % (base, qm.group(1), qm.group(2), now))

        cal_title, cal_body = entry_section(path, "Calibration")
        rows.append({
            "base": base,
            "global": global_name,
            # The published explanation, if this repo has sourced one, and the
            # entry's own calibration section, which is the verdict relating
            # the two. Both are read here, never cached and never retyped.
            "lit": parse_literature(base),
            "cal_title": cal_title,
            "cal_body": cal_body,
            "tier": tier_key,
            "tier_label": ci.TIER_LABEL[tier_key] if tier_key else None,
            "fields": fields,
            "missing": missing,
            "path": path,
            "cata_path": cata_path,
            # The artifact's own basename, which is `base` for every entry but
            # the CATA_ALIAS ones. Every `cata/<name>.tex` this document PRINTS
            # comes from here, so the document never names a file that is not
            # the one it read.
            "cata_base": cata_base,
            "rules": rules,
            "diag": diag,
            "frac": frac,
            "verdicts": vr,
            "sound": sound,
            "oos": voos.get(base) if voos.get(base, {}).get("out_of_scope") else None,
            # `make validate` names an entry even when it holds no rule at all
            # (cata/table.tex, 0 rules), and its own total counts that entry.
            # Counting `verdicts` instead would silently print 10 for 11.
            "in_validate": base in vrules,
            "block": (BLOCK_RE.search(status).group(1)
                      if BLOCK_RE.search(status) else None),
            "encodable": ENCODABLE in status,
        })

    # A sourced published explanation with no entry to attach it to would
    # be invisible in this document, so say so rather than drop it.
    lit_bases = sorted(
        f[:-3] for f in os.listdir(LIT_DIR)
        if f.endswith(".md") and f != "README.md") if os.path.isdir(LIT_DIR) else []
    for lb in lit_bases:
        if lb not in entries:
            disagreements.append(
                "catalog/_literature/%s.md holds a sourced published "
                "explanation, but there is no catalog/%s.md entry to print it "
                "beside; it does not appear in this document" % (lb, lb))

    # README's own coverage sentence, checked against the filesystem.
    reviewed = sum(1 for r in rows if ci.STUB_MARKER not in
                   open(r["path"], encoding="utf-8", errors="replace").read())
    stubs = len(rows) - reviewed
    m = re.search(r"\*\*(\d+) of (\d+) files\s*\u2014\s*(\d+) reviewed, "
                  r"(\d+) stubs\.\*\*", open(README_PATH, encoding="utf-8").read())
    if m and (int(m.group(3)), int(m.group(4))) != (reviewed, stubs):
        disagreements.append(
            "catalog/README.md's \"Coverage so far\" says %s of %s files -- "
            "%s reviewed, %s stubs; grepping every catalog/*.md for the stub "
            "marker today gives %d entry files, %d reviewed, %d stubs"
            % (m.group(1), m.group(2), m.group(3), m.group(4),
               len(rows), reviewed, stubs))

    return {
        "lit_bases": lit_bases,
        "rows": rows, "tier_of": tier_of, "release_count": release_count,
        "provenance": provenance, "readme": readme,
        "parse_failures": parse_failures, "disagreements": disagreements,
        "reviewed": reviewed, "stubs": stubs, "vtext": vtext,
    }


RULES_BUCKET = "Entries with explanation rules"


def bucket(rows):
    """The document's reading order, as the task fixed it.

    1. entries with generated rules, release globals first;
    2. entries blocked on a gap, grouped by the code, G before E;
    3. `encodable today, not encoded`;
    4. tier `out of scope`;
    5. everything left.

    Claiming runs in a different order from printing: tier `out of scope` is
    claimed BEFORE the gap grouping, so that section is the 28 constraints
    `tools/mzn_coverage.py` ranks out of scope rather than a leftover of
    whatever the gap groups did not take. Every one of them still names a
    blocking code, and the section is subdivided by it.
    """
    placed = set()

    def take(pred):
        got = [r for r in rows if r["base"] not in placed and pred(r)]
        placed.update(r["base"] for r in got)
        return got

    def codekey(c):
        if not c or not c[1:].isdigit():
            return (2, 0)
        return (0 if c.startswith("G") else 1, int(c[1:]))

    def by_code(rs):
        groups = {}
        for r in rs:
            groups.setdefault(r["block"] or "no blocking code stated",
                              []).append(r)
        return [(c, groups[c]) for c in sorted(groups, key=codekey)]

    with_rules = take(lambda r: r["rules"] or r["lit"])
    oos = take(lambda r: r["tier_label"] == "out of scope")
    blocked = take(lambda r: r["block"])
    enc = take(lambda r: r["encodable"])
    rest = take(lambda r: True)

    both = [r for r in with_rules if r["lit"]]
    gen_only = [r for r in with_rules if not r["lit"] and r["global"]]
    nomatch = [r for r in with_rules if not r["lit"] and not r["global"]]
    buckets = [
        (RULES_BUCKET,
         "Every entry that carries a rule of either kind: a \\emph{generated} "
         "rule, produced by this project from a decomposition and copied "
         "verbatim from \\texttt{cata/*.tex}, or a \\emph{published} rule, "
         "someone else's result sourced into \\texttt{catalog/\\_literature/} "
         "and printed inside a coloured bar that says so. This document "
         "re-renders neither: a generated rule is copied, a published one is "
         "laid out as its source file records it. Where an entry has both, "
         "the calibration relating them follows the pair.",
         [("Both kinds: a generated rule and a published one", both),
          ("Generated rules only", gen_only),
          ("Generated rules, no matching release global", nomatch)]),
        ("Entries blocked on a gap",
         "Grouped by the code the entry's own Status row names first. A "
         "\\texttt{G}-number is a gap in the decomposition input format "
         "(\\texttt{docs/DECOMP\\_FORMAT\\_NOTES.md}); an \\texttt{E}-number "
         "is an extension route from \\texttt{CHRISTMAS\\_LIST.md}. An entry "
         "naming more than one code says so in the Status text reproduced "
         "below, and is filed under the first.",
         by_code(blocked)),
        ("Encodable today, not encoded",
         "The current input format can already express the decomposition and "
         "no gap blocks it; nothing in the generator does it. There is no "
         "G-number to name, which is why this status value exists.",
         [("", enc)]),
        ("Out of scope",
         "Tier \\texttt{out of scope} in \\texttt{tools/mzn\\_coverage.py}'s "
         "ranking --- set variables, floats, graph and packing constraints "
         "this method does not address. Each still names the code that blocks "
         "it, and the subsections below are that code.",
         by_code(oos)),
        ("Remaining entries",
         "No generated rule, no blocking code in the Status row, and a tier "
         "inside scope. Most are the \\texttt{\\_fn} function variants, whose "
         "Status defers to the base entry rather than asserting one.",
         [("", rest)]),
    ]
    return [b for b in buckets if any(g[1] for g in b[2])]


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------

PREAMBLE = r"""\documentclass[10pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[margin=2.1cm]{geometry}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{longtable}
\usepackage{array}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{framed}
\usepackage{microtype}
\usepackage[hidelinks,bookmarks=true]{hyperref}

\setcounter{secnumdepth}{3}
\setcounter{tocdepth}{2}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.45em}
\sloppy

\newcommand{\entryfield}[2]{{\raggedright\textbf{#1}\quad #2\par}}
\newcommand{\diag}[1]{{\small\itshape\raggedright #1\par}}
%% A rule is copied verbatim from cata/*.tex. Some are wider than the page;
%% scaling the box down keeps every token of the rule rather than rewrapping,
%% reformatting or truncating it.
\newcommand{\rulebox}[1]{%
  \[\resizebox{\ifdim\width>\linewidth\linewidth\else\width\fi}{!}%
    {$\displaystyle #1$}\]}

%% ---- the two kinds of rule, and the one visual grammar that separates them.
%% A GENERATED rule is this project's output: plain text column, black, the
%% \rulebox above, under a bold "Generated rule" label carrying its verdict.
%% A PUBLISHED rule is someone else's result: everything about it sits inside
%% \begin{pubblock}, which draws a coloured bar down the left of every page it
%% spans, and every rule inside it carries its own "Published rule" label and
%% a [published] marker inside the display itself. Neither label depends on
%% the reader having seen the other, or the section heading, or the page
%% before.
\definecolor{litbar}{HTML}{5B2D8E}
\definecolor{calbar}{HTML}{4A4A4A}
\definecolor{tagquoted}{HTML}{1B6B2E}
\definecolor{tagderived}{HTML}{9A5B00}
\definecolor{tagsecondary}{HTML}{9A5B00}
\definecolor{tagnotsourced}{HTML}{A11212}
\definecolor{tagcomparison}{HTML}{23508C}

\newcommand{\provtag}[2]{{\small\sffamily\bfseries\textcolor{#1}{#2}}}

\newenvironment{pubblock}{%
  \par\smallskip
  \def\FrameCommand{\textcolor{litbar}{\vrule width 2.5pt}\hspace{9pt}}%
  \MakeFramed{\advance\hsize-\width\FrameRestore}}%
  {\endMakeFramed\par\smallskip}
\newenvironment{calblock}{%
  \par\smallskip
  \def\FrameCommand{\textcolor{calbar}{\vrule width 1pt}\hspace{9pt}}%
  \MakeFramed{\advance\hsize-\width\FrameRestore}}%
  {\endMakeFramed\par\smallskip}

\newcommand{\pubhead}[1]{{\sffamily\bfseries\large\textcolor{litbar}{#1}\par}}
\newcommand{\calhead}[1]{{\sffamily\bfseries\large\textcolor{calbar}{#1}\par}}
\newcommand{\litsub}[1]{\par\smallskip{\sffamily\bfseries\textcolor{litbar}{#1}\par}}
\newcommand{\litsubsub}[1]{\par{\sffamily\bfseries\small #1\par}}
\newcommand{\rulekind}[1]{\par{\small\sffamily\textcolor{litbar}{#1}\par}}
\newcommand{\genrulehead}[1]{\par{\small\textbf{#1}\par}}
%% One quoted line, shrunk to the measure if it is too wide. Shrinking keeps
%% every token where the paper put it; rewrapping would not.
\newcommand{\litline}[1]{\noindent
  \resizebox{\ifdim\width>\linewidth\linewidth\else\width\fi}{!}{#1}\par}
%% A published rule that the source file says translates faithfully. The
%% [published] marker is part of the display, so the rule cannot be read as a
%% generated one even by a reader who sees nothing else on the page.
\newcommand{\pubrulebox}[1]{%
  \[\resizebox{\ifdim\width>\linewidth\linewidth\else\width\fi}{!}%
    {$\displaystyle #1 \qquad
      \text{\normalfont\footnotesize\sffamily
        \textcolor{litbar}{[published]}}$}\]}
"""


def esc(s):
    return tex_escape(s)


def render_published(r, L):
    """The published explanation, inside the coloured bar that says so.

    The bar is drawn by `framed` and repeats on every page the block spans, so
    a reader who opens the document in the middle of one is inside a labelled
    region, not in front of an unattributed rule.
    """
    lit = r["lit"]
    if not lit:
        return
    w = L.append
    w("")
    w("\\begin{pubblock}")
    w("\\pubhead{Published explanation --- not this project's output}")
    w("{\\small\\sffamily Everything between this bar's ends is "
      "\\textbf{someone else's published result}, summarised under citation "
      "in %s and reproduced here with that file's provenance tags carried "
      "across unchanged. Nothing inside was produced by the generator in this "
      "repository, and no tag is upgraded: %s means the formula was "
      "transcribed from the fetched document, %s that it was obtained by a "
      "substitution the paper states in prose, %s that only a summary "
      "supports it, %s that it could not be obtained at all, and %s that the "
      "sentence is the source file's own reading rather than a claim about "
      "the paper. Tags occurring in this file: %s.\\par}"
      % (tt(lit["path"]),
         "\\provtag{tagquoted}{QUOTED}",
         "\\provtag{tagderived}{DERIVED}",
         "\\provtag{tagsecondary}{SECONDARY}",
         "\\provtag{tagnotsourced}{NOT SOURCED}",
         "\\provtag{tagcomparison}{COMPARISON}",
         ", ".join("\\provtag{%s}{%s}" % (PROV_COLOR[t], t)
                   for t in lit["tags"]) or "none"))
    for title, body in lit["sections"]:
        head = md_to_tex(title)
        if title == LIT_NOTSOURCED_SECTION:
            head += " \\ \\provtag{tagnotsourced}{NOT SOURCED}"
        w("\\litsub{%s}" % head)
        L.extend(render_md(body, title))
    if lit["method"]:
        w("\\litsub{How the source file was produced}")
        w("{\\small")
        L.extend(render_md(lit["method"], LIT_METHOD_SECTION))
        w("\\par}")
    w("\\end{pubblock}")


def render_calibration(r, L):
    """The verdict relating the pair, printed next to the pair.

    Two sources, kept apart: the entry's own calibration section, and the
    literature file's comparison section, which that file tags COMPARISON --
    its author's reading of the two rules, not a claim about the paper.
    """
    if not r["lit"]:
        return
    w = L.append
    w("")
    w("\\begin{calblock}")
    w("\\calhead{Calibration --- the generated rule against the published "
      "one}")
    w("{\\small\\sffamily Verdict, from this entry's own header table: "
      "%s.\\par}" % (md_to_tex(r["fields"].get("Calibration")) or "---"))
    if r["cal_body"]:
        w("\\litsubsub{From %s, section ``%s''}"
          % (tt("catalog/%s.md" % r["base"]), esc(r["cal_title"] or "")))
        L.extend(render_md(r["cal_body"], r["cal_title"]))
    for title, body in r["lit"]["calibration"]:
        w("\\litsubsub{From %s, section ``%s'' --- that file tags this section "
          "%s throughout: it is the reading of the session that sourced the "
          "paper, not a claim the paper makes}"
          % (tt(r["lit"]["path"]), esc(title),
             "\\provtag{tagcomparison}{COMPARISON}"))
        L.extend(render_md(body, title))
    w("\\end{calblock}")


def render_entry(r, L):
    w = L.append
    name = r["global"] or r["base"]
    w("\\subsubsection*{%s}" % tt(name))
    w("\\label{entry:%s}" % re.sub(r"[^A-Za-z0-9]", "-", r["base"]))
    f = r["fields"]
    w("\\entryfield{Tier}{%s}" % (md_to_tex(f.get("Tier")) or "---"))
    w("\\entryfield{Status}{%s}" % (md_to_tex(f.get("Status")) or "---"))
    w("\\entryfield{Generated}{%s}" % (md_to_tex(f.get("Generated")) or "---"))
    w("\\entryfield{Validator}{%s}" % (md_to_tex(f.get("Validator")) or "---"))
    w("\\entryfield{Calibration}{%s}" % (md_to_tex(f.get("Calibration")) or "---"))
    w("\\entryfield{Last measured}{%s}" % (md_to_tex(f.get("Last measured")) or "---"))
    w("\\entryfield{Blocking gap}{%s}"
      % (tt(r["block"]) if r["block"] else "none stated in the Status row"))
    w("\\entryfield{Entry}{\\texttt{catalog/%s.md}}" % esc(r["base"] + ""))
    if r["lit"]:
        w("\\entryfield{Published explanation}{sourced in %s --- %d rule "
          "section(s), printed below inside the coloured bar, followed by the "
          "calibration relating them to the generated rules above it.}"
          % (tt(r["lit"]["path"]), r["lit"]["n_rules"]))
    if r["missing"]:
        w("\\entryfield{\\textcolor{red}{Unparsed header rows}}{%s}"
          % ", ".join(tt(x) for x in r["missing"]))

    if r["rules"]:
        w("")
        w("\\textbf{Generated rules} --- this project's output, copied "
          "verbatim from \\texttt{cata/%s.tex} (%d, counted as occurrences of "
          "\\texttt{\\textbackslash{}frac}).\\par"
          % (esc(r["cata_base"]), r["frac"]))
        for k, body in enumerate(r["rules"], 1):
            v = next((x for x in r["verdicts"] if x["n"] == k), None)
            if v and v["verdict"]:
                tag = "\\textsc{verdict} %s" % md_to_tex(v["verdict"])
            elif r["oos"]:
                tag = "\\textsc{no verdict} --- the validator reports this " \
                      "entry out of scope"
            else:
                tag = "\\textsc{no verdict} --- this entry does not appear in " \
                      "the \\texttt{make validate} run"
            w("")
            w("{\\small\\textbf{Generated rule %d of %d} --- "
              "\\texttt{cata/%s.tex}, this project's generator. %s\\par}"
              % (k, len(r["rules"]), esc(r["cata_base"]), tag))
            if v and v["counterexample"]:
                w("{\\small\\textit{counterexample:} %s\\par}"
                  % md_to_tex(v["counterexample"]))
            w("\\rulebox{%s}" % body)
    elif r["cata_path"]:
        w("")
        w("\\textbf{Generated rules} --- \\texttt{cata/%s.tex} exists and "
          "emits none." % esc(r["cata_base"]))
    elif r["lit"]:
        w("")
        w("\\textbf{Generated rules} --- none. There is no "
          "\\texttt{cata/%s.tex}; the only explanation rules in this entry "
          "are the published ones below." % esc(r["cata_base"]))

    if r["oos"] and r["oos"].get("reason"):
        w("")
        w("\\diag{Validator, out of scope: %s}" % md_to_tex(r["oos"]["reason"]))

    if r["diag"]:
        w("")
        w("\\diag{%s}" % "\\\\ ".join(
            tex_escape(d).replace("\\textbackslash{}", "\\textbackslash{}")
            for d in r["diag"]))

    render_published(r, L)
    render_calibration(r, L)


def render_bucket(b, L):
    title, blurb, groups = b
    w = L.append
    w("\\clearpage")
    w("\\section{%s}" % title)
    w(blurb)
    for gname, grows in groups:
        if not grows:
            continue
        if gname:
            is_code = gname[:1] in ("G", "E") and gname[1:].isdigit()
            head = tt(gname) if is_code else esc(gname)
            w("\\subsection*{%s \\ \\normalsize(%d)}" % (head, len(grows)))
            w("\\addcontentsline{toc}{subsection}{%s (%d)}"
              % (head, len(grows)))
        for r in sorted(grows, key=lambda r: (r["global"] or "~" + r["base"])):
            render_entry(r, L)


def render_legend(data, L):
    """The front matter a reader needs before the first rule: which kind of
    rule they are looking at, and what the tag beside it means.

    Every definition here is lifted from the file that owns it --
    `catalog/_literature/README.md` for the provenance tags,
    `catalog/README.md` for the calibration verdicts -- so this page cannot
    drift away from them.
    """
    w = L.append
    rows = data["rows"]
    lit_rows = [r for r in rows if r["lit"]]
    w("\\section{How to read an entry: two kinds of rule}"
      "\\label{sec:legend}")
    w("This catalog contains rules of two kinds, and they are not the same "
      "sort of object. Telling them apart is the first thing to know about "
      "any rule in it.")
    w("\\begin{itemize}\\setlength{\\itemsep}{0.3em}")
    w("\\item \\textbf{Generated rules} are \\emph{this project's output}: "
      "what the generator derived from a decomposition. They are printed in "
      "the body text, in black, each under a bold label that names the "
      "\\texttt{cata/*.tex} file it was copied from and carries whatever "
      "verdict \\texttt{make validate} issued for it.")
    w("\\item \\textbf{Published rules} are \\emph{someone else's result}, "
      "summarised under citation. Every one of them sits inside a block with "
      "a coloured bar down its left margin, repeated on every page the block "
      "spans, opening with the words \\emph{Published explanation --- not "
      "this project's output}. Each rule inside carries its own label, and a "
      "published rule typeset as a fraction also carries the marker "
      "\\textcolor{litbar}{\\sffamily[published]} inside the display itself.")
    w("\\end{itemize}")
    w("A published rule is typeset as a "
      "$\\frac{\\text{premises}}{\\text{conclusion}}$ \\textbf{only where the "
      "source file states that its translation into this notation is "
      "faithful}. Where that file says the translation is not faithful, the "
      "paper's own form is printed instead and the file's reasons are printed "
      "under it. Most published explanations of these constraints quantify "
      "their premises over an object that exists only at propagation time --- "
      "a Hall interval, a strongly connected component of a residual graph, "
      "the cut of a flow network, the set of tasks with a compulsory part at "
      "a time point --- and this notation has no index set that names one. "
      "Forcing such a rule into a fraction would state something about the "
      "literature that the literature does not say.")
    w("Where an entry has both kinds, a third block follows the pair, with a "
      "thin grey bar: the \\emph{calibration}, the verdict relating the "
      "generated rule to the published one, on implication strength. Its "
      "vocabulary is below. A verdict in this document is never written as "
      "``correct''.")

    prov_body = lit_readme_provenance()
    if prov_body:
        w("\\subsection{Provenance tags, as \\texttt{catalog/\\_literature/"
          "README.md} defines them}")
        w("Lifted from the file that defines them, in its own order. Each tag "
          "carries across unchanged wherever the claim it marks is printed; "
          "this document never upgrades one.")
        L.extend(render_md(prov_body, "The provenance convention"))
    readme = data["readme"]
    if readme.get("calibration_values"):
        w("\\subsection{Calibration verdicts}")
        w("A separate axis from the status legend, which is in "
          "\\S\\ref{sec:howmade} with the rest of the status material: how a "
          "generated rule compares to the "
          "\\emph{published} one, on implication strength. One of %s."
          % md_to_tex(readme["calibration_values"]))

    w("\\subsection{How much of the literature is here}")
    w("\\textbf{%d} of the \\textbf{%d} entry files in \\texttt{catalog/} "
      "carry a published explanation: %s. That is \\textbf{%d} of the "
      "\\textbf{%d} MiniZinc release globals."
      % (len(lit_rows), len(rows),
         ", ".join(tt(r["base"]) for r in sorted(lit_rows,
                                                 key=lambda x: x["base"])),
         sum(1 for r in lit_rows if r["global"]), data["release_count"]))
    w("\\textbf{That is a count of what this repository has sourced, and "
      "nothing else.} It is not a claim that the literature on these three "
      "constraints is exhausted --- each file records what it could not "
      "obtain, in its own \\emph{What was not sourced} section, printed here "
      "with the rest --- and it is not a claim about the other %d release "
      "globals, whose literature, where any exists, is indexed in "
      "\\texttt{CHRISTMAS\\_LIST.md} and is not reproduced in this document. "
      "The coverage sentence on the title page is about \\emph{this method's} "
      "rules; it says nothing about the published ones."
      % (data["release_count"] - sum(1 for r in lit_rows if r["global"])))


def render(data, cmd_line, when, commit):
    rows = data["rows"]
    readme = data["readme"]
    L = []
    w = L.append
    w("%% catalog/catalog.tex -- GENERATED. Do not hand-edit.")
    w("%%%% Regenerate with: %s" % cmd_line)
    w("%%%% Generated: %s from commit %s" % (when, commit))
    w("%% Source: tools/catalog_tex.py, which reads tools/mzn_coverage.py")
    w("%% --json (via tools/catalog_index.py), catalog/*.md, cata/*.tex and")
    w("%% the output of `make validate`. Every number below is computed on")
    w("%% every run; none of it is hand-typed.")
    w(PREAMBLE)
    w("\\begin{document}")

    # ---- title page -----------------------------------------------------
    total_rules = sum(r["frac"] or 0 for r in rows)
    rule_rows = [r for r in rows if r["rules"]]
    release_rule_rows = [r for r in rule_rows if r["global"]]
    rules_release = sum(r["frac"] for r in release_rule_rows)
    checked = sum(len(r["verdicts"]) for r in rows)
    sound = sum(r["sound"] for r in rows)
    flagged = checked - sound
    oos_entries = [r for r in rows if r["oos"]]
    oos_rules = sum(len(r["rules"]) for r in oos_entries)
    sound_entries = [r for r in rows if r["sound"]]

    w("\\begin{titlepage}")
    w("\\vspace*{2cm}")
    w("{\\Huge\\bfseries Explanation rules by constraint decomposition\\par}")
    w("\\vspace{0.6em}")
    w("{\\LARGE The catalog, in one document\\par}")
    w("\\vspace{1.4em}")
    w("{\\large Generated %s from commit \\texttt{%s} by "
      "\\texttt{%s}.\\par}" % (esc(when), esc(commit), esc(cmd_line)))
    w("\\vspace{1.6em}")
    w("\\hrule")
    w("\\vspace{1.2em}")
    w("{\\large\\bfseries What this document claims\\par}")
    if readme["coverage"]:
        w(md_to_tex(readme["coverage"]))
        w("")
    if readme["enumeration"]:
        w(md_to_tex(readme["enumeration"]))
        w("")
    w("\\emph{Both paragraphs above are lifted verbatim from "
      "\\texttt{catalog/README.md} at generation time.}")
    w("\\vspace{1.0em}")
    w("\\hrule")
    w("\\vspace{1.2em}")
    w("{\\large\\bfseries Headline figures, computed at generation time\\par}")
    w("\\begin{itemize}\\setlength{\\itemsep}{0pt}")
    w("\\item \\textbf{%d} MiniZinc release globals "
      "(\\texttt{tools/mzn\\_coverage.py}, release \\texttt{%s}); "
      "\\textbf{%d} of them have a \\texttt{catalog/*.md} entry."
      % (data["release_count"], esc(data["provenance"].get("version", "?")),
         sum(1 for r in rows if r["global"])))
    w("\\item \\textbf{%d} entry files in \\texttt{catalog/}: \\textbf{%d} "
      "reviewed, \\textbf{%d} still carrying the auto-stub marker. "
      "(\\textbf{%d} of the files match no release global.)"
      % (len(rows), data["reviewed"], data["stubs"],
         sum(1 for r in rows if not r["global"])))
    w("\\item \\textbf{%d} of the %d release globals have any generated rule; "
      "those files hold \\textbf{%d} rules. Across all of "
      "\\texttt{cata/*.tex} there are \\textbf{%d} rules in \\textbf{%d} "
      "files."
      % (len(release_rule_rows), data["release_count"], rules_release,
         total_rules, len(rule_rows)))
    lit_rows = [r for r in rows if r["lit"]]
    w("\\item \\textbf{%d} entries carry a \\emph{published} explanation as "
      "well, sourced into \\texttt{catalog/\\_literature/}: %s, holding "
      "\\textbf{%d} rule sections between them. A published rule is someone "
      "else's result, summarised under citation; it is not this project's "
      "output, and this document keeps the two kinds visibly apart. "
      "\\emph{Three sourced constraints is not a survey of the literature} --- "
      "see \\S\\ref{sec:legend}."
      % (len(lit_rows),
         ", ".join(tt(r["base"]) for r in sorted(lit_rows,
                                                 key=lambda x: x["base"])),
         sum(r["lit"]["n_rules"] for r in lit_rows)))
    w("\\item \\texttt{make validate} checked \\textbf{%d} rules in "
      "\\textbf{%d} entries: \\textbf{%d} \\texttt{SOUND and MINIMAL} "
      "(in %d entries), \\textbf{%d} flagged. A further \\textbf{%d} rules in "
      "\\textbf{%d} entries are out of scope for the validator."
      % (checked, sum(1 for r in rows if r["in_validate"]), sound,
         len(sound_entries), flagged, oos_rules, len(oos_entries)))
    w("\\item \\emph{Sound and minimal is a floor, not strength.} Minimality "
      "is premise-droppability. \\texttt{all\\_different}'s one rule is sound "
      "and minimal and only ever fires at $n=2$.")
    w("\\end{itemize}")
    w("\\vspace{0.6em}")
    w("{\\bfseries Entries blocked, by the code their Status row names "
      "first:}\\par")
    counts = {}
    for r in rows:
        if r["block"]:
            counts[r["block"]] = counts.get(r["block"], 0) + 1
    order = sorted(counts, key=lambda c: (0 if c.startswith("G") else 1,
                                          int(c[1:])))
    w(", ".join("\\texttt{%s}~%d" % (c, counts[c]) for c in order) + ".")
    w("\\end{titlepage}")

    w("\\tableofcontents")
    w("\\clearpage")

    # ---- the explanations first, the status material behind them ---------
    # A reader who opens this document is looking for explanation rules. The
    # gap census, the summary tables and the disagreements all survive
    # unchanged; they simply stop being what the document opens with.
    render_legend(data, L)

    buckets = bucket(rows)
    first = [b for b in buckets if b[0] == RULES_BUCKET]
    rest = [b for b in buckets if b[0] != RULES_BUCKET]
    for b in first:
        render_bucket(b, L)

    # ---- how it was made -------------------------------------------------
    w("\\clearpage")
    w("\\section{How this document was made}\\label{sec:howmade}")
    w("Every figure, tier, status, verdict and rule below is read from the "
      "repository at generation time. Nothing is hand-typed, because a "
      "hand-typed number here is a number that will be wrong next week.")
    w("\\begin{itemize}\\setlength{\\itemsep}{0pt}")
    w("\\item Tiers: \\texttt{python3 tools/mzn\\_coverage.py --rank --json}, "
      "reached through \\texttt{tools/catalog\\_index.py}, whose "
      "\\texttt{ALIAS} table maps a \\texttt{cata/} basename to a release "
      "global name.")
    w("\\item Statuses, calibration verdicts and \"last measured\" lines: the "
      "six-row header table at the top of each \\texttt{catalog/*.md}, "
      "reproduced in full rather than summarised.")
    w("\\item Rules: \\texttt{cata/*.tex}, copied verbatim. This document does "
      "not re-render a rule, and the rule count is occurrences of "
      "\\texttt{\\textbackslash{}frac}, never \\texttt{grep -c} and never "
      "\\texttt{wc -l} (\\texttt{CLAUDE.md}, ``Traps'').")
    w("\\item Verdicts: one \\texttt{make validate} run, parsed from its own "
      "output.")
    w("\\item The claims paragraphs, the status legend and the calibration "
      "vocabulary: \\texttt{catalog/README.md}.")
    w("\\end{itemize}")
    w("A verdict is never written as ``correct''. The six status values and "
      "the six calibration verdicts below are the only vocabulary used.")

    if readme["status_legend"]:
        w("\\subsection{Status legend}")
        w("\\begin{longtable}{@{}>{\\raggedright\\arraybackslash}p{0.32\\textwidth}"
          ">{\\raggedright\\arraybackslash}p{0.62\\textwidth}@{}}")
        w("\\hline\\endhead")
        for k, v in readme["status_legend"]:
            w("%s & %s \\\\[0.3em]" % (md_to_tex(k), md_to_tex(v)))
        w("\\hline")
        w("\\end{longtable}")
    # ---- summary table ---------------------------------------------------
    w("\\section{Summary by tier}")
    w("Tier is \\texttt{tools/mzn\\_coverage.py}'s priority ranking. "
      "``Entries'' counts \\texttt{catalog/*.md} files; ``rules'' counts "
      "\\texttt{\\textbackslash{}frac} occurrences in the matching "
      "\\texttt{cata/*.tex}; ``sound+min'' counts rules this "
      "\\texttt{make validate} run called \\texttt{SOUND and MINIMAL}.")
    w("\\begin{longtable}{@{}lrrrrr@{}}")
    w("\\hline")
    w("tier & globals & entries & with rules & rules & sound+min \\\\")
    w("\\hline\\endhead")
    for key in ci.TIER_KEYS:
        label = ci.TIER_LABEL[key]
        globals_in = sum(1 for g, t in data["tier_of"].items() if t == key)
        mine = [r for r in rows if r["tier"] == key]
        w("%s & %d & %d & %d & %d & %d \\\\" % (
            esc(label), globals_in, len(mine),
            sum(1 for r in mine if r["rules"]),
            sum(r["frac"] or 0 for r in mine),
            sum(r["sound"] for r in mine)))
    nomatch = [r for r in rows if r["tier"] is None]
    w("\\hline")
    w("no release global & --- & %d & %d & %d & %d \\\\" % (
        len(nomatch), sum(1 for r in nomatch if r["rules"]),
        sum(r["frac"] or 0 for r in nomatch), sum(r["sound"] for r in nomatch)))
    w("\\hline")
    w("\\textbf{total} & %d & %d & %d & %d & %d \\\\" % (
        data["release_count"], len(rows), len([r for r in rows if r["rules"]]),
        sum(r["frac"] or 0 for r in rows), sum(r["sound"] for r in rows)))
    w("\\hline")
    w("\\end{longtable}")

    # ---- the one-row-per-entry table -------------------------------------
    w("\\section{Summary by entry}")
    w("\\begin{longtable}{@{}>{\\raggedright\\arraybackslash}p{0.26\\textwidth}l"
      ">{\\raggedright\\arraybackslash}p{0.32\\textwidth}rrl@{}}")
    w("\\hline")
    w("constraint & tier & status & rules & s+m & block \\\\")
    w("\\hline\\endhead")
    for r in sorted(rows, key=lambda r: (r["global"] or "~" + r["base"])):
        # The whole Status cell, truncated on LENGTH alone. Splitting it at
        # the first em dash would print "nothing generated" and drop the
        # "blocked on G3" that is the point of the row.
        short = md_strip(r["fields"].get("Status", ""))
        if len(short) > 58:
            short = short[:55].rstrip() + "..."
        w("%s & %s & %s & %s & %d & %s \\\\" % (
            tt(r["global"] or r["base"]),
            esc(r["tier_label"] or "---"),
            esc(short),
            "---" if r["frac"] is None else str(r["frac"]),
            r["sound"],
            tt(r["block"]) if r["block"] else "---"))
    w("\\hline")
    w("\\end{longtable}")

    # ---- disagreements ---------------------------------------------------
    w("\\section{Disagreements between computed and written numbers}")
    if data["disagreements"]:
        w("Each line is a number this run computed from an artifact next to a "
          "number written into a file. Neither side is preferred here; the "
          "disagreement is reported so it can be settled by whoever owns the "
          "file.")
        w("\\begin{itemize}\\setlength{\\itemsep}{0pt}")
        for d in sorted(data["disagreements"]):
            w("\\item %s" % md_to_tex(d))
        w("\\end{itemize}")
    else:
        w("None. Every count written into an entry matched the count this run "
          "computed from the artifact it describes.")

    w("\\section{Entries that did not parse}")
    if data["parse_failures"]:
        w("\\begin{itemize}\\setlength{\\itemsep}{0pt}")
        for base, missing in data["parse_failures"]:
            w("\\item %s --- header rows not found: %s"
              % (tt("catalog/%s.md" % base),
                 ", ".join(tt(m) for m in missing)))
        w("\\end{itemize}")
    else:
        w("None. All %d entry files carry the full six-row header table "
          "\\texttt{catalog/TEMPLATE.md} mandates." % len(rows))

    # ---- the entries -----------------------------------------------------
    for b in rest:
        render_bucket(b, L)

    w("\\end{document}")
    return "\n".join(L) + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true",
                    help="print, don't write catalog/catalog.tex")
    ap.add_argument("--out", metavar="FILE", default=OUT_PATH,
                    help="write somewhere other than catalog/catalog.tex")
    ap.add_argument("--validate-log", metavar="FILE",
                    help="reuse a saved `make validate` log instead of "
                         "re-running it")
    args = ap.parse_args(argv)

    data = collect(args.validate_log)
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"],
                            capture_output=True, text=True, cwd=REPO)
    commit = commit.stdout.strip() or "unknown"
    when = datetime.date.today().isoformat()
    text = render(data, "python3 tools/catalog_tex.py", when, commit)

    for d in data["disagreements"]:
        sys.stderr.write("disagreement: %s\n" % d)
    for base, missing in data["parse_failures"]:
        sys.stderr.write("unparsed: catalog/%s.md missing %s\n"
                         % (base, ", ".join(missing)))
    if _unmapped:
        sys.stderr.write("warning: no LaTeX mapping for %s (emitted as "
                         "[U+xxxx])\n" % " ".join(sorted(_unmapped)))

    if args.dry_run:
        sys.stdout.write(text)
    else:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
        sys.stderr.write("wrote %s (%d lines)\n"
                         % (args.out, text.count("\n")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
