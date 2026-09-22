#!/usr/bin/env python3
"""catalog_tex.py -- compile the catalog into one readable LaTeX document.

Produces `catalog/catalog.tex`: the whole catalog, end to end, with every
explanation rule typeset as the `\\frac{premises}{conclusion}` the generator
already emits.

**Nothing in the output is hand-typed.** Every count, tier, status, verdict and
rule is read at generation time from the repo:

  - `tools/mzn_coverage.py --json`  -- the 118 release globals and their
    priority tier. Reached through `tools/catalog_index.py`'s `load_ranking`,
    so this script and the index agree by construction rather than by
    coincidence, and the basename <-> release-global mapping is that script's
    `ALIAS` table, not a second copy of it.
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

    # 1. code spans, before anything can chew on their contents
    s = re.sub(r"`([^`]*)`",
               lambda m: keep("\\texttt{%s}" % tex_escape(m.group(1))), s)
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

        cata_path = cata.get(base)
        rules, diag, frac = ([], [], None)
        if cata_path:
            rules, diag, frac = read_cata(cata_path)
            if frac != len(rules):
                disagreements.append(
                    "%s: cata/%s.tex has %d `\\frac` but %d `$$...$$` groups; "
                    "the rules printed here are the $$ groups"
                    % (base, base, frac, len(rules)))

        # --- cross-check the entry's own numbers against the artifacts ------
        written = fields.get("Generated", "")
        wm = WRITTEN_GENERATED_RE.search(written)
        # An entry may legitimately report rules that live in a DIFFERENT
        # cata/*.tex (`disjunctive` points at cata/cumulative.tex and says so).
        # Only compare when the cell is talking about this entry's own file.
        named = set(re.findall(r"cata/([A-Za-z0-9_]+)\.tex", written))
        talks_about_self = (not named) or (base in named)
        if wm and talks_about_self:
            n_written = int(wm.group(1))
            if frac is not None and n_written != frac:
                disagreements.append(
                    "%s: entry's Generated row says %d rules, "
                    "`grep -o '\\frac' cata/%s.tex | wc -l` gives %d"
                    % (base, n_written, base, frac))
            if frac is None and n_written != 0:
                disagreements.append(
                    "%s: entry's Generated row says %d rules, but there is no "
                    "cata/%s.tex at all" % (base, n_written, base))

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

        rows.append({
            "base": base,
            "global": global_name,
            "tier": tier_key,
            "tier_label": ci.TIER_LABEL[tier_key] if tier_key else None,
            "fields": fields,
            "missing": missing,
            "path": path,
            "cata_path": cata_path,
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
        "rows": rows, "tier_of": tier_of, "release_count": release_count,
        "provenance": provenance, "readme": readme,
        "parse_failures": parse_failures, "disagreements": disagreements,
        "reviewed": reviewed, "stubs": stubs, "vtext": vtext,
    }


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

    with_rules = take(lambda r: r["rules"])
    oos = take(lambda r: r["tier_label"] == "out of scope")
    blocked = take(lambda r: r["block"])
    enc = take(lambda r: r["encodable"])
    rest = take(lambda r: True)

    buckets = [
        ("Entries with generated rules",
         "The release globals this method has produced rules for, plus the "
         "files under \\texttt{cata/} that match no release global. Rules are "
         "copied verbatim from \\texttt{cata/*.tex}; this document does not "
         "re-render one.",
         [("", [r for r in with_rules if r["global"]]),
          ("No matching release global",
           [r for r in with_rules if not r["global"]])]),
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
"""


def esc(s):
    return tex_escape(s)


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
    if r["missing"]:
        w("\\entryfield{\\textcolor{red}{Unparsed header rows}}{%s}"
          % ", ".join(tt(x) for x in r["missing"]))

    if r["rules"]:
        w("")
        w("\\textbf{Rules} --- copied verbatim from \\texttt{cata/%s.tex} "
          "(%d, counted as occurrences of \\texttt{\\textbackslash{}frac}).\\par"
          % (esc(r["base"]), r["frac"]))
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
            w("{\\small\\textbf{Rule %d.} %s\\par}" % (k, tag))
            if v and v["counterexample"]:
                w("{\\small\\textit{counterexample:} %s\\par}"
                  % md_to_tex(v["counterexample"]))
            w("\\rulebox{%s}" % body)
    elif r["cata_path"]:
        w("")
        w("\\textbf{Rules} --- \\texttt{cata/%s.tex} exists and emits none."
          % esc(r["base"]))

    if r["oos"] and r["oos"].get("reason"):
        w("")
        w("\\diag{Validator, out of scope: %s}" % md_to_tex(r["oos"]["reason"]))

    if r["diag"]:
        w("")
        w("\\diag{%s}" % "\\\\ ".join(
            tex_escape(d).replace("\\textbackslash{}", "\\textbackslash{}")
            for d in r["diag"]))


def render(data, cmd_line, when, commit):
    rows = data["rows"]
    readme = data["readme"]
    L = []
    w = L.append
    w("%% catalog/catalog.tex -- GENERATED. Do not hand-edit.")
    w("%% Regenerate with: %s" % cmd_line)
    w("%% Generated: %s from commit %s" % (when, commit))
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

    # ---- how it was made -------------------------------------------------
    w("\\section{How this document was made}")
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
    if readme["calibration_values"]:
        w("\\subsection{Calibration verdicts}")
        w("A separate axis from the status legend: how a generated rule "
          "compares to the \\emph{published} one, on implication strength. "
          "One of %s." % md_to_tex(readme["calibration_values"]))

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
    for title, blurb, groups in bucket(rows):
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
