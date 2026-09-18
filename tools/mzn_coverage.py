#!/usr/bin/env python3
"""Coverage classifier for CHRISTMAS_LIST.md against a MiniZinc release.

Answers only the mechanically checkable questions:

  * which globals a MiniZinc release ships (the ``include`` lines of
    ``std/globals.mzn``);
  * which of them ``CHRISTMAS_LIST.md`` has a row for, and which it does not
    (drift, in both directions);
  * the distribution of the machine-readable columns the list carries
    (E-code, solver class, literature-present flag);
  * structural defects in the list itself (a name in two rows, a row with no
    E-code).

It deliberately does NOT re-derive the literature column.  See docs/COVERAGE.md.

No network access.  Python 3.8+, standard library only.

Usage
-----
    python3 tools/mzn_coverage.py                     # vendored snapshot
    python3 tools/mzn_coverage.py --share /usr/local/share/minizinc
    python3 tools/mzn_coverage.py --json out.json
    python3 tools/mzn_coverage.py --check             # exit 1 on drift/defects
    python3 tools/mzn_coverage.py --share DIR --emit-snapshot > tools/data/x.txt
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import re
import subprocess
import sys
from collections import Counter, OrderedDict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_LIST = os.path.join(REPO, "CHRISTMAS_LIST.md")
DATA_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")

# The family tables live under "## <n>. <family>" headings.  Everything above
# section 1 is prose and solver tables and must not be parsed as rows.
FAMILY_HEADING = re.compile(r"^##\s+(\d+)\.\s+(.*)$")
OTHER_HEADING = re.compile(r"^##\s+(?!\d+\.)")
BACKTICKED = re.compile(r"`([^`]+)`")
ECODE = re.compile(r"\bE([0-7])\b")


# --------------------------------------------------------------------------
# release side
# --------------------------------------------------------------------------

def read_globals_from_share(share_dir):
    """Parse the canonical global names out of <share>/std/globals.mzn."""
    candidates = [
        os.path.join(share_dir, "std", "globals.mzn"),
        os.path.join(share_dir, "globals.mzn"),
        os.path.join(share_dir, "minizinc", "std", "globals.mzn"),
        os.path.join(share_dir, "share", "minizinc", "std", "globals.mzn"),
    ]
    for path in candidates:
        if os.path.isfile(path):
            return parse_globals_mzn(path), path
    raise SystemExit(
        "no globals.mzn under %r (tried: %s)" % (share_dir, ", ".join(candidates))
    )


def parse_globals_mzn(path):
    names = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = re.match(r'^\s*include\s+"([A-Za-z0-9_.]+)\.mzn"\s*;', line)
            if m:
                names.append(m.group(1))
    return names


def read_globals_from_snapshot(path):
    names = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line and not line.startswith("#"):
                names.append(line)
    return names


def detect_version(share_dir):
    """Best-effort release identification.  Returns (version, how)."""
    # 1. a minizinc binary sitting next to the share dir, or on PATH
    for exe in (
        os.path.join(share_dir, "..", "..", "bin", "minizinc"),
        os.path.join(share_dir, "..", "..", "minizinc"),
        "minizinc",
    ):
        try:
            out = subprocess.run(
                [exe, "--version"], capture_output=True, text=True, timeout=20
            )
        except (OSError, subprocess.SubprocessError):
            continue
        if out.returncode == 0:
            m = re.search(r"version\s+([0-9]+\.[0-9]+\.[0-9]+)", out.stdout)
            if m:
                return m.group(1), "`%s --version`" % exe
    # 2. a source checkout: CMakeLists.txt above share/minizinc
    for up in (
        os.path.join(share_dir, "..", "..", "CMakeLists.txt"),
        os.path.join(share_dir, "..", "..", "..", "CMakeLists.txt"),
    ):
        if os.path.isfile(up):
            with open(up, encoding="utf-8", errors="replace") as fh:
                text = fh.read()
            # the project() version, NOT cmake_minimum_required(VERSION 3.5.0)
            m = re.search(r"project\s*\([^)]*?VERSION\s+([0-9]+\.[0-9]+\.[0-9]+)",
                          text, re.S)
            if m:
                return m.group(1), "project(... VERSION ...) in %s" % os.path.normpath(up)
    # 3. floor from the newest versioned redefinitions file
    std = os.path.join(share_dir, "std")
    if os.path.isdir(std):
        vs = []
        for name in os.listdir(std):
            m = re.match(r"redefinitions-([0-9.]+)\.mzn$", name)
            if m:
                vs.append(tuple(int(p) for p in m.group(1).split(".")))
        if vs:
            floor = ".".join(str(p) for p in max(vs))
            return (
                ">= %s (floor only)" % floor,
                "newest redefinitions-*.mzn in std/; this is a LOWER BOUND, "
                "not the release",
            )
    return "unknown", "no binary, no CMakeLists.txt, no versioned redefinitions"


# --------------------------------------------------------------------------
# CHRISTMAS_LIST.md side
# --------------------------------------------------------------------------

class Row(object):
    __slots__ = ("section", "line", "raw_names", "names", "patterns",
                 "lit", "solver", "route", "ecodes", "flags")

    def as_dict(self):
        return {
            "section": self.section,
            "line": self.line,
            "names": sorted(self.names),
            "patterns": self.patterns,
            "ecodes": sorted(self.ecodes),
            "solver": self.solver,
            "literature": self.lit,
            "flags": self.flags,
        }


def expand_names(cells):
    """`global_cardinality`, `_closed`, `_low_up` -> the three full names.

    A backticked token beginning with '_' is a suffix on the *base* name of the
    cell -- the first full name in it -- not on the previously expanded one.
    `global_cardinality`, `_closed`, `_low_up` therefore yields
    global_cardinality_closed and global_cardinality_low_up, not
    global_cardinality_closed_low_up.  This is the list's own shorthand; it is
    not MiniZinc syntax.
    """
    out, patterns, base = [], [], None
    for tok in cells:
        tok = tok.strip()
        if not tok:
            continue
        if tok.startswith("_") and base is not None:
            tok = base + tok
        if "*" in tok:
            patterns.append(tok)
            continue
        if not re.match(r"^[A-Za-z][A-Za-z0-9_]*$", tok):
            continue  # prose inside backticks, e.g. a code fragment
        if base is None:
            base = tok
        if tok not in out:
            out.append(tok)
    return out, patterns


def parse_list(path):
    rows = []
    section = None
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            m = FAMILY_HEADING.match(line)
            if m:
                section = "%s. %s" % (m.group(1), m.group(2).strip())
                continue
            if OTHER_HEADING.match(line):
                section = None
                continue
            if section is None or not line.startswith("|"):
                continue
            cols = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cols) < 4:
                continue
            if set(cols[0]) <= set("-: ") or cols[0].lower() == "constraint":
                continue  # separator or header row
            r = Row()
            r.section = section
            r.line = lineno
            r.raw_names = cols[0]
            r.names, r.patterns = expand_names(BACKTICKED.findall(cols[0]))
            r.lit, r.solver, r.route = cols[1], cols[2], cols[3]
            r.ecodes = set("E" + d for d in ECODE.findall(cols[3]))
            r.flags = []
            if "(alias)" in cols[0]:
                r.flags.append("alias")
            if not r.ecodes:
                r.flags.append("no-ecode")
            rows.append(r)
    return rows


def classify_solver(cell):
    """Coarse class from the Solver column.  'native' wins over 'decomp'."""
    low = cell.lower()
    if "native" in low:
        return "native"
    if "decomp" in low:
        return "decomp"
    if cell.strip() in ("", "-", "--", "—"):
        return "unspecified"
    return "other"


def has_literature(cell):
    """Mechanical proxy only: a cell that is exactly a 'none' variant is 'none'.

    This does not judge whether the cited paper is right or complete -- that is
    the part of the list a script cannot regenerate.
    """
    s = cell.strip().strip("*").strip()
    if s in ("", "-", "--", "—"):
        return "unspecified"
    if re.match(r"^none\b", s, re.I):
        return "none"
    return "cited"


# --------------------------------------------------------------------------
# the classification itself
# --------------------------------------------------------------------------

def classify(release_globals, rows):
    release = set(release_globals)

    covered = {}          # global -> [row index, ...]
    duplicates = OrderedDict()
    listed_names = OrderedDict()

    for idx, r in enumerate(rows):
        here = list(r.names)
        for pat in r.patterns:
            for g in sorted(release):
                if fnmatch.fnmatchcase(g, pat) and g not in here:
                    here.append(g)
        for n in here:  # deduped within the row: a glob may re-hit an explicit name
            listed_names.setdefault(n, []).append(idx)

    for n, idxs in listed_names.items():
        if len(idxs) > 1:
            duplicates[n] = idxs
        if n in release:
            covered[n] = idxs

    missing = sorted(release - set(listed_names))
    extra = []
    for n in sorted(set(listed_names) - release):
        flags = sorted(set(f for i in listed_names[n] for f in rows[i].flags
                           if f == "alias"))
        extra.append(n + (" (list marks it an alias)" if flags else ""))

    ecodes = Counter()
    ecode_rows_by_global = {}
    solver = Counter()
    lit = Counter()
    for r in rows:
        reach = set(n for n in r.names if n in release)
        for pat in r.patterns:
            reach |= set(g for g in release if fnmatch.fnmatchcase(g, pat))
        for n in reach:
            ecode_rows_by_global[n] = sorted(r.ecodes)
        for code in (sorted(r.ecodes) or ["(none given)"]):
            ecodes[code] += 1
        solver[classify_solver(r.solver)] += 1
        lit[has_literature(r.lit)] += 1

    # per-global distributions (a row may name several globals)
    g_ecodes = Counter()
    for n in sorted(covered):
        codes = ecode_rows_by_global.get(n)
        g_ecodes["+".join(codes) if codes else "(none given)"] += 1

    return {
        "release_count": len(release),
        "row_count": len(rows),
        "listed_name_count": len(listed_names),
        "covered_count": len(covered),
        "missing_from_list": missing,
        "not_in_release": extra,
        "duplicate_names": {k: [rows[i].line for i in v]
                            for k, v in duplicates.items()},
        "rows_without_ecode": [
            {"line": r.line, "names": r.raw_names}
            for r in rows if "no-ecode" in r.flags
        ],
        "ecode_rows": OrderedDict(sorted(ecodes.items())),
        "ecode_globals": OrderedDict(sorted(g_ecodes.items())),
        "solver_rows": OrderedDict(sorted(solver.items())),
        "literature_rows": OrderedDict(sorted(lit.items())),
    }


# --------------------------------------------------------------------------
# reporting
# --------------------------------------------------------------------------

def render(result, provenance):
    L = []
    w = L.append
    w("MiniZinc coverage of CHRISTMAS_LIST.md")
    w("=" * 38)
    w("")
    w("Release source : %s" % provenance["source"])
    w("Release         : %s" % provenance["version"])
    w("Version known by: %s" % provenance["version_how"])
    w("List            : %s" % provenance["list"])
    w("Live parse      : %s" % ("yes" if provenance["live"] else
                                "NO -- vendored snapshot, see header of that file"))
    w("")
    w("Counts (all measured by parsing, not read off prose)")
    w("  globals in release ........ %d" % result["release_count"])
    w("  rows in family tables ..... %d" % result["row_count"])
    w("  distinct names named ...... %d" % result["listed_name_count"])
    w("  release globals covered ... %d  (%.1f%%)" % (
        result["covered_count"],
        100.0 * result["covered_count"] / max(1, result["release_count"])))
    w("  release globals missing ... %d" % len(result["missing_from_list"]))
    w("  names not in this release . %d" % len(result["not_in_release"]))
    w("")
    w("Drift: in the release, no row in the list (%d)" % len(result["missing_from_list"]))
    for n in result["missing_from_list"]:
        w("  + %s" % n)
    if not result["missing_from_list"]:
        w("  (none)")
    w("")
    w("Drift: named by the list, not a global of this release (%d)"
      % len(result["not_in_release"]))
    for n in result["not_in_release"]:
        w("  - %s" % n)
    if not result["not_in_release"]:
        w("  (none)")
    w("")
    w("Defects in the list (reported, never edited by this tool)")
    if result["duplicate_names"]:
        for n, lines in sorted(result["duplicate_names"].items()):
            w("  duplicate: `%s` named by rows at lines %s"
              % (n, ", ".join(str(x) for x in lines)))
    else:
        w("  no duplicate names")
    if result["rows_without_ecode"]:
        for d in result["rows_without_ecode"]:
            w("  no E-code: line %d  %s" % (d["line"], d["names"]))
    else:
        w("  every row carries an E-code")
    w("")
    w("Distribution: E-code, counted per row (a row may carry several)")
    for k, v in result["ecode_rows"].items():
        w("  %-12s %3d" % (k, v))
    w("")
    w("Distribution: E-code combination, counted per release global")
    for k, v in result["ecode_globals"].items():
        w("  %-12s %3d" % (k, v))
    w("")
    w("Distribution: solver column, per row")
    for k, v in result["solver_rows"].items():
        w("  %-12s %3d" % (k, v))
    w("")
    w("Distribution: literature column, per row (presence only -- the tool does")
    w("not and cannot check what is cited)")
    for k, v in result["literature_rows"].items():
        w("  %-12s %3d" % (k, v))
    return "\n".join(L)


def newest_snapshot():
    if not os.path.isdir(DATA_DIR):
        return None
    cands = sorted(f for f in os.listdir(DATA_DIR) if f.endswith("-globals.txt"))
    return os.path.join(DATA_DIR, cands[-1]) if cands else None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--share", metavar="DIR",
                    help="a MiniZinc share/minizinc directory (live parse)")
    ap.add_argument("--globals-file", metavar="FILE",
                    help="a globals.mzn to parse directly")
    ap.add_argument("--snapshot", metavar="FILE",
                    help="a vendored snapshot under tools/data/ (the default)")
    ap.add_argument("--list", metavar="FILE", default=DEFAULT_LIST,
                    help="CHRISTMAS_LIST.md (default: the one in this repo)")
    ap.add_argument("--json", metavar="FILE", help="also write the result as JSON")
    ap.add_argument("--emit-snapshot", action="store_true",
                    help="print the parsed global names, one per line, and exit")
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if there is drift or a structural defect")
    args = ap.parse_args(argv)

    live = False
    if args.share:
        names, src = read_globals_from_share(args.share)
        version, how = detect_version(args.share)
        live = True
        source = src
    elif args.globals_file:
        names = parse_globals_mzn(args.globals_file)
        version, how = "unknown", "--globals-file given; no share dir to inspect"
        live = True
        source = args.globals_file
    else:
        snap = args.snapshot or newest_snapshot()
        if not snap:
            raise SystemExit("no snapshot under %s and no --share given" % DATA_DIR)
        names = read_globals_from_snapshot(snap)
        m = re.search(r"minizinc-([0-9.]+)-globals", os.path.basename(snap))
        version = m.group(1) if m else "unknown"
        how = "the filename and provenance header of %s" % snap
        source = snap

    if args.emit_snapshot:
        print("\n".join(sorted(names)))
        return 0

    rows = parse_list(args.list)
    result = classify(names, rows)
    provenance = {"source": source, "version": version, "version_how": how,
                  "list": args.list, "live": live}
    print(render(result, provenance))

    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump({"provenance": provenance, "result": result,
                       "rows": [r.as_dict() for r in rows]}, fh, indent=2)

    if args.check:
        bad = (result["missing_from_list"] or result["not_in_release"]
               or result["duplicate_names"] or result["rows_without_ecode"])
        return 1 if bad else 0
    return 0


if __name__ == "__main__":
    sys.exit(main())
