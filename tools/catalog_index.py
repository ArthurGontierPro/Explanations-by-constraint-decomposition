#!/usr/bin/env python3
"""catalog_index.py -- regenerate catalog/INDEX.md, the one-row-per-global index.

Answers a single mechanical question: of the 118 MiniZinc release globals, how
many have a catalog entry (`catalog/<name>.md`), how many have generated rules
(`cata/<name>.tex`), and how many of those rules the validator (`make validate`)
calls SOUND and MINIMAL? Every number below is computed from the three
artifacts named above on every run -- none of it is hand-typed, per CLAUDE.md's
"Verify before you report".

Data sources (read, never re-derived):
  - tools/mzn_coverage.py --json   -- the 118 release globals, their priority
    tier (A-D / unclassified / out of scope), from its `result.ranking`.
  - catalog/*.md                   -- filenames only (existence), plus a grep
    for "blocked on G<n>" inside each, for the "blocking gap" column, plus a
    grep for STUB_MARKER, which splits the entries into *reviewed* (written by
    a person against catalog/TEMPLATE.md) and *stub* (machine-filled by
    tools/catalog_stub.py, every judgement field reading "not reviewed").
    The summary NEVER prints a bare entry count: it always reports the split,
    because "118 / 118" without it would read as 118 reviewed entries.
  - cata/*.tex                     -- rule counts. Every file is a SINGLE
    line with no trailing newline (see CLAUDE.md, "Traps"), so the only
    correct count is occurrences of the literal string "\\frac", never
    `grep -c` and never `wc -l`.
  - `make validate` output          -- per-entry SOUND-and-MINIMAL counts,
    parsed from its own "---- cata/<name>.tex  (N rules) ----" / "VERDICT"
    lines, plus its "out of scope" section for entries the validator refuses
    to check at all.

Usage:
    python3 tools/catalog_index.py                  # writes catalog/INDEX.md
    python3 tools/catalog_index.py --dry-run         # print, don't write
    python3 tools/catalog_index.py --validate-log F  # reuse a saved
                                                      # `make validate` log
                                                      # instead of re-running it

No network access. Python 3 standard library only.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CATALOG_DIR = os.path.join(REPO, "catalog")
CATA_DIR = os.path.join(REPO, "cata")
MZN_COVERAGE = os.path.join(REPO, "tools", "mzn_coverage.py")
INDEX_PATH = os.path.join(CATALOG_DIR, "INDEX.md")

# The marker tools/catalog_stub.py writes at the top of every file it
# generates. Defined HERE, and imported from here by catalog_stub.py, so the
# writer and the reader of the marker can never drift apart. A file carrying it
# is a machine-filled stub, not a reviewed entry; a file without it is never
# touched by the stub generator.
STUB_MARKER = "AUTO-STUB \u2014 NOT REVIEWED"

# Files under catalog/ that are not entries.
CATALOG_NON_ENTRIES = {"README.md", "TEMPLATE.md", "INDEX.md", "PROBLEMATIC.md"}
CATALOG_NON_ENTRY_DIRS = {"_literature"}

# --------------------------------------------------------------------------
# The alias map. This is the one thing a script cannot discover on its own:
# the file basename under cata/ or catalog/ and the MiniZinc release global
# name are, in general, spelled differently. Edit this table -- and only this
# table -- when a new cata/*.tex or catalog/*.md appears with a name that does
# not already match a release global exactly.
#
# Left side: basename (no extension) as it appears under cata/ AND catalog/
# (the two sibling sessions writing catalog/*.md are using the same
# constraint-name basenames as cata/*.tex; if that ever stops being true, split
# this into two maps).
#
# Right side: the MiniZinc release global name from tools/mzn_coverage.py's
# ranking, or None if no release global matches -- in which case the file is
# reported as UNMATCHED rather than silently dropped or guessed at.
#
# Provenance for every non-identity entry below is a grep of CHRISTMAS_LIST.md
# (2026-09-21): each of these rows explicitly names the cata/*.tex file next
# to the release global it corresponds to, so this is not a guess.
#   - "already in `cata/nvalues.tex`"                    -> nvalues: nvalue
#   - "`cata/among.tex`"                                  -> among: among
#   - "`cata/range.tex` and `cata/roots.tex` ... match
#      the repo's set-variable formulation" of MiniZinc's
#      `range`/`roots` globals                            -> range: range, roots: roots
#   - "already exists in `cata/regular.tex`"              -> regular: regular
#   - the repo's own `table` entry ... currently emits
#     an unsound empty-premise rule                       -> table: table
#   - `cata/increasing.tex` and `cata/decreasing.tex`      -> identity
#   - `cata/element.tex` generates 6 rules                -> element: element
#   - `cata/allequal.tex`                                  -> allequal: all_equal
#   - `all_different`'s Hall-set discussion cites the
#     repo's `alldifferent` entry throughout               -> alldifferent: all_different
#   - `gcc` entry documents ONLY the plain form (see
#     catalog/gcc.md's Gaps: `_low_up` is G4, out of
#     reach) -- do not fan this out to the five
#     `global_cardinality*` siblings, that would flatter
#     the index                                            -> gcc: global_cardinality
ALIAS = {
    "alldifferent": "all_different",
    "allequal": "all_equal",
    "among": "among",
    "cumulative": "cumulative",
    "decreasing": "decreasing",
    "element": "element",
    "gcc": "global_cardinality",
    "increasing": "increasing",
    "nvalues": "nvalue",
    "range": "range",
    "regular": "regular",
    "roots": "roots",
    "table": "table",
    # No release global matches these -- gccat constraints / an orphan, not
    # MiniZinc 2.10.1 globals under any spelling checked against
    # tools/data/minizinc-2.10.1-globals.txt. Recorded explicitly (None) so
    # catalog_index.py prints them as unmatched rather than dropping them.
    "atleastnvalues": None,   # gccat's atleast_nvalue; no MiniZinc global of that name
    "atmostnvalues": None,    # gccat's atmost_nvalue; no MiniZinc global of that name
    "sum": None,              # orphaned (nothing generates it, CLAUDE.md); ambiguous
                               # between the release's sum_pred and sum_set even if it
                               # were live
}

TIER_KEYS = [
    "A no-literature + solver-decomposes",
    "B no-literature + solver-native",
    "C literature + solver-decomposes",
    "D literature + solver-native",
    "- unclassified",
    "- out of scope",
]
TIER_LABEL = {
    "A no-literature + solver-decomposes": "A",
    "B no-literature + solver-native": "B",
    "C literature + solver-decomposes": "C",
    "D literature + solver-native": "D",
    "- unclassified": "unclassified",
    "- out of scope": "out of scope",
}

GAP_RE = re.compile(r"blocked on\s+(G\d+)", re.I)
FRAC_RE = re.compile(r"\\frac")

VALIDATE_ENTRY_RE = re.compile(
    r"^---- cata/(\S+)\.tex\s+\((\d+) rules?\) ----\s*$"
)
VALIDATE_OOS_RE = re.compile(
    r"^\s*cata/(\S+)\.tex\s+\((\d+) rules?,\s*(.*?)\)\s*$"
)
VALIDATE_VERDICT_RE = re.compile(r"VERDICT\s*:\s*(.+)$")


def run(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, cwd=REPO, **kw)


# --------------------------------------------------------------------------
# Sources
# --------------------------------------------------------------------------

def load_ranking():
    """global -> tier key, from tools/mzn_coverage.py --json."""
    out_path = os.path.join(REPO, "_build", "catalog_index_coverage.json")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    proc = run([sys.executable, MZN_COVERAGE, "--json", out_path, "--rank"])
    if proc.returncode not in (0, 1):
        # --check is not passed, so mzn_coverage.py itself returns 0; a
        # nonzero here means it actually crashed.
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
        raise SystemExit("tools/mzn_coverage.py failed (exit %d)" % proc.returncode)
    with open(out_path, encoding="utf-8") as fh:
        data = json.load(fh)
    result = data["result"]
    tier_of = {}
    for tier_key in TIER_KEYS:
        for entry in result["ranking"].get(tier_key, []):
            tier_of[entry["global"]] = tier_key
    return tier_of, result["release_count"], data["provenance"]


def list_catalog_entries():
    """basename (no .md) -> path, for real entries only."""
    entries = {}
    for name in sorted(os.listdir(CATALOG_DIR)):
        path = os.path.join(CATALOG_DIR, name)
        if name in CATALOG_NON_ENTRIES or name in CATALOG_NON_ENTRY_DIRS:
            continue
        if os.path.isdir(path):
            continue
        if not name.endswith(".md"):
            continue
        entries[name[:-3]] = path
    return entries


def list_cata_files():
    """basename (no .tex) -> path."""
    out = {}
    for name in sorted(os.listdir(CATA_DIR)):
        if name.endswith(".tex"):
            out[name[:-4]] = os.path.join(CATA_DIR, name)
    return out


def count_frac(path):
    with open(path, encoding="utf-8", errors="replace") as fh:
        content = fh.read()
    return len(FRAC_RE.findall(content))


def find_blocking_gap(md_path):
    with open(md_path, encoding="utf-8", errors="replace") as fh:
        content = fh.read()
    m = GAP_RE.search(content)
    return m.group(1) if m else None


def is_stub(md_path):
    """True if this catalog/*.md carries tools/catalog_stub.py's marker.

    Existence of a file is NOT evidence that a constraint has been looked at:
    106 of the 118 entries are machine-filled stubs whose every judgement
    field reads "not reviewed". This predicate is the only thing separating
    them from an entry a person wrote, so the index reports both numbers and
    never a bare total.
    """
    with open(md_path, encoding="utf-8", errors="replace") as fh:
        return STUB_MARKER in fh.read()


def get_validate_output(saved_log=None):
    if saved_log:
        with open(saved_log, encoding="utf-8", errors="replace") as fh:
            return fh.read()
    log_path = os.path.join(REPO, "_build", "catalog_index_validate.log")
    os.makedirs(os.path.dirname(log_path), exist_ok=True)
    proc = run(["make", "validate"])
    with open(log_path, "w", encoding="utf-8") as fh:
        fh.write(proc.stdout)
        fh.write(proc.stderr)
    if proc.returncode == 2:
        sys.stderr.write(
            "warning: `make validate` reported its own self-test/cross-check "
            "as broken (exit 2) -- validated counts below are not trustworthy; "
            "see %s\n" % log_path
        )
    return proc.stdout + proc.stderr


def parse_validate(text):
    """cata basename -> dict(rules, sound_minimal, verdicts, out_of_scope, reason)."""
    out = {}
    lines = text.splitlines()
    i = 0
    n = len(lines)
    while i < n:
        m = VALIDATE_ENTRY_RE.match(lines[i])
        if m:
            base, nrules = m.group(1), int(m.group(2))
            verdicts = []
            i += 1
            while i < n and not lines[i].startswith("----") and "== out of scope" not in lines[i]:
                vm = VALIDATE_VERDICT_RE.search(lines[i])
                if vm:
                    verdicts.append(vm.group(1).strip())
                i += 1
            sound = sum(1 for v in verdicts if v.startswith("SOUND and MINIMAL"))
            out[base] = {
                "rules": nrules,
                "sound_minimal": sound,
                "verdicts": verdicts,
                "out_of_scope": False,
                "reason": None,
            }
            continue
        if "== out of scope:" in lines[i]:
            i += 1
            while i < n and not lines[i].startswith("=="):
                om = VALIDATE_OOS_RE.match(lines[i])
                if om:
                    base, nrules, note = om.group(1), int(om.group(2)), om.group(3)
                    reason = None
                    j = i + 1
                    while j < n and lines[j].strip() and not lines[j].startswith("  cata/"):
                        stripped = lines[j].strip()
                        if stripped.startswith("reason:"):
                            reason = stripped[len("reason:"):].strip()
                            break
                        j += 1
                    out[base] = {
                        "rules": nrules,
                        "sound_minimal": 0,
                        "verdicts": [],
                        "out_of_scope": True,
                        "reason": reason or note,
                    }
                i += 1
            continue
        i += 1
    return out


# --------------------------------------------------------------------------
# Assembly
# --------------------------------------------------------------------------

def build(validate_log=None):
    tier_of, release_count, coverage_provenance = load_ranking()
    catalog_entries = list_catalog_entries()
    cata_files = list_cata_files()
    validate_data = parse_validate(get_validate_output(validate_log))

    # reverse alias: global -> basename, for every alias that resolves
    global_to_base = {g: b for b, g in ALIAS.items() if g is not None}

    # Identity resolution. A basename that IS a release global, spelled
    # exactly, needs no ALIAS row: tools/catalog_stub.py names every stub
    # after the release global, and 106 identity rows would drown the table.
    # ALIAS keeps doing the one job a script cannot do -- the names that
    # genuinely differ (alldifferent -> all_different) and the three
    # deliberate UNMATCHED rows.
    known_bases = set(cata_files) | set(catalog_entries)
    for base in sorted(known_bases):
        if base not in ALIAS and base in tier_of:
            global_to_base.setdefault(base, base)

    warnings = []
    for base in sorted(known_bases):
        if base in tier_of and base not in ALIAS:
            continue  # resolved by identity, above
        if base not in ALIAS:
            warnings.append(
                "no alias entry at all for basename %r (add it to ALIAS in "
                "tools/catalog_index.py)" % base
            )
        elif ALIAS[base] is None:
            warnings.append(
                "UNMATCHED: %r has no corresponding release global (see ALIAS "
                "comment for why)" % base
            )
        elif ALIAS[base] not in tier_of:
            warnings.append(
                "ALIAS maps %r -> %r, but %r is not a release global in "
                "tools/mzn_coverage.py's ranking (typo?)" % (base, ALIAS[base], ALIAS[base])
            )

    rows = []
    for tier_key in TIER_KEYS:
        entries = sorted(tier_of_entries(tier_of, tier_key))
        for global_name in entries:
            base = global_to_base.get(global_name)
            catalog_path = catalog_entries.get(base) if base else None
            cata_path = cata_files.get(base) if base else None

            generated = None
            if cata_path:
                generated = count_frac(cata_path)

            vdata = validate_data.get(base) if base else None
            if vdata is None:
                validated = None
                val_note = None
            elif vdata["out_of_scope"]:
                validated = None
                reason = vdata["reason"]
                if reason:
                    reason = reason.replace("|", "/")
                    if len(reason) > 70:
                        reason = reason[:67] + "..."
                    val_note = "out of scope: %s" % reason
                else:
                    val_note = "out of scope"
            else:
                validated = vdata["sound_minimal"]
                val_note = "%d/%d sound+minimal" % (vdata["sound_minimal"], vdata["rules"])

            gap = find_blocking_gap(catalog_path) if catalog_path else None
            stub = is_stub(catalog_path) if catalog_path else False

            rows.append({
                "global": global_name,
                "tier": tier_key,
                "base": base,
                "catalog_path": catalog_path,
                "stub": stub,
                "generated": generated,
                "validated": validated,
                "val_note": val_note,
                "gap": gap,
            })

    return rows, tier_of, release_count, coverage_provenance, warnings, catalog_entries, cata_files


def tier_of_entries(tier_of, tier_key):
    return [g for g, t in tier_of.items() if t == tier_key]


def render(rows, release_count, coverage_provenance, warnings, catalog_entries, cata_files, cmd_line, when):
    have_entry = sum(1 for r in rows if r["catalog_path"])
    reviewed = sum(1 for r in rows if r["catalog_path"] and not r["stub"])
    stubs = sum(1 for r in rows if r["catalog_path"] and r["stub"])
    have_generated = sum(1 for r in rows if r["generated"] not in (None, 0))
    have_validated = sum(1 for r in rows if r["validated"] not in (None, 0))

    by_tier_entry = {}
    by_tier_reviewed = {}
    by_tier_stub = {}
    by_tier_generated = {}
    by_tier_validated = {}
    by_tier_total = {}
    for r in rows:
        t = r["tier"]
        by_tier_total[t] = by_tier_total.get(t, 0) + 1
        if r["catalog_path"]:
            by_tier_entry[t] = by_tier_entry.get(t, 0) + 1
            if r["stub"]:
                by_tier_stub[t] = by_tier_stub.get(t, 0) + 1
            else:
                by_tier_reviewed[t] = by_tier_reviewed.get(t, 0) + 1
        if r["generated"] not in (None, 0):
            by_tier_generated[t] = by_tier_generated.get(t, 0) + 1
        if r["validated"] not in (None, 0):
            by_tier_validated[t] = by_tier_validated.get(t, 0) + 1

    L = []
    w = L.append
    w("<!--")
    w("  catalog/INDEX.md -- GENERATED. Do not hand-edit.")
    w("  Regenerate with: %s" % cmd_line)
    w("  Generated: %s" % when)
    w("  Source: tools/catalog_index.py (reads tools/mzn_coverage.py --json,")
    w("  catalog/*.md, cata/*.tex, and `make validate`'s output; see that")
    w("  script's ALIAS table for the cata/catalog basename <-> MiniZinc")
    w("  global-name mapping).")
    w("-->")
    w("")
    w("# Catalog index")
    w("")
    w("One row per MiniZinc release global (%d total, from "
      "`tools/mzn_coverage.py`, release %s). Every count below is computed on"
      % (release_count, coverage_provenance.get("version", "unknown")))
    w("every regeneration, never hand-typed -- see the header comment for how.")
    w("")
    w("## Summary")
    w("")
    w("- catalog entries: **%d / %d** (%d reviewed, %d stubs)"
      % (have_entry, release_count, reviewed, stubs))
    w("  A **stub** is a file `tools/catalog_stub.py` generated: it carries a")
    w("  machine-derived tier, citation line, solver class and rule count, and")
    w("  the words `not reviewed` in every field that would be a judgement.")
    w("  A **reviewed** entry is one a person wrote against `catalog/TEMPLATE.md`.")
    w("  **The entry count is never printed without this split** -- %d / %d with"
      % (have_entry, release_count))
    w("  %d of them stubs is a claim about filenames, not about work done."
      % stubs)
    w("- have any generated rule (`cata/*.tex`, `\\frac` count > 0): **%d / %d**"
      % (have_generated, release_count))
    w("- have any validated (SOUND and MINIMAL) rule: **%d / %d**"
      % (have_validated, release_count))
    w("")
    w("| tier | globals | entries | reviewed | stubs | generated rules | validated |")
    w("|---|---:|---:|---:|---:|---:|---:|")
    for t in TIER_KEYS:
        total = by_tier_total.get(t, 0)
        w("| %s | %d | %d | %d | %d | %d | %d |" % (
            TIER_LABEL[t], total,
            by_tier_entry.get(t, 0),
            by_tier_reviewed.get(t, 0),
            by_tier_stub.get(t, 0),
            by_tier_generated.get(t, 0),
            by_tier_validated.get(t, 0),
        ))
    w("")
    if warnings:
        w("## Warnings from this run")
        w("")
        for msg in warnings:
            w("- %s" % msg)
        w("")

    w("## All %d globals" % release_count)
    w("")
    w("| constraint | tier | catalog entry | kind | generated rules | validated | blocking gap |")
    w("|---|---|---|---|---:|---:|---|")
    for r in rows:
        constraint = "`%s`" % r["global"]
        tier = TIER_LABEL[r["tier"]]
        if r["catalog_path"]:
            entry_cell = "[%s](%s)" % (r["base"], os.path.basename(r["catalog_path"]))
        else:
            entry_cell = "—"
        if not r["catalog_path"]:
            kind_cell = "—"
        elif r["stub"]:
            kind_cell = "**stub**"
        else:
            kind_cell = "reviewed"
        generated_cell = "—" if r["generated"] is None else str(r["generated"])
        if r["validated"] is None:
            validated_cell = r["val_note"] if r["val_note"] else "—"
        else:
            validated_cell = str(r["validated"])
        gap_cell = r["gap"] if r["gap"] else "—"
        w("| %s | %s | %s | %s | %s | %s | %s |" % (
            constraint, tier, entry_cell, kind_cell, generated_cell,
            validated_cell, gap_cell))
    w("")
    w("## What this index cannot show")
    w("")
    w("- **Whether a rule is right**, only whether the validator called it SOUND")
    w("  and MINIMAL at n,m <= 4 (`docs/VALIDATOR.md`). Sound and minimal is a")
    w("  floor, not strength -- see CLAUDE.md.")
    w("- **Calibration against a published rule** (agrees/weaker/stronger/")
    w("  incomparable/out of reach) -- that verdict lives in each entry's own")
    w("  \"Calibration\" field and is not re-derived here.")
    w("- **Anything about a stub beyond the machine-derived fields it")
    w("  carries.** A `**stub**` row means a file exists holding a tier, a")
    w("  `CHRISTMAS_LIST.md` line number, a solver class and a `\\frac` count.")
    w("  It also means nobody has read the constraint. The entry column is not")
    w("  progress unless the kind column beside it says `reviewed`.")
    w("- **Entries that exist only as a claim.** This script trusts the")
    w("  filesystem (`catalog/*.md` existing) and `make validate`'s own output;")
    w("  it does not read entry prose for correctness.")
    w("- **A blocking gap for an entry that has no catalog/*.md yet.** The")
    w("  \"blocking gap\" column is only populated by grepping an *existing*")
    w("  entry for the phrase \"blocked on G<n>\"; a missing entry always shows")
    w("  — in that column even if a gap is already known informally.")
    w("  **And a stub never states one**, by design -- attributing a gap is a")
    w("  judgement -- so the column is empty for every one of them, whatever")
    w("  may already be known informally.")
    w("")
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                  formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true", help="print, don't write catalog/INDEX.md")
    ap.add_argument("--validate-log", metavar="FILE",
                    help="reuse a saved `make validate` log instead of re-running it")
    args = ap.parse_args(argv)

    rows, tier_of, release_count, coverage_provenance, warnings, catalog_entries, cata_files = \
        build(args.validate_log)

    when = datetime.date.today().isoformat()
    cmd_line = "python3 tools/catalog_index.py"
    text = render(rows, release_count, coverage_provenance, warnings,
                  catalog_entries, cata_files, cmd_line, when)

    for msg in warnings:
        sys.stderr.write("warning: %s\n" % msg)

    if args.dry_run:
        print(text)
    else:
        with open(INDEX_PATH, "w", encoding="utf-8") as fh:
            fh.write(text)
        sys.stderr.write("wrote %s\n" % INDEX_PATH)

    return 0


if __name__ == "__main__":
    sys.exit(main())
