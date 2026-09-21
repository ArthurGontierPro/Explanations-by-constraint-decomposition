#!/usr/bin/env python3
"""catalog_stub.py -- write a machine-filled `catalog/<name>.md` for every
MiniZinc release global that has no catalog entry yet.

The catalog's target is one entry per release global. Writing 118 entries by
hand is wave upon wave of work; claiming 118/118 because 118 files exist would
be a lie. This script takes the third option: it generates the *mechanical*
part of an entry -- the part a person would otherwise retype out of
`tools/mzn_coverage.py` and `CHRISTMAS_LIST.md` -- and marks every remaining
field `not reviewed`, loudly, at the top of the file.

**A stub states no judgement.** No status-legend value, no blocking gap, no
calibration verdict, no "probably E2". Those are review work, and a stub that
guessed one would be worse than a stub that says nothing, because a later
reader cannot tell a guess from a finding. What a stub may carry is exactly
what a script can derive and cite:

  * the priority tier                -- tools/mzn_coverage.py's ranking
  * literature present/absent,
    solver class, E-code route       -- the CHRISTMAS_LIST.md row, QUOTED
                                        VERBATIM with its line number
  * the name's provenance            -- tools/data/minizinc-*-globals.txt:<line>
  * a link to decomps/<name>.md      -- if that spec exists
  * the cata/<name>.tex rule count   -- occurrences of the literal "\\frac",
                                        never `grep -c` and never `wc -l`
                                        (CLAUDE.md, "Traps")

Re-running is safe. A file that does NOT carry STUB_MARKER is never written to
-- that is how a stub someone has since reviewed (and de-marked) survives, and
the run reports how many files it skipped for that reason. A file that does
carry the marker is rewritten only if its content actually changed; the
generation date alone does not count as a change, so a second run on a later
day is still a no-op.

Sources are reused, not re-implemented: `tools/mzn_coverage.py` is imported for
the release list, the CHRISTMAS_LIST.md parse and the ranking, and
`tools/catalog_index.py` for the basename <-> global-name ALIAS map and for
STUB_MARKER itself. Nothing here re-parses either file.

Usage:
    python3 tools/catalog_stub.py                 # write the missing stubs
    python3 tools/catalog_stub.py --dry-run       # report, write nothing
    python3 tools/catalog_stub.py --only NAME     # one global (repeatable)

No network access. Python 3 standard library only.
"""

from __future__ import annotations

import argparse
import datetime
import os
import re
import sys

TOOLS = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(TOOLS)
if TOOLS not in sys.path:
    sys.path.insert(0, TOOLS)

import mzn_coverage                                  # noqa: E402
from catalog_index import ALIAS, STUB_MARKER, TIER_LABEL, count_frac  # noqa: E402

CATALOG_DIR = os.path.join(REPO, "catalog")
CATA_DIR = os.path.join(REPO, "cata")
DECOMPS_DIR = os.path.join(REPO, "decomps")
LITERATURE_DIR = os.path.join(CATALOG_DIR, "_literature")
CHRISTMAS_LIST = os.path.join(REPO, "CHRISTMAS_LIST.md")

GEN_CMD = "python3 tools/catalog_stub.py"
DATE_RE = re.compile(r"\d{4}-\d{2}-\d{2}")

# The one thing in a stub that changes for no reason: the date it was made.
# Normalised away before comparing an existing stub with a freshly rendered
# one, so that "re-run it tomorrow" is still a no-op. Stubs contain no other
# dates -- every date in one is written by this script.
def undated(text):
    return DATE_RE.sub("@@DATE@@", text)


# --------------------------------------------------------------------------
# sources (all read through the existing tools, never re-parsed here)
# --------------------------------------------------------------------------

def load_sources():
    snapshot = mzn_coverage.newest_snapshot()
    if not snapshot:
        raise SystemExit("no globals snapshot under tools/data/")
    names = mzn_coverage.read_globals_from_snapshot(snapshot)
    rows = mzn_coverage.parse_list(CHRISTMAS_LIST)
    result = mzn_coverage.classify(names, rows)
    row_by_line = {r.line: r for r in rows}

    # global -> its ranking entry (tier key, ecodes, section, CHRISTMAS line)
    entry_of = {}
    tier_of = {}
    for tier_key, entries in result["ranking"].items():
        for e in entries:
            entry_of[e["global"]] = e
            tier_of[e["global"]] = tier_key

    # global -> line number in the vendored snapshot, for the name's provenance
    snap_line = {}
    with open(snapshot, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            s = line.strip()
            if s and not s.startswith("#"):
                snap_line[s] = lineno

    return {
        "snapshot": snapshot,
        "snapshot_rel": os.path.relpath(snapshot, REPO),
        "snap_line": snap_line,
        "release": names,
        "rows": rows,
        "row_by_line": row_by_line,
        "entry_of": entry_of,
        "tier_of": tier_of,
        "result": result,
    }


def base_of_global(name, tier_of):
    """The catalog/ and cata/ basename for a release global.

    ALIAS (owned by tools/catalog_index.py) for the names that differ --
    `all_different` is filed as `alldifferent` -- identity otherwise, which is
    what every stub this script writes uses.
    """
    for base, g in ALIAS.items():
        if g == name:
            return base
    return name


# --------------------------------------------------------------------------
# the mechanical readings of a CHRISTMAS_LIST.md row
# --------------------------------------------------------------------------

def solver_breakdown(cell):
    """Chuffed / Geas / Choco, from the solver cell and the legend alone.

    Legend, CHRISTMAS_LIST.md:106-109: `native` = explaining propagator in
    Chuffed, `decomp` = solved by decomposition; Geas natives are **[G]**,
    Choco LCG natives **[C]**, Choco LCG failures **[C<mark>]**. Nothing here
    is inferred beyond those four tokens.
    """
    chuffed = mzn_coverage.classify_solver(cell)
    m = re.search(r"native\s*\(`([^`]+)`\)", cell)
    if m:
        chuffed = "native (`%s`)" % m.group(1)
    geas = "`[G]` present" if "[G]" in cell else "absent"
    cm = re.search(r"\[C([^\]]*)\]", cell)
    if cm is None:
        choco = "absent"
    elif cm.group(1) == "":
        choco = "`[C]` present"
    else:
        choco = "`[C%s]` failure" % cm.group(1)
    return chuffed, geas, choco


def quote_block(text):
    """A verbatim cell as a markdown blockquote; empty cells say so."""
    text = (text or "").strip()
    if not text:
        return "> *(the cell is empty)*"
    return "> " + text


# --------------------------------------------------------------------------
# the stub itself
# --------------------------------------------------------------------------

def render_stub(name, src, today):
    entry = src["entry_of"][name]
    tier_key = src["tier_of"][name]
    row = src["row_by_line"][entry["line"]]
    cl = "CHRISTMAS_LIST.md:%d" % entry["line"]
    base = base_of_global(name, src["tier_of"])

    snap_ref = "%s:%s" % (src["snapshot_rel"], src["snap_line"].get(name, "?"))
    release = re.search(r"minizinc-([0-9.]+)-globals", os.path.basename(src["snapshot"]))
    release = release.group(1) if release else "unknown"

    tex_rel = "cata/%s.tex" % base
    tex_path = os.path.join(CATA_DIR, "%s.tex" % base)
    has_tex = os.path.isfile(tex_path)
    frac = count_frac(tex_path) if has_tex else None

    spec_rel = "decomps/%s.md" % name
    has_spec = os.path.isfile(os.path.join(DECOMPS_DIR, "%s.md" % name))

    lit_rel = "catalog/_literature/%s.md" % base
    has_lit_file = os.path.isfile(os.path.join(LITERATURE_DIR, "%s.md" % base))

    chuffed, geas, choco = solver_breakdown(row.solver)
    lit_class = entry["literature"]
    ecodes = ", ".join("`%s`" % c for c in entry["ecodes"]) or "*(none parsed from the route cell)*"

    if has_tex:
        generated_cell = ("%d rules in `%s` — counted, not reviewed"
                          % (frac, tex_rel))
    else:
        generated_cell = "no generator entry — there is no `%s`" % tex_rel

    L = []
    w = L.append
    w("<!-- %s. Machine-generated by %s; see the banner below. -->" % (STUB_MARKER, GEN_CMD))
    w("")
    w("# `%s`" % name)
    w("")
    w("> **%s.**" % STUB_MARKER)
    w("> Generated %s by `%s`." % (today, GEN_CMD))
    w("> Every field below is machine-derived and names the source it came from. Every")
    w("> field that would take judgement reads `not reviewed`, and that means **nobody has")
    w("> read this constraint** — not that there is nothing to say about it. This file")
    w("> exists so the catalog's denominator is honest; it is **not** evidence of work on")
    w("> `%s`, and `catalog/INDEX.md` counts stubs and reviewed entries" % name)
    w("> separately for that reason.")
    w("> **To upgrade it:** edit in place against `catalog/TEMPLATE.md` — the headings")
    w("> below are already in template order — and delete this banner. Deleting the")
    w("> banner is also what stops `%s` from ever rewriting the file." % GEN_CMD)
    w("")
    w("> **This entry lists the rules this method generated for the events it was asked to")
    w("> explain. It is not a list of all valid explanations of `%s`," % name)
    w("> and no claim of that kind is made anywhere in this catalog.** See")
    w('> `catalog/README.md`, "What the catalog claims".')
    w("")
    w("| | |")
    w("|---|---|")
    w("| **Tier** | **%s** (`%s`) — `python3 tools/mzn_coverage.py --rank` |"
      % (TIER_LABEL[tier_key], tier_key))
    w("| **Status** | `not reviewed` — no status-legend value has been assigned |")
    w("| **Generated** | %s |" % generated_cell)
    w("| **Validator** | `not reviewed` — `make validate` has not been run for this entry |")
    w("| **Calibration** | `not reviewed` |")
    w("| **Last measured** | %s, `%s` — machine-derived fields only; nothing here was validated |"
      % (today, GEN_CMD))
    w("")
    w("## Constraint")
    w("")
    w("`not reviewed` — no MiniZinc signature is vendored in this repo.")
    w("")
    w("**Provenance of the name:** `%s` lists `%s` as a global of" % (snap_ref, name))
    w("MiniZinc %s; that snapshot carries names only, never signatures." % release)
    w("`%s` files it under section `%s`." % (cl, entry["section"]))
    w("")
    w("## Published explanation")
    w("")
    if lit_class == "none":
        w("**Literature: absent.** The literature column of `%s` reads, verbatim:" % cl)
    elif lit_class == "cited":
        w("**Literature: present.** The literature column of `%s` reads, verbatim:" % cl)
    else:
        w("**Literature: unspecified** — the column is blank or a dash. Verbatim:")
    w("")
    w(quote_block(row.lit))
    w("")
    w("That is a quote of the list, not a reading of a paper: nothing has been fetched,")
    w("nothing has been read, and this stub makes no statement about any paper's content.")
    w("")
    if has_lit_file:
        w("**Rule shape:** a sourced shape exists at [`%s`](_literature/%s.md) — **`not"
          % (lit_rel, base))
        w("reviewed` here.** No sentence of it has been read into this file.")
    else:
        w("**Rule shape:** `pending C2` — there is no `%s`, so no" % lit_rel)
        w("published rule shape is stated here. (`catalog/TEMPLATE.md`: never write one")
        w("from memory.)")
    w("")
    w("## Solver support")
    w("")
    w("| | |")
    w("|---|---|")
    w("| Chuffed | %s |" % chuffed)
    w("| Geas | %s |" % geas)
    w("| Choco LCG | %s |" % choco)
    w("")
    w("Derived mechanically from the solver column of `%s`, which reads, verbatim:" % cl)
    w("")
    w(quote_block(row.solver))
    w("")
    w("Legend: `CHRISTMAS_LIST.md:106-109`. The table above is a `native`/`decomp` keyword")
    w("match plus the `[G]`/`[C]` markers and nothing else; anything the legend does not")
    w("cover is not represented.")
    w("")
    w("## Decomposition used here")
    w("")
    w("**Generator value:** `not reviewed` — no value in `explenation generator.ml` has")
    if has_tex:
        w("been identified for this entry here, although `%s` exists (see below)." % tex_rel)
    else:
        w("been identified, and nothing under `cata/` is emitted under this name.")
    w("**Emitted by:** `not reviewed`")
    if has_spec:
        w("**Spec:** [`%s`](../%s) — exists, **not read by this stub**." % (spec_rel, spec_rel))
    else:
        w("**Spec:** none — this constraint has no `%s`." % spec_rel)
    w("")
    w("`not reviewed` — the schema chain is review work: it takes reading the")
    w("decomposition and saying what it actually encodes, which is exactly the judgement a")
    w("stub must not fake.")
    w("")
    w("## Scope of this entry")
    w("")
    w("**Events the generator was asked to explain:** `not reviewed`.")
    w("")
    if has_tex:
        w("`%s` exists and its `%%%% generator diagnostics (W1-T3)` footer has **not** been"
          % tex_rel)
        w("read. Until it is, this entry does not state which events were asked for, how many")
        w("candidates each had, or what was dropped.")
    else:
        w("There is no `%s`, so there is no `%%%% generator diagnostics (W1-T3)`" % tex_rel)
        w("footer to read and no event list to state.")
    w("")
    w("## Generated rules")
    w("")
    if has_tex:
        w("**%d rules** in `%s`, counted with `grep -o '\\frac' %s | wc -l`"
          % (frac, tex_rel, tex_rel))
        w("(`grep -c` returns 1 for every entry — CLAUDE.md, \"Traps\").")
        w("")
        w("`not reviewed` — the rules are **not rendered here**. Rendering one means")
        w("reading its premises and conclusion off the LaTeX, and this stub has not done it.")
    else:
        w("**no generator entry** — there is no `%s`, so this method has" % tex_rel)
        w("generated nothing for this constraint. Whether that is a gap, a missing")
        w("decomposition or a constraint out of scope is `not reviewed`.")
    w("")
    w("## Status")
    w("")
    w("**`not reviewed`**")
    w("")
    w("No value from `catalog/README.md`'s status legend has been assigned, deliberately:")
    w("all six are verdicts, and this file states none. In particular this is **not**")
    w("`generated, unvalidated` and **not** a claim that anything is blocked — those are")
    w("findings, and nobody has looked.")
    w("")
    w("## Calibration (W3-T5, D-0013)")
    w("")
    w("**Verdict:** `not reviewed` — no comparison against a published rule has been")
    w("attempted. Note that `no published rule exists` is itself a verdict and is **not**")
    w("being claimed here, even where the literature column above reads `none`.")
    w("")
    w("## Gaps")
    w("")
    w("| gap | what it blocks here |")
    w("|---|---|")
    w("| `not reviewed` | no gap has been attributed to this constraint |")
    w("")
    w("**E-code route, quoted from `%s`** — this is the list's own routing" % cl)
    w("note, carried across verbatim, and not a verdict of this catalog:")
    w("")
    w(quote_block(row.route))
    w("")
    w("E-codes parsed out of that cell by `tools/mzn_coverage.py`: %s." % ecodes)
    w("Source: `docs/DECOMP_FORMAT_NOTES.md` for what the numbered gaps mean; no gap from it")
    w("has been applied here.")
    w("")
    w("## How this entry was produced")
    w("")
    w("- `%s`, %s — this entire file, in one pass." % (GEN_CMD, today))
    w("- `tools/mzn_coverage.py` (imported, not shelled out) → the release global list, the")
    w("  priority tier `%s`, and the `CHRISTMAS_LIST.md` row for this name." % tier_key)
    w("- `%s` read → the name and the release it ships in." % snap_ref)
    w("- `%s` read → the literature, solver and route cells quoted above, verbatim." % cl)
    w("- `os.path.isfile(\"%s\")` → %s." % (spec_rel, has_spec))
    if has_tex:
        w("- `grep -o '\\frac' %s | wc -l` (as a count of the literal string, in-process)"
          % tex_rel)
        w("  → %d." % frac)
    else:
        w("- `os.path.isfile(\"%s\")` → False." % tex_rel)
    w("- Nothing was compiled, run, validated or judged. There is no verdict anywhere in")
    w("  this file, because there is no reviewed claim in it to attach one to.")
    w("")
    return "\n".join(L)


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true",
                    help="report what would be written; write nothing")
    ap.add_argument("--only", metavar="GLOBAL", action="append", default=[],
                    help="restrict to this release global (repeatable)")
    args = ap.parse_args(argv)

    src = load_sources()
    today = datetime.date.today().isoformat()

    created, refreshed, unchanged, skipped_not_stub = [], [], [], []
    no_row = []

    for name in sorted(src["release"]):
        if args.only and name not in args.only:
            continue
        if name not in src["entry_of"]:
            # A release global with no CHRISTMAS_LIST.md row at all: every
            # quoted field would be missing, so no stub is written and the
            # drift is reported instead (tools/mzn_coverage.py --check is the
            # tool that owns that failure).
            no_row.append(name)
            continue

        base = base_of_global(name, src["tier_of"])
        existing = os.path.join(CATALOG_DIR, "%s.md" % base)
        target = os.path.join(CATALOG_DIR, "%s.md" % name)

        if os.path.isfile(existing) or os.path.isfile(target):
            path = existing if os.path.isfile(existing) else target
            with open(path, encoding="utf-8", errors="replace") as fh:
                old = fh.read()
            if STUB_MARKER not in old:
                skipped_not_stub.append(os.path.relpath(path, REPO))
                continue
            text = render_stub(name, src, today)
            if undated(old) == undated(text):
                unchanged.append(os.path.relpath(path, REPO))
                continue
            if not args.dry_run:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)
            refreshed.append(os.path.relpath(path, REPO))
            continue

        text = render_stub(name, src, today)
        if not args.dry_run:
            with open(target, "w", encoding="utf-8") as fh:
                fh.write(text)
        created.append(os.path.relpath(target, REPO))

    out = sys.stdout
    if args.dry_run:
        out.write("DRY RUN -- nothing written\n")
    out.write("stubs created ................. %d\n" % len(created))
    out.write("stubs refreshed (content moved) %d\n" % len(refreshed))
    out.write("stubs already current ......... %d\n" % len(unchanged))
    out.write("skipped, not a stub ........... %d  "
              "(no %s marker: a reviewed entry, never overwritten)\n"
              % (len(skipped_not_stub), STUB_MARKER))
    for p in skipped_not_stub:
        out.write("    %s\n" % p)
    if no_row:
        out.write("NO CHRISTMAS_LIST.md ROW ...... %d  (no stub written)\n" % len(no_row))
        for n in no_row:
            out.write("    %s\n" % n)
    return 0


if __name__ == "__main__":
    sys.exit(main())
