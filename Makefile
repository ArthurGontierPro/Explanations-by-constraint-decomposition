# Makefile — the wave-zero gate (W0-T2 + W0-T3) and the validator (W0-T1).
#
# There was no build system before this file and there still need not be one:
# `ocaml 'explenation generator.ml'` is a complete build. What was missing is a
# *gate* — something that fails when the generator stops reproducing the
# committed catalog. That is what `make check` is.
#
# Environment: OCaml 5.1.1 lives in the opam switch `baguette`, which is NOT on
# the default PATH. `which ocaml` returning nothing in a non-interactive shell is
# not evidence that OCaml is absent. Every recipe below sources the switch.

SWITCH   := baguette
OPAMENV  := eval $$(opam env --switch=$(SWITCH) --set-switch) &&
GEN      := explenation generator.ml
BUILDDIR := _build
GENDIR   := $(BUILDDIR)/gen
WARNDIR  := $(BUILDDIR)/warn

# cata/sum.tex is EXCLUDED from the golden diff, deliberately.
#
# It is orphaned: nothing in the generator's `main` produces it, so a run in a
# clean directory cannot emit it and a byte-diff of the whole tree will always
# report it as missing. Deleting or regenerating it is W1-T6 and belongs to the
# rule-engine session, not to this gate. The exclusion is therefore a *recorded*
# exception, not a silenced failure: `make check` prints it every run, and
# `make check-orphans` fails if the set of orphans ever changes (i.e. if a
# second file goes orphaned, or if sum.tex acquires a producer and this
# exclusion becomes stale).
ORPHANS := sum.tex

.PHONY: check check-golden check-orphans check-warnings validate validate-selftest coverage clean help

help:
	@echo "make check          — the gate: golden-file diff + orphan check + warning census"
	@echo "make check-golden   — regenerate cata/*.tex in a scratch dir and byte-diff"
	@echo "make check-orphans  — fail if the set of orphaned cata/*.tex changed"
	@echo "make check-warnings — census of compiler warnings (reports, never fails)"
	@echo "make validate       — run the validator (11 entries checked, 5 out of scope; docs/VALIDATOR.md)"
	@echo "make validate-selftest — just the validator's own positive/negative controls"
	@echo "make coverage       — MiniZinc coverage drift (advisory, W0-B)"
	@echo "make clean          — remove $(BUILDDIR)"

check: check-golden check-orphans check-warnings
	@echo ""
	@echo "GATE PASSED. Note this gate proves REPRODUCIBILITY, not correctness:"
	@echo "a .tex that regenerates byte-identically is still 'generated, unvalidated'."
	@echo "For correctness of the three in-scope entries, run: make validate"

# ---------------------------------------------------------------------------
# W0-T3 — golden files.
# The generator writes cata/*.tex RELATIVE TO THE CWD, so it is run in a scratch
# directory and the result is diffed against the committed tree. exp.tex is
# written to the cwd too and is diffed as well.
# ---------------------------------------------------------------------------
check-golden:
	@rm -rf $(GENDIR)
	@mkdir -p $(GENDIR)/cata
	@$(OPAMENV) cd $(GENDIR) && ocaml "$(CURDIR)/$(GEN)" \
	    > $(CURDIR)/$(BUILDDIR)/gen.stdout 2> $(CURDIR)/$(BUILDDIR)/gen.stderr
	@echo "== golden-file diff (cata/*.tex, exp.tex) =="
	@fail=0; \
	for f in cata/*.tex; do \
	  b=$$(basename $$f); \
	  case " $(ORPHANS) " in *" $$b "*) \
	    echo "  SKIP  $$b  (orphaned: nothing generates it; W1-T6)"; continue;; esac; \
	  if [ ! -f $(GENDIR)/cata/$$b ]; then \
	    echo "  FAIL  $$b  (committed but NOT generated -> newly orphaned)"; fail=1; \
	  elif cmp -s $$f $(GENDIR)/cata/$$b; then \
	    echo "  ok    $$b  ($$(grep -o '\\frac' $$f | wc -l) frac-occurrences)"; \
	  else \
	    echo "  FAIL  $$b  (byte-diff against committed output)"; \
	    diff $$f $(GENDIR)/cata/$$b | head -20; fail=1; \
	  fi; \
	done; \
	for g in $(GENDIR)/cata/*.tex; do \
	  b=$$(basename $$g); \
	  if [ ! -f cata/$$b ]; then echo "  FAIL  $$b  (generated but NOT committed)"; fail=1; fi; \
	done; \
	if cmp -s exp.tex $(GENDIR)/exp.tex; then echo "  ok    exp.tex"; \
	  else echo "  FAIL  exp.tex"; fail=1; fi; \
	if [ -s $(BUILDDIR)/gen.stderr ]; then \
	  echo "  FAIL  generator wrote to stderr:"; cat $(BUILDDIR)/gen.stderr; fail=1; fi; \
	if [ $$fail -ne 0 ]; then echo "GOLDEN-FILE CHECK FAILED"; exit 1; fi
	@echo "  -- all non-orphaned entries reproduce byte-for-byte"

# cata/*.tex have no trailing newline, so `wc -l` reports 0 for a file with
# content. CLAUDE.md's remedy — `grep -c '\frac'` — is also wrong, for the
# stronger reason that every cata/*.tex is a SINGLE line: grep -c counts
# matching lines, so it returns 1 for all 16 files regardless of content.
# Measured 2026-09-18: `awk 'END{print NR}'` = 1 for every file, while
# `grep -o '\frac' f | wc -l` ranges 1..6. The count above therefore uses
# grep -o | wc -l, and is labelled "\frac" rather than "rules" because nested
# fractions in a premise would inflate it.
check-orphans:
	@echo "== orphan check =="
	@rm -rf $(GENDIR).orph && mkdir -p $(GENDIR).orph/cata
	@$(OPAMENV) cd $(GENDIR).orph && ocaml "$(CURDIR)/$(GEN)" >/dev/null 2>&1
	@found=$$(for f in cata/*.tex; do b=$$(basename $$f); \
	   [ -f $(GENDIR).orph/cata/$$b ] || echo $$b; done | sort | tr '\n' ' '); \
	 want=$$(echo $(ORPHANS) | tr ' ' '\n' | sort | tr '\n' ' '); \
	 echo "  expected orphans: $$want"; \
	 echo "  actual   orphans: $$found"; \
	 if [ "$$found" != "$$want" ]; then \
	   echo "ORPHAN SET CHANGED — update ORPHANS in the Makefile and say why."; exit 1; fi
	@echo "  -- orphan set unchanged (see W1-T6)"

# ---------------------------------------------------------------------------
# Warning census. REPORTS, never fails: fixing a warning means editing
# 'explenation generator.ml', which this session does not own.
#
# Measured 2026-09-18 on OCaml 5.1.1 (opam switch baguette), by compiling a copy
# of the generator with `ocamlc -c` and counting lines matching 'Warning [0-9]':
#
#   default flags   0   <- NOT 16. OCaml 5.1.1 disables 27 and 39 by default.
#   -w +27+39      16   <- this is where the "16" figure comes from:
#                          14 unused-var-strict + 2 unused-rec-flag.
#                          The two 39s are printind_name_list / printiopl_list
#                          (generator lines 263-264), which match `i::tl` and
#                          never use `tl` — they are declared `rec` and do not
#                          recurse, so they print only the first index.
#   -w +40+41+42   42   <- 3 ambiguous-name + 39 disambiguated-name. The sharp
#                          one is `I belongs to several types: ind_name var_name`.
#   -w +a          91   <- also 32 fragile-match, 1 missing-mli.
#
# The numbers below are recomputed on every run; the ones above are what they
# were when this file was written. A change is informational, not a failure.
# ---------------------------------------------------------------------------
check-warnings:
	@echo "== warning census (informational; nothing here fails the gate) =="
	@rm -rf $(WARNDIR) && mkdir -p $(WARNDIR)
	@cp "$(GEN)" $(WARNDIR)/gen.ml
	@$(OPAMENV) cd $(WARNDIR) && \
	  for w in "" "-w +27+39" "-w +40+41+42" "-w +a"; do \
	    rm -f *.cm*; \
	    ocamlc $$w -c gen.ml > out.txt 2>&1 || true; \
	    n=$$(grep -c 'Warning [0-9]' out.txt || true); \
	    printf "  %-14s %3d warnings\n" "$${w:-(default)}" "$$n"; \
	  done
	@echo "  -- expected after W1-T3/T7 (2026-09-18): default 0, +27+39 8, +40+41+42 31, +a 57"
	@echo "  -- these move whenever the generator changes; re-measure, do not quote"

# ---------------------------------------------------------------------------
# W0-T1 — the validator. Covers THREE catalog entries, not the catalog.
# Read docs/VALIDATOR.md before believing anything it prints.
# ---------------------------------------------------------------------------
# Exit status: 0 nothing flagged, 1 something flagged, 2 the validator's own
# self-test or cross-check failed (in which case its verdicts mean nothing).
# Today it exits 1: of 42 rules in 11 entries, 11 are sound and minimal and 31
# are flagged; a further 14 rules in 5 entries are out of scope because the
# artifact is underspecified (W1-T2). That is the expected state until W1 fixes
# them, so `validate` is NOT part of `make check`. Re-measure these numbers, do
# not quote them.
validate: $(BUILDDIR)/validator
	@$(BUILDDIR)/validator . ; \
	 s=$$?; \
	 if [ $$s -eq 2 ]; then echo "VALIDATOR IS BROKEN (self-test/cross-check failed)"; exit 2; fi; \
	 exit 0

# Just the controls: does the checker still tell good rules from bad ones?
validate-selftest: $(BUILDDIR)/validator
	@$(BUILDDIR)/validator --selftest

$(BUILDDIR)/validator: validator.ml
	@mkdir -p $(BUILDDIR)
	@$(OPAMENV) ocamlopt -I $(BUILDDIR) validator.ml -o $(BUILDDIR)/validator
	@rm -f validator.cmi validator.cmx validator.o

# ---------------------------------------------------------------------------
# W0-B's MiniZinc coverage classifier. Advisory only: `--check` exits 1 today
# because there is real drift between CHRISTMAS_LIST.md and MiniZinc 2.10.1,
# and that drift is W0-B's finding to resolve, not a reason to fail this gate.
# Kept out of `make check` entirely and reported, not enforced.
# ---------------------------------------------------------------------------
coverage:
	@echo "== MiniZinc coverage drift (advisory; never fails) =="
	@python3 tools/mzn_coverage.py --check; \
	 s=$$?; \
	 if [ $$s -eq 0 ]; then echo "  -- no drift"; \
	 else echo "  -- drift reported (exit $$s); advisory, see W0-B / docs/COVERAGE.md"; fi

clean:
	@rm -rf $(BUILDDIR) *.cmi *.cmo *.cmx *.o
