# `all_different_except`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `all_different_except`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `generated, unvalidated` — **and the label undersells what is known.** One rule, measured **sound for `n ≥ 2`** by a check that is not `make validate`; minimality unmeasured. See Status for why no other legend value fits |
| **Generated** | **1** rule in **`cata/alldifferent_except.tex`** — **new 2026-09-22**, the artifact that closed `G8`'s exclusion half. Note the file's spelling: `alldifferent_except`, following `cata/alldifferent.tex`, not this entry's `all_different_except` |
| **Validator** | **not covered — the validator cannot see this file.** My `make validate` run (2026-09-22) names no `alldifferent_except` entry, in scope or out: `validator.ml`'s entry lists are hardcoded and it never scans `cata/`. That is **W1-T18**, opened 2026-09-22 |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:117` records `none` |
| **Last measured** | 2026-09-22, `make check`, `make validate`, `grep -o '\frac' cata/alldifferent_except.tex \| wc -l`, and reads of that artifact and `explenation generator.ml`. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

**Where the soundness figures come from, once.** `cata/alldifferent_except.tex` is **not**
validated by `make validate`. The figures below are **G-1's own exhaustive check over all
stores at `n,m ≤ 4` and all `v`**, carried into the artifact's `%% CAVEAT` footer by the
generator's `caveat` mechanism and quoted from there. They are a measurement by a different
instrument from the one the rest of this catalog uses, and they are **not** validator verdicts.
Nothing here is "validated".

## Constraint

`all_different_except(array[int] of var int: x, set of int: v)` — the values in `x` are
pairwise distinct, **except** that any number of them may take a value in the excepted set `v`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:18` carries the *name* only. The line above is the
reading `decomps/all_different.md` works from, where the excepted value is "a parameter for the
general one"; that file states it without a citation, so **treat the arity as recall**, and note
that it writes `v_0` for a single excepted value where MiniZinc's name (`_except`, not
`_except_value`) suggests a set. **The shipped artifact takes the single-value reading**: its
side condition is `t \in \llbracket1,m\rrbracket \setminus \{v\}`, one excluded parameter, and
`DExc` takes a *list* of elements so a set of them is expressible without a format change.
`CHRISTMAS_LIST.md:117` files it under section `1. AllDifferent family`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:117` — the row that covers
`all_different_except` and `all_different_except_0` together — reads, verbatim:

> none

**Rule shape:** nothing to state — there is no `catalog/_literature/all_different_except.md`,
no paper was fetched by this session and no web access was used.

**The neighbouring row does cite one, and it is not transferable.**
`CHRISTMAS_LIST.md:116` cites Downing, Feydy and Stuckey 2012, *Explaining alldifferent*, for
`all_different`; `catalog/_literature/alldifferent.md` sources it and `catalog/alldifferent.md`
calibrates against it. **Nothing from that file is carried into this entry**: the excepted
value changes the constraint's Hall-set structure, which is exactly what that paper's §5/§6
explanations are about, and asserting the transfer would be writing a published rule shape from
memory. That this entry now *has* a rule — and one that is `alldifferent`'s rule plus a side
condition — makes the transfer more tempting, not more legitimate. Whether it transfers is a
question for whoever sources `_literature/` next.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | `[G]` present |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:117`, solver cell `decomp **[G]**`; legend at
`CHRISTMAS_LIST.md:106-109`. Verified 2026-09-21. Note the `[G]`, which the other twelve
entries in the original slice do not have: Geas implements this one natively while Chuffed
decomposes it.

## Decomposition used here

**Generator value:** `alldiffexc`, `explenation generator.ml:1006-1007` (verified today).
**Emitted by:** `explainall [xacx] alldiffexc "cata/alldifferent_except.tex"`, line **1071**,
under a `caveat := [...]` block at **1062-1070** whose text the artifact reproduces verbatim.
**Seed event:** `xacx`, line **1023**.
**Spec:** [`decomps/all_different.md`](../decomps/all_different.md), which covers the family in
one file; shape **S2** in `decomps/_shapes.md` ("reify-and-count: Boolean sum against a bare
threshold"), where `all_different_except` and `all_different_except_0` are listed as instances
with the annotation "guarded index set, G8".

The chain is `all_different`'s:

1. `B_{i,t} ⇔ X_i = t` — `rule1`, AC.
2. `∑_i B_{i,t} ≤ 1` — `rule5`, single `Decomp_devent`.

**And that is *all* it is. Measured today: the `alldiffexc` value is byte-identical to
`alldiff` (`:890-891`) up to the binding name and leading whitespace.** The guard is not in the
decomposition at all — it rides on the **seed event**. `xacx` (`:1023`) is the `X` event whose
value index carries `Set (T 1, IN, DExc (D 2, [EPar "v"]))`, printed
`t \in \llbracket1,m\rrbracket \setminus \{v\}`. So:

- **What closed the gap is `DExc`**, one of four new `ind_set` formers
  (`explenation generator.ml:48-52`) that print their own containment and are therefore
  accepted by `ind_set_defined` (`:520-525`) without relaxing W1-T2 — `D of int` beyond 3 and
  `D2` are still refused, which is why `table`, `regular`, `roots` and `range` still emit
  nothing. `G8`'s exclusion half, closed in fact and not only in machinery.
- **What the decomposition still does not say is that the sum is restricted.** Step 2 sums over
  the same family `alldifferent` sums over; only the *event being explained* is guarded. For
  the one direction this shape can produce that is enough — the conclusion and the premise are
  about the same `t`, and the guard on `t` propagates to both, which is visible in the rendered
  rule below. It is worth knowing that the restriction is carried by the question and not by
  the model, because a different seed event would silently produce `alldifferent`'s rule again.

`CHRISTMAS_LIST.md:117`'s route cell said this all along, verbatim: "**E0**, same shape with a
guard on the excepted value". The cell was right about the schemas; the guard is what took
until 2026-09-22.

## Scope of this entry

**Events the generator was asked to explain:** two, both from the single seed event `xacx`
(arc consistency) — `X_i = t` and `X_i ≠ t`, each carrying the side condition
`t \in \llbracket1,m\rrbracket \setminus \{v\}`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t,~t \in \llbracket1,m\rrbracket \setminus \{v\}` | 1 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t,~t \in \llbracket1,m\rrbracket \setminus \{v\}` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |

The file states the empty answer itself:

```
%%   ** NO RULE EMITTED for X_{i}=t,~t \in \llbracket1,m\rrbracket \setminus \{v\}: 1 candidate(s), all blocked **
```

**One rule, not two, and that was predicted here before the artifact existed.** The previous
version of this entry said: "An `_except` entry, once G8 lands, would inherit exactly that: one
rule, not two." Measured today, it does. The `F` discard on `X_i = t` is the legitimate kind —
a branch reaching a constraint that is not reified — and deriving that direction from a
`≤`-direction sum needs counting across sums, **E4** (`CLAUDE.md`, `decomps/all_different.md`).
G8 did not change it and was never going to.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of
`cata/alldifferent_except.tex`.

## Generated rules

Rendered from `cata/alldifferent_except.tex` (single line, no trailing newline;
`grep -o '\\frac' cata/alldifferent_except.tex | wc -l` → **1**; `make check` independently
prints `ok alldifferent_except.tex (1 frac-occurrences)`).

### Rule 1 — `X_i ≠ t`

```
X_{i'} = t ,  ∀i' ,  i' ≠ i ,  i' ∈ [1,n] ,  i ∈ [1,n] ,  t ∈ [1,m] \ {v}
-------------------------------------------------------------------------- ⊢
X_{i} ≠ t ,  t ∈ [1,m] \ {v}
```

This is `cata/alldifferent.tex`'s rule with `t ∈ [1,m] \ {v}` on both sides of the line, and
nothing else. Read the two artifacts side by side and that is the entire diff.

**Verdict:** **`SOUND` for `n ≥ 2`**; **minimality not measured**.
**Measured by:** G-1's exhaustive check over all stores at `n,m ≤ 4` and all `v` — **not** by
`make validate`, which does not know this file exists (W1-T18). Quoted from the artifact's own
`%% CAVEAT (G-1, 2026-09-22)` footer:

```
%% v: SOUND for n >= 2 (100 firing cases, no counterexample). At n = 1 the universally
%% quantified premise is vacuously true and the rule concludes from nothing -- the
%% SHIPPED alldifferent rule does exactly the same (240 -> 140 firing cases, 30
%% counterexamples, all of them at n = 1), so this entry inherits alldifferent's
%% verdict and its weakness, including firing only when the others are already pinned.
```

**100 firing cases, 0 counterexamples at `n ≥ 2`.**

### The `n = 1` vacuity, and why it is the interesting part

At `n = 1` there is no `i' ≠ i`, so the premise `∀i' ≠ i: X_{i'} = t` is **vacuously true** and
the rule concludes `X_i ≠ t` from nothing. For a single variable that is plainly wrong, under
this constraint and under `all_different` alike.

**The shipped `alldifferent` rule does exactly the same thing**, and G-1 measured it: 240 cases,
140 firing, **30 counterexamples, every one of them at `n = 1`**. So this entry inherits
`alldifferent`'s verdict *and* its weakness, which is what the footer says and what this section
exists to surface.

**This does not contradict `catalog/alldifferent.md`'s `SOUND and MINIMAL`**, and the reason is
worth stating precisely, because it looks like a contradiction. `docs/VALIDATOR.md:184`
enumerates `alldifferent` at **`n, m ∈ {2,3,4}`** — **`n = 1` is not in the validator's scope at
all**. G-1's check ran the wider range and found the failures outside it. Two instruments, two
ranges, no disagreement: the validator's verdict is true of the sizes it enumerates, and it is
silent about `n = 1`. Anyone reading `sound and minimal at n,m <= 4` as covering `n = 1` is
reading in a size the sweep never ran. **This session did not edit `catalog/alldifferent.md`**;
the observation is reported here and in the handoff.

**The other inherited weakness is strength, not soundness.** The premise names *every* other
variable, so under `all_different_except` it fires only when all `n-1` others are already pinned
to the same non-excepted `t` — which, for `t ∉ v`, the constraint itself forbids as soon as
`n ≥ 3`. Same `n = 2` ceiling `catalog/alldifferent.md` records, same reason. Minimality, had it
been measured, would not have seen this: minimality is premise-droppability, not power (W1-T13).

## Status

**`generated, unvalidated`**

One rule exists and no verdict from `make validate` has been obtained, because the validator's
entry lists are hardcoded and it never scans `cata/` — **W1-T18**, opened 2026-09-22, the same
day this artifact was generated.

**The legend has no value for what is actually known here, and that is a finding, not a
formatting problem.** What is known: the rule is sound for `n ≥ 2` over all stores at `n,m ≤ 4`,
measured exhaustively by G-1; it concludes from nothing at `n = 1`; its minimality has not been
measured by anyone. `validated:` is wrong (not the validator, and minimality unknown);
`flagged` would assert a flag verdict nobody has issued for this artifact — contrast
[`at_most`](at_most.md), whose footer *does* state `NOT MINIMAL`, which is why that entry is
`flagged` and this one is not; `not validatable` is wrong, because the validator did not judge
this entry out of scope, it simply cannot see it. So the label is the weakest true one and the
paragraph above it carries what the label cannot.

**`G8` is closed and this file is half the demonstration** (`at_most`'s `DCard` is the other
half). The entry's previous status, `nothing generated — blocked on G8`, was retired on
2026-09-22.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:117`'s literature cell is `none`, the condition `catalog/TEMPLATE.md`
attaches to this verdict.

**Not `pending sourcing`, and still not a transfer from `all_different`.** Pending is for a row
citing something unread; this row cites nothing. And `catalog/alldifferent.md`'s verdict —
coincides with Downing §4 at `n = 2`, strictly weaker for every `n ≥ 3` — is **about a
different constraint**, stated against a paper this row does not cite. The arrival of a rule
that is visibly `alldifferent`'s rule plus a side condition does not change that: a comparison
needs a published premise on the other side, and `CHRISTMAS_LIST.md:117` supplies none.
Recording that non-transfer is the point of the verdict here.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **closed 2026-09-22.** `DExc (D 2, [EPar "v"])` names `[1,m] \ {v}` and prints it; the exclusion half of G8 is demonstrated by this artifact. `DExc` takes an element *list*, so an excepted *set* needs no further change |
| `E4` | not a gap — the missing `X_i = t` direction, inherited from `all_different` and unchanged by G8, as this entry predicted before the artifact existed |
| `G1` | **not** binding here, unlike the counting family: the threshold is 1, the same invisible 1 `all_different` already lives with, and `all_different_except` does not vary it |
| — (not a gap) | **the guard lives on the seed event, not in the decomposition.** `alldiffexc` is `alldiff` byte for byte; a different seed event over the same value would emit `alldifferent`'s rule under this file name. An encoding property worth knowing, not a format limitation |
| — (not a gap) | **W1-T18**: the gate cannot see this entry. A hole in `validator.ml`, not in the format |

Extensions: **E0** — `CHRISTMAS_LIST.md:117`, verbatim: "**E0**, same shape with a guard on the
excepted value". Right about the schema, and now right about the guard too.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering; **G8 at line 87**,
re-measured today — this entry previously cited `:80`).

## How this entry was produced

- `grep -o '\\frac' cata/alldifferent_except.tex | wc -l` → **1**. (`grep -c` returns 1 for
  every entry — `CLAUDE.md`, "Traps".)
- `make check` (run 2026-09-22, redirected then grepped) → `ok alldifferent_except.tex (1
  frac-occurrences)`, `GATE PASSED`. Reproducibility only.
- `make validate` (run 2026-09-22, redirected then grepped, per `CLAUDE.md` "Verify before you
  report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==` and
  `== 4 rules in 5 entries out of scope ==`. **No line of that run names this entry**, in scope
  or out. That is the Validator row, and it is W1-T18.
- `cata/alldifferent_except.tex` read, not run → the rule, the diagnostics footer and the
  `%% CAVEAT` block. **Every soundness figure in this entry is quoted from that block**, which
  records G-1's exhaustive check at `n,m ≤ 4`; none was produced by this session and none is a
  validator verdict.
- `cata/alldifferent.tex` read → the sibling rule the diff above is against.
- `explenation generator.ml` read, not run: `:48-52` (the four new `ind_set` formers),
  `:520-525` (`ind_set_defined`), `:534-537` (`printind_set`'s new cases), `:890-891`
  (`alldiff`), `:997-1005` (the `DExc` comment block), `:1006-1007` (`alldiffexc`), `:1023`
  (`xacx`), `:1062-1071` (the caveat block and the `explainall` call). All line numbers
  re-measured today (W1-T14).
- **`alldiff` vs `alldiffexc` compared mechanically**, not by eye: both values' two lines
  extracted, the binding name and leading whitespace stripped, `diff` → no output.
- `docs/VALIDATOR.md:180-187` read → the enumerated sizes, `n, m ∈ {2,3,4}`, which is how the
  `n = 1` counterexamples and `alldifferent`'s `SOUND and MINIMAL` verdict are reconciled above.
- `CHRISTMAS_LIST.md:117`, `:116`, `:106-109` read → this row's three cells, the
  `all_different` citation named in "Published explanation", and the solver legend.
- `tools/data/minizinc-2.10.1-globals.txt:18` read → the name.
- `docs/DECOMP_FORMAT_NOTES.md:87` read → G8's wording at its current line.
- `docs/ROADMAP.md:57` and `:62` read → W1-T13 (strength) and W1-T18 (the gate hole).
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/all_different.md:17-18` still says `_except` is "blocked by gap **G8**" — and it
   is not, as of `1e747ee`.** Checked today rather than copied: the *renumbering* complaint the
   previous version of this entry carried is **already fixed** in that file, which now reads
   "blocked by gap **G8** (this said G6 until 2026-09-21; G6 is the 2-D constant table, G8 is
   this)". What is stale there now is the block itself, plus its quotation of the type:
   `ind_set` is no longer "`generator line 6: type ind_set = D of int | D2 of ind_name list`"
   but six constructors at **`:48-52`**, and `DExc` is precisely the "named range minus one
   point" that paragraph says has no constructor.
2. **`decomps/all_different.md:8` and `:20-21` cite stale line numbers.** It gives `alldiff` at
   "l.808–809"; measured today, **890-891**. That number has now rotted twice this week
   (678-679 → 808-809 → 890-891 in that file's own history). W1-T14.
3. **The same file says `D2` "doesn't handle it beyond `\"setfils\"` — a placeholder string".**
   That string no longer exists: W1-T2 replaced it with a raise, now at
   `explenation generator.ml:533`. `D2` is still unimplemented and still refused; what changed
   is that the *use case* it was the hook for — an explicit value set — is now served by `DPar`
   and `DExc` instead.
4. **`catalog/alldifferent.md` is silent about `n = 1`**, and after G-1's measurement that
   silence reads as coverage. Its `SOUND and MINIMAL` is true of `n, m ∈ {2,3,4}`
   (`docs/VALIDATOR.md:184`) and says nothing about the 30 counterexamples G-1 found at `n = 1`.
   **Not this session's file to edit**; flagged here and in the handoff.
