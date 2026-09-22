# `count`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `count`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `encodable today, not encoded` — **G8 closed on 2026-09-22 and it was this entry's only wall.** Re-decided by U2, 2026-09-22. See Status |
| **Generated** | no generator entry — there is no `cata/count.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `count` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-21 for the tier, validator and scratch runs (below). **Status re-decided 2026-09-22 (U2)** against `explenation generator.ml` after commits `4547daf`/`1e747ee`; no new run |

## Constraint

`count(array[int] of var int: x, int: v, var int: c)` — `c` is the number of indices `i` with
`x[i] = v`. Per D-0003 the value `v` is taken as a parameter; a variable `v` is G3.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:42` carries the *name* only; the line above is
transcribed from `decomps/count.md` ("Signature"), which cites `CHRISTMAS_LIST.md` for the
parameter reading but gives the arity without a citation. **Treat the arity as recall.**
`CHRISTMAS_LIST.md:128` files it under `2. Counting and cardinality`.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:128` reads, verbatim:

> none specific

**Rule shape:** nothing to state — there is no `catalog/_literature/count.md`, no paper was
fetched by this session and no web access was used. See [`at_most.md`](at_most.md),
"Published explanation", for why `none specific` yields `no published rule exists` rather than
`pending sourcing`.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:128`, solver cell `decomp`; legend at `CHRISTMAS_LIST.md:106-109`.
Verified 2026-09-21. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. `explenation generator.ml` has no `count` value.
**Emitted by:** nothing — there is no `explainall … "cata/count.tex"` call.
**Spec:** [`decomps/count.md`](../decomps/count.md); shape **S3** in `decomps/_shapes.md`
("reify-and-count with a **channelled** count variable").

The specced chain is three atomic constraints:

1. `B_i ⇔ X_i = v` — `rule1`, AC, over `i ∈ [1,n]`.
2. `B'_p ⇔ C = p` — `rule1`, AC, over the count values `p`. This is the channel `nvalues`
   uses for `N` (`explenation generator.ml:840`).
3. `∑_i B_i = p ⇔ B'_p` — `rule7`, matched against the `p`-channel of step 2.

**Step 2 is what makes this S3 rather than S2**, and `decomps/_shapes.md` is emphatic about
why: the count channel is "the only thing in the corpus that lets a derived rule **conclude
something about a count variable** rather than only about the `X` literals". It is precisely
what the shipped `among` lacks — gap **G5**.

**Where the spec is wrong, and it took a run to see it.** `decomps/count.md` says step 3 is
`nvalues`' `B4` step "minus the intermediate per-value existential that `nvalue`/`among` need
and `count` does not (there is exactly one target value `v`, not a set)". Dropping that step is
not free: it leaves the value family unbound on the reified side, and the printer requires a
value index on every `X` literal. Measured — see "Scope of this entry", run (a).

## Scope of this entry

**Events the generator was asked to explain:** none in the repository. Three **scratch runs**
(bounded in "How this entry was produced") asked the generator for the four events
`X_i = t`, `X_i ≠ t`, `N = p`, `N ≠ p`, over three authorings of S3.

**(a) The spec as written** — steps 1-3, no intermediate step, reified side
`imap [foralli;p_out]` / `imap [i_out;forallp]`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | 1 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | 1 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `N=p` | — | — | **run aborted**: `Failure "hd"`, `printglobal_eventtex`, `explenation generator.ml:512` |
| `N \neq p` | — | — | not reached |

The two `X` rules are written to the file, then the run exits 2. The `X` literal that survives
into the `N = p` explanation carries neither a `P`- nor a `T`-family index, and line 512 takes
`hd` of exactly that list. **This is a printer crash reachable from a decomposition in this
repo's own spec corpus.**

**(b) The same, with the value family universally bound on the reified side**
(`imap [foralli;forallt;p_out]`): exit 0, **5** rules, three of which conclude `N = p` or
`N ≠ p` — so the S3 channel does do what G5 says `among` cannot. But `∀t` says "for every
value", and `count(x, v, c)` counts **one** value. The run therefore prices the honest cost:
S3 emits, and what it emits is closer to `nvalue` than to `count`.

**(c) `count` as `among` with a value set, plus the channel `among` is missing** — step 2 of
`among` (`explenation generator.ml:852`, `ontin (D 4)`) with the `nvalues` count channel added:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **0** | `undefined index set 1` — `REFUSED … (D4) — W1-T2` |
| `X_{i} \neq t` | 1 | **0** | `undefined index set 1` — `REFUSED … (D4) — W1-T2` |
| `N=p` | 1 | **0** | `undefined index set 1` — `REFUSED … (D4) — W1-T2` |
| `N \neq p` | 2 | **0** | `undefined index set 2` — `REFUSED … (D4) — W1-T2` |

Exit 0, **0 rules**, every candidate refused on the undefined `D_4`. **This is `among`'s
result, arrived at independently**, and it is the finding that sets this entry's status:
fixing G5 does not unblock `count`, because G8 blocks it first.

## Generated rules

**None in this repository.** `cata/count.tex` does not exist; `grep -o '\\frac'` has no file to
read. The rules quoted above are scratch output and are not catalog artifacts.

## Status

**`encodable today, not encoded`**

**This status changed on 2026-09-22 and the previous one — `nothing generated — blocked on G8` —
is retired, not softened.** G8 was closed that day (session G-1, commits `4547daf` and
`1e747ee`), and the wall the paragraphs below measured is the one it took down. There is now no
gap to name, which is why this entry uses the legend value `catalog/README.md` added for exactly
that case rather than inventing a G-number.

**What the block was, and why it is gone.** The measured obstacle was the *value*: `v` cannot be
a bare parameter, because an `X` literal with no value index raises `Failure "hd"` at
`explenation generator.ml:512`, so `v` had to be written as a one-element value **set** — and
`ind_set` had no former for one. `ind_set` now has four (`explenation generator.ml:48-52`), and
`DPar` is the one this needs: `at_most`'s seed event is
`Set (T 1, IN, DPar ("\\{v\\}", D 2))` (`:1022`), which keeps the value index `t` the printer
demands and pins it to the singleton `{v}`. `ind_set_defined` admits it (`:520-525`) because
`printind_set` renders its own containment (`:536`), so it is not a `D_4`. `cata/at_most.tex`
ships the result. The same seed serves `count`.

**What was never the block, restated because it is now the whole of the work.** The **count
variable** `c` is the easy part: `nvalues`' `N` channel works (`explenation generator.ml:921-924`,
a `rule7` whose `Reified_devent` carries `N`), and scratch run (b) emitted three rules concluding
about it. **G5 is not `count`'s defect** — it is shipped `among`'s missing count channel, and S3
has the channel by construction. That distinction is now load-bearing, because `among` is the
cautionary case: G8's closure gave it two rules and both are measured **UNSOUND**
([`among.md`](among.md)), precisely because its count is channelled nowhere. `count` does not
share that fault, but nothing about this status predicts a verdict.

**What would have to be written** — a decomposition value in the generator's `(*Decompositions*)`
block, on the `at_most` pattern at `explenation generator.ml:994-995`:

1. `Decomp (1, rule1, [Global_devent (X …); Reified_devent ((B 1) …)])` — `B1_i ⇔ X_i = t`.
2. `Decomp (1, rule1, [Global_devent (N …); Reified_devent ((B 4) …)])` — the count channel,
   copied from `nvalues` (`:922`). `G2` still applies: `var_name` has no letter meaning "the
   count of a given value", so `c` borrows `N`.
3. `Decomp (2, rule7, [Decomp_devent ((B 1) …); Reified_devent ((B 4) …)])` — the Boolean sum
   `=`, with the `Reified_devent` present, which is what separates this from `among`'s G5 bug.

plus a seed `Global_event` restricting `t` to `DPar ("\\{v\\}", D 2)` and one `explainall`
line. **Nothing here was run.** This is a reading of the generator's types and of the two
demonstrators G-1 shipped, not a measurement: no value was authored, no artifact was produced,
and no rule of this constraint has been seen, let alone judged.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:128` names no paper. Independently, with 0 rules in the repository there is
no premise to place in an implication order, so the verdict would be unavailable even if a
shape were sourced. Note, as `catalog/at_most.md` does, that this is a statement about the
*row*: the same file cites Downing, Feydy and Stuckey 2012 for `global_cardinality`
(`:127`), and `count` is a one-value `global_cardinality`. Nobody has read that paper for this
purpose; `catalog/_literature/gcc.md` sources it for `gcc` and its content is not transferred
here.

## Gaps

| gap | what it blocks here |
|---|---|
| `G8` | **CLOSED 2026-09-22** (`4547daf`, `1e747ee`). It was the binding one, measured: `ind_set` named only whole predefined ranges, so the counted value `v` had no one-element set and `D_4` was refused by W1-T2. `DPar` now writes it — see Status. The row is kept because the measurement above it was real |
| — (unnumbered) | **the printer requires a value index on every `X` literal** — the parameter reading of `v` raises `Failure "hd"` at `explenation generator.ml:512`. Measured twice (here and under [`at_most.md`](at_most.md)); it is in neither `docs/DECOMP_FORMAT_NOTES.md` nor `docs/ROADMAP.md`, and it is the sibling of W1-T10 and W1-T15 in the same printer |
| `G2` | `var_name` is the closed variant `X \| B of int \| T \| I \| V \| N \| O` (`explenation generator.ml:3`) and has no letter for "the count of a given value", so `count`'s own `c` must borrow `N` (`nvalue`'s) or `O` (`gcc`'s). Mechanically harmless in one file; it means the printed letter is another constraint's |
| `G5` | **not `count`'s.** G5 is the shipped `among`'s missing count channel; S3 has the channel, and run (b) measured it concluding about `N` |
| `G1` | not binding: `count`'s comparison is against a *variable*, which the channel carries, not against a bare constant |
| `G3` | only for the general MiniZinc form with `v` a variable |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`, verbatim: "**E0** — this is `rule5/6/7` exactly as
built". With G8 closed, that cell is now right about the index sets as well as the schemas,
which it was not when this entry was written.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (2026-09-21) → tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 128.
- `make validate` (2026-09-21, output redirected then grepped) → `== 34 rules checked in 11
  entries: 13 SOUND and MINIMAL, 21 flagged ==`, `== 2 rules in 5 entries out of scope
  (underspecified artifact) ==`. No line names a `count` entry.
- `CHRISTMAS_LIST.md:128`, `:127`, `:106-109` read → the cells quoted above.
- `tools/data/minizinc-2.10.1-globals.txt:42` read → the name.
- `explenation generator.ml` read, not run: `:3` (`var_name`), `:245-246`
  (`reified_devent`'s placeholder), `:459-464` (`ind_set_defined`, `printind_set`'s raises),
  `:512` (the `hd` in `printglobal_eventtex`), `:839-842` (`nvalues`, the `N` channel),
  `:851-853` (`among`, the `ontin (D 4)` step).
- **Three scratch generator runs, 2026-09-21.** `explenation generator.ml` was copied into this
  session's scratch directory; each run appended one S3 authoring plus
  `explainall [xac;nac] … "cata/r4_count*.tex"` and was run with OCaml 5.1.1
  (`eval $(opam env --switch=baguette --set-switch); ocaml <copy>.ml`), stdout and stderr
  redirected to files and then grepped. (a) exit **2**, `Failure "hd"`, backtrace naming
  `printglobal_eventtex` at line 512, 2 rules written before the abort. (b) exit **0**, 5
  `\frac`. (c) exit **0**, 0 `\frac`, the four `REFUSED … (D4) — W1-T2` diagnostics quoted in
  "Scope of this entry".
- **Nothing was added to the repository.** `explenation generator.ml` is untouched, no file
  under `cata/` was written or changed, and `make check`'s goldens are unaffected. The three
  authorings are this session's own; a fourth could behave differently. The claims that do not
  depend on the authoring are the ones read off `:459`, `:512` and `:852`.
- **Not fetched, not read:** the MiniZinc library (not vendored) and any paper. No web access.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/count.md:9` cites the `count` row at `CHRISTMAS_LIST.md:125`.** Measured
   2026-09-21: the row is at **128**. The quoted text ("E0 — this is rule5/6/7 exactly as
   built") is correct.
2. **`decomps/count.md:20,23` cite `nvalues` at "generator lines 406-407" and "line 409".**
   Measured: `nvalues` is at **839-842**. W1-T14's rot.
3. **`decomps/count.md:24-25`'s "minus the intermediate per-value existential … `count` does
   not [need]" is contradicted by run (a).** Dropping that step aborts the printer. The file's
   G2 note is sound; this sentence is not.
4. **[`catalog/count_fn.md`](count_fn.md) quotes this entry's Status.** It read `not reviewed`
   off the stub on 2026-09-21, then `nothing generated — blocked on G8`; as of 2026-09-22 it is
   `encodable today, not encoded`. U2 updated that quotation in the same commit as this change.

5. **Everything above discrepancy 4 was measured on 2026-09-21 and G8 closed on 2026-09-22.**
   The three scratch runs, the `Failure "hd"` at `:512` and the four `REFUSED … (D4)`
   diagnostics all still stand as records of what the format was; they are no longer a record of
   what it is. Only the Status section has been re-decided, and it says so.
