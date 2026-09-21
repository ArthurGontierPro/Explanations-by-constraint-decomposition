# `count`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `count`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G8` — **the same wall as [`among`](among.md)**, measured. See Status |
| **Generated** | no generator entry — there is no `cata/count.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `count` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, and **three scratch generator runs** (below) |

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

**`nothing generated — blocked on G8`**, and it is worth stating what that supersedes.

The obvious reading of `count` in this corpus — the one `CHRISTMAS_LIST.md:128` prices at
**E0** and `decomps/count.md` prices at E0 as well — is that every schema already exists, so
the entry is a morning's authoring. Measured, it is not:

- the **value** `v` cannot be a parameter (an `X` literal without a value index raises at
  `:512`), so it must be a one-element value set, which is `ontin (D k)` for a `D k` that
  `ind_set_defined` (`:459`) does not admit and W1-T2 refuses. **G8.**
- the **count variable** `c` is the easy part. `nvalues`' `N` channel works; run (b) emitted
  three rules concluding about it. G5 — the defect that makes shipped `among` conclude nothing
  about its count — is **not** `count`'s problem, because S3 has the channel by construction.
- so the pricing to carry forward is: **E0 for the schemas, G8 for the value**, and the E0 cell
  is right about the schemas and silent about the index sets, exactly as it is for
  `at_most`/`at_least`/`exactly`.

Nothing here is validated, flagged or refuted; the content of the entry is the negative result
and the three runs behind it.

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
| `G8` | **the binding one, measured.** `ind_set` names only whole predefined ranges, so the counted value `v` has no one-element set; `D_4` is refused by W1-T2. Identical to [`among`](among.md)'s wall |
| — (unnumbered) | **the printer requires a value index on every `X` literal** — the parameter reading of `v` raises `Failure "hd"` at `explenation generator.ml:512`. Measured twice (here and under [`at_most.md`](at_most.md)); it is in neither `docs/DECOMP_FORMAT_NOTES.md` nor `docs/ROADMAP.md`, and it is the sibling of W1-T10 and W1-T15 in the same printer |
| `G2` | `var_name` is the closed variant `X \| B of int \| T \| I \| V \| N \| O` (`explenation generator.ml:3`) and has no letter for "the count of a given value", so `count`'s own `c` must borrow `N` (`nvalue`'s) or `O` (`gcc`'s). Mechanically harmless in one file; it means the printed letter is another constraint's |
| `G5` | **not `count`'s.** G5 is the shipped `among`'s missing count channel; S3 has the channel, and run (b) measured it concluding about `N` |
| `G1` | not binding: `count`'s comparison is against a *variable*, which the channel carries, not against a bare constant |
| `G3` | only for the general MiniZinc form with `v` a variable |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`, verbatim: "**E0** — this is `rule5/6/7` exactly as
built". Closing G8 is part of **E2**/W2-T1, as `catalog/among.md` records.
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
4. **[`catalog/count_fn.md`](count_fn.md) quotes this entry's Status as `not reviewed`**, read
   off the stub on 2026-09-21. It is now `nothing generated — blocked on G8`. That file is not
   this session's to edit.
