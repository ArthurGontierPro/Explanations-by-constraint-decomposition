# `at_most`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `at_most`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `nothing generated — blocked on G1` — **and on `G8` for the counted value.** See Status |
| **Generated** | no generator entry — there is no `cata/at_most.tex` |
| **Validator** | out of scope: no artifact. My `make validate` run (2026-09-21) names no `at_most` entry |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-21, `python3 tools/mzn_coverage.py --rank --json`, `make validate`, and a **scratch generator run** (below) |

## Constraint

`at_most(int: n, array[int] of var int: x, int: v)` — the value `v` occurs at most `n` times
in `x`. Both `n` and `v` are parameters in the standard MiniZinc global, so the constraint has
no decision variable other than `x`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:30` carries the *name* only; the signature line above
is transcribed from `decomps/at_most.md` ("Signature"), which records it without a citation of
its own. **Treat it as recall, not as a citation.** `CHRISTMAS_LIST.md:128` files it under
section `2. Counting and cardinality` and gives no signature.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:128` — the row that covers
`count`, `at_least`, `at_most` and `exactly` together — reads, verbatim:

> none specific

**Rule shape:** nothing to state. There is no `catalog/_literature/at_most.md`, no paper was
fetched by this session, and no web access was used. `catalog/README.md` step 2 forbids writing
a published rule shape from memory and this entry writes none.

Note the wording: the cell is `none specific`, not `none`. `tools/mzn_coverage.py` normalises
it to `none` in its ranking output (measured, 2026-09-21). The distinction is worth keeping —
"none specific" is the list's judgement that the counting constraints are covered, if at all,
only by the general cardinality literature it cites elsewhere — but it names no paper, so the
calibration verdict below is `no published rule exists` and not `pending sourcing`.

## Solver support

| | |
|---|---|
| Chuffed | decomp |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:128`, whose solver cell reads, verbatim, `decomp`. Legend at
`CHRISTMAS_LIST.md:106-109`. Verified 2026-09-21: the row carries no `[G]`, no `[C]` and no
`[C✗]`. The machine-filled stub read this correctly.

## Decomposition used here

**Generator value:** none. `explenation generator.ml` has no `at_most` value.
**Emitted by:** nothing — there is no `explainall … "cata/at_most.tex"` call.
**Spec:** [`decomps/at_most.md`](../decomps/at_most.md); shape **S2** in `decomps/_shapes.md`
("reify-and-count: Boolean sum against a bare threshold").

The specced chain is two atomic constraints:

1. `B_i ⇔ X_i = v` — `rule1`, AC.
2. `∑_i B_i ≤ n` — `rule5`, a single `Decomp_devent` with **no** `Reified_devent`.

**`at_most` and `all_different` are the same shape, and in this format they are the same
value.** `decomps/_shapes.md` merges them into S2 and calls it "the largest merge". Measured
today, the merge is tighter than that file claims: the S2 `rule5` encoding of `at_most` is

```ocaml
[Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
 Decomp (2, rule5, [Decomp_devent (true, (B 1), id, oni)])]
```

which is `alldiff` at **`explenation generator.ml:808-809`** character for character. Neither
`n` nor `v` appears anywhere in it, because the format has nowhere to put them. See Status.

## Scope of this entry

**Events the generator was asked to explain:** none in the repository — the generator has never
been invoked for `at_most`, so there is no `%% generator diagnostics (W1-T3)` footer in the tree
to read. What follows is from **a scratch run**, described and bounded in "How this entry was
produced".

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 1 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |

The `F` discard on `X_i = t` is the legitimate kind — a branch reaching a constraint that is not
reified — and it is the same one `cata/alldifferent.tex` takes. `CLAUDE.md` records why the
missing `X_i = t` rule is **not** a bug: deriving it from a `≤`-direction sum needs counting
across sums, which is **E4**.

## Generated rules

**None in this repository.** `cata/at_most.tex` does not exist.

**What the shape emits when run** (scratch, 2026-09-21) — one rule, and it is
`cata/alldifferent.tex`'s rule, because it is `cata/alldifferent.tex`:

```
X_{i'} = t,  ∀i',  i' ≠ i,  i' ∈ [1,n],  i ∈ [1,n]
--------------------------------------------------- ⊢
X_{i} ≠ t
```

**Verdict:** none of its own. `cmp` of the scratch artifact against `cata/alldifferent.tex`
returns **byte-identical**, so the only verdict available is `alldifferent`'s, which
`catalog/alldifferent.md` carries and `make validate` reports as `1 SOUND and MINIMAL`. That
verdict is about `all_different`. **It is not evidence about `at_most`**, and the reason is the
whole content of this entry: the artifact cannot tell the two constraints apart.

## Status

**`nothing generated — blocked on G1`** — and on **G8** for the counted value `v`.

Nothing is generated because no `at_most` value exists in the generator. What this entry
establishes is that authoring one would not produce an `at_most` entry:

- **G1 — the threshold `n` never reaches the page.** It lives only as the choice of `rule5`
  over `rule6`/`rule7`; `reified_devent` returns the placeholder `Reified_devent (true, T, id,
  id)` for a constraint carrying none (`explenation generator.ml:245-246`), which matches no
  real variable, so no branch ever mentions a constant. `at_most(2,x,v)` and `at_most(3,x,v)`
  would be byte-identical files.
- **G8 — the counted value `v` has no expression either**, and this is the part the spec
  underestimates. `decomps/at_most.md` says `v` is "baked in as a constant, not an event".
  Measured: it cannot be. An `X` literal with no value index raises
  `Failure "hd"` at `explenation generator.ml:512` before any rule is printed
  (`printglobal_eventtex`, `hd (isppp … @ isttt …)` on an empty list). Writing `v` as a
  one-element value set instead is `ontin (D k)` for an undefined `D k`, which `ind_set_defined`
  (`:459`) rejects and W1-T2 refuses — measured on `count`, four events, 0 rules.
- **Consequence, and it is the finding.** With the threshold invisible and the value
  unexpressible, the S2 encoding of `at_most` *is* `alldiff`. `decomps/at_most.md` predicted
  that two `at_most` entries with different `n` would be byte-identical; measured today the
  collapse is one step worse — `at_most` and `all_different` are byte-identical too.

Neither gap is a defect of the shape. Both are defects of the encoding, and both are **one
defect shared with `at_least`, `exactly` and `all_different`**, exactly as `decomps/_shapes.md`
argues: fix S2 once and four entries change together.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:128`'s literature cell is `none specific` and names no paper, which is the
condition `catalog/TEMPLATE.md` attaches to this verdict. It is **not** `pending sourcing`:
pending is for a row that cites something nobody has read, and this row cites nothing.

Two things this verdict does not say. It does not say no paper explains a cardinality
constraint — the same file cites Downing, Feydy and Stuckey 2012 for `global_cardinality`
(`CHRISTMAS_LIST.md:127`), and `at_most` is a `global_cardinality` with one covered value. And
it is not a statement about strength: with 0 rules there is no premise to place in an
implication order in either direction.

## Gaps

| gap | what it blocks here |
|---|---|
| `G1` | **the named one.** No way to carry a bare integer threshold into the printed rule, so `n` — the whole content of `at_most` — is invisible. One defect shared with `at_least`, `exactly` and `all_different` (`decomps/_shapes.md`, S2) |
| `G8` | `ind_set` names only whole predefined ranges, so the counted value `v` cannot be written as a singleton value set. Same wall as `among`'s parameter set `v` (`catalog/among.md`) |
| — (unnumbered) | **the printer requires a value index on every `X` literal.** Baking `v` in as a constant raises `Failure "hd"` at `explenation generator.ml:512`. Measured; recorded here because it is not in `docs/DECOMP_FORMAT_NOTES.md` and not on the roadmap. It is the sibling of W1-T10 (`"ERROR B "`) and W1-T15, in the same printer |
| `G3` | only for the general MiniZinc form in which `v` may be a variable. D-0003 and `decomps/at_most.md` both take the parameter reading, so this is not binding today |
| `E4` | not a gap — the missing `X_i = t` rule needs counting across sums, per `CLAUDE.md` and `decomps/all_different.md` |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`, verbatim: "**E0** — this is `rule5/6/7` exactly as
built". That cell is right about the schemas and silent about G1 and G8, which is why the entry
is empty and the route says it is free.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering).

## How this entry was produced

- `python3 tools/mzn_coverage.py --rank --json` (run 2026-09-21) → `at_most` in tier
  `A no-literature + solver-decomposes`, ecodes `["E0"]`, `CHRISTMAS_LIST.md` line 128, section
  `2. Counting and cardinality`, literature normalised to `none`.
- `make validate` (run 2026-09-21, output redirected to a file then grepped, per `CLAUDE.md`
  "Verify before you report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL,
  21 flagged ==` and `== 2 rules in 5 entries out of scope (underspecified artifact) ==`. No
  line of that run names an `at_most` entry; that is the **Validator** row.
- `CHRISTMAS_LIST.md:128` read → the literature, solver and route cells, quoted verbatim above;
  `:106-109` → the solver legend; `:127` → the `global_cardinality` citation named in
  Calibration.
- `tools/data/minizinc-2.10.1-globals.txt:30` read → the name.
- `explenation generator.ml:808-809` read → `alldiff`, the value quoted above.
  `:245-246` → `reified_devent`'s placeholder. `:459-464` → `ind_set_defined` and
  `printind_set`'s two raises. `:512` → the `hd` in `printglobal_eventtex`.
- **Scratch generator run, 2026-09-21** — `explenation generator.ml` was copied to this
  session's scratch directory, the S2 `rule5` value above appended with
  `explainall [xac] … "cata/r4_atmost.tex"`, and run under OCaml 5.1.1
  (`eval $(opam env --switch=baguette --set-switch); ocaml <copy>.ml`). Exit 0; the artifact
  carries 1 `\frac` (`grep -o '\\frac' … | wc -l`) and the diagnostics footer quoted in "Scope".
  `cmp <scratch> cata/alldifferent.tex` → **no output: byte-identical.**
  A second scratch run appended a global event `Global_event (true, X, [Ind (I 1, [])], AC)` —
  an `X` literal with the value baked in — and exited **2** with
  `Failure "hd"`, backtrace naming `printglobal_eventtex`, line 512. That is the measurement
  behind the unnumbered gap above.
- **Nothing was added to the repository by any of this.** `explenation generator.ml` is
  untouched, no file under `cata/` was written or changed, and `make check`'s goldens are
  unaffected. The scratch authoring is this session's own; a different authoring of the same
  shape could behave differently, and the two claims that do not depend on the authoring are the
  ones read off `:808-809` and `:512`.
- **Not fetched, not read:** the MiniZinc library (not vendored here) and any paper. No web
  access was used.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/at_most.md:17-19` cites `alldifferent`'s `rule5` step at "generator line 388".**
   Measured 2026-09-21: it is at **809**. Same rot as W1-T14 records; the *value* name `alldiff`
   still resolves.
2. **`decomps/at_most.md`'s "`v` … baked in as constants, not events" is not encodable.** See
   the `:512` measurement above. The file's G1 analysis is right; its treatment of `v` as
   unproblematic is not.
