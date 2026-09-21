# `strictly_increasing`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `strictly_increasing`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` (shared row with `increasing`, `decreasing` and `strictly_decreasing`) |
| **Status** | **`nothing generated`** — and **no status-legend value fits.** The legend's only `nothing generated` form requires a gap number; there is no gap. See Status |
| **Generated** | **0** rules — there is no `cata/strictly_increasing.tex` and no generator value for it |
| **Validator** | out of scope: nothing to validate. `make validate` reads `cata/*.tex` and this constraint has no artifact there |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:193` literature cell reads `none specific` |
| **Last measured** | 2026-09-21, `make validate`, `grep -o '\frac' cata/*.tex`, `ls cata/`, `python3 tools/mzn_coverage.py --rank` |

## Read this first: the shift is free, and nothing has been run on it

`strictly_increasing` is [`increasing`](increasing.md) with its threshold moved by one.
[`increasing`](increasing.md) is **validated: sound and minimal at n,m ≤ 4**, 2 rules, 2
`SOUND and MINIMAL` — re-measured in this session's own `make validate` run, quoted below. The
question this entry exists to settle is the one `docs/ROADMAP.md`'s framing leaves open:
**does the strict variant cost a gap, or is the shift free?**

**Measured by reading the generator: the shift is free at the encoding level.** Every piece it
needs already exists, and the `Addint` path it would use is already exercised by the
non-strict pair:

| what the shift needs | where it is | exercised today? |
|---|---|---|
| a constant shift on the `T` (value) index family | `tplus`/`tmoin`, `explenation generator.ml:794-795` | **no** — see below |
| composing two index operators into one | `imap` / `OpSeq`, `:801`, "applied right to left" `:799-800` | yes — `incr`'s siblings use `imap` at `:828`, `:842`, `:855` |
| a printer for a constant index shift | the `Addint` case, `:471` (plain) and `:503` (LaTeX) | **yes** — `incr`/`decr`'s `imoin 1`/`iplus 1` are `OpShift (FI,…)` and print through it |
| a name for a `T`-family index | `printind_name`, `:430`, renders `T a` as `t` | yes |
| the two rule schemas themselves | `rule1` BC channel + `rule4` two-literal clause, `incr` at `:830-831`, `decr` at `:832-833` | yes |

So ``imap [imoin 1; tmoin 1]` descending and `imap [iplus 1; tplus 1]` ascending — the composed shift the strict variant needs —` is writable in the existing
vocabulary, and `decomps/increasing.md:12-16`'s pricing — "same shape, same two rule schemas
(rule1 + rule4), threshold shifted by one … **E0**, no new schema" — holds when checked against
the current file.

**Three things that qualification does not cover, stated so "free" is not read as "done".**

1. **`tplus` and `tmoin` are used by no shipped decomposition.** The generator keeps its own
   census of which index operators are live (`:758-761`): "the decompositions use id, oni, ont,
   onr, ontin, i_out, t_out, p_out, foralli, forallt, forallp, iplus, imoin, tplusci, tmoinci,
   tprimin and imap; the rest are kept because they are the format's vocabulary". Neither
   `tplus` nor `tmoin` is on that list. The *printer case* they route to is exercised; the
   operators themselves have never been printed.
2. **Nothing was run.** No value was added to the generator (this session does not own that
   file), nothing was compiled, and no `.tex` was produced. "Free at the encoding level" is a
   claim about the vocabulary, read off `explenation generator.ml`; it is not a claim that the
   result would validate.
3. **The boundary condition now falls off two index sets instead of one.**
   [`increasing`](increasing.md#generated-rules) records that its rules "have no instance at
   `i = 1`" because `i-1` leaves `[1,n]`, that the `.tex` prints `i'=i-1` with no range
   condition, and that the validator's index-equation handling supplies the bound. A strict
   variant shifts `t` as well, so `t-1` can leave `[1,m]` the same way. `G8` — `ind_set` names
   only whole predefined ranges, so "`t ∈ [2,m]`" cannot be written
   (`docs/DECOMP_FORMAT_NOTES.md:76`) — is the same note [`increasing`](increasing.md#gaps)
   already carries for `i`, applying to a second family. **Whether the validator's index-equation
   controls handle a shifted `t` as they handle a shifted `i` is not established**, because
   there is no artifact to put in front of them.

**The answer, in one line:** the shift costs **no gap**; it costs one unexercised pair of
operators and one unrun validation.

## Constraint

`strictly_increasing(array [$X] of var int: x)`

The array is strictly increasing: `x[i] < x[i+1]` for every adjacent pair, where [`increasing`](increasing.md) requires only `x[i] <= x[i+1]`.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:119` carries the *name* only; this checkout holds
no `.mzn` file. The signature above is [`increasing`](increasing.md#constraint)'s with the
comparator strengthened, and that entry marks its own as recall. Treat this one the same way.

## Published explanation

**Citation:** none. The literature column of `CHRISTMAS_LIST.md:193` — the row for
`increasing`, `decreasing` and `strictly_*` together — reads, verbatim:

> none specific

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent.md`,
`cumulative.md` and `gcc.md` only (`ls catalog/_literature/`, 2026-09-21), and no paper is
cited for this constraint anywhere in the literature index. **No published rule shape is stated
in this entry, from memory or otherwise.** No web access was used and no paper was fetched.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | absent |

Source: `CHRISTMAS_LIST.md:193`, solver-column legend at `CHRISTMAS_LIST.md:106-108`. One
solver cell covers all four names on the row. No solver on the row ships an explaining
propagator; **this is a constraint everyone decomposes**, which is what puts it in tier A.

## Decomposition used here

**Generator value:** none. No value in `explenation generator.ml` encodes a `strictly_*`
variant, and none of the fifteen `explainall` calls (lines 879-893) mentions one. The two
non-strict siblings are emitted at `:884` (`incr` → `cata/increasing.tex`) and `:883`
(`decr` → `cata/decreasing.tex`).
**Emitted by:** nothing.
**Spec:** **`decomps/increasing.md`** — its first line is
`# increasing, decreasing, strictly_increasing, strictly_decreasing`, and `:12-16` is about
this constraint specifically.

> **Stub field corrected.** The auto-stub read `**Spec:** none — this constraint has no
> `decomps/strictly_increasing.md`.` That probe is an exact-filename `os.path.isfile`, and it
> misses a spec that covers four constraints under the first one's name. A spec exists, it
> addresses this variant in its own paragraph, and this entry is written against it.

Shape **S1**, "adjacent-position binary clause (2-local chain)" (`decomps/_shapes.md:32`),
which was Shape **A** in `decomps/_shapes-seq.md:12-29` and **P2** in
`decomps/increasing.md:3`. The base, `incr` at `explenation generator.ml:830-831`:

```ocaml
let incr = [Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
            Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id); Decomp_devent (true, (B 1), imoin 1, iplus 1)])]
```

and `decr` (`:832-833`) is that with the two `Decomp_devent` signs in the `rule4` clause
swapped, nothing else — which `decomps/increasing.md:8-10` states and this session confirmed by
reading both values.

**Zero genuine auxiliaries, and that is what makes this family different from every other one
this session reviewed.** `B 1` is defined in the same `Decomp` as a reification of a
`Global_devent`, so the printer substitutes it back before emitting anything
(`decomps/_shapes-seq.md:26-29`); `cata/increasing.tex` prints only `X` literals. The
accumulated-state auxiliary that blocks [`value_precede`](value_precede.md) on `G17`, and the
`"ERROR B "`-turned-raise of W1-T10, are **both absent here**. `decomps/_shapes.md:337-341` is
the declared reason S1 and S5 are different shapes rather than one.

## Scope of this entry

**Events the generator was asked to explain:** **none.** No `explainall` call names this
constraint, so there is no `cata/strictly_increasing.tex` and no
`%% generator diagnostics (W1-T3)` footer to read.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` (would be, from `xbc`, `explenation generator.ml:868`) | — | **0** | not run: the decomposition has not been encoded |
| `X_{i}<t` (would be, the negation) | — | **0** | as above |

**What the base was asked, for comparison**, from the `%% generator diagnostics (W1-T3)` footer
of `cata/increasing.tex`: two events, 2 candidates each, 1 rule each, with
`dropped F 1, cycle 0, duplicate 0, undefined index set 0` on both. The `F` drops are
legitimate — W1-T3 measured that all 22 branch drops across all 16 entries were `F`, and no
`IM`/`FE`/`R` ever occurred (`CLAUDE.md`, "Traps").

**No equality event would be answerable here either.** The decomposition reifies a *bound*
(`BC`), so `X_i = t` has no reified counterpart to descend into — [`increasing`](increasing.md)'s
observation, and the shift does not change it.

## Generated rules

**None.** There is no `cata/strictly_increasing.tex` (`ls cata/` → 16 files, none of this
name; 2026-09-21). Nothing is rendered here and nothing is claimed.

**The base's rules are not reproduced here** — they are [`increasing`](increasing.md)'s
and are rendered in that entry. What this session re-measured of them is only their verdicts,
below, because the strict variant's whole case rests on the base being validated.

## Status

**`nothing generated`** — and **no value in `catalog/README.md`'s six-item status legend fits
this entry.** That is stated rather than papered over, because choosing the nearest one would
be a fabrication in either direction.

- `nothing generated — blocked on G<n>` is the legend's only "nothing generated" form and **the
  gap number is required, not optional**. There is no gap. Writing `G8` there would convert a
  boundary note that [`increasing`](increasing.md#gaps) already carries — and that does not
  stop *it* being validated 2/2 — into a blocker, which it is not.
- `generated, unvalidated` and `not validatable` both assert that "rules exist in `cata/`".
  None do.
- `validated`, `partly validated` and `flagged` all presuppose rules to judge.

**The honest description is a state the legend has no word for: encodable today, not encoded.**
Of this session's fourteen entries, only this pair and its dual are in it — every other one is
blocked on a numbered gap. That is a finding about the legend as much as about the constraint,
and it is left visible for the legend's owner rather than resolved here.

What *is* established, and by what means:

- **The base is validated.** `make validate`, this session's own run, 2026-09-21:
  `---- cata/increasing.tex  (2 rules) ----`, two `VERDICT   : SOUND and MINIMAL`
  lines, each `readings  : 1 (1 sound, 0 unsound)` `(no binder)` and
  `cross-check: store sweep agrees with singleton reduction`.
- **Sound and minimal is a floor, not strength** (`catalog/README.md`). It means no premise is
  droppable — each of the base's rules has exactly one — not that the pair is the strongest
  schema available.
- **The shift is free at the encoding level**, by reading; **unexercised and unvalidated**, by
  the generator's own operator census. Both halves are in "Read this first" with their line
  numbers.
- **Nothing about this constraint is validated, flagged or refuted**, because there is nothing
  to judge.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:193` records `none specific` for this family, which is the condition
`catalog/TEMPLATE.md` attaches to this verdict — and it is the same verdict
[`increasing`](increasing.md#calibration-w3-t5-d-0013) carries off the same row. It is a
statement about the repo's literature index, which cost one session of web research over all
118 MiniZinc globals (`CLAUDE.md`, "Context budget"); this session did not search the web and
has no access.

There are **0** generated rules on this side, so no implication order could be stated even if a
shape were sourced. **Not compared on minimality**, per `catalog/README.md`: none of the three
sourced papers proves any explanation minimal, so the axis when it opens is implication
strength.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **none blocks this constraint.** Every schema and every index operator the decomposition needs exists (`rule1` BC channel, `rule4` two-literal clause, `OpShift` on both the `i` and the `t` families, `imap` to compose them). This row is the entry's finding, not an empty field |
| `G8` | **a boundary note, not a blocker, and [`increasing`](increasing.md#gaps) already carries it for `i`.** `ind_set` names only whole predefined ranges (`docs/DECOMP_FORMAT_NOTES.md:76`), so neither "`i ∈ [2,n]`" nor "`t ∈ [2,m]`" can be written and the range condition on a shifted index goes unprinted. The base is validated 2/2 with that note standing |
| — | **`G3`, `G7`, `G12`, `G13` and `G17` are all NOT this entry's.** No variable-vs-variable comparison, no instance-dependent chain, no integer sum, and — the one that separates this family from the rest of this session's fourteen — **no genuine auxiliary**: `B 1` is a reification the printer substitutes away (`decomps/_shapes-seq.md:26-29`) |

Extensions: **E0** (`CHRISTMAS_LIST.md:193`, and `decomps/increasing.md:15`: "**E0**, no new
schema"). Unlike in the `lex_*` entries, E0 needs no qualification here — the event vocabulary
exists as well as the schemas.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (run 2026-09-21, redirected to a file then grepped, never skimmed) → no entry
  of this name; `cata/increasing.tex` at **2 rules, 2 `SOUND and MINIMAL`**, quoted
  under Status. Run totals: **34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged;
  2 rules in 5 entries out of scope (underspecified artifact)**.
- `grep -o '\frac' cata/increasing.tex | wc -l` → **2**, consistent with the validator's
  rule count. (`grep -c` would return 1 — `CLAUDE.md`, "Traps".)
- `ls cata/` → 16 `.tex` files, none named `strictly_increasing.tex`.
- `ls catalog/_literature/` → `README.md`, `alldifferent.md`, `cumulative.md`, `gcc.md`.
- `python3 tools/mzn_coverage.py --rank` → `strictly_increasing` under
  `A no-literature + solver-decomposes`, ecode `E0`,
  `§9. Ordering, sorting, channelling:193`. Confirms the stub's tier row.
- `explenation generator.ml` read, not run → `:430` (`printind_name`), `:471`, `:503` (the two
  `Addint` printer cases), `:758-761` (the generator's own census of which index operators the
  decompositions use — the evidence that `tplus`/`tmoin` are unexercised), `:794-795`
  (`tplus`/`tmoin`), `:799-801` (`imap`/`OpSeq`, right-to-left), `:828`, `:842`, `:855`
  (shipped uses of `imap`), `:830-831` (`incr`), `:832-833` (`decr`), `:868` (`xbc`), `:883`,
  `:884` (the two emitting calls), `:879-893`. **Every line number was checked against the
  current file today** (W1-T14).
- `CHRISTMAS_LIST.md:193`, `:106-108` read → the literature, solver and route cells, and the
  legend.
- `decomps/increasing.md` (all 27 lines), `decomps/_shapes.md:32, 337-341`,
  `decomps/_shapes-seq.md:12-29` read → the four-constraint spec, `:12-16` on this variant, S1,
  the S1-vs-S5 distinction, and why `B 1` washes out.
- `docs/DECOMP_FORMAT_NOTES.md:76` read → G8.
- `catalog/increasing.md` and `catalog/README.md` read → the base entry's rendering and
  boundary note, and the status legend this entry reports as not fitting.
- `tools/data/minizinc-2.10.1-globals.txt:119` read → the name.
- **Not fetched, not written:** no paper. No published rule shape appears anywhere above.
- **Not run:** no generator value was added and nothing was compiled. The "shift is free" claim
  is **reasoning from reading the index-operator vocabulary**, labelled as such in place, and
  its three qualifications are stated with it.

**Discrepancies noted, not fixed (this session does not own those files).**

1. **`catalog/increasing.md` quotes `CHRISTMAS_LIST.md:193` as reading `**already correct in
   the repo**; cata/increasing.tex and cata/decreasing.tex are cleanly dual`.** That row was
   reworded on 2026-09-21 and now reads "each is **validated sound and minimal, 2/2**
   (2026-09-21). Wording fixed the same day: this row said 'already correct', which
   `catalog/README.md` forbids". The quote is of a superseded version; `increasing.md`'s own
   "Noted contradiction" paragraph, which flags the banned word, is what prompted the fix and
   now describes a state that no longer exists.
2. **`decomps/increasing.md:7` says the pair is "validated 2/2 each (task brief)"** and `:22`
   declines to re-verify "since the task brief already reports 2/2". Re-measured in this
   session's own `make validate` run: 2/2 each, confirmed. The number is right; its cited
   source was a task brief rather than a run, which `CLAUDE.md` distinguishes.
3. **`decomps/increasing.md:26-27` says `CHRISTMAS_LIST.md` and the task brief "agree is
   already correct".** `catalog/README.md` bans that word for a catalog entry; the defensible
   statement is `validated: sound and minimal at n,m <= 4`.
