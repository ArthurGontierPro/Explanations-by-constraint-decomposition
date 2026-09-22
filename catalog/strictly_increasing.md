# `strictly_increasing`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `strictly_increasing`, and no claim
> of that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — `A no-literature + solver-decomposes`, ecode `E0` (shared row with `increasing`, `decreasing` and `strictly_decreasing`) |
| **Status** | **`generated, unvalidated`** *by this catalog's instrument* — `make validate` cannot see this file (**W1-T18**). Measured by a second instrument: both rules **SOUND** over every strictly increasing assignment at every `n,m ∈ {1,2,3,4,5}` and both **MINIMAL**. Was `encodable today, not encoded` until this session (A-1) encoded it. See Status |
| **Generated** | **2** rules in `cata/strictly_increasing.tex` — **new 2026-09-22** (session A-1), from generator value `sincr` |
| **Validator** | **not covered — the validator cannot see this file.** `make validate` (run 2026-09-22) names no `strictly_increasing` entry, in scope or out: `validator.ml`'s entry lists are hardcoded and it never scans `cata/`. That is **W1-T18** |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:193` literature cell reads `none specific` |
| **Last measured** | 2026-09-22 (session A-1), `make check`, `make validate`, `grep -o '\frac' cata/strictly_increasing.tex \| wc -l`, and this session's own exhaustive assignment sweep with per-premise droppability and two controls. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

## Read this first: the shift was free, and it has now been run

**Superseded, 2026-09-22 (session A-1), and kept rather than deleted because the prediction
below is the point.** This section previously ended "the shift costs **no gap**; it costs one
unexercised pair of operators and one unrun validation", and named the exact operators the
strict variant would need. Both halves held: the operators are now exercised, the artifact
exists, and **nothing was added to the language** to make it happen — no constructor, no
schema, no printer case. `tplus`/`tmoin` had never been used by any decomposition; `sincr` is
the first use. What follows is the original reading, with the three qualifications it raised
answered in place.

### The original reading (2026-09-21), unchanged

`strictly_increasing` is [`increasing`](increasing.md) with its threshold moved by one.
[`increasing`](increasing.md) is **validated: sound and minimal at n,m ∈ {2,3,4}**, 2 rules, 2
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

   > **ANSWERED 2026-09-22.** `sincr` (`explenation generator.ml:957`) was added and run; the
   > artifact exists and both its rules are sound and minimal under this session's sweep. The
   > qualification was correct to raise and is now discharged by measurement rather than by
   > argument.
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

   > **STILL OPEN 2026-09-22, and for a different reason than expected.** The artifact now
   > exists, so it *could* be put in front of the validator — except that `make validate`
   > cannot see any new entry at all (**W1-T18**), so the question of how it parses a shifted
   > `t` remains unanswered by that instrument. This session's sweep answers the *soundness*
   > question independently: at `t = 1` the shifted threshold `t-1 = 0` leaves `[1,m]`, and the
   > premise `X_{i'} ≥ 0` is then trivially true — which is harmless, because the conclusion
   > `X_i ≥ 1` is trivially true too. Measured, not argued: 0 counterexamples, `t` swept over
   > all of `[1,m]` at every size.

**The answer, in one line:** the shift cost **no gap** — it cost one previously unexercised
pair of operators, now exercised, and one validation this session ran itself because the
repo's own validator cannot.

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

**Generator value:** `sincr`, `explenation generator.ml:957`.
**Emitted by:** `explainall [xbc] sincr "cata/strictly_increasing.tex"`, line **1182**, with
the seed `xbc` at **1136** — the same seed `increasing` uses, unchanged. The non-strict
siblings are emitted at `:1178` (`incr`) and `:1177` (`decr`).
**Spec:** **`decomps/increasing.md`** — its first line is
`# increasing, decreasing, strictly_increasing, strictly_decreasing`, and `:12-16` is about
this constraint specifically.

> **Stub field corrected.** The auto-stub read `**Spec:** none — this constraint has no
> `decomps/strictly_increasing.md`.` That probe is an exact-filename `os.path.isfile`, and it
> misses a spec that covers four constraints under the first one's name. A spec exists, it
> addresses this variant in its own paragraph, and this entry is written against it.

**The value, in full**, so the one-word claim can be checked rather than believed:

```ocaml
let sincr = [Decomp (1, rule1, [Global_devent (true, X, id, id, BC); Reified_devent (true, (B 1), id, id)]);
             Decomp (2, rule4, [Decomp_devent (false, (B 1), id, id);
                                Decomp_devent (true, (B 1), imap [imoin 1;tmoin 1], imap [iplus 1;tplus 1])])]
```

It is `incr` with `imoin 1`/`iplus 1` replaced by `imap [imoin 1;tmoin 1]`/`imap [iplus 1;tplus 1]`
and nothing else. **Those are the two operators this entry named on 2026-09-21**, before
anything was run.

**Why that composition and not another.** Under the order encoding `B1_{i,t} ⇔ X_i ≥ t`:

| constraint | meaning | clause |
|---|---|---|
| `increasing` | `∀t: X_i ≥ t → X_{i+1} ≥ t` | `¬B1_{i,t} ∨ B1_{i+1,t}` |
| `strictly_increasing` | `∀t: X_i ≥ t → X_{i+1} ≥ t+1` | `¬B1_{i,t} ∨ B1_{i+1,t+1}` |

so the second literal moves in **both** families at once: ascending `imap [iplus 1; tplus 1]`.
The descending operator carries an event that matched the second literal back to the clause's
base index `(i-1,t-1)`, hence `imap [imoin 1; tmoin 1]`. The two are inverses and the
generator's own run report says so (`print_devent`, `:232`).

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

**Events the generator was asked to explain:** **two** — `X_i ≥ t` and `X_i < t`, from the
single seed `xbc`, exactly as `increasing` is asked. Read off the
`%% generator diagnostics (W1-T3)` footer of `cata/strictly_increasing.tex`:

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i} \geq t` | 2 | **1** | `F` 1 |
| `X_{i}<t` | 2 | **1** | `F` 1 |

**That footer is byte-identical to `cata/increasing.tex`'s**, which is the sharpest available
statement that the shift changed the rules and not the derivation: same two events, same two
candidates, same single `F` discard each, same rule count. The `F` drops are
legitimate — W1-T3 measured that all 22 branch drops across all 16 entries were `F`, and no
`IM`/`FE`/`R` ever occurred (`CLAUDE.md`, "Traps").

**No equality event would be answerable here either.** The decomposition reifies a *bound*
(`BC`), so `X_i = t` has no reified counterpart to descend into — [`increasing`](increasing.md)'s
observation, and the shift does not change it.

## Generated rules

`grep -o '\frac' cata/strictly_increasing.tex | wc -l` → **2**, measured 2026-09-22.

| # | rule | verdict (second instrument; **not** `make validate`) |
|---|---|---|
| 1 | `X_{i'} ≥ t'`, `i'=i-1`, `t'=t-1`  ⊢  `X_i ≥ t` | **SOUND**, **MINIMAL** |
| 2 | `X_{i'} < t'`, `i'=i+1`, `t'=t+1`  ⊢  `X_i < t` | **SOUND**, **MINIMAL** |

Beside [`increasing`](increasing.md)'s, which are the same two rules with `t' = t`:

| | `increasing` | `strictly_increasing` |
|---|---|---|
| upward | `X_{i-1} ≥ t ⊢ X_i ≥ t` | `X_{i-1} ≥ t−1 ⊢ X_i ≥ t` |
| downward | `X_{i+1} < t ⊢ X_i < t` | `X_{i+1} < t+1 ⊢ X_i < t` |

### How the verdicts were obtained

**This session's own sweep, not `make validate`.** Exhaustive enumeration of every strictly
increasing `X ∈ [1,m]^n`, for every `n, m ∈ {1,2,3,4,5}` — **`n = 1` included**. Off-the-end
indices follow `validator.ml`'s own stated convention (`:69-74`): a premise naming a
non-existent variable is **FALSE**, so the rule instance cannot fire.

**0 counterexamples on both rules at every size swept.** Firings at `n,m ≤ 4`: **62 / 39**; at
`n,m ≤ 5`: **222 / 150**. **Both minimal**: each rule has exactly one premise and dropping it
fails **222 / 351** times.

**At `n = 1` both rules fire 0 times**, and that is said out loud rather than reported as
"0 counterexamples". Every premise names `X_{i-1}` or `X_{i+1}`, neither of which exists at
`n = 1`, so there is nothing to be unsound about. This is a different `n = 1` story from
[`alldifferent`](alldifferent.md)'s (fires, and fails) and from [`minimum`](minimum.md)'s
(fires, and holds); the catalog now has an instance of each.

### The shift is not cosmetic, measured two ways

A rule that merely relabels `increasing`'s would also pass a soundness sweep on strictly
increasing sequences, since every strictly increasing sequence is increasing. Two controls
separate the cases:

1. **Run against *non-strictly* increasing sequences, both rules FAIL** — **103** and **155**
   counterexamples at `n,m ≤ 4`. So they genuinely require strictness and are not
   `increasing`'s rules under another name.
2. **On the strict model they fire *more* than `increasing`'s own rules do** — **222 / 150**
   against **150 / 78** over the same assignments — and the firing sets are supersets, since
   `X_{i-1} ≥ t` implies `X_{i-1} ≥ t−1`. **Strictly stronger, not merely different.**

That second number is worth keeping beside `catalog/README.md`'s warning that sound-and-minimal
is a floor: here the floor is cleared *and* a strength comparison exists, because there is a
sibling rule set to compare against. Most entries have no such sibling.

## Status

**`generated, unvalidated`** — by this catalog's instrument, for the same reason
[`maximum`](maximum.md) and [`minimum`](minimum.md) carry it: `make validate` cannot see the
file (**W1-T18**).

**It is not `validated: sound and minimal at n,m ∈ {2,3,4}`.** That legend value means every
rule got `SOUND and MINIMAL` from `make validate`, and no rule here went through `make validate`
at all. **Nor is it the legend's plain "nobody has looked"**: somebody looked, over a wider
range than the validator's and with two controls the validator does not run.

### The status this entry used to carry, and what its life cycle shows

This file has now held three statuses in two days, and the sequence is the finding:

1. **`nothing generated`, with the observation that no legend value fitted** (2026-09-21).
   That observation is what caused `encodable today, not encoded` to be *added* to
   `catalog/README.md`'s legend — this entry was the reason the legend grew.
2. **`encodable today, not encoded`** (2026-09-21, the new value's first case).
3. **`generated, unvalidated`** (2026-09-22, this session).

**`encodable today, not encoded` is the one status in the legend a session can close by
typing.** Every other one names something to *discover*: a gap, a verdict, a paper. This one
names work nobody has done, and it stayed true for one day. Whoever maintains the legend should
expect it to be a short-lived state by construction, not a resting place — which is an argument
for treating any entry that carries it as a **task**, exactly as this session's brief did.

What was established before this session, and by what means:

- **The base is validated.** `make validate`, this session's own run, 2026-09-21:
  `---- cata/increasing.tex  (2 rules) ----`, two `VERDICT   : SOUND and MINIMAL`
  lines, each `readings  : 1 (1 sound, 0 unsound)` `(no binder)` and
  `cross-check: store sweep agrees with singleton reduction`.
- **Sound and minimal is a floor, not strength** (`catalog/README.md`). It means no premise is
  droppable — each of the base's rules has exactly one — not that the pair is the strongest
  schema available.
- **The shift is free at the encoding level**, by reading; **unexercised and unvalidated**, by
  the generator's own operator census. Both halves are in "Read this first" with their line
  numbers. **Both are now discharged**: the operators are exercised and the rules are swept.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.**

`CHRISTMAS_LIST.md:193` records `none specific` for this family, which is the condition
`catalog/TEMPLATE.md` attaches to this verdict — and it is the same verdict
[`increasing`](increasing.md#calibration-w3-t5-d-0013) carries off the same row. It is a
statement about the repo's literature index, which cost one session of web research over all
118 MiniZinc globals (`CLAUDE.md`, "Context budget"); this session did not search the web and
has no access.

There are **2** generated rules on this side as of 2026-09-22, but still no published shape to
order them against, so the verdict is unchanged. **Not compared on minimality**, per
`catalog/README.md`: none of the three sourced papers proves any explanation minimal, so the
axis when it opens is implication strength.

**An implication order *within* this repo does exist and is recorded above**, under "The shift
is not cosmetic": these rules are strictly stronger than [`increasing`](increasing.md)'s on
strictly increasing sequences. That is a comparison against a sibling entry, not a calibration
against literature, and it is deliberately not reported in this section.

## Gaps

| gap | what it blocks here |
|---|---|
| — | **none blocks this constraint, and this is now measured rather than read.** Every schema and every index operator the decomposition needs existed already (`rule1` BC channel, `rule4` two-literal clause, `OpShift` on both the `i` and the `t` families, `imap` to compose them), and the shipped `sincr` uses exactly those. **No constructor, schema or printer case was added.** This row is the entry's finding, not an empty field |
| `G8` | **a boundary note, not a blocker, and [`increasing`](increasing.md#gaps) already carries it for `i`.** `ind_set` names only whole predefined ranges (`docs/DECOMP_FORMAT_NOTES.md:76`), so neither "`i ∈ [2,n]`" nor "`t ∈ [2,m]`" can be written and the range condition on a shifted index goes unprinted. The base is validated 2/2 with that note standing, and **this entry's sweep shows the unprinted `t` bound is harmless**: at `t = 1` the premise `X_{i'} ≥ 0` is vacuously true and so is the conclusion `X_i ≥ 1`, so no counterexample arises from it |
| — | **`G3`, `G7`, `G12`, `G13` and `G17` are all NOT this entry's.** No variable-vs-variable comparison, no instance-dependent chain, no integer sum, and — the one that separates this family from the rest of this session's fourteen — **no genuine auxiliary**: `B 1` is a reification the printer substitutes away (`decomps/_shapes-seq.md:26-29`) |

Extensions: **E0** (`CHRISTMAS_LIST.md:193`, and `decomps/increasing.md:15`: "**E0**, no new
schema"). Unlike in the `lex_*` entries, E0 needs no qualification here — the event vocabulary
exists as well as the schemas.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

### 2026-09-22 (session A-1) — what changed

- `explenation generator.ml` edited (this session owns it): value `sincr` at line **957**,
  `caveat` block and `explainall` call at **1182**. `tplus`/`tmoin` (`:876-877`) are used by a
  decomposition for the first time. Run under OCaml 5.1.1 in the `baguette` switch; exit 0,
  empty stderr; `cata/strictly_increasing.tex` produced and committed.
- `make check` (run 2026-09-22, redirected then grepped) → **GATE PASSED**, exit 0, **22** `ok`
  lines, no `FAIL`. Every pre-existing non-orphaned `cata/*.tex` reproduces byte-for-byte, as
  does `exp.tex`; the orphan set is unchanged (`sum.tex`). **The warning census did not move**:
  0 / 6 / 36 / 61, identical to the run before this change.
- `make validate` (run 2026-09-22, redirected then grepped) → **34 rules checked in 11 entries:
  13 SOUND and MINIMAL, 21 flagged; 4 rules in 5 entries out of scope.** Unchanged by this
  entry, and it names no `strictly_increasing` entry at all — the direct measurement of W1-T18.
- An exhaustive assignment sweep over every strictly increasing `X ∈ [1,m]^n` for every
  `n,m ∈ {1,2,3,4,5}`, with per-premise droppability, plus **two controls** (the same rules
  against non-strictly increasing sequences; `increasing`'s rules against the strict model).
  Written and run by this session; counts quoted from the run.
- `grep -o '\frac' cata/strictly_increasing.tex | wc -l` → **2**.
- Line numbers re-checked by `grep -n` after the final edit (W1-T14). **Note that the
  2026-09-21 numbers below have all moved**, because this session inserted values above them;
  they are left as written and dated rather than silently renumbered.

### 2026-09-21 — the original entry

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
   statement is `validated: sound and minimal at n,m ∈ {2,3,4}`.
