# `at_most`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `at_most`,
> and no claim of that kind is made anywhere in this catalog.** See
> `catalog/README.md`, "What the catalog claims".

| | |
|---|---|
| **Tier** | **A** (`A no-literature + solver-decomposes`), ecode `E0` — `python3 tools/mzn_coverage.py --rank --json`, run 2026-09-21 |
| **Status** | `flagged` — the one rule is **`NOT MINIMAL`**. It is also **`SOUND`**, and *neither verdict came from `make validate`*: see Validator |
| **Generated** | **1** rule in `cata/at_most.tex` — **new 2026-09-22**, the artifact that closed `G1` |
| **Validator** | **not covered — the validator cannot see this file.** My `make validate` run (2026-09-22) names no `at_most` entry, in scope or out: `validator.ml`'s entry lists are hardcoded and it never scans `cata/`. That is **W1-T18**, opened 2026-09-22 |
| **Calibration** | **no published rule exists** — `CHRISTMAS_LIST.md:128` records `none specific` |
| **Last measured** | 2026-09-22, `make check`, `make validate`, `grep -o '\frac' cata/at_most.tex \| wc -l`, and reads of `cata/at_most.tex` and `explenation generator.ml`. The Tier row is the 2026-09-21 `mzn_coverage.py` run, unre-run |

**Where the soundness numbers in this entry come from, once, so no line below has to
repeat it.** `cata/at_most.tex` is **not** validated by `make validate`. Every soundness and
minimality figure here is **G-1's own exhaustive check over all stores at `n,m ≤ 4`**, carried
into the artifact's `%% CAVEAT` footer by the generator's `caveat` mechanism and quoted from
there. It is a measurement, by a different instrument from the one the rest of this catalog
uses, and it is **not** a validator verdict. Nothing here is "validated".

## Constraint

`at_most(int: n, array[int] of var int: x, int: v)` — the value `v` occurs at most `n` times
in `x`. Both `n` and `v` are parameters in the standard MiniZinc global, so the constraint has
no decision variable other than `x`. **The generator spells the threshold `c`**, not `n`
(`n` is already the size of the index range `[1,n]` in every printed rule), and this entry
follows the generator: `c` below is MiniZinc's `n`.

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

**Generator value:** `atmost`, `explenation generator.ml:994-995` (verified today).
**Emitted by:** `explainall [xacv] atmost "cata/at_most.tex"`, line **1061**, under a
`caveat := [...]` block at **1053-1060** whose text the artifact reproduces verbatim.
**Seed event:** `xacv`, line **1022**.
**Spec:** [`decomps/at_most.md`](../decomps/at_most.md); shape **S2** in `decomps/_shapes.md`
("reify-and-count: Boolean sum against a bare threshold").

The chain is two atomic constraints, as the spec says:

```ocaml
let atmost = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
              Decomp (2, rule5, [Decomp_devent (true, (B 1), id, oniin (DCard ("S",D 1,EQ,BPar ("c",1))))])]
```

1. `B_i ⇔ X_i = v` — `rule1`, AC.
2. `∑_i B_i ≤ c` — `rule5`, a single `Decomp_devent` with **no** `Reified_devent`.

**What changed on 2026-09-22, and it is the whole reason this entry was rewritten.** Step 2's
ascending index op is no longer `oni` (all of `[1,n]`) but `oniin (DCard ("S", D 1, EQ, BPar
("c",1)))` — "a subset `S` of `[1,n]` with `|S| = c+1`". `DCard` is one of four new `ind_set`
formers (`explenation generator.ml:48-52`) that **print their own definition**, so the
threshold reaches the page as data rather than living only in the author's choice of `rule5`
over `rule6`/`rule7`. That is **G1**, closed in fact and not only in machinery.

**And the value `v` reaches the page from the other end** — not from the decomposition but
from the **seed event**. `xacv` (`:1022`) is the `X` event with a side condition on its value
index: `Set (T 1, IN, DPar ("\{v\}", D 2))`, printed `t \in \{v\},~\{v\} \subseteq [[1,m]]`.
So the rule states which value it is about. Two things follow that a reader should not have to
infer:

- **`\{v\}` is encoded as a *named parameter subset*, not as a singleton.** `DPar` carries a
  name and a parent set and prints containment; nothing in the artifact says `|\{v\}| = 1`.
  The name happens to be the two characters `\{v\}`, which renders as a singleton and is not
  one to the generator. Read off `:1022` and `:536`, not measured.
- **`DCard` reprints its full definition at every mention**, so `S \subseteq [[1,n]],~|S|=c+1`
  appears **twice** in the premise below. That is a rendering property of `printind_set`
  (`:537`), not two different conditions.

**Why `|S| = c+1` and not `|S| = c`** is argued in the generator's own comment block
(`:957-993`) and is not re-derived here: `apprim` appends the parent index's own membership to
the sibling's modifiers, so the premise says `i ∈ S` as well as `∀i' ∈ S, i' ≠ i`, and the
`c+1` members of `S` other than `i` are then exactly `c` witnesses. Writing `|S| = c` with `i`
excluded instead makes the rule vacuous.

**`at_most` and `all_different` are no longer the same file.** The previous version of this
entry measured that the S2 encoding of `at_most` was `alldiff` character for character and
produced a byte-identical artifact. That is now false in both halves: the decomposition
differs at step 2, and `cata/at_most.tex` differs from `cata/alldifferent.tex`. The *finding*
that made it true — a threshold with nowhere to live — is what `DCard` fixed.

## Scope of this entry

**Events the generator was asked to explain:** two, both from the single seed event `xacv`
(arc consistency) — `X_i = t` and `X_i ≠ t`, each carrying the value side condition
`t \in \{v\},~\{v\} \subseteq [[1,m]]`. **Nothing was asked about `c`**: the threshold is
index data, not an event, so there is no literal to name it with and no rule concludes
anything about it.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t,~t \in \{v\},~\{v\} \subseteq \llbracket1,m\rrbracket` | 1 | **0** | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t,~t \in \{v\},~\{v\} \subseteq \llbracket1,m\rrbracket` | 1 | **1** | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |

The file states the empty answer itself:

```
%%   ** NO RULE EMITTED for X_{i}=t,~t \in \{v\},~\{v\} \subseteq \llbracket1,m\rrbracket: 1 candidate(s), all blocked **
```

The `F` discard on `X_i = t` is the legitimate kind — a branch reaching a constraint that is
not reified — and it is the same one `cata/alldifferent.tex` takes. `CLAUDE.md` records why
the missing `X_i = t` rule is **not** a bug: deriving it from a `≤`-direction sum needs
counting across sums, which is **E4**. G1 did not change that and was never going to.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/at_most.tex`.

## Generated rules

Rendered from `cata/at_most.tex` (single line, no trailing newline;
`grep -o '\\frac' cata/at_most.tex | wc -l` → **1**; `make check` independently prints
`ok at_most.tex (1 frac-occurrences)`).

### Rule 1 — `X_i ≠ t`

```
X_{i'} = t ,  ∀i' ,  i' ≠ i ,  i' ∈ S ,  S ⊆ [1,n] ,  |S| = c+1 ,
              i ∈ S ,  S ⊆ [1,n] ,  |S| = c+1 ,
              t ∈ {v} ,  {v} ⊆ [1,m]
------------------------------------------------------------------ ⊢
X_{i} ≠ t ,  t ∈ {v} ,  {v} ⊆ [1,m]
```

(The second `S ⊆ [1,n], |S| = c+1` is `printind_set` restating `S`'s definition at its second
mention, not a second condition. The conclusion carries the value side condition too, which is
why it is shown below the line.)

**Verdict:** `SOUND`, and **`NOT MINIMAL`**.
**Measured by:** G-1's exhaustive check over all stores at `n,m ≤ 4`, all `v` and all `c` —
**not** by `make validate`, which does not know this file exists (W1-T18). Quoted from the
artifact's own `%% CAVEAT (G-1, 2026-09-22)` footer:

```
%% exhaustive check over all n,m <= 4, all v and all c: SOUND, 4706 firing cases, no
%% counterexample. NOT minimal: dropping `i in S` leaves it sound (same 4706 cases),
%% because a premise with i outside S is unsatisfiable under at_most(c). That conjunct
%% is appended by apprim, not written by the decomposition.
```

**4706 firing cases, 0 counterexamples**; dropping `i ∈ S` leaves the rule sound over the same
4706 cases, so that conjunct is droppable and the rule is not minimal. **The droppable
conjunct is the machinery's, not the decomposition's**: `apprim` appends the parent index's
membership to every sibling it builds, which is also why `cata/alldifferent.tex`'s premise ends
with `i ∈ [1,n]`. `docs/ROADMAP.md:57` (W1-T13) now carries this as evidence.

**In words.** If some `c+1` positions include `i` and the other `c` of them all take the
bounded value `v`, then `v`'s quota is used up and `X_i ≠ v`. That is a real `at_most`
argument, and it is the first rule in this catalog whose premise *states the threshold*.

## Status

**`flagged`**

One rule is generated, and its measured verdict is `NOT MINIMAL`, which is one of the flagged
verdicts in `catalog/README.md`'s legend. Three things this status does and does not say:

- **It is not a validator verdict.** `make validate` (my run, 2026-09-22) does not mention this
  entry at all — not in scope, not out of scope. `validator.ml`'s lists are hardcoded and it
  never scans `cata/`, which is **W1-T18** on the roadmap, opened the same day this file was
  generated. So the project's only correctness gate is silent here, and the verdict above comes
  from a hand-written exhaustive check instead.
- **Sound is established, at those sizes, by that check**; 4706 firing cases with no
  counterexample at `n,m ≤ 4` is a measurement, not a proof for general `n,m`.
- **`NOT MINIMAL` here is mild, and it is not about strength.** The droppable conjunct is
  `i ∈ S`, which is unsatisfiable to violate: a store with `i ∉ S` cannot fire the rule under
  `at_most(c)` anyway. Minimality is premise-droppability, so a redundant-but-true conjunct
  flags the rule without weakening it — and, equally, dropping it would not make the rule
  stronger. W1-T13 is the standing item for the fact that nothing in this repo measures
  strength.

`G1` is **closed** and this file is the demonstration; the entry's previous status,
`nothing generated — blocked on G1`, was retired on 2026-09-22.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule exists.**

`CHRISTMAS_LIST.md:128`'s literature cell is `none specific` and names no paper, which is the
condition `catalog/TEMPLATE.md` attaches to this verdict. It is **not** `pending sourcing`:
pending is for a row that cites something nobody has read, and this row cites nothing.

**This verdict is unchanged by the arrival of a rule, and the reason it is unchanged has
changed.** It used to rest on there being no premise on either side; now there is a premise on
ours — `∃S ⊆ [1,n], |S| = c+1, i ∈ S, ∀i' ∈ S \ {i}: X_{i'} = v` — and still none on theirs, so
there is still nothing to place in an implication order. What the verdict does **not** say is
that no paper explains a cardinality constraint: the same file cites Downing, Feydy and Stuckey
2012 for `global_cardinality` (`CHRISTMAS_LIST.md:127`), and `at_most` is a
`global_cardinality` with one covered value. Whether that transfers is for whoever sources
`catalog/_literature/` next; this entry asserts nothing about it.

## Gaps

| gap | what it blocks here |
|---|---|
| `G1` | **closed 2026-09-22, and this entry is the demonstration.** `DCard` carries the threshold as index data, so `|S| = c+1` prints. `at_most(2,…)` and `at_most(3,…)` no longer render identically |
| `G8` | **closed as a blocker here.** The counted value is written `DPar ("\{v\}", D 2)` on the seed event and prints. What remains is a *rendering* point, not a gap: the encoding is a named subset, so nothing in the artifact asserts that `\{v\}` is a singleton |
| `E4` | not a gap — the missing `X_i = t` direction still needs counting across sums, per `CLAUDE.md` and `decomps/all_different.md`. Unchanged by G1 |
| `G3` | only for the general MiniZinc form in which `v` may be a variable. D-0003 and `decomps/at_most.md` both take the parameter reading, and the generator's own comment (`:980-981`) says G3 is why `v` has to be a parameter |
| — (not a gap) | **the printer still requires a value index on every `X` literal** — `hd (isppp … @ isttt …)` in `printglobal_eventtex`, **`explenation generator.ml:585`** (re-measured today; this entry used to cite `:512`). G-1 did not remove that requirement, it routed around it: the value index is kept and given a side condition instead of being baked in as a constant |
| — (not a gap) | **W1-T18**: the gate cannot see this entry. Not a format gap; a hole in `validator.ml` |

Extensions: **E0** — `CHRISTMAS_LIST.md:128`, verbatim: "**E0** — this is `rule5/6/7` exactly as
built". That cell was right about the schemas all along; what it was silent about, G1 and G8,
is what took until 2026-09-22.
Source: `docs/DECOMP_FORMAT_NOTES.md` (consolidated wave-two numbering; **G1 at line 10**,
**G8 at line 87**, both re-measured today — this entry previously cited `:76` for G8).

## How this entry was produced

- `grep -o '\\frac' cata/at_most.tex | wc -l` → **1**. (`grep -c` returns 1 for every entry —
  `CLAUDE.md`, "Traps" — so it is not used.)
- `make check` (run 2026-09-22, redirected then grepped) → `ok alldifferent_except.tex (1
  frac-occurrences)`, `ok among.tex (2 …)`, `ok at_most.tex (1 …)`, `GATE PASSED`. The artifact
  reproduces byte-for-byte; the gate proves that and nothing about correctness.
- `make validate` (run 2026-09-22, redirected then grepped, per `CLAUDE.md` "Verify before you
  report") → `== 34 rules checked in 11 entries: 13 SOUND and MINIMAL, 21 flagged ==` and
  `== 4 rules in 5 entries out of scope (underspecified artifact) ==`. **No line of that run
  names `at_most`.** That is the Validator row, and it is W1-T18.
- `cata/at_most.tex` read, not run → the rule, the diagnostics footer and the `%% CAVEAT`
  block. **Every soundness/minimality number in this entry is quoted from that block**, which
  records G-1's exhaustive check at `n,m ≤ 4`; none of them was produced by this session and
  none of them is a validator verdict.
- `explenation generator.ml` read, not run: `:48-52` (the four new `ind_set` formers),
  `:520-525` (`ind_set_defined`, which still refuses `D of int` beyond 3 and `D2`), `:534-537`
  (`printind_set` for `DSub`/`DExc`/`DPar`/`DCard`), `:585` (the `hd` in
  `printglobal_eventtex`), `:890-891` (`alldiff`), `:957-993` (the `c+1` argument),
  `:994-995` (`atmost`), `:1022` (`xacv`), `:1053-1061` (the caveat block and the
  `explainall` call). All line numbers re-measured today (W1-T14).
- `CHRISTMAS_LIST.md:128` read → the literature, solver and route cells, quoted verbatim above;
  `:106-109` → the solver legend; `:127` → the `global_cardinality` citation named in
  Calibration.
- `docs/DECOMP_FORMAT_NOTES.md:10` and `:87` read → G1's and G8's wording, at their current
  lines.
- `docs/ROADMAP.md:57` and `:62` read → W1-T13 (which now cites this entry's `NOT MINIMAL` as
  evidence) and W1-T18.
- `tools/data/minizinc-2.10.1-globals.txt:30` read → the name.
- **Nothing was run from a scratch copy of the generator for this version of the entry.** The
  previous version's scratch-run measurements are superseded by the shipped artifact and have
  been removed rather than left to look like current evidence.
- **Not fetched, not read:** the MiniZinc library (not vendored here) and any paper. No web
  access was used.

**Discrepancies noted, not fixed** (none of these files is this session's).

1. **`decomps/at_most.md:17-19` cites `alldifferent`'s `rule5` step at "generator line 388".**
   Measured 2026-09-22: `alldiff` is at **890-891**. The value name still resolves; the number
   has now rotted twice (it was measured at 809 on 2026-09-21). W1-T14.
2. **`decomps/at_most.md`'s "`v` … baked in as constants, not events" is still not encodable,
   and the shipped artifact does something else.** `v` is not baked in: it rides on the seed
   event's value index as a `DPar` side condition. The spec's G1 analysis was right and is now
   spent; its treatment of `v` remains wrong in the direction it proposed.
3. **`decomps/at_most.md` and `docs/DECOMP_FORMAT_NOTES.md:10` both present G1 as open.** It is
   closed as of `1e747ee` and this file is the evidence. Neither document is this session's.
