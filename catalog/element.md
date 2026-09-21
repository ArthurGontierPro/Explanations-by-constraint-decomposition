# `element`

> **This entry lists the rules this method generated for the events it was asked to
> explain. It is not a list of all valid explanations of `element`, and no claim of
> that kind is made anywhere in this catalog.** See `catalog/README.md`, "What the catalog
> claims".

| | |
|---|---|
| **Tier** | **A** — no literature + solver decomposes (`tools/mzn_coverage.py --rank`, ecodes `E0`) |
| **Status** | `partly validated` |
| **Generated** | 6 rules in `cata/element.tex` |
| **Validator** | 2 `SOUND and MINIMAL`, 4 `VACUOUS` |
| **Calibration** | **no published rule** — `CHRISTMAS_LIST.md:194` records "none found" |
| **Last measured** | 2026-09-21, `make validate` (E2's own run) and `python3 tools/mzn_coverage.py --rank --json` |

## Constraint

`element(var int: i, array [int] of var int: x, var int: v)`

`v = x[i]`: the value `v` is the `i`-th entry of the array.

**Provenance of the signature:** not vendored in this repo.
`tools/data/minizinc-2.10.1-globals.txt:61` carries the *name* only, and MiniZinc ships
several arities and index-set variants of it. The signature above is recall; the
decomposition below is read off the generator and is quotable.

## Published explanation

**Citation:** none. `CHRISTMAS_LIST.md:194` records the literature column as `none found` —
a searched-and-empty finding, phrased differently from the plain `none` used elsewhere.

**Rule shape:** nothing to source. `catalog/_literature/` holds `alldifferent`, `cumulative`
and `gcc` only.

**One claim in that row needs the counts beside it.** It says "`cata/element.tex` generates 6
rules; **2 of 6 are validated sound-and-minimal**, the rest unvalidated". The "rest
unvalidated" is now out of date in the direction of being *worse*: the remaining four are not
unvalidated, they are **`VACUOUS`** — measured, with the reason below.

## Solver support

| | |
|---|---|
| Chuffed | `decomp` |
| Geas | absent |
| Choco LCG | `[C]` present |

Source: `CHRISTMAS_LIST.md:194`, solver-column legend at `CHRISTMAS_LIST.md:106-108`.

## Decomposition used here

**Generator value:** `elem`, `explenation generator.ml:834-838`
**Emitted by:** `explainall [xac;i;v] elem "cata/element.tex"`, line 885
**Spec:** `decomps/element.md` (shape **P3** in `decomps/_shapes-perm.md`, "three-way channel
via cross-variable OR-clauses"). **Its line citation "lines 692-696" no longer resolves** —
the value is at 834-838.

```ocaml
let elem = [Decomp (1, rule1, [Global_devent (true, X, id, id, AC); Reified_devent (true, (B 1), id, id)]);
            Decomp (2, rule1, [Global_devent (true, I, id, id, AC); Reified_devent (true, (B 2), id, id)]);
            Decomp (3, rule1, [Global_devent (true, V, id, id, AC); Reified_devent (true, (B 3), id, id)]);
            Decomp (4, rule4, [Decomp_devent (false, (B 3), foralli, i_out); Decomp_devent (false, (B 2), forallt, t_out); Decomp_devent (true,  (B 1), id, id)]);
            Decomp (4, rule4, [Decomp_devent (true,  (B 3), foralli, i_out); Decomp_devent (false, (B 2), forallt, t_out); Decomp_devent (false, (B 1), id, id)])]
```

- **steps 1-3, `rule1` ×3** — one arc-consistent channel per user variable:
  `B1_{i,t} ⇔ X_i = t`, `B2_i ⇔ I = i`, `B3_t ⇔ V = t`. This is `element`'s "five-`Decomp`
  detour", and `docs/DECOMP_FORMAT_NOTES.md` **G9** names it: there is no `Global ⇔ Global`
  channel schema, `rule1` is fixed to `Global ⇔ Reified`, so an array-to-array (here
  scalar-to-array) channel has to be built out of three reifications and clauses.
- **steps 4-5, `rule4` ×2** — the biconditional `(I = i ∧ V = t) ⇔ X_i = t`, De Morgan-expanded
  into two clauses: `¬B3_t ∨ ¬B2_i ∨ B1_{i,t}` and `B3_t ∨ ¬B2_i ∨ ¬B1_{i,t}`.

**Three `var_name` constructors are live here at once — `X`, `I`, `V` — and `I` is the one
`CLAUDE.md` warns about.** `I` belongs to both `ind_name` and `var_name`, OCaml resolves the
ambiguity silently, and `ocamlc -w +40+41+42` reports it (31 warnings after W1-T7; the census
lives in `make check`). A site that means `var_name.I` and gets `ind_name.I` is a semantic bug
with no compile error. Nothing in this entry is claimed to *be* such a bug; it is recorded
because `element` is the one shipped decomposition where the collision is live.

### The defect: `V` and `I` are scalars carrying a quantifier they do not need

**This is why four of six rules are `VACUOUS`, it is diagnosed and confirmed, and it is not
fixed.** Roadmap W1-T9 (`docs/ROADMAP.md:53`) carries it; the diagnosis is W2-C's, read off
the source.

In `Decomp 4`, the descending index operator composed onto `B3` (the **`V`** channel) is
`foralli`, and the one composed onto `B2` (the **`I`** channel) is `forallt`. Each scalar has
been given *the other variable's* quantifier. But `V` and `I` are scalar globals — one
instance each, no array index — so at a fixed query `(i,t)` they need **no binder at all**.
What should stand there is plain point substitution, `id`, exactly as `B1` has in the same
clause.

The printed consequence is premises reading `∀t: V = t` and `∀i: I = i`, which **no store
satisfies**: a scalar cannot equal every value in `[1,m]`. Hence `VACUOUS` — "sound, but no
store in scope satisfies the premises, so the rule can never fire"
(`docs/VALIDATOR.md:227-228`).

**The obvious fix does not work, and this has been tried.** `docs/ROADMAP.md:47` (W1-T1)
records that W3-S attempted the two principled remedies and **both made the verdict worse,
4 `VACUOUS` → 4 `UNSOUND`**, and then stopped — recorded there as the right call. The reason
is scope, not substitution: the correct rule needs **one binder scoping both premises
jointly** (`∃t. V = t ∧ X_i ≠ t`), and the printer scopes binders per literal while
`validator.ml:333-336` binds such an index as a per-literal `∃`. No parser change rescues it.
`OpPoint` (the `gcc` repair's unbound-but-ranged emitter) has landed, so **once binders have
rule-level scope the fix is two tokens in `elem`'s `Decomp 4`** — that is the roadmap's
assessment, and this entry adopts it rather than proposing anything.

## Scope of this entry

**Events the generator was asked to explain:** six, from three global events —
`xac` (`explenation generator.ml:869`) giving `X_i = t` / `X_i ≠ t`,
`i` (line 872) giving `I = i` / `I ≠ i`, and
`v` (line 873) giving `V = t` / `V ≠ t`.

| event | candidates | rules emitted | dropped |
|---|---|---|---|
| `X_{i}=t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `X_{i} \neq t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `I=i` | 2 | **0** | `dropped F 2` — `** NO RULE EMITTED for I=i: 2 candidate(s), all blocked **` |
| `I \neq i` | 2 | 2 | `dropped F 0, cycle 0, duplicate 0, undefined index set 0` |
| `V=t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |
| `V \neq t` | 2 | 1 | `dropped F 1, cycle 0, duplicate 0, undefined index set 0` |

**`I = i` gets nothing.** Both candidate branches reach a blocking `F` leaf, and W1-T3's
diagnostics say so explicitly rather than leaving the reader to infer completeness from an
absence. A rule concluding `I = i` would have to say something like "every other index is
excluded" or "position `i` is the only one carrying `V`'s value", and neither is reachable:
the first needs a universally quantified premise over `i' ≠ i` on a *scalar* channel, which
`addprim` could build but `rule4` never calls for on `B2`; the second needs the same joint
binder scope that W1-T1 blocks.

**Flagged, because it contradicts `CLAUDE.md`.** The "Traps" section says
`element.tex`'s `I=i` "is the same case" as `alldifferent`'s missing equality, and prices both
at **E4** — "counting across sums". That attribution does not fit this decomposition:
`alldifferent` is `rule1` + `rule5`, a Boolean sum, and the argument there is that an equality
is not derivable from a `≤` direction. **`elem` contains no Boolean-sum schema at all** — it
is `rule1` ×3 + `rule4` ×2, verified at l.834-838. Whatever blocks `I = i` here, it is not a
missing sum, so E4 is not the route. The symptom coincides; the cause stated does not
transfer.

Source: the `%% generator diagnostics (W1-T3)` block at the foot of `cata/element.tex`.

## Generated rules

Rendered from `cata/element.tex` (`grep -o '\\frac' cata/element.tex | wc -l` → 6).
`[1,n]` is the position index set, `[1,m]` the value set.

### Rule 1 — `X_i = t`

```
I=i    V=t
----------- ⊢
X_{i}=t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(no binder) ; (no binder)`.
`cross-check: store sweep agrees with singleton reduction`

### Rule 2 — `X_i ≠ t`

```
I=i    V ≠ t
------------- ⊢
X_{i} ≠ t
```

**Verdict:** `SOUND and MINIMAL`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(no binder) ; (no binder)`.
`cross-check: store sweep agrees with singleton reduction`

### Rule 3 — `I ≠ i`

```
X_{i} ≠ t ,  ∀t ,  t ∈ [1,m]        V=t ,  ∀t ,  t ∈ [1,m]
----------------------------------------------------------- ⊢
I ≠ i
```

**Verdict:** `VACUOUS — no store in scope satisfies the premises, so it is sound only because
it can never fire`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(premises never hold) forall t ; forall t`.
`cross-check: store sweep agrees with singleton reduction`

### Rule 4 — `I ≠ i`

```
X_{i}=t ,  ∀t ,  t ∈ [1,m]          V ≠ t ,  ∀t ,  t ∈ [1,m]
------------------------------------------------------------- ⊢
I ≠ i
```

**Verdict:** `VACUOUS` (same text as rule 3's).
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(premises never hold) forall t ; forall t`.

### Rule 5 — `V = t`

```
X_{i}=t ,  ∀i ,  i ∈ [1,n]          I=i ,  ∀i ,  i ∈ [1,n]
----------------------------------------------------------- ⊢
V=t
```

**Verdict:** `VACUOUS`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(premises never hold) forall i ; forall i`.

### Rule 6 — `V ≠ t`

```
X_{i} ≠ t ,  ∀i ,  i ∈ [1,n]        I=i ,  ∀i ,  i ∈ [1,n]
----------------------------------------------------------- ⊢
V ≠ t
```

**Verdict:** `VACUOUS`
**Reading(s) checked:** `1 (1 sound, 0 unsound)` — `(premises never hold) forall i ; forall i`.

**Which rules can fire.** Rules 1 and 2 fire: both premises are single unquantified literals,
and `I = i ∧ V = t` is satisfiable under `element` for every `(i,t)` in range. Rules 3-6
**can never fire**, and unlike `alldifferent`'s dead rule the validator *does* catch it — the
`VACUOUS` flag exists precisely for this, and it catches these four because the premises are
unsatisfiable in *any* store, not merely in the constrained ones. (`alldifferent`'s rule
escapes it because it is satisfiable at `n = 2`, which is in scope; see
[`alldifferent.md`](alldifferent.md).)

**Note what rules 1 and 2 are, and are not.** They read the array *from* the index and value
variables. Nothing shipped here reads in the other direction — no rule concludes `I = i`
at all, and the two rules that conclude `V` are among the dead four. So the working half of
`element` is the half a solver needs least: given `I` and `V` fixed, `X_i` follows. The
pruning a solver actually wants from `element` — narrowing `I` from the array, or `V` from
`I` — is exactly the part that is `VACUOUS` or absent.

## Status

**`partly validated`**

Established: rules 1 and 2 are `SOUND and MINIMAL` at `n, m ∈ {2,3,4}` (all 9 pairs; store
sweep held at `n = m = 2` because the `I`/`V` auxiliaries multiply the store space,
`docs/VALIDATOR.md:185`). The hand-encoded ground semantics passes its gccat cross-check for
this constraint — `element: VALUE determined by INDEX and TABLE  gccat Celement  ok` — and one
of the validator's own controls, `V-atom sound+minimal`, is built on this entry
(`docs/VALIDATOR.md:255`).

Not established: anything about the other four. They are sound in the degenerate sense only.
**Reporting this entry as "6 rules" would be an overclaim** — that is the correction
`CHRISTMAS_LIST.md:194` already records against an earlier phrasing, and it holds a second
time now that the four are measured rather than merely unchecked.

**Sound and minimal is a floor, not strength**, and here the floor is visible in the shape of
the entry rather than in a single rule: two rules pass, and they are the two that do the least
work.

## Calibration (W3-T5, D-0013)

**Verdict: no published rule.** `CHRISTMAS_LIST.md:194` records `none found` for `element` —
the index searched and came back empty. Nothing is sourced into `catalog/_literature/`; this
session has no web access and did not search. No implication comparison against a paper is
statable, and none is fabricated here.

Worth recording alongside that, because it changes what "no literature" means for this entry:
**`element` has a `[C]` native in Choco LCG** (`CHRISTMAS_LIST.md:194`). So an explaining
implementation exists in a solver without a paper describing its explanations — which puts
`element` in tier A (no literature, and Chuffed decomposes) while still having a native
elsewhere. Calibration against that implementation is not possible from this repo: no source
is vendored, and `CLAUDE.md` forbids web-searching ahead of the index.

The comparison that *is* available is against the entry's own spec, and it fails in a
specific place. `decomps/element.md` derives shape P3 and states that the two `rule4` clauses
are sound as a biconditional expansion — which they are. The loss is entirely in the index
operators composed onto them, not in the shape. So **the decomposition is right and the
encoding of it is wrong**, and no amount of literature would change that.

## Gaps

| gap | what it blocks here |
|---|---|
| `G9` | **no `Global ⇔ Global` channel schema.** `rule1` is fixed to `Global ⇔ Reified`, so `element` is built as a five-`Decomp` detour through three reifications. `docs/DECOMP_FORMAT_NOTES.md` names `element`'s detour as the thing `inverse`, `sort` and `arg_sort` would each have to re-derive |
| `G17` | **no pivot-elimination pass**, so an auxiliary cannot be removed from a finished rule. Not biting here (`B1`/`B2`/`B3` wash out), but it is the reason the detour costs coverage rather than only rule length |
| — | **the live blocker is roadmap W1-T1, not a `G`-number.** Binders are scoped per literal; the correct rule needs `∃t` scoping both premises jointly. `docs/ROADMAP.md:47` states it, and `docs/ROADMAP.md:53` records that `element` is correctly *not* fixed until it lands |
| — | **not E4.** `CLAUDE.md` prices `I=i` at E4 by analogy with `alldifferent`; `elem` has no Boolean sum, so that route does not apply here (see Scope) |

Extensions: **E0** (`CHRISTMAS_LIST.md:194`). `sort`/`arg_sort` are priced **E2** there and
described as "composes `element`", so this entry's defect propagates to them.
Source: `docs/DECOMP_FORMAT_NOTES.md`, consolidated wave-two numbering.

## How this entry was produced

- `make validate` (E2's own run, 2026-09-21) → `---- cata/element.tex  (6 rules) ----`, two
  `VERDICT   : SOUND and MINIMAL` (rules 1-2) and four
  `VERDICT   : VACUOUS — no store in scope satisfies the premises, so it is sound only because
  it can never fire` (rules 3-6), each with `[sound  ] (premises never hold) forall t ; forall
  t` or `… forall i ; forall i`. Run totals: **34 rules checked in 11 entries: 13 SOUND and
  MINIMAL, 21 flagged; 2 rules in 5 entries out of scope**; 19/19 invariants hold, including
  `element: VALUE determined by INDEX and TABLE`; all 11 controls behaved, including
  `V-atom sound+minimal` and `I-atom unsound`.
- `python3 tools/mzn_coverage.py --rank --json` → `element` in
  `A no-literature + solver-decomposes`, `ecodes: ['E0']`, `line: 194`.
- `grep -o '\\frac' cata/element.tex | wc -l` → 6.
- `cata/element.tex` read, not run → the six rules and the diagnostics footer, including the
  `** NO RULE EMITTED for I=i: 2 candidate(s), all blocked **` line quoted above.
- `explenation generator.ml:834-838, 869, 872-873, 885` read, not run → the `elem` value (and
  the fact that it contains **no** `rule5/6/7`), the three global events, the emitting call.
  Checked against the current file; `decomps/element.md`'s "lines 692-696" does not resolve.
- `docs/ROADMAP.md:47` and `:53` read, **before reporting** (`CLAUDE.md`, "Verify before you
  report") → W1-T1 is `TODO` and blocks this; W1-T9 is `PARTIAL` with `element` explicitly not
  fixed, and the two attempted repairs' `4 VACUOUS → 4 UNSOUND` outcome. Both quoted, not
  re-derived.
- `docs/DECOMP_FORMAT_NOTES.md` G9, G17 read → the gap attributions.
- `docs/VALIDATOR.md:185, 227-228, 255` read → store-sweep cap, the `VACUOUS` definition, the
  `V-atom` control.
- `CHRISTMAS_LIST.md:194`, `:106-108` read → literature (`none found`), solver (`decomp [C]`),
  legend.
- **The "which rules can fire" paragraph is reasoning about the printed rules**, resting on
  the validator's `(premises never hold)` annotation, which is the measurement.
