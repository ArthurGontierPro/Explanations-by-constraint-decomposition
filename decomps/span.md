# span

> **Correction, W3-D 2026-09-18 — this file's "Shape D / E0" claim is withdrawn.**
> `span`'s `S = min_i(start_i)` compares two decision variables, which is gap **G3**, the same
> wall `decomps/maximum.md` records as "not a derivation gap, it is a missing primitive".
> The precedent this file leaned on does not hold: `range`/`roots` (generator l.714–719) are
> Boolean **sums** over a value-restricted family (`rule6` = `∑ ≥`, `rule7` = `∑ =`), not a
> ∀-bound-plus-∃-tight pair, so they are no basis for a min/max constraint. `span` has **no
> shape** and is listed among the G3-blocked constraints in `decomps/_shapes.md`. The body
> below is left as written — its own hedge already said it should be redone rather than
> patched, and redoing it needs the real MiniZinc signature.

**Signature — hedge.** `CHRISTMAS_LIST.md` §4 gives only "none / decomp / E0" for `span`, no
predicate signature. Read from general knowledge of MiniZinc's scheduling globals (not
verified against a spec text, which is out of this session's scoped reading): a task with
start `S` and end `E` spans a set of subtask intervals, `S = min_i(start_i)`,
`E = max_i(end_i)`. **Flagging this as reconstructed, not confirmed**, per the reporting rule
against fabricating claims — if the real signature differs this file should be redone, not
patched.

**Decomposition, under that reading.** Shape D (`decomps/_shapes-seq.md`, reusing `range`'s
existing min/max-over-index-set pattern):

- `S ≤ start_i`, for every `i` — `S` is a lower bound (`rule6`-style, "for all").
- `∃ i: S = start_i` — the bound is tight for some subtask (`rule7`-style, "achieved").
- Symmetrically for `E`/`end_i` with `≥`/max.

**E-code: E0** per `CHRISTMAS_LIST.md`, consistent with reusing `range`'s existing schemas —
nothing new needed **if** the reconstructed signature above is right. `S`/`E` are the task's
own start/end, i.e. genuinely part of the constraint's signature, not invented auxiliaries — no
D-0004 concern, modulo the same G2 naming gap already recorded (no `var_name` slot for "this
constraint's own variable" without borrowing another constraint's letter).
