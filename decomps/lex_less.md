# lex_less

**Signature.** `lex_less(array[int] of var int: x, array[int] of var int: y)` — `x` is
lexicographically strictly less than `y`, same length. Both `var` arrays — this is why it
needs variable-vs-variable comparison, unlike the counting-family pilot which sidesteps that
by treating its second operand as a par (D-0003).

**Decomposition (maths).** Shape B (`decomps/_shapes-seq.md`):

- `tied_1 = true` (base case: nothing compared yet).
- `tied_{i+1} ⇔ tied_i ∧ (X_i = Y_i)`, for `i ∈ [1,n-1]` — "still equal up to position `i`".
- `tied_i → X_i ≤ Y_i`, for every `i` (a tied prefix cannot have already lost).
- `∃ i: tied_i ∧ X_i < Y_i` (somewhere the sequences strictly diverge in `x`'s favour) —
  equivalently, per position: `¬tied_i ∨ X_i < Y_i ∨ (tied_i ∧ ¬tied_{i+1})`, i.e. the standard
  clause-per-position encoding.

**Rule schemas.**
1. `tied_{i+1} ⇔ tied_i ∧ (X_i = Y_i)` → `rule3` (conjunction), fixed shift by 1, same
   mechanics as `incr`'s `rule4` chain but AND instead of OR.
2. `X_i = Y_i` itself → **blocked by `DECOMP_FORMAT_NOTES.md`'s G3**: `Global_event`/
   `ind_modifs` express `X_i = t` for a domain value `t`, never `X_i = Y_i` for two decision
   variables. This is not new — G3 already names this exact wall — but `lex_less` is a second,
   independent constraint that needs it (the format notes previously only had `count`/`among`'s
   variable-`v` case pinned to it).
3. The final strict-vs-non-strict comparator → `rule4` disjunction per position.

**E-code: E0** per `CHRISTMAS_LIST.md` (native, `lex.cpp`), but the decomposition cannot
actually be encoded today because of G3 — `rule1`'s channel `B ⇔ X_i = t` has no counterpart
for `B ⇔ X_i = Y_i`. This is worth separating from "E0 means the schema exists": here the
**schema shapes** (`rule3`, `rule4`) exist, the **event vocabulary** (var-vs-var literal) does
not.

**Auxiliaries.** `tied_i`, same status as `value_precede`'s `b_i` — a genuine accumulated
state, not a reification of a single literal, hence subject to the same `"ERROR B "` risk
described in `decomps/value_precede.md` and `_gaps-seq.md`.

**Literature.** `CHRISTMAS_LIST.md` cites Chu & Stuckey (IJCAI 2011) for LCG-compatible static
symmetry breaking generally, but notes explicitly "no dedicated `lex` explanation paper found".
Repeating that here rather than treating the citation as `lex`-specific.
