# regular

**Signature.** `regular(array[int] of var int: x, int: Q, int: S, array[int,int] of int: d,
int: q0, set of int: F)` — the word `x[1..n]` is accepted by the DFA `(Q, S, d, q0, F)`.

**Two shapes, and choosing between them is the whole question.**

- **`EXT-2a`** — the chain of binary clauses on consecutive `X`, **no state variables**. This is
  what the generator ships (l.712–713) and what `cata/regular.tex` contains. Auxiliary-free
  beyond the `rule1` reification, every premise in the user's vocabulary. D-0003 and D-0004 both
  cite it as the worked example, and on explanation quality both are right.
- **`EXT-2b`** — the layered Boolean state matrix `S_{i,q}`, which is what MiniZinc's
  `a[i+1] = d[a[i], xs[i]]` amounts to. Covers all of `regular`. Leaks `S_{i,q}` into premises,
  which D-0004 forbids by default.

See `_shapes-ext.md` for the maths, rule schemas and index families of each.

**E-code.** EXT-2a: **E2**, and specifically gap **X2** — `t' ∈ D(t)`, a value set indexed by
another index, *not* D-0006's "2-D constant table" (that is `table`'s X1). EXT-2b: **E1 + E2**.
`CHRISTMAS_LIST.md` §5 gives `regular` E2 and says it "only needs `D_8`/`D_9` defined in the
printer and 2-D table side conditions"; the first half is right, the second half names X1 where
X2 is what EXT-2a wants.

**The coverage limit of the shipped decomposition (gap X11).** EXT-2a is sound, complete and
auxiliary-free for the **strictly 2-local** languages — those whose automaton state is a
function of the last symbol read — and is not a decomposition of `regular` in general: a
conjunction of binary constraints on consecutive positions cannot express "an even number of
`a`s". Derived by reading generator l.713 and asking what a consecutive-pair chain can define;
**not measured**, and `docs/VALIDATOR.md` l.332 puts `regular` out of scope entirely (`D_8`,
`D_9` undefined), so nothing measured bears on it either way.

This does **not** reopen D-0003. D-0003 decides where decompositions come from and rejects
importing MiniZinc's; that stands, and this file imports nothing. What is recorded here is the
*scope* of the decomposition this repo already chose — which D-0003 never states — and it is the
kind of thing `docs/GCCAT.md`'s D-0008 proposal (a per-entry `complete`/`partial` label against
a stated Purpose) exists to carry.

**M-1's inlining criterion, tested here.** `docs/GCCAT.md` proposes inlining a state when its
state predicate is "a finite disjunction over user literals". For general `regular` the state
predicate is the DNF of all prefixes reaching `q`; over finite domains that *is* a finite
disjunction over user literals, so the criterion passes general `regular` and draws no line.
The sharpened form that survives contact — **the state predicate must be a *clause*, a
disjunction in which every disjunct is a single literal** — passes exactly the strictly 2-local
case (`X_{i-1} ∈ V_q`) and fails general `regular`. That is EXT-2a's boundary, arrived at
independently, which is the strongest thing this session can say for the criterion. Full table
in `_shapes-ext.md`.

**Second defect, read off `cata/regular.tex` (gap X3).** The premises name `t'` with
`t' ∈ D_8`/`D_9` and **no binder**, because `OpPrim` does not bind (source l.45 comment; `prim_node`
l.94 omits the `EXFORALL` that `sum_node` l.93 adds). "For some `t'`" and "for every `t'`" are
different rules and the printed entry does not say which.

**Is `regular` still the smallest complete contribution available?** On the evidence read here,
yes, with one correction to the claim's scope. It is on Choco's LCG-unsupported list
(`CHRISTMAS_LIST.md` §5, `[C✗]`), the decomposition already exists, and it needs one extension
(X2) rather than the two or three every other §5/§6 entry needs. The correction is that
completing it at X2 delivers a complete method for the **strictly 2-local fragment**; delivering
`regular` entire additionally needs E1 and X8 (pivot elimination), at which point `mdd` comes
nearly free and the contribution is no longer small. Both are defensible plans; they are not the
same plan, and W3-T3's one-line framing does not currently distinguish them.
