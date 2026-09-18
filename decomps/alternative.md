# alternative

**Signature — hedge, lower confidence than `span`.** `CHRISTMAS_LIST.md` §4 gives only
"none / decomp / E0", no predicate signature, and this session's scoped reading (§3-§4 only,
no web search) does not pin down `alternative`'s exact MiniZinc arity. Read tentatively as: a
task is scheduled at exactly one of several optional alternative slots/options, an
"exactly-one-of" choice. **Not independently confirmed — flagged rather than asserted**, more
strongly than `span.md`'s hedge, because "which of several options is active" has more than
one standard encoding and this session cannot tell which MiniZinc picked without reading past
its scope.

**Decomposition, under that reading.** Shape C (`decomps/_shapes-seq.md`, reused from the
counting-family pilot):

- `B_k ⇔` "option `k` is chosen", for `k` ranging over the alternatives.
- `∑_k B_k = 1` (`rule7`, exactly-one) — same schema `among`/`exactly` already use.
- `B_k → (task's start/duration = option k's start/duration)` (`rule3`-style implication per
  option) — this half needs whatever the option's parameters are (var or par is not
  established here).

**E-code: E0** per `CHRISTMAS_LIST.md`, consistent with reusing existing `rule3`/`rule7` **if**
the reconstructed reading above is right; not claiming more than that. Recommend whoever
revisits this family re-derive `alternative` against the actual MiniZinc predicate signature
before treating this file as more than a placeholder.
