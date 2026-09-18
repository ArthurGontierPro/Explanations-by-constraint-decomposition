# cost_regular

**Signature.** As `regular`, plus a cost matrix `c[q,s]` and a total-cost variable, constrained
against a bound.

**Shape: `EXT-4`** — `EXT-2b` plus an integer accumulator `C_{i+1} = C_i + c[q,t]` and a final
comparison. See `_shapes-ext.md`.

**E-code: E1 + E2 + E3**, as `CHRISTMAS_LIST.md` §5 gives it (Gange, Stuckey & Van Hentenryck,
CP 2013, *Explaining propagators for edge-valued decision diagrams*).

**The requirement this session adds (gap X9).** The accumulator is the first construct in §5 or
§6 that needs **arithmetic on variable values** rather than on indices. Every arithmetic
construct in the format — `Addint`, `Addcst`, `OpShift`, `OpShiftC` — rewrites an `ind_name`
inside an index list. `C_{i+1} = C_i + c[q,t]` relates two *variables* through a constant read
from a 2-D table; there is no encoding for it at all, and E3 as D-0006 defines it
("multi-family cardinality") is not it.

**Auxiliaries.** `C_i` leaks and cannot be inlined: a counter's value is not a disjunction of
user literals under any reading of M-1's criterion, which is the one part of that criterion this
session found needs no repair. D-0004's exception clause covers it by the same argument as
`mdd`, and the entry must print `C_i`'s definition beside its rules.
