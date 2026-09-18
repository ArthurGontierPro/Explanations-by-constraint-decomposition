# cumulatives

**Signature.** `cumulatives(array[int] of var int: s, array[int] of var int: d,
array[int] of var int: r, array[int] of var int: m, array[int] of var int: b)` — tasks are
assigned to machines and each machine's capacity is respected.

**Shape: `SCH-2` + modifier `M-mach`** (`_shapes-ext.md`): the sum at machine `k` and time `t`
ranges over `{ i : M_i = k }`.

**E-code: E2 + E4** (`CHRISTMAS_LIST.md` §6), plus two gaps of its own.

**Gap X6 — summation over a variable-determined index set.** `ind_set` and every `ind_op` are
static; nothing in the format has an extent that depends on a decision variable. The
auxiliary-free workaround is the right decomposition and is expressible *in the schemas*:
`B3_{i,k,t} ⇔ (M_i = k) ∧ B2_{i,t}` by `rule3`, then sum `B3` over `i` at fixed `(k,t)`. `M_i = k`
is an ordinary AC literal on a user variable, so nothing leaks under D-0004.

**Gap X7 — but that workaround needs four index families** (task `i`, time `t`, machine `k`,
plus the value family the `M_i = k` reification consumes), and `ind_fam` is the closed enum
`FI | FT | FP | FR` with hardcoded printers `i`/`t`/`p`/`r` (source l.38, l.373). A machine index
would have to print as `p` or `r`.

Everything `cumulative.md` says about weights (X5), the capacity never printing (X4) and the E4
window argument (X10) applies here unchanged, once per machine.
