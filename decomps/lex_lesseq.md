# lex_lesseq

Instance of `decomps/lex_less.md`: identical decomposition, the final per-position disjunction
drops the "strict somewhere" requirement — `tied_n` (fully tied through the last position) is
an accepting outcome instead of a violation. Same schemas (`rule3` chain + `rule4`
disjunction), same G3 blocker, same `tied_i` auxiliary-leak status. No new file needed.
