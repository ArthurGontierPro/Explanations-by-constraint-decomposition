# regular_regexp

**Signature.** As `regular`, with the language given by a regular expression.

**Shape.** Whichever of `EXT-2a` / `EXT-2b` the compiled automaton falls into: EXT-2a when the
expression denotes a strictly 2-local language (the state is a function of the last symbol),
EXT-2b otherwise. See `regular.md`; nothing else differs.

**E-code: E2** (EXT-2a) or **E1 + E2** (EXT-2b). The compilation step is a modelling act outside
the format and adds no requirement of its own.
