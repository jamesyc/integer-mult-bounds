# Packed monomial reindexing proposal

This source links the literal chronological packed D → P → X → global-phase circuit to the already accepted decoded monomial, for arbitrary complex payloads. It reuses the existing circuit_eq_decoded theorem and PR593 circuit semantics, without a new circuit induction.

The caller supplies both matrix inverse equations, inverseRows/Q/alpha lengths of nine, and offset < 512. Bit zero is the least significant coordinate. P reads the inverse rows; the quadratic phase remains evaluated at the input/preimage, and the entire stored global phase is retained.

Four symbolic facts cover bounded source XOR, offset action, global phase, and the four-gate composition. No address enumeration, selected record certificate, canonical-child equation, emitted stream equality, or expanded physical-work assertion is included.

Proposed closure: 15 local modules, retaining 14 current prerequisites, plus the unchanged 2,663 cached external pairs. Matrix and quadratic terminal reviews and a separately reviewed binding are required before the one bounded compiler check. Hard limits remain 60 seconds / 4 GiB; review limits are 45 seconds / 3.5 GiB. No research publication is authorized by this proposal, which contains no author-checked κ.
