# Packed strict-upper quadratic phases

This source-only proposal identifies PR593 qv with the existing raw9 qvalue for paired nine-entry lists and derives the exact diagonal payload reindexing. Its first step turns the shifted parity in each source row into the strict-upper binary sum. Only nine coordinate positions are split; all packed-address bits and phase coefficients remain symbolic.

The paired-list evaluator is treated by a symbolic finite-sum induction, preserving its simultaneous stopping behavior. Both length-nine hypotheses are explicit. The equality retains the complete natural exponent modulo four and the exact complex phase; it does not replace the Gaussian convention or discard a global scalar.

The proposed dependency is PackedParityReindex, plus an explicit already-cached FinCases import. Expected scope is 13 local modules, 12 retained after parity acceptance, one new root, the same 2,663 cached pairs and three probes. Only one private four-case Boolean fact and nine coordinate-index branches are used. No 512-address test, finite selected phase replay or compiler admission is included.

Monomial composition, raw circuit/recipe decoding, and the expanded physical executor remain separate source obligations. This proposal is prepared for independent source/API/resource review.
