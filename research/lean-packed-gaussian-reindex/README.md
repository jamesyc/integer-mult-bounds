# Packed Gaussian reindexing

A source-only adapter for the exact bit-zero Gaussian gate. It identifies
PR593 cg(1,true) on Fin512-indexed complex payloads with the accepted Gaussian
C0 on nine-coordinate ZMod2 addresses through the explicit little-endian
payload equivalence. The two coefficients remain (1+i)/2 and (1-i)/2,
including their global phase convention.

Four proposed facts expose modulo-512 XOR, its bit-zero coordinate action,
payload reindexing and conjugation on arbitrary payloads. They use no selected
record enumeration and no new circuit induction.

The prospective first check is12/11/1 with2,663 cached source/object pairs.
Ten inputs are current; PR593Clifford must pass its separate gate and terminal
review before this adapter can run. Four axiom probes are required. Caps are
60 seconds/4 GiB hard and45 seconds/3.5 GiB review.

Matrix/parity/qvalue decoding, serialized child data, raw emitted recipes,
expanded work and physical execution remain separate obligations. This
interface has no author-checked kappa and no publication authorization.
