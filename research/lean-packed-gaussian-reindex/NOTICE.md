Apache-2.0.

This adapter is prepared with OpenAI assistance. It reuses the exact circuit
gate semantics from PR593, HyperplaneEnd/Clifford.lean, by Jeremy Kothe with
Claude Opus5.5 (Anthropic) assistance in omp, exact head
fdb6dcc6d7bc29764c5b6b4d32b7fa050acf74a4, source SHA256
c0c51407b4fa6ff230a79d5f3b07c83b7d1c4b433ce03513f0c4fb725bf3cbe1.
Source: https://github.com/CrocSwap/integer-mult-bounds/blob/fdb6dcc6d7bc29764c5b6b4d32b7fa050acf74a4/research/hyperplane-end-lean/HyperplaneEnd/Clifford.lean

It consumes the accepted Current535PackedCoordinates equivalence and the
existing CliffordNineBitDecoder Gaussian operator. Those imports retain their
own attribution, including reused PR509 and Gaussian/frame foundations. This
source introduces only a representation adapter, no circuit induction or
new Clifford algebra. The upstream source is unchanged and remains subject
to its separate compatibility gate. No selected finite certificate is adopted.
