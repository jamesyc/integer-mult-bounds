# Attribution

Apache-2.0. Prepared with OpenAI assistance.

The interpreted matrix, qvalue, rank and greedy-basis conventions are from
research/direct-delivery504-global/vendor/clifford/clifford_exact.py at
CrocSwap/integer-mult-bounds commit f19cb621be2caf3a7291a37c343c1c55afe935e0,
SHA256 2982ead07721e83358dc67c6f49c2b4c16a236a6bebdfd72f58221be1f5d0962.
Preserve that project's LICENSE/NOTICE and its icekylinx and PR425/433/514/523
credits. This bounded transcription follows the prior accepted child009
basis certificate; its log-function substitution is new proof-local support.

Matrix linearity/equivalences and finite-field operations reuse Mathlib;
logarithm bounds reuse Lean core. The exact Gaussian and monomial semantics
reuse the accepted local GaussianPhaseNormalization, CliffordMonomialDecoder
and RankOneRecipeCertificate modules. The eventual stream consumer remains
PR509 by DreamingOfClouds with Claude Opus 5.5 (Anthropic), via Claude Code,
commit 7b9c720ecc9f483c383e7cd9c2ab81f06ee5df59, and its PR484/425/458/471
lineage. No generic stream or Clifford induction is reimplemented here.
