# Source-linked Clifford monomial decoder

This source proposal connects one exact compiler convention to the previously
checked `DirectedChildRecipes` interface. It is uncompiled and has no selected
finite-certificate claim.

## The hypothesis reduced

The selected compiler constructs each monomial as chronological `D → P → X →
phase` (`clifford_exact.py`, lines 81–90 and 127–132). Once the actual primitive
semantics and decoded fields are bound, the caller no longer needs to assume
that this sequence equals an invertible linear map with the advertised
monomial formula. Existing Mathlib unit-action and coordinate-equivalence
constructors supply linearity and inverse laws; `circuit_eq_decoded` proves the
all-payload formula with the combined exponent reduced modulo four.

At the source input coordinate `x`, the output at `offset(linear(x))` is
`omega^((phase + q(x)) % 4) * v(x)`. The exponent is evaluated at the input
coordinate. In the selected interpretation, `linear(x) = mv(matrix_rows,x)`,
`offset(x) = x xor b`, and `q(x)` is the exact upper-triangular `qvalue` from
lines 59–60, with bit `i` denoting the coefficient of `2^i`. The field binding
must prove these identities; the source proposal does not parse JSON.

`rankZero_execution` then discharges the rank-zero monomial execution equation
for a constructed null-right child. Rank zero invokes its left operator alone.
The earlier directed-child theorem and its public statements are unchanged.

## Inputs still required

- Certified address equivalences for the serialized matrix and XOR offset,
  including finite-width bounds and the actual inverse, rather than an assumed
  identification of a noninvertible matrix with a permutation.
- Exact raw `qvalue`, linear Z4 and global-phase field decoding, and the supplied
  unit `omega` with `omega^4 = 1` (the intended complex instance is `i`).
- Equality of the selected executor to the four interpreted primitives.
- Canonical old-to-new child equality, including positive-rank Gaussian blocks,
  compiler assertion soundness and reused baseline validity.
- Complete relabel coverage, ordinary/residual wrappers, labels, expanded
  physical work, scalar rows/columns, ownership and costs.

No full child `hoperator` premise is removed by this monomial sublemma. No
finite recipe has been checked, and neither the tableau assertions nor the
supplier scripts were executed. There is no ordinary-Hadamard substitution or
new generic stream/Clifford-factorization induction.

## Proposed check and attribution

`GATE_PROPOSAL.json` records the separate one-root check, exact current local
boundary and installed external import inventory. Compiler admission is still
required. The previous source-proposal commit is `e116c667d6d3af1bf2bf98bc89f73360ed26425f`.
See `NOTICE.md` for attribution. This conditional interface has no multiplier
bound or author-checked kappa; publication is outside the proposal.
