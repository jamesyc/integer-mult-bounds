# One selected canonical Gaussian child

Source proposal only. No compiler acceptance or publication is claimed here.

This module targets exactly CLIFFORD-RECIPES `/children/7` at selected commit
`f19cb621be2caf3a7291a37c343c1c55afe935e0`: old frame 0 (`[]`), new frame 9
(`[11]`), rank 1. The earlier `CliffordChild009Decoder` certificate supplies its
literal left/right fields and low-coordinate inverses. The right monomial keeps
its nonzero global phase 1, offset 1, and input-coordinate quadratic phase.

## Concrete statement

For every complex payload on four low bits times an arbitrary spectator type,
`selected_child_operator` identifies the interpreted child `L C0 R` with
`K C0 K^-1`, where `K = D_Q P_G`. This is the direct old-to-new direction. `C0`
is the Gaussian-dyadic gate `((1+i) I + (1-i) X0) / 2`, not a convention chosen
from binary frame data. The inverse and linearity of this gate come from the
already accepted `GaussianPhaseNormalization.exactGate`.

The bounded data certificate translates the source's greedy rank/basis loop for
this one nine-coordinate input. Each rank insertion has ten explicit loop tests;
exhaustion returns `none`. Successful evaluation produces
`[11,1,2,4,16,32,64,128,256]`, then checks the source transpose and correction
`Q = I + G^-T G^-1`. The candidate inverse is separately identified with the
accepted coordinate inverse. No generic rank correctness theorem is asserted.
The two branch amplitudes are compared in all 16 low-bit cases, with arbitrary
payload values retained. There is no zero-state test or numerical replay.

This removes the canonical-child all-payload operator-equation hypothesis for
this one interpreted record. It also fixes the phase unit to actual complex i.
It reuses PR509 composition, existing Mathlib operator constructors, and the
previous Gaussian phase lemmas; no generic conjugation or Gaussian induction is
reproved.

## Boundaries still required

- Connect the Python packed nine-bit address representation and actual executor
  primitives to this four-low-bit/spectator interpretation. Taking the spectator
  type to be five bits covers the intended payload size, but is not that wiring
  proof.
- Bind this record and its event occurrence to the exact serialized stream and
  phase-tagged registry. The sibling record certificate pins the JSON bytes;
  this module does not execute a JSON parser or the supplier code.
- Other directed children, ordinary/endpoint/residual adapters, label coverage,
  full dirty row and column facts, coefficient/tableau work, owner and cost
  suppliers remain separate.
- The comparison is to the explicitly decoded canonical source formula. It does
  not use the upstream tableau-plus-zero-state assertions as a soundness axiom.

## Proposed check

`GATE_PROPOSAL.json` pins seven local modules, six already current and this one
new root. The external import union includes the actual Complex and Grind
instance imports; it is not inferred from an earlier module count. A separate
release and exact source/current/retained-lock driver review must precede a
single bounded check under the existing caps. No prerequisite rebuild is
proposed. This conditional package has no author-checked kappa and has no
assistant-publication authorization.
