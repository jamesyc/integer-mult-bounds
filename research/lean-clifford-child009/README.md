# One selected directed-child decoder: 0 → 9

This source proposal translates exactly `children[7]` in the pinned
`CLIFFORD-RECIPES.json`: old frame 0 (`[]`), new frame 9 (`[11]`), rank 1.
`SELECTED_RECORD.json` preserves all record fields and source hashes.
It was chosen because the right monomial has global phase 1, offset 1,
nonidentity address maps and a nonzero quadratic phase.

## First bounded certificate

`CliffordChild009Decoder.lean` contains the exact two stored matrix/phase lists,
explicit matrix maps and inverses, the source's strict-upper-tail parity
convention, and a certificate for every four-bit input. Ordinary kernel
`decide` and 16 Boolean cases are used; no native-decide axiom or upstream
script is involved. The remaining five matrix rows are identity rows; their
phase coefficients are zero, and no low row reads a higher bit. Those literal
facts are separately certified. Payload formulas keep an arbitrary spectator
factor, which the selected address interpretation instantiates with the five
higher bits.

The low tuple is `(bit0, bit1, bit2, bit3)` in the source's little-endian integer
coordinate convention. `dot4` is the parity of the selected row bits.
`qvalue4` retains the source row-tail parity before multiplying by two and
reducing modulo four. The right offset flips bit 0. Its global phase 1 is not
absorbed into a label or dropped.

The two payload conclusions reuse the accepted monomial decoder rather than
prove linearity or stream composition again. They certify field-level
mathematical interpretation for this one record. They do not claim that the
Python interpreter has been formally verified, or that every raw address/event
has been wired into this interpretation.

## Next operator equality

The exact source `basis_extend([11],9)` chooses
`[11,1,2,4,16,32,64,128,256]`. The candidate canonical basis matrix has rows
`[3,5,8,1,16,32,64,128,256]`, inverse rows
`[8,9,10,4,16,32,64,128,256]`, and the canonical diagonal has rows
`[8,8,0,3,0,0,0,0,0]`. These source correspondences have been inspected, but
this first module does not prove the greedy-basis computation or the Gaussian
operator identity.

The next target is the all-payload equation
`L ∘ C0 ∘ R = K ∘ C0 ∘ K⁻¹`, where `K = D_Q ∘ P_G` and `C0` is the
source Gaussian-dyadic gate. It must retain the nontrivial right phase and
offset, use the actual complex phase unit, and keep all spectator values.
No tableau-only or zero-state shortcut is used to assert that target here.

Complete recipe/event coverage, labels, other children, endpoint/residual
wrappers, expanded work, scalar rows/columns, ownership and costs remain
separate. This record is not a coverage or end-to-end multiplier certificate.
The source proposal is uncompiled and has no author-checked kappa or publication
scope. `GATE_PROPOSAL.json` describes the separate bounded admission needed.
