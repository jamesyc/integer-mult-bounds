import Current799Record3Literals

/-!
Source-only resource redesign of the preserved current799 record3 allocation failure.
Exact source data and conventions are unchanged; see the original frozen source
binding and the redesign proposal. Apache-2.0; prepared with OpenAI assistance.
PR593 helpers and generic soundness retain their original attribution.
-/
set_option Elab.async false

namespace CurrentMain.Current799Record3Packed
open HyperplaneEnd.Clifford HyperplaneEnd.Exact

/-- The original gate predicate certifies both inverse reads and every adjoint. -/
theorem gate_validity :
    cOk 512 fOld = true ∧ cOk 512 fNew = true ∧
    cOk 512 wL = true ∧ cOk 512 wR = true := by
  decide +kernel

end CurrentMain.Current799Record3Packed

#print axioms CurrentMain.Current799Record3Packed.gate_validity
