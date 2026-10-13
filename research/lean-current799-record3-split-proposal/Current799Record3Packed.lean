import Current799Record3Validity

/-!
Source-only resource redesign of the preserved current799 record3 allocation failure.
Exact source data and conventions are unchanged; see the original frozen source
binding and the redesign proposal. Apache-2.0; prepared with OpenAI assistance.
PR593 helpers and generic soundness retain their original attribution.
-/
set_option Elab.async false

namespace CurrentMain.Current799Record3Packed
open HyperplaneEnd.Clifford HyperplaneEnd.Exact

/-- The exact record's two zero offsets and two zero global phases are omitted
only from the packed decision, with their complex action proved below. -/
def rightCore : List Gate := [
  .dg [75, 75, 0, 75, 0, 0, 11, 0, 0] [1, 1, 0, 1, 0, 0, 2, 0, 0],
  .pm [11, 65, 66, 4, 72, 16, 32, 128, 256] [21, 19, 8, 7, 32, 64, 23, 128, 256]
]

def leftCore : List Gate := [
  .dg [1, 0, 0, 0, 0, 0, 0, 0, 0] [3, 0, 0, 0, 0, 0, 0, 0, 0],
  .pm [3, 5, 8, 17, 32, 64, 1, 128, 256] [64, 65, 66, 4, 72, 16, 32, 128, 256]
]

def rhsReduced : List Gate := rightCore ++ [.cg 1 true] ++ leftCore

private theorem zero_xg_apply (v : Fin 512 → ℂ) : gL 512 (.xg 0) v = v := by
  funext x
  simp only [gL_apply, gC, Nat.xor_zero]
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt x.isLt

private theorem zero_phase_apply (v : Fin 512 → ℂ) : gL 512 (.ph 0) v = v := by
  funext x
  simp only [gL_apply, gC, pow_zero, one_mul]

/-- Removing the four literal identity gates preserves the complete complex action. -/
theorem rhs_reduced (v : Fin 512 → ℂ) : cL 512 rhs v = cL 512 rhsReduced v := by
  simp only [rhs, rhsReduced, wR, wL, rightCore, leftCore,
    List.cons_append, List.nil_append, cL_cons, cL_nil,
    LinearMap.comp_apply, LinearMap.id_apply, zero_xg_apply, zero_phase_apply]

/-- One Gaussian on either side, radix16 and scale1; ten tree-gate evaluations. -/
theorem exact_packed_check : check lhs rhsReduced = true := by
  decide +kernel

/-- The public all-payload conclusion remains the original full recipe, including
its literal zero offsets and phases. -/
theorem packed_child (v : Fin 512 → ℂ) :
    cL 512 rhs v =
      (cE fNew gate_validity.2.1) ((cE fOld gate_validity.1).symm v) := by
  rw [rhs_reduced]
  have h := LinearMap.congr_fun (cL_eq_of_check lhs rhsReduced exact_packed_check) v
  simpa only [lhs, cL_append_apply, cE_apply, cE_symm_apply] using h.symm

end CurrentMain.Current799Record3Packed

#print axioms CurrentMain.Current799Record3Packed.rhs_reduced
#print axioms CurrentMain.Current799Record3Packed.exact_packed_check
#print axioms CurrentMain.Current799Record3Packed.packed_child
