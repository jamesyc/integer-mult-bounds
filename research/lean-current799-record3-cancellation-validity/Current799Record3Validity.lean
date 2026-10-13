import Current799Record3Literals
import PackedGateValidity

/-!
Symbolic replacement of the preserved record3 validity-only allocation failure.
The public cOk conjunction and all imported source literals are unchanged.
Only nine coordinate positions are split; all address values remain symbolic.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md.
-/
set_option Elab.async false
namespace CurrentMain.Current799Record3Packed
open HyperplaneEnd.Clifford HyperplaneEnd.Exact
open CliffordNineBitDecoder PackedGateValidity
open scoped BigOperators Matrix

private def aRows : List Nat := [3, 5, 8, 17, 32, 64, 1, 128, 256]
private def aiRows : List Nat := [64, 65, 66, 4, 72, 16, 32, 128, 256]
private def bRows : List Nat := [11, 65, 66, 4, 72, 16, 32, 128, 256]
private def biRows : List Nat := [21, 19, 8, 7, 32, 64, 23, 128, 256]

private def actionA (x : Address) : Address :=
  ![x 0 + x 1, x 0 + x 2, x 3, x 0 + x 4, x 5, x 6, x 0, x 7, x 8]
private def actionAi (x : Address) : Address :=
  ![x 6, x 0 + x 6, x 1 + x 6, x 2, x 3 + x 6, x 4, x 5, x 7, x 8]
private def actionB (x : Address) : Address :=
  ![x 0 + x 1 + x 3, x 0 + x 6, x 1 + x 6, x 2,
    x 3 + x 6, x 4, x 5, x 7, x 8]
private def actionBi (x : Address) : Address :=
  ![x 0 + x 2 + x 4, x 0 + x 1 + x 4, x 3, x 0 + x 1 + x 2,
    x 5, x 6, x 0 + x 1 + x 2 + x 4, x 7, x 8]

private theorem a_action (x : Address) : matrix aRows *ᵥ x = actionA x := by
  ext i
  fin_cases i <;> simp [matrix, aRows, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, mask, Nat.testBit_eq_decide_div_mod_eq, actionA, add_assoc]
private theorem ai_action (x : Address) : matrix aiRows *ᵥ x = actionAi x := by
  ext i
  fin_cases i <;> simp [matrix, aiRows, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, mask, Nat.testBit_eq_decide_div_mod_eq, actionAi, add_assoc]
private theorem b_action (x : Address) : matrix bRows *ᵥ x = actionB x := by
  ext i
  fin_cases i <;> simp [matrix, bRows, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, mask, Nat.testBit_eq_decide_div_mod_eq, actionB, add_assoc]
private theorem bi_action (x : Address) : matrix biRows *ᵥ x = actionBi x := by
  ext i
  fin_cases i <;> simp [matrix, biRows, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, mask, Nat.testBit_eq_decide_div_mod_eq, actionBi, add_assoc]

private theorem actionA_Ai (x : Address) :
    actionA (actionAi x) = x := by
  ext i
  fin_cases i
  · change (x 6 + (x 0 + x 6)) = x 0
    calc (x 6 + (x 0 + x 6)) = ((x 6 + x 6) + x 0) := by ac_rfl
      _ = x 0 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · change (x 6 + (x 1 + x 6)) = x 1
    calc (x 6 + (x 1 + x 6)) = ((x 6 + x 6) + x 1) := by ac_rfl
      _ = x 1 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · change (x 6 + (x 3 + x 6)) = x 3
    calc (x 6 + (x 3 + x 6)) = ((x 6 + x 6) + x 3) := by ac_rfl
      _ = x 3 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem actionAi_A (x : Address) :
    actionAi (actionA x) = x := by
  ext i
  fin_cases i
  · rfl
  · change ((x 0 + x 1) + x 0) = x 1
    calc ((x 0 + x 1) + x 0) = ((x 0 + x 0) + x 1) := by ac_rfl
      _ = x 1 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · change ((x 0 + x 2) + x 0) = x 2
    calc ((x 0 + x 2) + x 0) = ((x 0 + x 0) + x 2) := by ac_rfl
      _ = x 2 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · change ((x 0 + x 4) + x 0) = x 4
    calc ((x 0 + x 4) + x 0) = ((x 0 + x 0) + x 4) := by ac_rfl
      _ = x 4 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · rfl
  · rfl
  · rfl

private theorem actionB_Bi (x : Address) :
    actionB (actionBi x) = x := by
  ext i
  fin_cases i
  · change ((((x 0 + x 2) + x 4) + ((x 0 + x 1) + x 4)) + ((x 0 + x 1) + x 2)) = x 0
    calc ((((x 0 + x 2) + x 4) + ((x 0 + x 1) + x 4)) + ((x 0 + x 1) + x 2)) = (((((x 0 + x 0) + (x 1 + x 1)) + (x 2 + x 2)) + (x 4 + x 4)) + x 0) := by ac_rfl
      _ = x 0 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · change (((x 0 + x 2) + x 4) + (((x 0 + x 1) + x 2) + x 4)) = x 1
    calc (((x 0 + x 2) + x 4) + (((x 0 + x 1) + x 2) + x 4)) = ((((x 0 + x 0) + (x 2 + x 2)) + (x 4 + x 4)) + x 1) := by ac_rfl
      _ = x 1 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · change (((x 0 + x 1) + x 4) + (((x 0 + x 1) + x 2) + x 4)) = x 2
    calc (((x 0 + x 1) + x 4) + (((x 0 + x 1) + x 2) + x 4)) = ((((x 0 + x 0) + (x 1 + x 1)) + (x 4 + x 4)) + x 2) := by ac_rfl
      _ = x 2 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · change (((x 0 + x 1) + x 2) + (((x 0 + x 1) + x 2) + x 4)) = x 4
    calc (((x 0 + x 1) + x 2) + (((x 0 + x 1) + x 2) + x 4)) = ((((x 0 + x 0) + (x 1 + x 1)) + (x 2 + x 2)) + x 4) := by ac_rfl
      _ = x 4 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · rfl
  · rfl
  · rfl

private theorem actionBi_B (x : Address) :
    actionBi (actionB x) = x := by
  ext i
  fin_cases i
  · change ((((x 0 + x 1) + x 3) + (x 1 + x 6)) + (x 3 + x 6)) = x 0
    calc ((((x 0 + x 1) + x 3) + (x 1 + x 6)) + (x 3 + x 6)) = ((((x 1 + x 1) + (x 3 + x 3)) + (x 6 + x 6)) + x 0) := by ac_rfl
      _ = x 0 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · change ((((x 0 + x 1) + x 3) + (x 0 + x 6)) + (x 3 + x 6)) = x 1
    calc ((((x 0 + x 1) + x 3) + (x 0 + x 6)) + (x 3 + x 6)) = ((((x 0 + x 0) + (x 3 + x 3)) + (x 6 + x 6)) + x 1) := by ac_rfl
      _ = x 1 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · change ((((x 0 + x 1) + x 3) + (x 0 + x 6)) + (x 1 + x 6)) = x 3
    calc ((((x 0 + x 1) + x 3) + (x 0 + x 6)) + (x 1 + x 6)) = ((((x 0 + x 0) + (x 1 + x 1)) + (x 6 + x 6)) + x 3) := by ac_rfl
      _ = x 3 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · rfl
  · change (((((x 0 + x 1) + x 3) + (x 0 + x 6)) + (x 1 + x 6)) + (x 3 + x 6)) = x 6
    calc (((((x 0 + x 1) + x 3) + (x 0 + x 6)) + (x 1 + x 6)) + (x 3 + x 6)) = (((((x 0 + x 0) + (x 1 + x 1)) + (x 3 + x 3)) + (x 6 + x 6)) + x 6) := by ac_rfl
      _ = x 6 := by simp only [ZModModule.add_self, zero_add, add_zero]
  · rfl
  · rfl

private theorem a_inverse : matrix aRows * matrix aiRows = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ai_action, a_action, Matrix.one_mulVec]
  exact actionA_Ai (Pi.single j 1)

private theorem ai_inverse : matrix aiRows * matrix aRows = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, a_action, ai_action, Matrix.one_mulVec]
  exact actionAi_A (Pi.single j 1)

private theorem b_inverse : matrix bRows * matrix biRows = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, bi_action, b_action, Matrix.one_mulVec]
  exact actionB_Bi (Pi.single j 1)

private theorem bi_inverse : matrix biRows * matrix bRows = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, b_action, bi_action, Matrix.one_mulVec]
  exact actionBi_B (Pi.single j 1)

/-- The exact original source validity statement, discharged compositionally. -/
theorem gate_validity :
    cOk 512 fOld = true ∧ cOk 512 fNew = true ∧
    cOk 512 wL = true ∧ cOk 512 wR = true := by
  have ha := permutation_ok aRows aiRows rfl rfl a_inverse ai_inverse
  have hai := permutation_ok aiRows aRows rfl rfl ai_inverse a_inverse
  have hb := permutation_ok bRows biRows rfl rfl b_inverse bi_inverse
  simp only [aRows, aiRows, bRows, biRows] at ha hai hb
  have hx := translation_ok 0 (by decide)
  have hg := gaussian_ok 1 (by decide) true
  simp [cOk, fOld, fNew, wL, wR, diagonal_ok, phase_ok, ha, hai, hb, hx, hg]

end CurrentMain.Current799Record3Packed

#print axioms CurrentMain.Current799Record3Packed.gate_validity
