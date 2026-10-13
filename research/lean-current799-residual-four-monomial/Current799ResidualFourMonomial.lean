import PackedMonomialReindex

/-!
The exact current799 R(4,FULL) right monomial as a packed/coordinate operator.
Source key "4" is the full-terminal residual entry, not a literal "4:1" key.
Only the right-monomial interpretation is proved. The residual endpoint and
actual entry/event executor remain independent suppliers. See SOURCE_BINDING.json.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md.
-/
set_option Elab.async false
namespace CurrentMain.Current799ResidualFourMonomial
open CliffordNineBitDecoder Current535PackedCoordinates RankOneRecipeCertificate
open HyperplaneEnd.Clifford (Gate cL)
open scoped BigOperators Matrix

def rows : List Nat := [1, 258, 4, 264, 16, 32, 320, 384, 256]
def quadraticRows : List Nat := [256, 256, 0, 256, 0, 0, 256, 256, 203]
def alpha : List Nat := [0, 0, 2, 0, 2, 2, 0, 0, 0]
def offset : Nat := 309
def phase : Nat := 3

private def shear (x : Address) : Address := x + x 8 • mask 202

/-- Row masks add coordinate8 to coordinates1,3,6,7 and fix every other coordinate. -/
private theorem matrix_action (x : Address) : matrix rows *ᵥ x = shear x := by
  ext i
  fin_cases i <;>
    simp [matrix, rows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      shear, mask, Nat.testBit_eq_decide_div_mod_eq, add_assoc]

private theorem shear_eight (x : Address) : shear x 8 = x 8 := by
  simp [shear, mask, Nat.testBit_eq_decide_div_mod_eq]

private theorem shear_twice (x : Address) : shear (shear x) = x := by
  have he := shear_eight x
  ext i
  change (x i + x 8 * mask 202 i) + shear x 8 * mask 202 i = x i
  rw [he, add_assoc, ZModModule.add_self, add_zero]

/-- Both inverse equations are the same exact involutive matrix identity. -/
theorem matrix_inverse : matrix rows * matrix rows = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, matrix_action, matrix_action, shear_twice,
    Matrix.one_mulVec]

private theorem matrix_offset : matrix rows *ᵥ mask offset = mask 511 := by
  rw [matrix_action]
  ext i
  fin_cases i <;> simp [shear, offset, mask, Nat.testBit_eq_decide_div_mod_eq]

noncomputable section

def right : Monomial Address :=
  monomial rows rows quadraticRows alpha offset phase matrix_inverse matrix_inverse

def circuit : List Gate :=
  [.dg quadraticRows alpha, .pm rows rows, .xg offset, .ph phase]

/-- The nonzero XOR offset is read before the inverse matrix. Its transformed
value is511, not309. This is an arbitrary-address identity. -/
theorem preimage_read (y : Address) :
    right.preimage y = matrix rows *ᵥ y + mask 511 := by
  change (coordinateEquiv rows rows matrix_inverse matrix_inverse).symm
    ((offsetEquiv offset).symm y) = _
  rw [offsetEquiv_symm_apply, coordinateEquiv_symm_apply,
    Matrix.mulVec_add, matrix_offset]

/-- Exact D→P→X309→phase3 order, with no quotient by global phase. -/
theorem packed_reindex (v : Packed → ℂ) :
    payloadEquiv (cL 512 circuit v) = right.operator (payloadEquiv v) := by
  exact PackedMonomialReindex.monomial_reindex rows rows quadraticRows alpha
    rfl rfl rfl offset phase (by decide) matrix_inverse matrix_inverse v

/-- The source phase is evaluated at the preimage, with global exponent3 intact. -/
theorem packed_apply (v : Packed → ℂ) (y : Address) :
    payloadEquiv (cL 512 circuit v) y =
      Complex.I ^ ((3 + qvalue quadraticRows alpha (matrix rows *ᵥ y + mask 511)) % 4) *
        payloadEquiv v (matrix rows *ᵥ y + mask 511) := by
  rw [packed_reindex, Monomial.operator_apply]
  simp only [Monomial.exponent, preimage_read]
  rfl

end
end CurrentMain.Current799ResidualFourMonomial

#print axioms CurrentMain.Current799ResidualFourMonomial.matrix_inverse
#print axioms CurrentMain.Current799ResidualFourMonomial.preimage_read
#print axioms CurrentMain.Current799ResidualFourMonomial.packed_reindex
#print axioms CurrentMain.Current799ResidualFourMonomial.packed_apply
