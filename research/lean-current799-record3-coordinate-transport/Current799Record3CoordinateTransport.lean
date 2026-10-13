import CliffordChild002Canonical
import Current799Record3Literals

/-!
Fresh reconstruction after loss of the uncommitted transport draft.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md.
This reuses the accepted historical mask45 all-payload theorem through explicit
coordinate permutations. Every phase statement is universal in all nine bits.
No packed-tree check, source evaluator, or physical executor is replayed here.
-/
set_option Elab.async false

namespace CurrentMain.Current799Record3CoordinateTransport

open CliffordNineBitDecoder RankOneRecipeCertificate
open scoped BigOperators Matrix

def pAddress (x : Address) : Address :=
  ![x 0, x 2, x 1, x 3, x 4, x 6, x 5, x 7, x 8]

def tAddress (x : Address) : Address :=
  ![x 0, x 1, x 3, x 2, x 4, x 5, x 6, x 7, x 8]

theorem p_involutive (x : Address) : pAddress (pAddress x) = x := by
  funext i
  fin_cases i <;> rfl

theorem t_involutive (x : Address) : tAddress (tAddress x) = x := by
  funext i
  fin_cases i <;> rfl

def pEquiv : Address ≃ Address :=
  ⟨pAddress, pAddress, p_involutive, p_involutive⟩

def tEquiv : Address ≃ Address :=
  ⟨tAddress, tAddress, t_involutive, t_involutive⟩

def aRows : List Nat := Current799Record3Packed.leftMono.G
def aiRows : List Nat := [64, 65, 66, 4, 72, 16, 32, 128, 256]
def bRows : List Nat := Current799Record3Packed.rightMono.G
def biRows : List Nat := [21, 19, 8, 7, 32, 64, 23, 128, 256]
def canonicalQ : List Nat := [64, 64, 0, 64, 0, 0, 75, 0, 0]
def canonicalAlpha : List Nat := [0, 0, 0, 0, 0, 0, 1, 0, 0]

theorem offsets_and_global_phases :
    Current799Record3Packed.leftMono.b = 0 ∧
    Current799Record3Packed.leftMono.p = 0 ∧
    Current799Record3Packed.rightMono.b = 0 ∧
    Current799Record3Packed.rightMono.p = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Rows act on column vectors; all input coordinates remain arbitrary. -/
theorem a_transport (x : Address) :
    matrix aRows *ᵥ x =
      pAddress (matrix CliffordChild002Canonical.leftRows *ᵥ tAddress x) := by
  funext i
  fin_cases i <;>
    simp [aRows, Current799Record3Packed.leftMono,
      CliffordChild002Canonical.leftRows, pAddress, tAddress,
      Matrix.mulVec, dotProduct, matrix, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, add_assoc]

theorem ai_transport (x : Address) :
    matrix aiRows *ᵥ x =
      tAddress (matrix CliffordChild002Canonical.leftInverseRows *ᵥ pAddress x) := by
  funext i
  fin_cases i <;>
    simp [aiRows, CliffordChild002Canonical.leftInverseRows, pAddress, tAddress,
      Matrix.mulVec, dotProduct, matrix, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, add_assoc]

theorem b_transport (x : Address) :
    matrix bRows *ᵥ x =
      tAddress (matrix CliffordChild002Canonical.rightRows *ᵥ pAddress x) := by
  funext i
  fin_cases i <;>
    simp [bRows, Current799Record3Packed.rightMono,
      CliffordChild002Canonical.rightRows, pAddress, tAddress,
      Matrix.mulVec, dotProduct, matrix, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, add_assoc]

theorem bi_transport (x : Address) :
    matrix biRows *ᵥ x =
      pAddress (matrix CliffordChild002Canonical.rightInverseRows *ᵥ tAddress x) := by
  funext i
  fin_cases i <;>
    simp [biRows, CliffordChild002Canonical.rightInverseRows, pAddress, tAddress,
      Matrix.mulVec, dotProduct, matrix, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, add_assoc]

/-- Both inverse orientations follow from universal transport and the accepted
old matrix equations. No new matrix-product decision is used. -/
theorem inverse_actions (x : Address) :
    matrix aRows *ᵥ (matrix aiRows *ᵥ x) = x ∧
    matrix aiRows *ᵥ (matrix aRows *ᵥ x) = x ∧
    matrix bRows *ᵥ (matrix biRows *ᵥ x) = x ∧
    matrix biRows *ᵥ (matrix bRows *ᵥ x) = x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a_transport, ai_transport, t_involutive, Matrix.mulVec_mulVec,
      CliffordChild002Canonical.left_inverses.1, Matrix.one_mulVec, p_involutive]
  · rw [ai_transport, a_transport, p_involutive, Matrix.mulVec_mulVec,
      CliffordChild002Canonical.left_inverses.2, Matrix.one_mulVec, t_involutive]
  · rw [b_transport, bi_transport, p_involutive, Matrix.mulVec_mulVec,
      CliffordChild002Canonical.right_inverses.1, Matrix.one_mulVec, t_involutive]
  · rw [bi_transport, b_transport, t_involutive, Matrix.mulVec_mulVec,
      CliffordChild002Canonical.right_inverses.2, Matrix.one_mulVec, p_involutive]

/-- These are full strict-upper quadratic identities, not conclusions inferred
from linear-basis probes. All bit values remain symbolic. -/
theorem left_phase (x : Address) :
    qvalue Current799Record3Packed.leftMono.Q Current799Record3Packed.leftMono.α
      (tAddress x) =
    qvalue CliffordChild002Canonical.leftQ CliffordChild002Canonical.leftAlpha x := by
  simp [qvalue, Current799Record3Packed.leftMono,
    CliffordChild002Canonical.leftQ, CliffordChild002Canonical.leftAlpha,
    tAddress, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
    Nat.add_assoc, add_assoc]

theorem right_phase (x : Address) :
    qvalue Current799Record3Packed.rightMono.Q Current799Record3Packed.rightMono.α
      (pAddress x) =
    qvalue CliffordChild002Canonical.rightQ CliffordChild002Canonical.rightAlpha x := by
  simp [qvalue, Current799Record3Packed.rightMono,
    CliffordChild002Canonical.rightQ, CliffordChild002Canonical.rightAlpha,
    pAddress, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
    Nat.add_assoc, add_assoc]

theorem canonical_phase (x : Address) :
    qvalue canonicalQ canonicalAlpha x =
      CliffordChild002Canonical.canonicalPhase (pAddress x) := by
  simp [CliffordChild002Canonical.canonicalPhase,
    qvalue, canonicalQ, canonicalAlpha, CliffordChild002Canonical.canonicalQ,
    defaultAlpha, pAddress, matrix, Fin.sum_univ_succ,
    Nat.testBit_eq_decide_div_mod_eq, Nat.add_assoc, add_assoc]

def reindexP (v : Address → ℂ) : Address → ℂ := fun x => v (pAddress x)
def reindexT (v : Address → ℂ) : Address → ℂ := fun x => v (tAddress x)

theorem reindexP_twice (v : Address → ℂ) : reindexP (reindexP v) = v := by
  funext x
  exact congrArg v (p_involutive x)

theorem reindexT_twice (v : Address → ℂ) : reindexT (reindexT v) = v := by
  funext x
  exact congrArg v (t_involutive x)

noncomputable section

theorem t_preserves_zero_flip (x : Address) :
    tAddress (flipZero x) = flipZero (tAddress x) := by
  funext i
  fin_cases i <;>
    simp [tAddress, flipZero, mask, Nat.testBit_eq_decide_div_mod_eq]

theorem gaussian_commutes_T (v : Address → ℂ) :
    reindexT (gaussian v) = gaussian (reindexT v) := by
  funext x
  simp only [reindexT, gaussian_apply, t_preserves_zero_flip]

def leftTransport (v : Address → ℂ) : Address → ℂ :=
  reindexP (CliffordChild002Canonical.left.operator (reindexT v))

def rightTransport (v : Address → ℂ) : Address → ℂ :=
  reindexT (CliffordChild002Canonical.right.operator (reindexP v))

def oldCanonical : (Address → ℂ) ≃ₗ[ℂ] (Address → ℂ) :=
  canonicalK CliffordChild002Canonical.canonicalLinear.toEquiv
    CliffordChild002Canonical.canonicalPhase

def canonicalTransport (v : Address → ℂ) : Address → ℂ :=
  reindexP (oldCanonical (reindexT v))

def canonicalInverseTransport (v : Address → ℂ) : Address → ℂ :=
  reindexT (oldCanonical.symm (reindexP v))

private theorem old_left_preimage (y : Address) :
    CliffordChild002Canonical.left.preimage y =
      matrix CliffordChild002Canonical.leftInverseRows *ᵥ y := by
  change matrix CliffordChild002Canonical.leftInverseRows *ᵥ
    (y + -(mask CliffordChild002Canonical.leftOffset)) = _
  have hz : mask CliffordChild002Canonical.leftOffset = 0 := by
    funext i
    simp [CliffordChild002Canonical.leftOffset, mask,
      Nat.testBit_eq_decide_div_mod_eq]
  rw [hz, neg_zero, add_zero]

private theorem old_right_preimage (y : Address) :
    CliffordChild002Canonical.right.preimage y =
      matrix CliffordChild002Canonical.rightInverseRows *ᵥ y := by
  change matrix CliffordChild002Canonical.rightInverseRows *ᵥ
    (y + -(mask CliffordChild002Canonical.rightOffset)) = _
  have hz : mask CliffordChild002Canonical.rightOffset = 0 := by
    funext i
    simp [CliffordChild002Canonical.rightOffset, mask,
      Nat.testBit_eq_decide_div_mod_eq]
  rw [hz, neg_zero, add_zero]

private theorem old_left_exponent (y : Address) :
    CliffordChild002Canonical.left.exponent y =
      qvalue CliffordChild002Canonical.leftQ CliffordChild002Canonical.leftAlpha
        (CliffordChild002Canonical.left.preimage y) := by
  change (0 + qvalue _ _ _) % 4 = qvalue _ _ _
  simp only [Nat.zero_add, qvalue, Nat.mod_mod]

private theorem old_right_exponent (y : Address) :
    CliffordChild002Canonical.right.exponent y =
      qvalue CliffordChild002Canonical.rightQ CliffordChild002Canonical.rightAlpha
        (CliffordChild002Canonical.right.preimage y) := by
  change (0 + qvalue _ _ _) % 4 = qvalue _ _ _
  simp only [Nat.zero_add, qvalue, Nat.mod_mod]

/-- Exact current inverse-read and serialized preimage phase, on any payload. -/
theorem left_transport_apply (v : Address → ℂ) (y : Address) :
    leftTransport v y =
      Complex.I ^ qvalue Current799Record3Packed.leftMono.Q
        Current799Record3Packed.leftMono.α (matrix aiRows *ᵥ y) *
      v (matrix aiRows *ᵥ y) := by
  change CliffordChild002Canonical.left.operator (reindexT v) (pAddress y) = _
  rw [Monomial.operator_apply, old_left_exponent, old_left_preimage,
    ai_transport, left_phase]
  rfl

theorem right_transport_apply (v : Address → ℂ) (y : Address) :
    rightTransport v y =
      Complex.I ^ qvalue Current799Record3Packed.rightMono.Q
        Current799Record3Packed.rightMono.α (matrix biRows *ᵥ y) *
      v (matrix biRows *ᵥ y) := by
  change CliffordChild002Canonical.right.operator (reindexP v) (tAddress y) = _
  rw [Monomial.operator_apply, old_right_exponent, old_right_preimage,
    bi_transport, right_phase]
  rfl

/-- Canonical K has output-coordinate phase, unlike the monomial input phase. -/
theorem canonical_transport_apply (v : Address → ℂ) (y : Address) :
    canonicalTransport v y =
      Complex.I ^ qvalue canonicalQ canonicalAlpha y * v (matrix aiRows *ᵥ y) := by
  change oldCanonical (reindexT v) (pAddress y) = _
  rw [oldCanonical, canonicalK_apply, canonical_phase, ai_transport]
  rfl

theorem canonical_transport_inverse (v : Address → ℂ) :
    canonicalTransport (canonicalInverseTransport v) = v ∧
    canonicalInverseTransport (canonicalTransport v) = v := by
  constructor
  · simp only [canonicalTransport, canonicalInverseTransport,
      reindexT_twice, LinearEquiv.apply_symm_apply, reindexP_twice]
  · simp only [canonicalTransport, canonicalInverseTransport,
      reindexP_twice, LinearEquiv.symm_apply_apply, reindexT_twice]

/-- Reuses the accepted old45 theorem. No new rank-one certificate is decided.
A later packed gate-list adapter must connect these exact read formulas to
the accepted current literals; no physical event executor is claimed here. -/
theorem transported_child (v : Address → ℂ) :
    leftTransport (gaussian (rightTransport v)) =
      canonicalTransport (gaussian (canonicalInverseTransport v)) := by
  simp only [leftTransport, rightTransport, canonicalTransport,
    canonicalInverseTransport, gaussian_commutes_T, reindexT_twice]
  exact congrArg reindexP (CliffordChild002Canonical.selected_child_operator (reindexP v))

end
end CurrentMain.Current799Record3CoordinateTransport

#print axioms CurrentMain.Current799Record3CoordinateTransport.a_transport
#print axioms CurrentMain.Current799Record3CoordinateTransport.ai_transport
#print axioms CurrentMain.Current799Record3CoordinateTransport.b_transport
#print axioms CurrentMain.Current799Record3CoordinateTransport.bi_transport
#print axioms CurrentMain.Current799Record3CoordinateTransport.inverse_actions
#print axioms CurrentMain.Current799Record3CoordinateTransport.left_phase
#print axioms CurrentMain.Current799Record3CoordinateTransport.right_phase
#print axioms CurrentMain.Current799Record3CoordinateTransport.canonical_phase
#print axioms CurrentMain.Current799Record3CoordinateTransport.gaussian_commutes_T
#print axioms CurrentMain.Current799Record3CoordinateTransport.left_transport_apply
#print axioms CurrentMain.Current799Record3CoordinateTransport.right_transport_apply
#print axioms CurrentMain.Current799Record3CoordinateTransport.canonical_transport_apply
#print axioms CurrentMain.Current799Record3CoordinateTransport.canonical_transport_inverse
#print axioms CurrentMain.Current799Record3CoordinateTransport.transported_child
