import CliffordNineBitDecoder

/-!
One pinned f19 rank-one recipe, interpreted on all nine address coordinates.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md.
Every closed source/inverse/basis/phase certificate below requires kernel
checking. No theorem about a raw physical executor is assumed or claimed.
-/
set_option Elab.async false

namespace CurrentMain.CliffordChild003Canonical

open CliffordNineBitDecoder
open RankOneRecipeCertificate
open scoped BigOperators Matrix

def oldFrame : Nat := 0
def newFrame : Nat := 3
def rank : Nat := 1
def oldDescriptor : List Nat := []
def newDescriptor : List Nat := [384]
def singletonMask : Nat := 384
def leftRows : List Nat := [2, 4, 8, 16, 32, 64, 128, 257, 1]
def leftInverseRows : List Nat := [256, 1, 2, 4, 8, 16, 32, 64, 384]
def leftQ : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0]
def leftAlpha : List Nat := [3, 0, 0, 0, 0, 0, 0, 0, 0]
def leftOffset : Nat := 0
def leftPhase : Nat := 0
def rightRows : List Nat := [128, 1, 2, 4, 8, 16, 32, 64, 384]
def rightInverseRows : List Nat := [2, 4, 8, 16, 32, 64, 128, 1, 257]
def rightQ : List Nat := [0, 0, 0, 0, 0, 0, 0, 384, 128]
def rightAlpha : List Nat := [0, 0, 0, 0, 0, 0, 0, 1, 2]
def rightOffset : Nat := 0
def rightPhase : Nat := 0
def canonicalBasis : List Nat := [384, 1, 2, 4, 8, 16, 32, 64, 128]
def canonicalRows : List Nat := [2, 4, 8, 16, 32, 64, 128, 257, 1]
def canonicalInverseRows : List Nat := [256, 1, 2, 4, 8, 16, 32, 64, 384]
def canonicalQ : List Nat := [0, 0, 0, 0, 0, 0, 0, 256, 384]

theorem record_key : oldFrame = 0 ∧ newFrame = 3 ∧ rank = 1 ∧
    oldDescriptor = [] ∧ newDescriptor = [singletonMask] := by decide +kernel

theorem raw_fields_bounded :
    (leftRows ++ leftInverseRows ++ leftQ ++ rightRows ++ rightInverseRows ++ rightQ ++
      canonicalRows ++ canonicalInverseRows ++ canonicalQ).all (fun x => decide (x < 512)) = true ∧
    (leftAlpha ++ rightAlpha).all (fun x => decide (x < 4)) = true := by decide +kernel

theorem left_inverses :
    matrix leftRows * matrix leftInverseRows = 1 ∧
    matrix leftInverseRows * matrix leftRows = 1 := by
  constructor <;> decide +kernel

theorem right_inverses :
    matrix rightRows * matrix rightInverseRows = 1 ∧
    matrix rightInverseRows * matrix rightRows = 1 := by
  constructor <;> decide +kernel

theorem canonical_inverses :
    matrix canonicalRows * matrix canonicalInverseRows = 1 ∧
    matrix canonicalInverseRows * matrix canonicalRows = 1 := by
  exact left_inverses

/-- Exact greedy basis (including fuel ten), transpose and Gram-correction
data, rather than a chosen replacement basis. -/
theorem canonical_source_certificate :
    sourceBasis [singletonMask] = some canonicalBasis ∧
    transpose9 canonicalBasis = canonicalRows ∧
    gramCorrection9 canonicalInverseRows = canonicalQ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← fastBasis_eq_sourceBasis]
    decide +kernel
  · decide +kernel
  · decide +kernel

def left : Monomial Address :=
  monomial leftRows leftInverseRows leftQ leftAlpha leftOffset leftPhase
    left_inverses.1 left_inverses.2

def right : Monomial Address :=
  monomial rightRows rightInverseRows rightQ rightAlpha rightOffset rightPhase
    right_inverses.1 right_inverses.2

def canonicalLinear : Address ≃ₗ[Bit] Address :=
  coordinateEquiv canonicalRows canonicalInverseRows canonical_inverses.1 canonical_inverses.2

def canonicalPhase : Address → Nat := qvalue canonicalQ (defaultAlpha canonicalQ)

def outputFlip (y : Address) : Address := y + mask singletonMask

theorem canonical_first_column : canonicalLinear (mask 1) = mask singletonMask := by
  decide +kernel

/-- Source-specific9-by-9 inverse product for the selected two-bit direction. -/
private theorem inverse_product_shape :
    matrix rightInverseRows * matrix leftInverseRows =
      1 + Matrix.vecMulVec (mask singletonMask) (mask singletonMask) := by
  decide +kernel

private theorem right_first_column :
    matrix rightInverseRows *ᵥ mask 1 = mask singletonMask := by
  decide +kernel

private def sumTwo (a b : Bit) : Bit := a + b
private def parity (y : Address) : Bit := sumTwo (y 7) (y 8)

private theorem left_preimage (y : Address) :
    left.preimage y = matrix leftInverseRows *ᵥ y := by
  change matrix leftInverseRows *ᵥ (y + -(mask leftOffset)) = _
  have hz : mask leftOffset = 0 := by decide +kernel
  rw [hz, neg_zero, add_zero]

private theorem right_preimage (y : Address) :
    right.preimage y = matrix rightInverseRows *ᵥ y := by
  change matrix rightInverseRows *ᵥ (y + -(mask rightOffset)) = _
  have hz : mask rightOffset = 0 := by decide +kernel
  rw [hz, neg_zero, add_zero]

private theorem mask_dot (y : Address) :
    dotProduct (mask singletonMask) y = parity y := by
  simp [Nat.testBit_eq_decide_div_mod_eq, dotProduct, mask, singletonMask, parity,
    sumTwo, Fin.sum_univ_succ, add_assoc]

private theorem outer_action (y : Address) :
    Matrix.vecMulVec (mask singletonMask) (mask singletonMask) *ᵥ y =
      parity y • mask singletonMask := by
  funext i
  change (∑ j, mask singletonMask i * mask singletonMask j * y j) =
    parity y * mask singletonMask i
  calc
    (∑ j, mask singletonMask i * mask singletonMask j * y j) =
        mask singletonMask i * dotProduct (mask singletonMask) y := by
      simp only [dotProduct, Finset.mul_sum, mul_assoc]
    _ = parity y * mask singletonMask i := by rw [mask_dot, mul_comm]

/-- Seven spectator address coordinates remain arbitrary. -/
private theorem source_zero (y : Address) :
    source0 left right y = y + parity y • mask singletonMask := by
  rw [source0, right_preimage, left_preimage, Matrix.mulVec_mulVec,
    inverse_product_shape, Matrix.add_mulVec, Matrix.one_mulVec, outer_action]

private theorem source_one (y : Address) :
    source1 left right flipZero y =
      (y + parity y • mask singletonMask) + mask singletonMask := by
  rw [source1, right_preimage, flipZero, Matrix.mulVec_add, right_first_column,
    ← right_preimage, ← source0, source_zero]

private def leftPhaseTwo (b : Bit) : Nat := (3 * b.val) % 4
private def rightPhaseTwo (a b : Bit) : Nat :=
  (a.val + 2 * b.val + 2 * (a.val * b.val)) % 4
private def canonicalPhaseTwo (a b : Bit) : Nat :=
  (b.val + 2 * (a.val * b.val)) % 4

private theorem left_quadratic (x : Address) :
    qvalue leftQ leftAlpha x = leftPhaseTwo (x 0) := by
  simp [Nat.testBit_eq_decide_div_mod_eq, qvalue, leftQ, leftAlpha,
    leftPhaseTwo, matrix, Fin.sum_univ_succ]

private theorem right_quadratic (x : Address) :
    qvalue rightQ rightAlpha x = rightPhaseTwo (x 7) (x 8) := by
  simp [Nat.testBit_eq_decide_div_mod_eq, qvalue, rightQ, rightAlpha,
    rightPhaseTwo, matrix, Fin.sum_univ_succ, Nat.add_assoc, add_assoc]

private theorem left_preimage_zero (y : Address) : left.preimage y 0 = y 8 := by
  rw [left_preimage]
  simp [Nat.testBit_eq_decide_div_mod_eq, Matrix.mulVec, dotProduct, matrix,
    leftInverseRows, Fin.sum_univ_succ]

private theorem left_exponent (y : Address) : left.exponent y = leftPhaseTwo (y 8) := by
  change (0 + qvalue leftQ leftAlpha (left.preimage y)) % 4 = _
  rw [left_quadratic, left_preimage_zero]
  simp only [Nat.zero_add, leftPhaseTwo, Nat.mod_mod]

private theorem right_exponent (y : Address) :
    right.exponent y = rightPhaseTwo (right.preimage y 7) (right.preimage y 8) := by
  change (0 + qvalue rightQ rightAlpha (right.preimage y)) % 4 = _
  rw [right_quadratic]
  simp only [Nat.zero_add, rightPhaseTwo, Nat.mod_mod]

private theorem canonical_phase (y : Address) :
    canonicalPhase y = canonicalPhaseTwo (y 7) (y 8) := by
  simp [Nat.testBit_eq_decide_div_mod_eq, canonicalPhase, qvalue, canonicalQ,
    defaultAlpha, canonicalPhaseTwo, matrix, Fin.sum_univ_succ, Nat.add_assoc]

private def phaseZeroTwo (a b : Bit) : Nat :=
  let s := sumTwo a b
  leftPhaseTwo b + rightPhaseTwo (a + s) (b + s)
private def phaseOneTwo (a b : Bit) : Nat :=
  let s := sumTwo a b
  leftPhaseTwo b + rightPhaseTwo (a + s + 1) (b + s + 1)

private theorem phase_zero (y : Address) :
    phase0 left right y = phaseZeroTwo (y 7) (y 8) := by
  rw [phase0, left_exponent, right_exponent]
  change leftPhaseTwo (y 8) + rightPhaseTwo (source0 left right y 7)
    (source0 left right y 8) = _
  rw [source_zero]
  simp [Nat.testBit_eq_decide_div_mod_eq, phaseZeroTwo, parity, singletonMask,
    mask, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem phase_one (y : Address) :
    phase1 left right flipZero y = phaseOneTwo (y 7) (y 8) := by
  rw [phase1, left_exponent, right_exponent]
  change leftPhaseTwo (y 8) + rightPhaseTwo (source1 left right flipZero y 7)
    (source1 left right flipZero y 8) = _
  rw [source_one]
  simp [Nat.testBit_eq_decide_div_mod_eq, phaseOneTwo, parity, singletonMask,
    mask, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

private theorem canonical_phase_flip (y : Address) :
    canonicalPhase (outputFlip y) = canonicalPhaseTwo (y 7 + 1) (y 8 + 1) := by
  rw [canonical_phase]
  simp [Nat.testBit_eq_decide_div_mod_eq, outputFlip, singletonMask, mask, Pi.add_apply]

/-- Four scalar phase cases cover the selected two-bit direction. -/
private theorem four_phase_cases : ∀ a b : Bit,
    (sumTwo a b = 0 ∧ phaseZeroTwo a b % 4 = 0 ∧
      (phaseOneTwo a b + canonicalPhaseTwo (a + 1) (b + 1)) % 4 =
        canonicalPhaseTwo a b % 4) ∨
    (sumTwo a b = 1 ∧
      (phaseZeroTwo a b + canonicalPhaseTwo (a + 1) (b + 1) + 1) % 4 =
        canonicalPhaseTwo a b % 4 ∧ phaseOneTwo a b % 4 = 1) := by
  decide +kernel

/-- Symbolic read-address identities and four scalar cases cover all nine
coordinates; no complete address function is enumerated. -/
theorem branch_phase_certificate :
    Certificate left right flipZero outputFlip canonicalPhase := by
  intro y
  rcases four_phase_cases (y 7) (y 8) with ⟨hs, h0, h1⟩ | ⟨hs, h0, h1⟩
  · have hp : parity y = 0 := hs
    refine Or.inl ⟨?_, ?_, ?_, ?_⟩
    · rw [source_zero, hp, zero_smul, add_zero]
    · rw [source_one, hp, zero_smul, add_zero]
      rfl
    · rw [phase_zero]
      exact h0
    · rw [phase_one, canonical_phase_flip, canonical_phase]
      exact h1
  · have hp : parity y = 1 := hs
    refine Or.inr ⟨?_, ?_, ?_, ?_⟩
    · rw [source_zero, hp, one_smul]
      rfl
    · rw [source_one, hp, one_smul, add_assoc, ZModModule.add_self, add_zero]
    · rw [phase_zero, canonical_phase_flip, canonical_phase]
      exact h0
    · rw [phase_one]
      exact h1

theorem canonical_transport (y : Address) :
    canonicalLinear (flipZero (canonicalLinear.symm y)) = outputFlip y := by
  exact transport_from_linearity (· + ·) canonicalLinear.toEquiv (mask 1)
    (mask singletonMask) (fun x z => canonicalLinear.map_add x z) canonical_first_column y

noncomputable section

/-- Exact old=[]→new singleton interpreted identity for arbitrary complex
payloads, retaining the serialized global and preimage phases. -/
theorem selected_child_operator (v : Address → ℂ) :
    left.operator (gaussian (right.operator v)) =
      canonicalK canonicalLinear.toEquiv canonicalPhase
        (gaussian ((canonicalK canonicalLinear.toEquiv canonicalPhase).symm v)) :=
  sandwich_operator left right canonicalLinear.toEquiv canonicalPhase
    flipZero outputFlip gaussian gaussian_apply canonical_transport branch_phase_certificate v

/-- Arbitrary independent spectators are retained pointwise. -/
theorem selected_child_with_spectators {S : Type*} (v : S → Address → ℂ) (s : S) :
    left.operator (gaussian (right.operator (v s))) =
      canonicalK canonicalLinear.toEquiv canonicalPhase
        (gaussian ((canonicalK canonicalLinear.toEquiv canonicalPhase).symm (v s))) :=
  selected_child_operator (v s)

end
end CurrentMain.CliffordChild003Canonical

#print axioms CurrentMain.CliffordChild003Canonical.record_key
#print axioms CurrentMain.CliffordChild003Canonical.raw_fields_bounded
#print axioms CurrentMain.CliffordChild003Canonical.left_inverses
#print axioms CurrentMain.CliffordChild003Canonical.right_inverses
#print axioms CurrentMain.CliffordChild003Canonical.canonical_inverses
#print axioms CurrentMain.CliffordChild003Canonical.canonical_source_certificate
#print axioms CurrentMain.CliffordChild003Canonical.canonical_first_column
#print axioms CurrentMain.CliffordChild003Canonical.branch_phase_certificate
#print axioms CurrentMain.CliffordChild003Canonical.canonical_transport
#print axioms CurrentMain.CliffordChild003Canonical.selected_child_operator
#print axioms CurrentMain.CliffordChild003Canonical.selected_child_with_spectators
