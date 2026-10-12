import CliffordNineBitDecoder

/-!
One pinned f19 rank-one recipe, interpreted on all nine address coordinates.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md.
Every closed source/inverse/basis/phase certificate below requires kernel
checking. No theorem about a raw physical executor is assumed or claimed.
-/
set_option Elab.async false

namespace CurrentMain.CliffordChild002Canonical

open CliffordNineBitDecoder
open RankOneRecipeCertificate
open scoped BigOperators Matrix

def oldFrame : Nat := 0
def newFrame : Nat := 2
def rank : Nat := 1
def oldDescriptor : List Nat := []
def newDescriptor : List Nat := [45]
def singletonMask : Nat := 45
def leftRows : List Nat := [3, 4, 9, 17, 32, 1, 64, 128, 256]
def leftInverseRows : List Nat := [32, 33, 2, 36, 40, 16, 64, 128, 256]
def leftQ : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0]
def leftAlpha : List Nat := [3, 0, 0, 0, 0, 0, 0, 0, 0]
def leftOffset : Nat := 0
def leftPhase : Nat := 0
def rightRows : List Nat := [13, 33, 2, 36, 40, 16, 64, 128, 256]
def rightInverseRows : List Nat := [25, 4, 19, 11, 32, 27, 64, 128, 256]
def rightQ : List Nat := [45, 0, 45, 45, 0, 13, 0, 0, 0]
def rightAlpha : List Nat := [1, 0, 1, 1, 0, 2, 0, 0, 0]
def rightOffset : Nat := 0
def rightPhase : Nat := 0
def canonicalBasis : List Nat := [45, 1, 2, 4, 8, 16, 64, 128, 256]
def canonicalRows : List Nat := [3, 4, 9, 17, 32, 1, 64, 128, 256]
def canonicalInverseRows : List Nat := [32, 33, 2, 36, 40, 16, 64, 128, 256]
def canonicalQ : List Nat := [32, 0, 32, 32, 0, 45, 0, 0, 0]

theorem record_key : oldFrame = 0 ∧ newFrame = 2 ∧ rank = 1 ∧
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

/-- The selected inverse product is a rank-one binary update. This is a
9-by-9 matrix identity, not enumeration of address functions. -/
private theorem inverse_product_shape :
    matrix rightInverseRows * matrix leftInverseRows =
      1 + Matrix.vecMulVec (mask singletonMask) (mask singletonMask) := by
  decide +kernel

private theorem right_first_column :
    matrix rightInverseRows *ᵥ mask 1 = mask singletonMask := by
  decide +kernel

private def sumFour (a b c d : Bit) : Bit := a + b + c + d
private def parity (y : Address) : Bit := sumFour (y 0) (y 2) (y 3) (y 5)

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
  simp [dotProduct, mask, singletonMask, parity, sumFour, Fin.sum_univ_succ]

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

/-- The other five address coordinates remain arbitrary. -/
private theorem source_zero (y : Address) :
    source0 left right y = y + parity y • mask singletonMask := by
  rw [source0, right_preimage, left_preimage, Matrix.mulVec_mulVec,
    inverse_product_shape, Matrix.add_mulVec, Matrix.one_mulVec, outer_action]

private theorem source_one (y : Address) :
    source1 left right flipZero y =
      (y + parity y • mask singletonMask) + mask singletonMask := by
  rw [source1, right_preimage, flipZero, Matrix.mulVec_add, right_first_column,
    ← right_preimage, ← source0, source_zero]

private def leftPhaseFour (d : Bit) : Nat := (3 * d.val) % 4
private def rightPhaseFour (a b c d : Bit) : Nat :=
  (a.val + b.val + c.val + 2 * d.val +
    2 * (a.val * (b + c + d).val + b.val * (c + d).val + c.val * d.val)) % 4
private def canonicalPhaseFour (a b c d : Bit) : Nat :=
  (d.val + 2 * (a.val * d.val + b.val * d.val + c.val * d.val)) % 4

private theorem left_quadratic (x : Address) :
    qvalue leftQ leftAlpha x = leftPhaseFour (x 0) := by
  simp [qvalue, leftQ, leftAlpha, leftPhaseFour, matrix, Fin.sum_univ_succ]

private theorem right_quadratic (x : Address) :
    qvalue rightQ rightAlpha x = rightPhaseFour (x 0) (x 2) (x 3) (x 5) := by
  simp [qvalue, rightQ, rightAlpha, rightPhaseFour, matrix, Fin.sum_univ_succ,
    Nat.add_assoc]

private theorem left_preimage_zero (y : Address) : left.preimage y 0 = y 5 := by
  rw [left_preimage]
  simp [Matrix.mulVec, dotProduct, matrix, leftInverseRows, Fin.sum_univ_succ]

private theorem left_exponent (y : Address) : left.exponent y = leftPhaseFour (y 5) := by
  change (0 + qvalue leftQ leftAlpha (left.preimage y)) % 4 = _
  rw [left_quadratic, left_preimage_zero]
  simp only [Nat.zero_add, leftPhaseFour, Nat.mod_mod]

private theorem right_exponent (y : Address) :
    right.exponent y = rightPhaseFour (right.preimage y 0) (right.preimage y 2)
      (right.preimage y 3) (right.preimage y 5) := by
  change (0 + qvalue rightQ rightAlpha (right.preimage y)) % 4 = _
  rw [right_quadratic]
  simp only [Nat.zero_add, rightPhaseFour, Nat.mod_mod]

private theorem canonical_phase (y : Address) :
    canonicalPhase y = canonicalPhaseFour (y 0) (y 2) (y 3) (y 5) := by
  simp [canonicalPhase, qvalue, canonicalQ, defaultAlpha, canonicalPhaseFour,
    matrix, Fin.sum_univ_succ, Nat.add_assoc]

private def phaseZeroFour (a b c d : Bit) : Nat :=
  let s := sumFour a b c d
  leftPhaseFour d + rightPhaseFour (a + s) (b + s) (c + s) (d + s)
private def phaseOneFour (a b c d : Bit) : Nat :=
  let s := sumFour a b c d
  leftPhaseFour d + rightPhaseFour (a + s + 1) (b + s + 1) (c + s + 1) (d + s + 1)

private theorem phase_zero (y : Address) :
    phase0 left right y = phaseZeroFour (y 0) (y 2) (y 3) (y 5) := by
  rw [phase0, left_exponent, right_exponent]
  change leftPhaseFour (y 5) + rightPhaseFour (source0 left right y 0)
    (source0 left right y 2) (source0 left right y 3) (source0 left right y 5) = _
  rw [source_zero]
  simp [phaseZeroFour, parity, singletonMask, mask, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

private theorem phase_one (y : Address) :
    phase1 left right flipZero y = phaseOneFour (y 0) (y 2) (y 3) (y 5) := by
  rw [phase1, left_exponent, right_exponent]
  change leftPhaseFour (y 5) + rightPhaseFour (source1 left right flipZero y 0)
    (source1 left right flipZero y 2) (source1 left right flipZero y 3)
    (source1 left right flipZero y 5) = _
  rw [source_one]
  simp [phaseOneFour, parity, singletonMask, mask, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]

private theorem canonical_phase_flip (y : Address) :
    canonicalPhase (outputFlip y) =
      canonicalPhaseFour (y 0 + 1) (y 2 + 1) (y 3 + 1) (y 5 + 1) := by
  rw [canonical_phase]
  simp [outputFlip, singletonMask, mask, Pi.add_apply]

/-- Exactly sixteen scalar phase cases. No full-address function equality,
matrix product, basis evaluator or operator is recomputed inside this decision. -/
private theorem sixteen_phase_cases : ∀ a b c d : Bit,
    (sumFour a b c d = 0 ∧ phaseZeroFour a b c d % 4 = 0 ∧
      (phaseOneFour a b c d + canonicalPhaseFour (a + 1) (b + 1) (c + 1) (d + 1)) % 4 =
        canonicalPhaseFour a b c d % 4) ∨
    (sumFour a b c d = 1 ∧
      (phaseZeroFour a b c d + canonicalPhaseFour (a + 1) (b + 1) (c + 1) (d + 1) + 1) % 4 =
        canonicalPhaseFour a b c d % 4 ∧ phaseOneFour a b c d % 4 = 1) := by
  decide +kernel

/-- All nine coordinates and arbitrary payloads are covered by symbolic
read-address identities plus the sixteen scalar phase cases. -/
theorem branch_phase_certificate :
    Certificate left right flipZero outputFlip canonicalPhase := by
  intro y
  rcases sixteen_phase_cases (y 0) (y 2) (y 3) (y 5) with
    ⟨hs, h0, h1⟩ | ⟨hs, h0, h1⟩
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
end CurrentMain.CliffordChild002Canonical

#print axioms CurrentMain.CliffordChild002Canonical.record_key
#print axioms CurrentMain.CliffordChild002Canonical.raw_fields_bounded
#print axioms CurrentMain.CliffordChild002Canonical.left_inverses
#print axioms CurrentMain.CliffordChild002Canonical.right_inverses
#print axioms CurrentMain.CliffordChild002Canonical.canonical_inverses
#print axioms CurrentMain.CliffordChild002Canonical.canonical_source_certificate
#print axioms CurrentMain.CliffordChild002Canonical.canonical_first_column
#print axioms CurrentMain.CliffordChild002Canonical.branch_phase_certificate
#print axioms CurrentMain.CliffordChild002Canonical.canonical_transport
#print axioms CurrentMain.CliffordChild002Canonical.selected_child_operator
#print axioms CurrentMain.CliffordChild002Canonical.selected_child_with_spectators
