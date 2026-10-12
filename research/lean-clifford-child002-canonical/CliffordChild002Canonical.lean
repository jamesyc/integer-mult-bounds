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
  constructor <;> decide +kernel

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

/-- All512 address cases include both read addresses and complete Z4 phases.
No selected row or operator equation is a premise of this finite certificate. -/
theorem branch_phase_certificate :
    Certificate left right flipZero outputFlip canonicalPhase := by
  unfold Certificate
  decide +kernel

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
