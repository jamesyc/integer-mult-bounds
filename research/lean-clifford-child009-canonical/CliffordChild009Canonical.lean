import CliffordChild009Decoder
import GaussianPhaseNormalization
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.GrindInstances

/-!
One selected directed-child identity, old=0/new=9/rank=1, over complete complex
payloads. The fixed raw record and input/preimage phase convention are inherited
from CliffordChild009Decoder. The canonical frame uses the source's greedy basis
for [11], its exact binary inverse and Q correction. Gaussian inverse/linearity
are reused from GaussianPhaseNormalization. Apache-2.0; see NOTICE.md.

This does not identify a serialized physical executor, prove another record, or
supply residual wrappers and expanded coefficient/tableau work.
-/
namespace CurrentMain.CliffordChild009Canonical

open CliffordChild009Decoder
open CliffordMonomialDecoder

/-- Bounded translation of the source rank loop. Every selected mask is below
2^9. Ten loop tests allow all nine pivot eliminations and the terminal zero test.
Exhaustion is `none`, never a fabricated rank. -/
private def insertPivot : Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat))
  | 0, _, _ => none
  | fuel + 1, pivots, x =>
      if x = 0 then some pivots else
      match pivots.lookup x.log2 with
      | none => some ((x.log2, x) :: pivots)
      | some y => insertPivot fuel pivots (x ^^^ y)

private def rank9 (rows : List Nat) : Option Nat := do
  let pivots ← rows.foldlM (fun p x => insertPivot 10 p x) []
  return pivots.length

/-- Source `basis_extend(cols,9)`, with its rank calls checked rather than an
assumed basis. The final assertion is also explicit. -/
private def basisExtend9 (cols : List Nat) : Option (List Nat) := do
  let out ← (cols ++ (List.range 9).map (fun i => 2 ^ i)).foldlM
    (fun out x => do
      let r ← rank9 (out ++ [x])
      return if r > out.length then out ++ [x] else out) []
  if out.length = 9 then return out else none

private def transpose9 (rows : List Nat) : List Nat :=
  (List.range 9).map (fun j => (List.range 9).foldl
    (fun out i => out + if (rows.getD i 0).testBit j then 2 ^ i else 0) 0)

private def parity9 (x : Nat) : Bool :=
  (List.range 9).foldl (fun out i => out ^^ x.testBit i) false

private def gramCorrection9 (inverseRows : List Nat) : List Nat :=
  let cols := transpose9 inverseRows
  (List.range 9).map (fun i => (2 ^ i) ^^^ ((List.range 9).foldl
    (fun out j => out + if parity9 ((cols.getD i 0) &&& (cols.getD j 0))
      then 2 ^ j else 0) 0))

def canonicalBasis : List Nat := [11, 1, 2, 4, 16, 32, 64, 128, 256]
def canonicalInverseRows : List Nat := [8, 9, 10, 4, 16, 32, 64, 128, 256]
def canonicalQ : List Nat := [8, 8, 0, 3, 0, 0, 0, 0, 0]

/-- Only the fixed selected nine-coordinate data are reduced. This checks the
source greedy order, transpose and I+G^-T G^-1 correction, not a generic rank
algorithm or any of the other 2,921 child records. -/
theorem canonical_data_certificate :
    basisExtend9 [11] = some canonicalBasis ∧
    transpose9 canonicalBasis = leftRows ∧
    gramCorrection9 canonicalInverseRows = canonicalQ ∧
    transpose9 canonicalQ = canonicalQ ∧
    (∀ r ∈ canonicalBasis, r < 512) ∧
    (∀ r ∈ canonicalInverseRows, r < 512) := by
  decide +kernel

/-- The proposed inverse is proved by the already certified coordinate inverse;
its upper five rows are literal identity. No source `inv` assertion is assumed. -/
theorem canonical_inverse_decode (x : Low) :
    mv4 canonicalInverseRows x = leftEquiv.symm x ∧
    canonicalInverseRows.drop 4 = [16, 32, 64, 128, 256] := by
  rcases x with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def canonicalPhase (x : Low) : Nat :=
  ((if x.1 && x.2.2.2 then 2 else 0) +
   (if x.2.1 && x.2.2.2 then 2 else 0)) % 4

theorem canonical_phase_decode (x : Low) :
    qvalue4 canonicalQ (List.replicate 9 0) x = canonicalPhase x := by
  rcases x with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

noncomputable section

/-- The phase unit is actual complex i, rather than an unspecified fourth root. -/
def imagUnit : ℂˣ where
  val := Complex.I
  inv := -Complex.I
  val_inv := by simp
  inv_val := by simp

theorem imagUnit_four : imagUnit ^ 4 = 1 := by
  apply Units.ext
  change Complex.I ^ 4 = 1
  exact Complex.I_pow_four

variable {S : Type*}

private def flipZero (x : Low × S) : Low × S := (offsetEquiv x.1, x.2)

private theorem flipZero_twice (x : Low × S) : flipZero (flipZero x) = x := by
  rcases x with ⟨⟨a, b, c, d⟩, s⟩
  cases a <;> rfl

/-- The source Gaussian C0, with its exact dyadic normalization. This packages
an existing ExactFrame as a Mathlib LinearEquiv without redoing its algebra. -/
def gaussian : (Low × S → ℂ) ≃ₗ[ℂ] (Low × S → ℂ) :=
  let E := GaussianPhaseNormalization.exactGate Complex.I ((2 : ℂ)⁻¹)
    Complex.I_mul_I (mul_inv_cancel₀ two_ne_zero) flipZero flipZero_twice
  { toFun := E.encode
    invFun := E.decode
    left_inv := E.left_inverse
    right_inv := E.right_inverse
    map_add' := E.encode_add
    map_smul' := E.encode_scale }

@[simp] theorem gaussian_apply (v : Low × S → ℂ) (x : Low) (s : S) :
    gaussian v (x, s) =
      GaussianPhaseNormalization.a Complex.I ((2 : ℂ)⁻¹) * v (x, s) +
      GaussianPhaseNormalization.b Complex.I ((2 : ℂ)⁻¹) * v (offsetEquiv x, s) := rfl

/-- Source K=perm(G).then(diag(Q)), hence D_Q after P_G. -/
def canonicalK : (Low × S → ℂ) ≃ₗ[ℂ] (Low × S → ℂ) :=
  (push (liftAddress leftEquiv)).trans
    (diagonal imagUnit (fun x => canonicalPhase x.1))

@[simp] theorem canonicalK_apply (v : Low × S → ℂ) (x : Low) (s : S) :
    canonicalK v (x, s) = Complex.I ^ canonicalPhase x * v (leftEquiv.symm x, s) := rfl

private theorem right_apply (v : Low × S → ℂ) (x : Low) (s : S) :
    rightDecoded imagUnit v (x, s) =
      Complex.I ^ ((1 + rightPhase ((rightEquiv.trans offsetEquiv).symm x)) % 4) *
        v ((rightEquiv.trans offsetEquiv).symm x, s) := by
  have h := right_decoded_apply imagUnit v ((rightEquiv.trans offsetEquiv).symm x) s
  change rightDecoded imagUnit v
    ((rightEquiv.trans offsetEquiv) ((rightEquiv.trans offsetEquiv).symm x), s) = _ at h
  rw [Equiv.apply_symm_apply] at h
  simpa only [Units.val_pow_eq_pow_val] using h

/-- The finite proof keeps arbitrary complex payloads and an arbitrary spectator
type. It compares both Gaussian branches, retaining offset 1 and global phase 1
of the stored right monomial. It is not a zero-state or tableau test. -/
theorem decoded_child_on_canonical (v : Low × S → ℂ) :
    leftDecoded imagUnit (gaussian (rightDecoded imagUnit (canonicalK v))) =
      canonicalK (gaussian v) := by
  have hp := GaussianPhaseNormalization.phase_coefficients Complex.I ((2 : ℂ)⁻¹)
    Complex.I_mul_I
  have ha := hp.2
  have hb := hp.1
  have ha' : GaussianPhaseNormalization.a Complex.I ((2 : ℂ)⁻¹) * Complex.I =
      -GaussianPhaseNormalization.b Complex.I ((2 : ℂ)⁻¹) := by
    simpa only [mul_comm] using ha
  have hb' : GaussianPhaseNormalization.b Complex.I ((2 : ℂ)⁻¹) * Complex.I =
      GaussianPhaseNormalization.a Complex.I ((2 : ℂ)⁻¹) := by
    simpa only [mul_comm] using hb
  funext y
  rcases y with ⟨y, s⟩
  obtain ⟨x, rfl⟩ := leftEquiv.surjective y
  rw [left_decoded_apply, canonicalK_apply]
  simp only [gaussian_apply, right_apply, canonicalK_apply]
  rcases x with ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [canonicalPhase,
      leftPhase, rightPhase, leftEquiv, leftMap, leftInverse, rightEquiv,
      rightMap, rightInverse, offsetEquiv, Equiv.trans_apply,
      Units.val_pow_eq_pow_val, imagUnit, pow_succ, Complex.I_mul_I,
      mul_add, add_mul, ← mul_assoc, ha, hb, ha', hb', add_comm]

/-- Canonical [] is identity. Canonical [11] is K C0 K^-1, in the direct
old→new direction from phases_delta.py. -/
def canonicalOld : (Low × S → ℂ) ≃ₗ[ℂ] (Low × S → ℂ) := LinearEquiv.refl _ _
def canonicalNew : (Low × S → ℂ) ≃ₗ[ℂ] (Low × S → ℂ) :=
  (canonicalK.symm.trans gaussian).trans canonicalK

def selectedChild : DirectedChildRecipes.Child ℂ (Low × S → ℂ) where
  rank := 1
  left := leftDecoded imagUnit
  right := some (rightDecoded imagUnit)
  right_none_iff_rank_zero := by simp

/-- Discharges this one interpreted record's canonical-child operator equation
for all payloads. The block argument is C0 only because this record has rank 1;
no meaning is assigned here to other ranks or raw physical recipe execution. -/
theorem selected_child_operator (v : Low × S → ℂ) :
    DirectedChildRecipes.Child.eval (fun _ => gaussian) selectedChild v =
      canonicalNew (canonicalOld.symm v) := by
  have h := decoded_child_on_canonical (canonicalK.symm v)
  simpa only [DirectedChildRecipes.Child.eval, selectedChild,
    LinearEquiv.apply_symm_apply, canonicalNew, canonicalOld,
    LinearEquiv.trans_apply, LinearEquiv.refl_symm, LinearEquiv.refl_apply] using h

end
end CurrentMain.CliffordChild009Canonical

#print axioms CurrentMain.CliffordChild009Canonical.canonical_data_certificate
#print axioms CurrentMain.CliffordChild009Canonical.canonical_inverse_decode
#print axioms CurrentMain.CliffordChild009Canonical.canonical_phase_decode
#print axioms CurrentMain.CliffordChild009Canonical.imagUnit_four
#print axioms CurrentMain.CliffordChild009Canonical.gaussian
#print axioms CurrentMain.CliffordChild009Canonical.decoded_child_on_canonical
#print axioms CurrentMain.CliffordChild009Canonical.selected_child_operator
