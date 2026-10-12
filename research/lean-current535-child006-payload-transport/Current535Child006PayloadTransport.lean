import Current535RecipeLabelBindings

/-!
Explicit low-four/high-five address transport for current535 child0→6/[11].
This reuses the checked historical child009 identity. The actual bit order,
forward/inverse row actions, input-coordinate phases, right offset/global
phase1 and Gaussian C0 are bound below. Apache-2.0; see NOTICE.md.
-/
set_option Elab.async false

namespace CurrentMain.Current535Child006PayloadTransport

open scoped BigOperators Matrix
open CliffordNineBitDecoder (Bit Address matrix mask qvalue)

abbrev Low := CliffordChild009Decoder.Low
abbrev High := Fin 5 → Bit
abbrev SplitAddress := Low × High

def ofBool (b : Bool) : Bit := if b then 1 else 0
def toBool (b : Bit) : Bool := decide (b = 1)

@[simp] theorem ofBool_toBool (b : Bit) : ofBool (toBool b) = b := by
  have h : ∀ z : Bit, ofBool (toBool z) = z := by decide +kernel
  exact h b

@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> rfl

@[simp] theorem ofBool_xor (a b : Bool) : ofBool (a ^^ b) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide +kernel

@[simp] theorem ofBool_not (a : Bool) : ofBool (!a) = ofBool a + 1 := by
  cases a <;> decide +kernel

def split (x : Address) : SplitAddress :=
  ((toBool (x 0), toBool (x 1), toBool (x 2), toBool (x 3)),
    fun i => x ⟨i.val + 4, by omega⟩)

def join (x : SplitAddress) : Address :=
  ![ofBool x.1.1, ofBool x.1.2.1, ofBool x.1.2.2.1, ofBool x.1.2.2.2,
    x.2 0, x.2 1, x.2 2, x.2 3, x.2 4]

theorem join_split (x : Address) : join (split x) = x := by
  funext i
  fin_cases i <;> simp [join, split]

theorem split_join (x : SplitAddress) : split (join x) = x := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  apply Prod.ext
  · simp [split, join]
  · funext i
    fin_cases i <;> simp [split, join]

def addressEquiv : Address ≃ SplitAddress where
  toFun := split
  invFun := join
  left_inv := join_split
  right_inv := split_join

/-- The low bit index remains its little-endian source index; higher bits
4–8 become High indices0–4, with no permutation or payload restriction. -/
theorem coordinate_order (x : Address) :
    (addressEquiv x).1 =
      (toBool (x 0), toBool (x 1), toBool (x 2), toBool (x 3)) ∧
    (∀ i : Fin 5, (addressEquiv x).2 i = x ⟨i.val + 4, by omega⟩) := by
  exact ⟨rfl, fun _ => rfl⟩

def leftInverseRows : List Nat := [8, 9, 10, 4, 16, 32, 64, 128, 256]
def rightInverseRows : List Nat := [5, 3, 8, 7, 16, 32, 64, 128, 256]

theorem left_rows (x : SplitAddress) :
    matrix CliffordChild009Decoder.leftRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.leftEquiv x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, CliffordChild009Decoder.leftRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.leftEquiv,
      CliffordChild009Decoder.leftMap, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem right_rows (x : SplitAddress) :
    matrix CliffordChild009Decoder.rightRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.rightEquiv x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, CliffordChild009Decoder.rightRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.rightEquiv,
      CliffordChild009Decoder.rightMap, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem left_inverse_rows (x : SplitAddress) :
    matrix leftInverseRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.leftEquiv.symm x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, leftInverseRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.leftEquiv,
      CliffordChild009Decoder.leftInverse, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem right_inverse_rows (x : SplitAddress) :
    matrix rightInverseRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.rightEquiv.symm x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, rightInverseRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.rightEquiv,
      CliffordChild009Decoder.rightInverse, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem offset_rows (x : SplitAddress) :
    join x + mask 1 =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.offsetEquiv x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [join, mask, Nat.testBit_eq_decide_div_mod_eq,
      CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.offsetEquiv,
      Equiv.prodCongr_apply, Prod.map_apply]

theorem left_phase (x : SplitAddress) :
    qvalue CliffordChild009Decoder.leftQ CliffordChild009Decoder.leftAlpha (join x) =
      CliffordChild009Decoder.leftPhase x.1 := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [qvalue, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
      CliffordChild009Decoder.leftQ, CliffordChild009Decoder.leftAlpha,
      CliffordChild009Decoder.leftPhase, join, ofBool]

theorem right_phase (x : SplitAddress) :
    qvalue CliffordChild009Decoder.rightQ CliffordChild009Decoder.rightAlpha (join x) =
      CliffordChild009Decoder.rightPhase x.1 := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [qvalue, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
      CliffordChild009Decoder.rightQ, CliffordChild009Decoder.rightAlpha,
      CliffordChild009Decoder.rightPhase, join, ofBool]

theorem canonical_phase (x : SplitAddress) :
    qvalue CliffordChild009Canonical.canonicalQ (List.replicate 9 0) (join x) =
      CliffordChild009Canonical.canonicalPhase x.1 := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [qvalue, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
      CliffordChild009Canonical.canonicalQ, CliffordChild009Canonical.canonicalPhase,
      join, ofBool]

noncomputable section

/-- Precomposition by the certified address split, not an assumed type equality. -/
def payloadEquiv : (SplitAddress → ℂ) ≃ₗ[ℂ] (Address → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ addressEquiv

def carry (A : (SplitAddress → ℂ) ≃ₗ[ℂ] (SplitAddress → ℂ)) :
    (Address → ℂ) ≃ₗ[ℂ] (Address → ℂ) :=
  (payloadEquiv.symm.trans A).trans payloadEquiv

@[simp] theorem carry_apply (A) (v : Address → ℂ) :
    carry A v = payloadEquiv (A (payloadEquiv.symm v)) := rfl

def leftPacked := carry (CliffordChild009Decoder.leftDecoded CliffordChild009Canonical.imagUnit)
def rightPacked := carry (CliffordChild009Decoder.rightDecoded CliffordChild009Canonical.imagUnit)
def canonicalKPacked := carry CliffordChild009Canonical.canonicalK
def canonicalNewPacked := carry CliffordChild009Canonical.canonicalNew

theorem gaussian_transport : carry CliffordChild009Canonical.gaussian =
    CliffordNineBitDecoder.gaussian := by
  apply LinearEquiv.ext
  intro v
  funext y
  obtain ⟨x, rfl⟩ := addressEquiv.symm.surjective y
  rcases x with ⟨x, h⟩
  change CliffordChild009Canonical.gaussian (payloadEquiv.symm v) (split (join (x, h))) = _
  rw [split_join, CliffordChild009Canonical.gaussian_apply,
    CliffordNineBitDecoder.gaussian_apply]
  change _ = _ + _ * v (join (x, h) + mask 1)
  rw [offset_rows]
  rfl

/-- Exact forward source monomial action, with its phase at the input address. -/
theorem left_source_action (v : Address → ℂ) (x : Address) :
    leftPacked v (matrix CliffordChild009Decoder.leftRows *ᵥ x) =
      Complex.I ^ ((0 + qvalue CliffordChild009Decoder.leftQ
        CliffordChild009Decoder.leftAlpha x) % 4) * v x := by
  obtain ⟨z, rfl⟩ := addressEquiv.symm.surjective x
  rcases z with ⟨z, h⟩
  rw [left_rows]
  change CliffordChild009Decoder.leftDecoded CliffordChild009Canonical.imagUnit
    (payloadEquiv.symm v) (split (join
      (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.leftEquiv (z, h)))) = _
  rw [split_join]
  rw [CliffordChild009Decoder.left_decoded_apply, left_phase]
  simpa only [Units.val_pow_eq_pow_val]

/-- Right offset1 and global phase1 remain literal, including for dirty payloads. -/
theorem right_source_action (v : Address → ℂ) (x : Address) :
    rightPacked v ((matrix CliffordChild009Decoder.rightRows *ᵥ x) + mask 1) =
      Complex.I ^ ((1 + qvalue CliffordChild009Decoder.rightQ
        CliffordChild009Decoder.rightAlpha x) % 4) * v x := by
  obtain ⟨z, rfl⟩ := addressEquiv.symm.surjective x
  rcases z with ⟨z, h⟩
  rw [right_rows, offset_rows]
  change CliffordChild009Decoder.rightDecoded CliffordChild009Canonical.imagUnit
    (payloadEquiv.symm v) (split (join
      (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.offsetEquiv
        (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.rightEquiv (z, h))))) = _
  rw [split_join]
  rw [CliffordChild009Decoder.right_decoded_apply, right_phase]
  simpa only [Units.val_pow_eq_pow_val]

theorem canonicalK_source_action (v : Address → ℂ) (x : Address) :
    canonicalKPacked v x =
      Complex.I ^ qvalue CliffordChild009Canonical.canonicalQ (List.replicate 9 0) x *
        v (matrix leftInverseRows *ᵥ x) := by
  obtain ⟨z, rfl⟩ := addressEquiv.symm.surjective x
  rcases z with ⟨z, h⟩
  change CliffordChild009Canonical.canonicalK (payloadEquiv.symm v) (split (join (z, h))) = _
  rw [split_join, CliffordChild009Canonical.canonicalK_apply,
    canonical_phase, left_inverse_rows]
  rfl

private theorem carry_symm (A) : (carry A).symm = carry A.symm := by
  apply LinearEquiv.ext
  intro v
  rfl

/-- The frame operator is K C0 K^-1, not K alone. -/
theorem canonical_new_shape (v : Address → ℂ) :
    canonicalNewPacked v =
      canonicalKPacked (CliffordNineBitDecoder.gaussian (canonicalKPacked.symm v)) := by
  simp only [canonicalNewPacked, canonicalKPacked, carry_symm, ← gaussian_transport,
    carry_apply, LinearEquiv.symm_apply_apply, CliffordChild009Canonical.canonicalNew,
    LinearEquiv.trans_apply]

/-- Reuse the accepted phase-sensitive child009 theorem under the explicit
address equivalence. No state-column or tableau test replaces this equality. -/
theorem selected_child_operator (v : Address → ℂ) :
    leftPacked (CliffordNineBitDecoder.gaussian (rightPacked v)) =
      canonicalNewPacked v := by
  have h := CliffordChild009Canonical.selected_child_operator (payloadEquiv.symm v)
  have hh := congrArg payloadEquiv h
  simpa only [← gaussian_transport, leftPacked, rightPacked, canonicalNewPacked,
    carry_apply, LinearEquiv.symm_apply_apply, DirectedChildRecipes.Child.eval,
    CliffordChild009Canonical.selectedChild, CliffordChild009Canonical.canonicalOld,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply] using hh

end
end CurrentMain.Current535Child006PayloadTransport

#print axioms CurrentMain.Current535Child006PayloadTransport.addressEquiv
#print axioms CurrentMain.Current535Child006PayloadTransport.coordinate_order
#print axioms CurrentMain.Current535Child006PayloadTransport.left_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.right_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.left_inverse_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.right_inverse_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.offset_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.left_phase
#print axioms CurrentMain.Current535Child006PayloadTransport.right_phase
#print axioms CurrentMain.Current535Child006PayloadTransport.canonical_phase
#print axioms CurrentMain.Current535Child006PayloadTransport.gaussian_transport
#print axioms CurrentMain.Current535Child006PayloadTransport.left_source_action
#print axioms CurrentMain.Current535Child006PayloadTransport.right_source_action
#print axioms CurrentMain.Current535Child006PayloadTransport.canonicalK_source_action
#print axioms CurrentMain.Current535Child006PayloadTransport.canonical_new_shape
#print axioms CurrentMain.Current535Child006PayloadTransport.selected_child_operator
