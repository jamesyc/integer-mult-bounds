import Current535Child006Phases

/-! Exact explicit low-four/high-five operator transport for current535 child0→6/[11].
Apache-2.0; see NOTICE.md. Reuses the accepted all-payload child009 identity
and separately checked source coordinate/phase correspondence. -/
set_option Elab.async false
namespace CurrentMain.Current535Child006PayloadTransport
open scoped BigOperators Matrix
open CliffordNineBitDecoder (Bit Address matrix mask qvalue)

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
  simp only [show addressEquiv.symm (z, h) = join (z, h) from rfl]
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
  simp only [show addressEquiv.symm (z, h) = join (z, h) from rfl]
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
  simp only [show addressEquiv.symm (z, h) = join (z, h) from rfl]
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

#print axioms CurrentMain.Current535Child006PayloadTransport.gaussian_transport
#print axioms CurrentMain.Current535Child006PayloadTransport.left_source_action
#print axioms CurrentMain.Current535Child006PayloadTransport.right_source_action
#print axioms CurrentMain.Current535Child006PayloadTransport.canonicalK_source_action
#print axioms CurrentMain.Current535Child006PayloadTransport.canonical_new_shape
#print axioms CurrentMain.Current535Child006PayloadTransport.selected_child_operator
