import Current535First45KeyRestriction
import Current535Child002Canonical

/-!
Interpreted recipe supplier for the four checked current535 first45 A/B blocks.
The selected [459] all-payload certificate supplies the only relabel key used.
Rational scalar decoding and original labels are retained. PR509 Stream's
conjugation theorem is applied unchanged, with no new stream induction.
Apache-2.0; source and theorem attribution are retained in NOTICE.md.
-/
set_option Elab.async false

namespace CurrentMain.Current535First45Recipes
open CliffordNineBitDecoder (Address gaussian)
open CanonicalFrameCoverage (Register Row)
open CurrentScalarCentreBand (ScalarEvent decodeRows rawRowsRun decoded_rows_run)
open Current535First45KeyRestriction (RelabelsUse KeyedDecoded)

abbrev Payload := Address → ℂ
abbrev Label := Fin 997
abbrev FrameMap := Label → Payload ≃ₗ[ℚ] Payload
abbrev RecipeTable := Label → Label → Payload → Payload

noncomputable section

/-- The selected canonical frame is K C0 K^-1, with the exact checked source
basis and phase. Restricting scalars changes neither function nor inverse. -/
def frameTwo : Payload ≃ₗ[ℚ] Payload :=
  let K := RankOneRecipeCertificate.canonicalK
    Current535Child002Canonical.canonicalLinear.toEquiv
    Current535Child002Canonical.canonicalPhase
  ((K.symm.trans gaussian).trans K).restrictScalars ℚ

theorem frameTwo_apply (v : Payload) :
    frameTwo v =
      RankOneRecipeCertificate.canonicalK
        Current535Child002Canonical.canonicalLinear.toEquiv
        Current535Child002Canonical.canonicalPhase
        (gaussian ((RankOneRecipeCertificate.canonicalK
          Current535Child002Canonical.canonicalLinear.toEquiv
          Current535Child002Canonical.canonicalPhase).symm v)) := rfl

/-- Interpreted serialized left / exact Gaussian C0 / right recipe for0→2. -/
def recipe02 (v : Payload) : Payload :=
  Current535Child002Canonical.left.operator
    (gaussian (Current535Child002Canonical.right.operator v))

theorem recipe02_exact (v : Payload) : recipe02 v = frameTwo v :=
  Current535Child002Canonical.selected_child_operator v

/-- Only the selected directed key is filled. The fallback is arbitrary and
is never used by relabels in these four source-bound blocks. -/
def recipes (fallback : RecipeTable) (old new : Label) (v : Payload) : Payload :=
  if old = 0 ∧ new = 2 then recipe02 v else fallback old new v

/-- Event-restricted RecipesExact needs no unused frame or recipe certificate.
The caller still identifies its charts at0and2 with the exact selected maps. -/
theorem recipes_exact (T : FrameMap) (fallback : RecipeTable)
    (es : List (ScalarEvent 997))
    (hzero : T 0 = LinearEquiv.refl ℚ Payload) (htwo : T 2 = frameTwo)
    (hkeys : RelabelsUse 0 2 es) : LemmaG.Stream.RecipesExact T (recipes fallback) es := by
  intro r old new hm v
  obtain ⟨rfl, rfl⟩ := hkeys r old new hm
  rw [hzero, htwo]
  simpa only [recipes, if_pos (show (0 : Label) = 0 ∧ (2 : Label) = 2 from ⟨rfl, rfl⟩),
    LinearEquiv.refl_symm, LinearEquiv.refl_apply] using recipe02_exact v

/-- The exact selected decoder, WellLabelled, local recipe certificate, scalar
run and interpreted all-payload conjugation remain visible together.
This does not identify physRun with a packed or expanded physical executor. -/
def InterpretedBlock (T : FrameMap) (fallback : RecipeTable)
    (rows : List (Row 997)) (labels : Register → Label) : Prop :=
  ∃ es : List (ScalarEvent 997), decodeRows rows = some es ∧
    LemmaG.Stream.WellLabelled es labels ∧
    LemmaG.Stream.RecipesExact T (recipes fallback) es ∧
    (∀ h : Register → Payload,
      rawRowsRun rows h = some (LemmaG.Stream.scalRun es h)) ∧
    (∀ h : Register → Payload,
      LemmaG.Stream.physRun (recipes fallback) es h =
        LemmaG.Stream.D T (LemmaG.Stream.labRun es labels)
          (LemmaG.Stream.scalRun es (LemmaG.Stream.Dinv T labels h)))

theorem keyed_block (T : FrameMap) (fallback : RecipeTable)
    (rows : List (Row 997)) (labels : Register → Label)
    (hzero : T 0 = LinearEquiv.refl ℚ Payload) (htwo : T 2 = frameTwo)
    (hkeyed : KeyedDecoded 0 2 rows labels) : InterpretedBlock T fallback rows labels := by
  obtain ⟨es, hd, hw, hk⟩ := hkeyed
  have hr := recipes_exact T fallback es hzero htwo hk
  exact ⟨es, hd, hw, hr, fun h => decoded_rows_run rows es hd h,
    fun h => LemmaG.Stream.conj' T (recipes fallback) es labels h hr hw⟩

variable (T : FrameMap) (fallback : RecipeTable)
variable (hzero : T 0 = LinearEquiv.refl ℚ Payload) (htwo : T 2 = frameTwo)

theorem selected_forward_A :
    InterpretedBlock T fallback Current535CoverageData.forwardA Current535CoverageData.labels0 :=
  keyed_block T fallback _ _ hzero htwo Current535First45KeyRestriction.selected_forward_A

theorem selected_forward_B :
    InterpretedBlock T fallback Current535CoverageData.forwardB Current535CoverageData.labels24 :=
  keyed_block T fallback _ _ hzero htwo Current535First45KeyRestriction.selected_forward_B

theorem selected_backward_A :
    InterpretedBlock T fallback Current535CoverageData.backwardA Current535CoverageData.labels0 :=
  keyed_block T fallback _ _ hzero htwo Current535First45KeyRestriction.selected_backward_A

theorem selected_backward_B :
    InterpretedBlock T fallback Current535CoverageData.backwardB Current535CoverageData.labels24 :=
  keyed_block T fallback _ _ hzero htwo Current535First45KeyRestriction.selected_backward_B

end
end CurrentMain.Current535First45Recipes

#print axioms CurrentMain.Current535First45Recipes.frameTwo_apply
#print axioms CurrentMain.Current535First45Recipes.recipe02_exact
#print axioms CurrentMain.Current535First45Recipes.recipes_exact
#print axioms CurrentMain.Current535First45Recipes.keyed_block
#print axioms CurrentMain.Current535First45Recipes.selected_forward_A
#print axioms CurrentMain.Current535First45Recipes.selected_forward_B
#print axioms CurrentMain.Current535First45Recipes.selected_backward_A
#print axioms CurrentMain.Current535First45Recipes.selected_backward_B
