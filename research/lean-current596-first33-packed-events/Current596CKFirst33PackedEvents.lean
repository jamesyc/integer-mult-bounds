import Current596CKFirst33Transport
import Current5996CKPackedRecipe
import Mathlib.Algebra.Algebra.Rat

/-!
Current selected main5996 CK first33 interpreted packed-event composition.
The four current24/9 source-bound typed blocks retain their signed rational
decoding and label checks. The only relabel key0→2 executes the exact packed
right / Gaussian / left recipe. Both endpoint chart equations remain explicit.
This applies the accepted PR509 conjugation theorem without a stream induction
or finite predicate. It does not equate Python/vectorized emitted execution,
the omitted pre-A source state, adapters or expanded physical work with physRun.
Conditional source context: kappa=16127213726553/10000000000000000.
Apache-2.0; PR509, PR593, PR596 and accepted source attribution retained.
Prepared with OpenAI assistance.
-/
set_option Elab.async false

namespace CurrentMain.Current596CKFirst33PackedEvents
open CliffordNineBitDecoder (Address gaussian)
open CanonicalFrameCoverage (Register Row)
open CurrentScalarCentreBand (ScalarEvent decodeRows rawRowsRun decoded_rows_run)
open Current9594CKFirst33KeyRestriction (RelabelsUse KeyedDecoded)
open Current535PackedCoordinates (Packed payloadEquiv)

abbrev Payload := Packed → ℂ
abbrev Label := Fin 1082
abbrev FrameMap := Label → Payload ≃ₗ[ℚ] Payload
abbrev RecipeTable := Label → Label → Payload → Payload

noncomputable section

/-- Exact selected canonical chart reindexed to packed payloads. The canonical
rational restriction changes neither the function nor its inverse. -/
def frameTwo : Payload ≃ₗ[ℚ] Payload :=
  let K := RankOneRecipeCertificate.canonicalK
    Current5996CKFirstRecipe.canonicalLinear.toEquiv
    Current5996CKFirstRecipe.canonicalPhase
  ((payloadEquiv.trans ((K.symm.trans gaussian).trans K)).trans
    payloadEquiv.symm).restrictScalars ℚ

theorem frameTwo_apply (v : Payload) :
    frameTwo v = payloadEquiv.symm
      (RankOneRecipeCertificate.canonicalK
        Current5996CKFirstRecipe.canonicalLinear.toEquiv
        Current5996CKFirstRecipe.canonicalPhase
        (gaussian ((RankOneRecipeCertificate.canonicalK
          Current5996CKFirstRecipe.canonicalLinear.toEquiv
          Current5996CKFirstRecipe.canonicalPhase).symm (payloadEquiv v)))) := rfl

/-- Exact packed source recipe: right monomial, Gaussian C0, then left. -/
def recipe02 (v : Payload) : Payload :=
  HyperplaneEnd.Clifford.cL 512 Current5996CKPackedRecipe.recipe v

theorem recipe02_exact (v : Payload) : recipe02 v = frameTwo v :=
  Current5996CKPackedRecipe.packed_canonical_child v

/-- Only the selected directed key is filled. The fallback is arbitrary and
is never used by relabels in these four source-bound current24/9 blocks. -/
def recipes (fallback : RecipeTable) (old new : Label) (v : Payload) : Payload :=
  if old = 0 ∧ new = 2 then recipe02 v else fallback old new v

/-- Event-restricted RecipesExact needs no unused frame or recipe certificate.
The caller still identifies its charts at0and2 with the exact selected maps. -/
theorem recipes_exact (T : FrameMap) (fallback : RecipeTable)
    (es : List (ScalarEvent 1082))
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
    (rows : List (Row 1082)) (labels : Register → Label) : Prop :=
  ∃ es : List (ScalarEvent 1082), decodeRows rows = some es ∧
    LemmaG.Stream.WellLabelled es labels ∧
    LemmaG.Stream.RecipesExact T (recipes fallback) es ∧
    (∀ h : Register → Payload,
      rawRowsRun rows h = some (LemmaG.Stream.scalRun es h)) ∧
    (∀ h : Register → Payload,
      LemmaG.Stream.physRun (recipes fallback) es h =
        LemmaG.Stream.D T (LemmaG.Stream.labRun es labels)
          (LemmaG.Stream.scalRun es (LemmaG.Stream.Dinv T labels h)))

theorem keyed_block (T : FrameMap) (fallback : RecipeTable)
    (rows : List (Row 1082)) (labels : Register → Label)
    (hzero : T 0 = LinearEquiv.refl ℚ Payload) (htwo : T 2 = frameTwo)
    (hkeyed : KeyedDecoded 0 2 rows labels) : InterpretedBlock T fallback rows labels := by
  obtain ⟨es, hd, hw, hk⟩ := hkeyed
  have hr := recipes_exact T fallback es hzero htwo hk
  exact ⟨es, hd, hw, hr, fun h => decoded_rows_run rows es hd h,
    fun h => LemmaG.Stream.conj' T (recipes fallback) es labels h hr hw⟩

variable (T : FrameMap) (fallback : RecipeTable)
variable (hzero : T 0 = LinearEquiv.refl ℚ Payload) (htwo : T 2 = frameTwo)

include hzero htwo

theorem selected_forward_A :
    InterpretedBlock T fallback Current596CKFirst33Transport.forwardA Current596CKFirst33Transport.labels0 :=
  keyed_block T fallback _ _ hzero htwo Current596CKFirst33Transport.selected_forward_A

theorem selected_forward_B :
    InterpretedBlock T fallback Current596CKFirst33Transport.forwardB Current596CKFirst33Transport.labels24 :=
  keyed_block T fallback _ _ hzero htwo Current596CKFirst33Transport.selected_forward_B

theorem selected_backward_A :
    InterpretedBlock T fallback Current596CKFirst33Transport.backwardA Current596CKFirst33Transport.labels0 :=
  keyed_block T fallback _ _ hzero htwo Current596CKFirst33Transport.selected_backward_A

theorem selected_backward_B :
    InterpretedBlock T fallback Current596CKFirst33Transport.backwardB Current596CKFirst33Transport.labels24 :=
  keyed_block T fallback _ _ hzero htwo Current596CKFirst33Transport.selected_backward_B

end
end CurrentMain.Current596CKFirst33PackedEvents

#print axioms CurrentMain.Current596CKFirst33PackedEvents.frameTwo_apply
#print axioms CurrentMain.Current596CKFirst33PackedEvents.recipe02_exact
#print axioms CurrentMain.Current596CKFirst33PackedEvents.recipes_exact
#print axioms CurrentMain.Current596CKFirst33PackedEvents.keyed_block
#print axioms CurrentMain.Current596CKFirst33PackedEvents.selected_forward_A
#print axioms CurrentMain.Current596CKFirst33PackedEvents.selected_forward_B
#print axioms CurrentMain.Current596CKFirst33PackedEvents.selected_backward_A
#print axioms CurrentMain.Current596CKFirst33PackedEvents.selected_backward_B

/- The public types must retain both endpoint chart assumptions. -/
#check @CurrentMain.Current596CKFirst33PackedEvents.selected_forward_A
#check @CurrentMain.Current596CKFirst33PackedEvents.selected_forward_B
#check @CurrentMain.Current596CKFirst33PackedEvents.selected_backward_A
#check @CurrentMain.Current596CKFirst33PackedEvents.selected_backward_B
