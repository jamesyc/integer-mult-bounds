import Current5996CKPackedRecipe

/-!
Exact current PR799 ordinal2 binding, also byte-identical in PR741:
0 -> 4, rank1, ordered [] -> [459]. The prior CK-HPE record uses new label2.
Every serialized operator field agrees; labels are not silently identified.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md and SOURCE_BINDING.json.
-/
set_option Elab.async false
namespace CurrentMain.Current799FirstPackedRecipe
open Current535PackedCoordinates
open RankOneRecipeCertificate
open HyperplaneEnd.Clifford (cL)

def oldFrame : Nat := 0
def newFrame : Nat := 4
def rank : Nat := 1
def oldDescriptor : List Nat := []
def newDescriptor : List Nat := [459]

theorem key_and_descriptors :
    oldFrame = 0 ∧ newFrame = 4 ∧ rank = 1 ∧
    oldDescriptor = [] ∧ newDescriptor = [459] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem left_fields :
    Current9594CKFirstRecipe.leftRows = [3, 5, 8, 17, 32, 64, 129, 257, 1] ∧
    Current9594CKFirstRecipe.leftQ = [1, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    Current9594CKFirstRecipe.leftAlpha = [3, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    Current9594CKFirstRecipe.leftOffset = 0 ∧
    Current9594CKFirstRecipe.leftPhase = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem right_fields : Current9594CKFirstRecipe.rightPresent = true ∧
    Current9594CKFirstRecipe.rightRows = [203, 257, 258, 4, 264, 16, 32, 320, 384] ∧
    Current9594CKFirstRecipe.rightQ = [459, 459, 0, 459, 0, 0, 459, 459, 203] ∧
    Current9594CKFirstRecipe.rightAlpha = [1, 1, 0, 1, 0, 0, 1, 1, 2] ∧
    Current9594CKFirstRecipe.rightOffset = 0 ∧
    Current9594CKFirstRecipe.rightPhase = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


abbrev recipe := Current5996CKPackedRecipe.recipe
abbrev canonicalLinear := Current5996CKFirstRecipe.canonicalLinear
abbrev canonicalPhase := Current5996CKFirstRecipe.canonicalPhase

noncomputable section
/-- Full phase-sensitive all-payload equality for the exact matched source
record. The Fin1005 event and physical execution suppliers remain separate. -/
theorem packed_canonical_child (v : Packed → ℂ) :
    cL 512 recipe v = payloadEquiv.symm
      (canonicalK canonicalLinear.toEquiv canonicalPhase
        (CliffordNineBitDecoder.gaussian ((canonicalK canonicalLinear.toEquiv canonicalPhase).symm
          (payloadEquiv v)))) :=
  Current5996CKPackedRecipe.packed_canonical_child v
end
end CurrentMain.Current799FirstPackedRecipe

#print axioms CurrentMain.Current799FirstPackedRecipe.key_and_descriptors
#print axioms CurrentMain.Current799FirstPackedRecipe.left_fields
#print axioms CurrentMain.Current799FirstPackedRecipe.right_fields
#print axioms CurrentMain.Current799FirstPackedRecipe.packed_canonical_child
