import CliffordChild002Canonical

/-!
Two exact current535 label bindings, retaining both accepted payload models.
The serialized fields are literal current catalog records; only frame IDs move.
The all-payload proofs are reused unchanged. Apache-2.0; see NOTICE.md.
No raw event executor, packed-address equivalence or physical-work supplier is
identified by this small binding module.
-/
namespace CurrentMain.Current535RecipeLabelBindings

structure MonomialFields where
  rows : List Nat
  quadratic : List Nat
  linearZ4 : List Nat
  offset : Nat
  phase : Nat

structure RecipeFields where
  oldFrame : Nat
  newFrame : Nat
  rank : Nat
  left : MonomialFields
  right : Option MonomialFields

def current11 : RecipeFields where
  oldFrame := 0
  newFrame := 6
  rank := 1
  left := { rows := [3, 5, 8, 1, 16, 32, 64, 128, 256],
            quadratic := [0, 0, 0, 0, 0, 0, 0, 0, 0],
            linearZ4 := [2, 0, 0, 0, 0, 0, 0, 0, 0],
            offset := 0, phase := 0 }
  right := some { rows := [11, 9, 10, 4, 16, 32, 64, 128, 256],
                  quadratic := [3, 3, 0, 0, 0, 0, 0, 0, 0],
                  linearZ4 := [3, 3, 0, 2, 0, 0, 0, 0, 0],
                  offset := 1, phase := 1 }

def current45 : RecipeFields where
  oldFrame := 0
  newFrame := 420
  rank := 1
  left := { rows := [3, 4, 9, 17, 32, 1, 64, 128, 256],
            quadratic := [1, 0, 0, 0, 0, 0, 0, 0, 0],
            linearZ4 := [3, 0, 0, 0, 0, 0, 0, 0, 0],
            offset := 0, phase := 0 }
  right := some { rows := [13, 33, 2, 36, 40, 16, 64, 128, 256],
                  quadratic := [45, 0, 45, 45, 0, 13, 0, 0, 0],
                  linearZ4 := [1, 0, 1, 1, 0, 2, 0, 0, 0],
                  offset := 0, phase := 0 }

def current11OldDescriptor : List Nat := []
def current11NewDescriptor : List Nat := [11]
def current45OldDescriptor : List Nat := []
def current45NewDescriptor : List Nat := [45]

/-- Historical fields refer to the actual accepted decoder constants. The
literal offsets/global phases are those in its leftDecoded/rightDecoded. -/
def historical11 : RecipeFields where
  oldFrame := 0
  newFrame := 9
  rank := 1
  left := { rows := CliffordChild009Decoder.leftRows,
            quadratic := CliffordChild009Decoder.leftQ,
            linearZ4 := CliffordChild009Decoder.leftAlpha,
            offset := 0, phase := 0 }
  right := some { rows := CliffordChild009Decoder.rightRows,
                  quadratic := CliffordChild009Decoder.rightQ,
                  linearZ4 := CliffordChild009Decoder.rightAlpha,
                  offset := 1, phase := 1 }

def historical45 : RecipeFields where
  oldFrame := CliffordChild002Canonical.oldFrame
  newFrame := CliffordChild002Canonical.newFrame
  rank := CliffordChild002Canonical.rank
  left := { rows := CliffordChild002Canonical.leftRows,
            quadratic := CliffordChild002Canonical.leftQ,
            linearZ4 := CliffordChild002Canonical.leftAlpha,
            offset := CliffordChild002Canonical.leftOffset,
            phase := CliffordChild002Canonical.leftPhase }
  right := some { rows := CliffordChild002Canonical.rightRows,
                  quadratic := CliffordChild002Canonical.rightQ,
                  linearZ4 := CliffordChild002Canonical.rightAlpha,
                  offset := CliffordChild002Canonical.rightOffset,
                  phase := CliffordChild002Canonical.rightPhase }

theorem current11_key :
    (current11.oldFrame, current11.newFrame, current11.rank) = (0, 6, 1) := rfl

theorem current45_key :
    (current45.oldFrame, current45.newFrame, current45.rank) = (0, 420, 1) := rfl

/-- Every serialized field, including phase, offset, right presence and rank,
is retained. The only change from the historical record is newFrame 9→6. -/
theorem current11_fields : current11 = { historical11 with newFrame := 6 } := rfl

/-- Full serialized equality with the explicit historical 2→420 ID change. -/
theorem current45_fields : current45 = { historical45 with newFrame := 420 } := rfl

/-- Ordered singleton descriptor agrees with the already certified greedy basis. -/
theorem current11_descriptors :
    current11OldDescriptor = [] ∧
    current11NewDescriptor = CliffordChild009Canonical.canonicalBasis.take 1 := by
  exact ⟨rfl, rfl⟩

theorem current45_descriptors :
    current45OldDescriptor = CliffordChild002Canonical.oldDescriptor ∧
    current45NewDescriptor = CliffordChild002Canonical.newDescriptor := by
  exact ⟨rfl, rfl⟩

noncomputable section

/-- The current [11] record reuses the accepted Low×S interpretation; its
arbitrary spectator type is not silently identified with a packed address. -/
abbrev current11Child {S : Type*} :
    DirectedChildRecipes.Child ℂ (CliffordChild009Decoder.Low × S → ℂ) :=
  CliffordChild009Canonical.selectedChild

theorem current11_interpreted_rank {S : Type*} :
    (current11Child (S := S)).rank = current11.rank := rfl

theorem current11_operator {S : Type*}
    (v : CliffordChild009Decoder.Low × S → ℂ) :
    DirectedChildRecipes.Child.eval (fun _ => CliffordChild009Canonical.gaussian)
      current11Child v =
        CliffordChild009Canonical.canonicalNew
          (CliffordChild009Canonical.canonicalOld.symm v) :=
  CliffordChild009Canonical.selected_child_operator v

/-- The current [45] record keeps the accepted nine-coordinate Address model. -/
abbrev current45Left := CliffordChild002Canonical.left
abbrev current45Right := CliffordChild002Canonical.right

theorem current45_operator (v : CliffordNineBitDecoder.Address → ℂ) :
    current45Left.operator (CliffordNineBitDecoder.gaussian (current45Right.operator v)) =
      RankOneRecipeCertificate.canonicalK
        CliffordChild002Canonical.canonicalLinear.toEquiv
        CliffordChild002Canonical.canonicalPhase
        (CliffordNineBitDecoder.gaussian
          ((RankOneRecipeCertificate.canonicalK
            CliffordChild002Canonical.canonicalLinear.toEquiv
            CliffordChild002Canonical.canonicalPhase).symm v)) :=
  CliffordChild002Canonical.selected_child_operator v

theorem current45_with_spectators {S : Type*}
    (v : S → CliffordNineBitDecoder.Address → ℂ) (s : S) :
    current45Left.operator
        (CliffordNineBitDecoder.gaussian (current45Right.operator (v s))) =
      RankOneRecipeCertificate.canonicalK
        CliffordChild002Canonical.canonicalLinear.toEquiv
        CliffordChild002Canonical.canonicalPhase
        (CliffordNineBitDecoder.gaussian
          ((RankOneRecipeCertificate.canonicalK
            CliffordChild002Canonical.canonicalLinear.toEquiv
            CliffordChild002Canonical.canonicalPhase).symm (v s))) :=
  current45_operator (v s)

end
end CurrentMain.Current535RecipeLabelBindings

#print axioms CurrentMain.Current535RecipeLabelBindings.current11_key
#print axioms CurrentMain.Current535RecipeLabelBindings.current45_key
#print axioms CurrentMain.Current535RecipeLabelBindings.current11_fields
#print axioms CurrentMain.Current535RecipeLabelBindings.current45_fields
#print axioms CurrentMain.Current535RecipeLabelBindings.current11_descriptors
#print axioms CurrentMain.Current535RecipeLabelBindings.current45_descriptors
#print axioms CurrentMain.Current535RecipeLabelBindings.current11_interpreted_rank
#print axioms CurrentMain.Current535RecipeLabelBindings.current11_operator
#print axioms CurrentMain.Current535RecipeLabelBindings.current45_operator
#print axioms CurrentMain.Current535RecipeLabelBindings.current45_with_spectators
