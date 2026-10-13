import Current799DeclaredEntrance
import Current799InitialLabels
import Current799ResidualFourMonomial
import Mathlib.Algebra.Algebra.Rat

/-!
Selected PR799 entrance values with the exact packed R(4,FULL) right monomial
and the accepted declared initial labels. The chosen entry action uses R inverse
on the eight selected residual registers and identity on the other eight.
All nonselected actions remain arbitrary. Equality of the actual executor to
this modeled fold is a hypothesis, including its inverse-action convention.
Both typed destination traces, actual prefix composition, the incoming chart
and the frame-zero interpretation also remain hypotheses. No label execution,
whole-state hstart, canonical residual endpoint or physical realization follows.
Reuses accepted proofs without finite decisions or new stream induction.
Prepared with OpenAI assistance. Apache-2.0. See SOURCE_BINDING.json.
-/
set_option Elab.async false
namespace CurrentMain.Current799PackedEntrance
open LemmaG LemmaG.Stream
open Current535PackedCoordinates (Packed payloadEquiv)
open Current799ScalarSupport Current799EntryConnection Current799EntryFold

abbrev Payload := Packed → ℂ

noncomputable section

/-- Exact packed residual equivalence. Restriction to rational scalars keeps
the same action and inverse, including offset309 and global phase3. -/
def residual : Payload ≃ₗ[ℚ] Payload :=
  ((payloadEquiv.trans Current799ResidualFourMonomial.right.operator).trans
    payloadEquiv.symm).restrictScalars ℚ

theorem residual_apply (v : Payload) :
    residual v = HyperplaneEnd.Clifford.cL 512
      Current799ResidualFourMonomial.circuit v := by
  calc
    residual v = payloadEquiv.symm
        (Current799ResidualFourMonomial.right.operator (payloadEquiv v)) := rfl
    _ = HyperplaneEnd.Clifford.cL 512 Current799ResidualFourMonomial.circuit v := by
      rw [← Current799ResidualFourMonomial.packed_reindex,
        LinearEquiv.symm_apply_apply]

/-- Cancellation of the interpreted forward packed residual. This does not
identify the actual inverse executor or any separately emitted inverse list. -/
theorem residual_inverse_apply (v : Payload) :
    residual.symm (HyperplaneEnd.Clifford.cL 512
      Current799ResidualFourMonomial.circuit v) = v := by
  rw [← residual_apply, LinearEquiv.symm_apply_apply]

/-- Only the selected sixteen operators are fixed. The other712 entry
operators, and the eight unscheduled centre operators, remain arbitrary. -/
def actions (fallback : Fin 736 → Payload → Payload)
    (i : Fin 736) (v : Payload) : Payload :=
  if i ∈ selectedSupport then entryValue residual.symm i v else fallback i v

theorem actions_selected (fallback : Fin 736 → Payload → Payload)
    (i : Fin 736) (hi : i ∈ selectedSupport) (v : Payload) :
    actions fallback i v = entryValue residual.symm i v := by
  simp only [actions, if_pos hi]

/-- The first declared entrance on the selected support. The sixteen operator
equations and initial-label equations are discharged for the defined model.
The actual executor equality still supplies the connection to that model. -/
theorem selected_declared_entrance
    (rec : Fin 1005 → Fin 1005 → Payload → Payload)
    (pre earlyA : List (Event (Fin 736) (Fin 1005) ℚ))
    (hpre : HasDestinationTrace pre preconditionTargets preconditionRuns)
    (hearly : HasDestinationTrace earlyA earlyATargets earlyARuns)
    (actualEntry actualPrefix : (Fin 736 → Payload) → (Fin 736 → Payload))
    (fallback : Fin 736 → Payload → Payload)
    (T : Fin 1005 → Payload → Payload)
    (hexecEntry : actualEntry =
      IndependentEntryFold.runUpdates (actions fallback) entryRegisters)
    (hexecPrefix : actualPrefix =
      fun h => physRun rec earlyA (actualEntry (physRun rec pre h)))
    (hzero : ∀ v, T 0 v = v)
    (h x : Fin 736 → Payload)
    (hinput : ∀ i ∈ selectedSupport, h i = incomingChart residual (T 4) x i)
    (i : Fin 736) (hi : i ∈ selectedSupport) :
    actualPrefix h i = T (Current799First33CoverageData.labels0 i) (x i) := by
  exact Current799DeclaredEntrance.selected_declared_entrance
    rec pre earlyA hpre hearly actualEntry actualPrefix (actions fallback) residual
    T Current799First33CoverageData.labels0 hexecEntry hexecPrefix
    (actions_selected fallback) hzero Current799InitialLabels.selected_initial_labels
    h x hinput i hi

end
end CurrentMain.Current799PackedEntrance

#print axioms CurrentMain.Current799PackedEntrance.residual_apply
#print axioms CurrentMain.Current799PackedEntrance.residual_inverse_apply
#print axioms CurrentMain.Current799PackedEntrance.actions_selected
#print axioms CurrentMain.Current799PackedEntrance.selected_declared_entrance
#check @CurrentMain.Current799PackedEntrance.actions_selected
#check @CurrentMain.Current799PackedEntrance.selected_declared_entrance
