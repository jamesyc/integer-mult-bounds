import Current799ScalarSupport

/-!
Selected PR799 entrance connection for the first climb-bearing 33-row block.
The two source-bound scalar destination traces remain explicit premises.
The full emitted entry executor is supplied with an explicit pointwise action
on the selected sixteen registers; no executor implementation is inferred.

Eight selected registers use the residual pre wrapper for entrance frame4,
terminal frame1 (FULL), whose source record uses the legacy key "4". Its
interpreted right monomial R and inverse action remain supplied. The other
eight selected registers have the frame0 plain entrance action. The chart
corollary requires incoming values R(T4(x)) at residual registers; this is the
value side of PR593's prew chart. It does not establish prew labels or hstart,
residual matrix/phase decoding, the Python executor, or physical work maps.

Attribution: accepted PR509/PR516 stream semantics and source-bound support
lemmas; source wrapper order from PR799's retained HPE emitter and PR593's
pre_recipe interface. No extra upstream module or finite certificate imported.
Prepared with OpenAI assistance. Apache-2.0.
-/
set_option Elab.async false
namespace CurrentMain.Current799EntryConnection
open LemmaG LemmaG.Stream Current799ScalarSupport

/-- Exact selected residual pre-wrapper registers, in emitted source order. -/
def residualRegisters : List Nat := [571, 573, 583, 585, 594, 595, 596, 597]

/-- Only the selected entry action is specified; other registers are unrestricted. -/
def entryValue {M : Type*} (Rinv : M → M) (i : Fin 736) (v : M) : M :=
  if i.val ∈ residualRegisters then Rinv v else v

/-- Required interface of the actual full entry executor on this support. -/
def HasSelectedEntryAction {M : Type*}
    (entry : (Fin 736 → M) → (Fin 736 → M)) (Rinv : M → M) : Prop :=
  ∀ h i, i ∈ selectedSupport → entry h i = entryValue Rinv i (h i)

/-- Incoming residual prew chart R ∘ T4; plain frame0 chart is identity. -/
def incomingChart {M : Type*} (R T4 : M → M) (x : Fin 736 → M) (i : Fin 736) : M :=
  if i.val ∈ residualRegisters then R (T4 (x i)) else x i

/-- Desired values at the declared entrance frame4 or frame0. -/
def enteredChart {M : Type*} (T4 : M → M) (x : Fin 736 → M) (i : Fin 736) : M :=
  if i.val ∈ residualRegisters then T4 (x i) else x i

section Connection
variable {Λ K M : Type*} [Semiring K] [AddCommMonoid M] [Module K M]

theorem entryValue_inverse_chart (R : M ≃ₗ[K] M) (T4 : M → M)
    (x : Fin 736 → M) (i : Fin 736) :
    entryValue R.symm i (incomingChart R T4 x i) = enteredChart T4 x i := by
  by_cases hi : i.val ∈ residualRegisters
  · simp only [entryValue, incomingChart, enteredChart, if_pos hi,
      LinearEquiv.symm_apply_apply]
  · simp only [entryValue, incomingChart, enteredChart, if_neg hi]

/-- Composition through both arbitrary interpreted scalar segments and the
supplied entry executor. Neither typed destination trace is discharged here. -/
theorem supported_first_climb_entry_value
    (rec : Λ → Λ → M → M) (pre earlyA : List (Event (Fin 736) Λ K))
    (hpre : HasDestinationTrace pre preconditionTargets preconditionRuns)
    (hearly : HasDestinationTrace earlyA earlyATargets earlyARuns)
    (entry : (Fin 736 → M) → (Fin 736 → M)) (Rinv : M → M)
    (hentry : HasSelectedEntryAction entry Rinv)
    (h : Fin 736 → M) (i : Fin 736) (hi : i ∈ selectedSupport) :
    physRun rec earlyA (entry (physRun rec pre h)) i = entryValue Rinv i (h i) := by
  rw [interpreted_run_preserves_support rec earlyATargets earlyARuns
    earlyA hearly (entry (physRun rec pre h)) i hi]
  rw [hentry (physRun rec pre h) i hi]
  rw [interpreted_run_preserves_support rec preconditionTargets preconditionRuns
    pre hpre h i hi]

/-- If the incoming values have the residual prew chart, the first-climb values
have T4 at the eight residual entries and identity at the eight plain entries.
Actual labels and PR593's hstart remain separate from this value equation. -/
theorem supported_first_climb_chart
    (rec : Λ → Λ → M → M) (pre earlyA : List (Event (Fin 736) Λ K))
    (hpre : HasDestinationTrace pre preconditionTargets preconditionRuns)
    (hearly : HasDestinationTrace earlyA earlyATargets earlyARuns)
    (entry : (Fin 736 → M) → (Fin 736 → M))
    (R : M ≃ₗ[K] M) (T4 : M → M)
    (hentry : HasSelectedEntryAction entry R.symm)
    (h x : Fin 736 → M)
    (hinput : ∀ i ∈ selectedSupport, h i = incomingChart R T4 x i)
    (i : Fin 736) (hi : i ∈ selectedSupport) :
    physRun rec earlyA (entry (physRun rec pre h)) i = enteredChart T4 x i := by
  rw [supported_first_climb_entry_value rec pre earlyA hpre hearly entry
    R.symm hentry h i hi, hinput i hi]
  exact entryValue_inverse_chart R T4 x i
end Connection
end CurrentMain.Current799EntryConnection

#print axioms CurrentMain.Current799EntryConnection.entryValue_inverse_chart
#print axioms CurrentMain.Current799EntryConnection.supported_first_climb_entry_value
#print axioms CurrentMain.Current799EntryConnection.supported_first_climb_chart
#check @CurrentMain.Current799EntryConnection.supported_first_climb_entry_value
#check @CurrentMain.Current799EntryConnection.supported_first_climb_chart
