import Current799EntryFold

/-!
Source-only composition proposal for the selected sixteen registers at the
first declared Fin1005 entrance. Reuses the accepted 728-entry nodup fold and
two source-bound support segments. The actual executor equalities, destination
traces, selected operator equations, incoming chart and declared-label values
remain explicit premises. No whole-state label or physical-executor claim.
-/
set_option Elab.async false
namespace CurrentMain.Current799DeclaredEntrance
open LemmaG LemmaG.Stream
open Current799ScalarSupport Current799EntryConnection Current799EntryFold

section
variable {K M : Type*} [Semiring K] [AddCommMonoid M] [Module K M]

/-- Thin composition of the accepted entry fold and both support segments. -/
theorem folded_prefix_chart
    (rec : Fin 1005 → Fin 1005 → M → M)
    (pre earlyA : List (Event (Fin 736) (Fin 1005) K))
    (hpre : HasDestinationTrace pre preconditionTargets preconditionRuns)
    (hearly : HasDestinationTrace earlyA earlyATargets earlyARuns)
    (actualEntry : (Fin 736 → M) → (Fin 736 → M))
    (act : Fin 736 → M → M) (R : M ≃ₗ[K] M) (T4 : M → M)
    (hexecEntry : actualEntry = IndependentEntryFold.runUpdates act entryRegisters)
    (hselected : ∀ i ∈ selectedSupport, ∀ v, act i v = entryValue R.symm i v)
    (h x : Fin 736 → M)
    (hinput : ∀ i ∈ selectedSupport, h i = incomingChart R T4 x i)
    (i : Fin 736) (hi : i ∈ selectedSupport) :
    physRun rec earlyA (actualEntry (physRun rec pre h)) i = enteredChart T4 x i := by
  exact supported_first_climb_chart rec pre earlyA hpre hearly actualEntry R T4
    (selected_executor_action actualEntry act R.symm hexecEntry hselected)
    h x hinput i hi

/-- Values agree with the declared frame interpretation on the selected support.
This does not assert that actual prefix label execution reaches labels, nor a
whole-state hstart premise. Operators outside this support remain arbitrary. -/
theorem selected_declared_entrance
    (rec : Fin 1005 → Fin 1005 → M → M)
    (pre earlyA : List (Event (Fin 736) (Fin 1005) K))
    (hpre : HasDestinationTrace pre preconditionTargets preconditionRuns)
    (hearly : HasDestinationTrace earlyA earlyATargets earlyARuns)
    (actualEntry actualPrefix : (Fin 736 → M) → (Fin 736 → M))
    (act : Fin 736 → M → M) (R : M ≃ₗ[K] M)
    (T : Fin 1005 → M → M) (labels : Fin 736 → Fin 1005)
    (hexecEntry : actualEntry = IndependentEntryFold.runUpdates act entryRegisters)
    (hexecPrefix : actualPrefix =
      fun h => physRun rec earlyA (actualEntry (physRun rec pre h)))
    (hselected : ∀ i ∈ selectedSupport, ∀ v, act i v = entryValue R.symm i v)
    (hzero : ∀ v, T 0 v = v)
    (hlabels : ∀ i ∈ selectedSupport,
      labels i = if i.val ∈ residualRegisters then 4 else 0)
    (h x : Fin 736 → M)
    (hinput : ∀ i ∈ selectedSupport, h i = incomingChart R (T 4) x i)
    (i : Fin 736) (hi : i ∈ selectedSupport) :
    actualPrefix h i = T (labels i) (x i) := by
  rw [hexecPrefix,
    folded_prefix_chart rec pre earlyA hpre hearly actualEntry act R (T 4)
      hexecEntry hselected h x hinput i hi,
    hlabels i hi]
  by_cases hr : i.val ∈ residualRegisters
  · simp only [enteredChart, if_pos hr]
  · simpa only [enteredChart, if_neg hr] using (hzero (x i)).symm
end
end CurrentMain.Current799DeclaredEntrance

#print axioms CurrentMain.Current799DeclaredEntrance.folded_prefix_chart
#print axioms CurrentMain.Current799DeclaredEntrance.selected_declared_entrance
#check @CurrentMain.Current799DeclaredEntrance.folded_prefix_chart
#check @CurrentMain.Current799DeclaredEntrance.selected_declared_entrance
