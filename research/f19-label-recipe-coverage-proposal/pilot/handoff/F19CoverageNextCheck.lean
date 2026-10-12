/- Checks only raw rows 10979 through 11042 in each canonical-frame projection,
starting at the accepted full pilot checkpoint. The append results reuse the
accepted 128-row pilot. Omitted adapters and all operator claims remain outside. -/
import F19CoveragePilotBoundary

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace CurrentMain.F19SelectedCoverage.NextCheck
open CurrentMain.F19SelectedCoverage

theorem exact_next_source_indices :
    NextData.forward.map Row.sourceIndex = List.range' 10979 64 ∧
    NextData.backward.map Row.sourceIndex = List.range' 10979 64 := by
  decide +kernel

theorem forward_checked :
    checkRows PilotData.data NextData.forward NextData.checkpointLabels = true := by
  decide +kernel

theorem backward_checked :
    checkRows PilotData.data NextData.backward NextData.checkpointLabels = true := by
  decide +kernel

theorem forward_wellLabelled :
    LemmaG.Stream.WellLabelled (NextData.forward.map Row.event)
      NextData.checkpointLabels :=
  checkRows_wellLabelled PilotData.data NextData.forward
    NextData.checkpointLabels forward_checked

theorem backward_wellLabelled :
    LemmaG.Stream.WellLabelled (NextData.backward.map Row.event)
      NextData.checkpointLabels :=
  checkRows_wellLabelled PilotData.data NextData.backward
    NextData.checkpointLabels backward_checked

theorem forward_composed_wellLabelled :
    LemmaG.Stream.WellLabelled ((PilotData.forward ++ NextData.forward).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨PilotCheck.selected_pilot_wellLabelled.1, ?_⟩
  rw [PilotBoundary.forward_checkpoint]
  exact forward_wellLabelled

theorem backward_composed_wellLabelled :
    LemmaG.Stream.WellLabelled ((PilotData.backward ++ NextData.backward).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨PilotCheck.selected_pilot_wellLabelled.2, ?_⟩
  rw [PilotBoundary.backward_checkpoint]
  exact backward_wellLabelled

#print axioms exact_next_source_indices
#print axioms forward_checked
#print axioms backward_checked
#print axioms forward_wellLabelled
#print axioms backward_wellLabelled
#print axioms forward_composed_wellLabelled
#print axioms backward_composed_wellLabelled
end CurrentMain.F19SelectedCoverage.NextCheck
