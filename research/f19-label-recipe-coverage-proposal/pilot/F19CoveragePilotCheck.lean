/- The only finite claim is the two literal 128-row canonical-frame slices.
Boundary adapters are excluded. No scalar, Clifford, or physical endpoint is claimed. -/
import F19CoveragePilotData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace CurrentMain.F19SelectedCoverage.PilotCheck
open CurrentMain.F19SelectedCoverage

theorem exact_source_indices :
    PilotData.data.forward.map Row.sourceIndex = List.range' 10851 128 ∧
    PilotData.data.backward.map Row.sourceIndex = List.range' 10851 128 := by
  decide

theorem selected_pilot_checked : checkPilot PilotData.data = true := by
  have hs : pilotShapeB PilotData.data = true := by decide +kernel
  have hf : checkRows PilotData.data PilotData.data.forward
      (initialLabels PilotData.data) = true := by decide +kernel
  have hb : checkRows PilotData.data PilotData.data.backward
      (initialLabels PilotData.data) = true := by decide +kernel
  exact Bool.and_eq_true_iff.mpr ⟨hs, Bool.and_eq_true_iff.mpr ⟨hf, hb⟩⟩

theorem selected_pilot_wellLabelled : ProjectedWellLabelled PilotData.data :=
  checkPilot_wellLabelled PilotData.data selected_pilot_checked

#print axioms exact_source_indices
#print axioms selected_pilot_checked
#print axioms selected_pilot_wellLabelled
end CurrentMain.F19SelectedCoverage.PilotCheck
