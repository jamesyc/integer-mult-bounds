/- Bounded selected f19 canonical-frame coverage experiment. No operator or full-stream claim. -/
import F19CoverageChunkA
import F19CoverageCheckDecomposition

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.ChunkBDirect
open CurrentMain.F19SelectedCoverage

theorem exact_source_indices :
    BatchData.forwardB.map Row.sourceIndex = List.range' 11107 64 ∧
    BatchData.backwardB.map Row.sourceIndex = List.range' 11107 64 := by
  decide +kernel

theorem forward_checked :
    checkRows PilotData.data BatchData.forwardB BatchData.labels256 = true := by
  decide +kernel

theorem forward_wellLabelled :
    LemmaG.Stream.WellLabelled (BatchData.forwardB.map Row.event) BatchData.labels256 :=
  checkRows_wellLabelled PilotData.data BatchData.forwardB BatchData.labels256 forward_checked

theorem forward_composed_wellLabelled :
    LemmaG.Stream.WellLabelled
      ((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨ChunkA.forward_composed_wellLabelled, ?_⟩
  rw [ChunkA.forward_composed_checkpoint256]
  exact forward_wellLabelled

theorem backward_checked :
    checkRows PilotData.data BatchData.backwardB BatchData.labels256 = true := by
  decide +kernel

theorem backward_wellLabelled :
    LemmaG.Stream.WellLabelled (BatchData.backwardB.map Row.event) BatchData.labels256 :=
  checkRows_wellLabelled PilotData.data BatchData.backwardB BatchData.labels256 backward_checked

theorem backward_composed_wellLabelled :
    LemmaG.Stream.WellLabelled
      ((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨ChunkA.backward_composed_wellLabelled, ?_⟩
  rw [ChunkA.backward_composed_checkpoint256]
  exact backward_wellLabelled


#print axioms exact_source_indices
#print axioms forward_checked
#print axioms forward_wellLabelled
#print axioms forward_composed_wellLabelled
#print axioms backward_checked
#print axioms backward_wellLabelled
#print axioms backward_composed_wellLabelled
end CurrentMain.F19SelectedCoverage.ChunkBDirect
