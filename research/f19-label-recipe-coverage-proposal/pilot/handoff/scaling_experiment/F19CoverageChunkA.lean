/- Bounded selected f19 canonical-frame coverage experiment. No operator or full-stream claim. -/
import F19CoverageBoundary192

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.ChunkA
open CurrentMain.F19SelectedCoverage

theorem exact_source_indices :
    BatchData.forwardA.map Row.sourceIndex = List.range' 11043 64 ∧
    BatchData.backwardA.map Row.sourceIndex = List.range' 11043 64 := by
  decide +kernel

theorem forward_checked :
    checkRows PilotData.data BatchData.forwardA BatchData.labels192 = true := by
  decide +kernel

theorem forward_wellLabelled :
    LemmaG.Stream.WellLabelled (BatchData.forwardA.map Row.event) BatchData.labels192 :=
  checkRows_wellLabelled PilotData.data BatchData.forwardA BatchData.labels192 forward_checked

theorem forward_support :
    (BatchData.forwardA.map Row.event).all (Boundary192.supportedB BatchData.new256) = true := by
  decide +kernel

theorem forward_touched :
    BatchData.new256.all (fun r =>
      LemmaG.Stream.labRun (BatchData.forwardA.map Row.event)
        BatchData.labels192 r == (2 : FrameLabel)) = true := by
  decide +kernel

theorem forward_checkpoint256 :
    LemmaG.Stream.labRun (BatchData.forwardA.map Row.event) BatchData.labels192 =
      BatchData.labels256 :=
  Boundary192.sparse_checkpoint BatchData.forwardA BatchData.labels192 BatchData.new256
    forward_support forward_touched

theorem forward_composed_wellLabelled :
    LemmaG.Stream.WellLabelled
      (((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨NextCheck.forward_composed_wellLabelled, ?_⟩
  rw [Boundary192.forward_composed_checkpoint192]
  exact forward_wellLabelled

theorem forward_composed_checkpoint256 :
    LemmaG.Stream.labRun
      (((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA).map Row.event)
      (initialLabels PilotData.data) = BatchData.labels256 := by
  rw [List.map_append, LemmaG.Stream.labRun_append,
    Boundary192.forward_composed_checkpoint192]
  exact forward_checkpoint256

theorem backward_checked :
    checkRows PilotData.data BatchData.backwardA BatchData.labels192 = true := by
  decide +kernel

theorem backward_wellLabelled :
    LemmaG.Stream.WellLabelled (BatchData.backwardA.map Row.event) BatchData.labels192 :=
  checkRows_wellLabelled PilotData.data BatchData.backwardA BatchData.labels192 backward_checked

theorem backward_support :
    (BatchData.backwardA.map Row.event).all (Boundary192.supportedB BatchData.new256) = true := by
  decide +kernel

theorem backward_touched :
    BatchData.new256.all (fun r =>
      LemmaG.Stream.labRun (BatchData.backwardA.map Row.event)
        BatchData.labels192 r == (2 : FrameLabel)) = true := by
  decide +kernel

theorem backward_checkpoint256 :
    LemmaG.Stream.labRun (BatchData.backwardA.map Row.event) BatchData.labels192 =
      BatchData.labels256 :=
  Boundary192.sparse_checkpoint BatchData.backwardA BatchData.labels192 BatchData.new256
    backward_support backward_touched

theorem backward_composed_wellLabelled :
    LemmaG.Stream.WellLabelled
      (((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨NextCheck.backward_composed_wellLabelled, ?_⟩
  rw [Boundary192.backward_composed_checkpoint192]
  exact backward_wellLabelled

theorem backward_composed_checkpoint256 :
    LemmaG.Stream.labRun
      (((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA).map Row.event)
      (initialLabels PilotData.data) = BatchData.labels256 := by
  rw [List.map_append, LemmaG.Stream.labRun_append,
    Boundary192.backward_composed_checkpoint192]
  exact backward_checkpoint256


#print axioms exact_source_indices
#print axioms forward_checked
#print axioms forward_wellLabelled
#print axioms forward_support
#print axioms forward_touched
#print axioms forward_checkpoint256
#print axioms forward_composed_wellLabelled
#print axioms forward_composed_checkpoint256
#print axioms backward_checked
#print axioms backward_wellLabelled
#print axioms backward_support
#print axioms backward_touched
#print axioms backward_checkpoint256
#print axioms backward_composed_wellLabelled
#print axioms backward_composed_checkpoint256
end CurrentMain.F19SelectedCoverage.ChunkA
