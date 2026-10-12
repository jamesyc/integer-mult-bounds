/- Fresh current535 canonical-frame checks for exactly raw10691..10735, both orientations.
The current997-frame catalog and initializer are certified at this literal boundary.
No pre-A admissibility, omitted-adapter, scalar endpoint or operator conclusion. -/
import Current535CoverageData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535CoverageCheck
open CurrentMain.CanonicalFrameCoverage


theorem current_table_shape :
    Current535CoverageData.frameDimensions.size = 997 ∧ Current535CoverageData.initialOriginalLabels.size = 728 ∧
    Current535CoverageData.children.size = 2927 := by decide +kernel

theorem exact_A_source_indices :
    Current535CoverageData.forwardA.map Row.sourceIndex = List.range' 10691 24 ∧
    Current535CoverageData.backwardA.map Row.sourceIndex = List.range' 10691 24 := by decide +kernel

theorem exact_B_source_indices :
    Current535CoverageData.forwardB.map Row.sourceIndex = List.range' 10715 21 ∧
    Current535CoverageData.backwardB.map Row.sourceIndex = List.range' 10715 21 := by decide +kernel

theorem forward_A_labels_checked :
    labelRowsB Current535CoverageData.forwardA Current535CoverageData.labels0 = true := by decide +kernel

theorem forward_A_children_checked :
    childRowsB Current535CoverageData.data Current535CoverageData.forwardA = true := by decide +kernel

theorem forward_A_checked :
    checkRows Current535CoverageData.data Current535CoverageData.forwardA Current535CoverageData.labels0 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_A_labels_checked, forward_A_children_checked⟩

theorem forward_A_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535CoverageData.forwardA.map Row.event) Current535CoverageData.labels0 :=
  checkRows_wellLabelled Current535CoverageData.data Current535CoverageData.forwardA Current535CoverageData.labels0 forward_A_checked

theorem forward_support24 :
    (Current535CoverageData.forwardA.map Row.event).all (supportedB Current535CoverageData.support24) = true := by decide +kernel

theorem forward_touched24 :
    Current535CoverageData.support24.all (fun r =>
      LemmaG.Stream.labRun (Current535CoverageData.forwardA.map Row.event) Current535CoverageData.labels0 r ==
        (2 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint24 :
    LemmaG.Stream.labRun (Current535CoverageData.forwardA.map Row.event) Current535CoverageData.labels0 = Current535CoverageData.labels24 :=
  sparse_checkpoint Current535CoverageData.forwardA Current535CoverageData.labels0 (fun _ => (2 : FrameLabel 997))
    Current535CoverageData.support24 forward_support24 forward_touched24

theorem forward_B_labels_checked :
    labelRowsB Current535CoverageData.forwardB Current535CoverageData.labels24 = true := by decide +kernel

theorem forward_B_children_checked :
    childRowsB Current535CoverageData.data Current535CoverageData.forwardB = true := by decide +kernel

theorem forward_B_checked :
    checkRows Current535CoverageData.data Current535CoverageData.forwardB Current535CoverageData.labels24 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_B_labels_checked, forward_B_children_checked⟩

theorem forward_B_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535CoverageData.forwardB.map Row.event) Current535CoverageData.labels24 :=
  checkRows_wellLabelled Current535CoverageData.data Current535CoverageData.forwardB Current535CoverageData.labels24 forward_B_checked

theorem forward_support45 :
    (Current535CoverageData.forwardB.map Row.event).all (supportedB Current535CoverageData.support45) = true := by decide +kernel

theorem forward_touched45 :
    Current535CoverageData.support45.all (fun r =>
      LemmaG.Stream.labRun (Current535CoverageData.forwardB.map Row.event) Current535CoverageData.labels24 r ==
        (2 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint45 :
    LemmaG.Stream.labRun (Current535CoverageData.forwardB.map Row.event) Current535CoverageData.labels24 = Current535CoverageData.labels45 :=
  sparse_checkpoint Current535CoverageData.forwardB Current535CoverageData.labels24 (fun _ => (2 : FrameLabel 997))
    Current535CoverageData.support45 forward_support45 forward_touched45

theorem forward_composed_wellLabelled45 :
    LemmaG.Stream.WellLabelled ((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_A_wellLabelled, ?_⟩
  rw [forward_checkpoint24]
  exact forward_B_wellLabelled

theorem forward_composed_checkpoint45 :
    LemmaG.Stream.labRun ((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB).map Row.event) Current535CoverageData.labels0 = Current535CoverageData.labels45 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_checkpoint24]
  exact forward_checkpoint45

theorem backward_A_labels_checked :
    labelRowsB Current535CoverageData.backwardA Current535CoverageData.labels0 = true := by decide +kernel

theorem backward_A_children_checked :
    childRowsB Current535CoverageData.data Current535CoverageData.backwardA = true := by decide +kernel

theorem backward_A_checked :
    checkRows Current535CoverageData.data Current535CoverageData.backwardA Current535CoverageData.labels0 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_A_labels_checked, backward_A_children_checked⟩

theorem backward_A_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535CoverageData.backwardA.map Row.event) Current535CoverageData.labels0 :=
  checkRows_wellLabelled Current535CoverageData.data Current535CoverageData.backwardA Current535CoverageData.labels0 backward_A_checked

theorem backward_support24 :
    (Current535CoverageData.backwardA.map Row.event).all (supportedB Current535CoverageData.support24) = true := by decide +kernel

theorem backward_touched24 :
    Current535CoverageData.support24.all (fun r =>
      LemmaG.Stream.labRun (Current535CoverageData.backwardA.map Row.event) Current535CoverageData.labels0 r ==
        (2 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint24 :
    LemmaG.Stream.labRun (Current535CoverageData.backwardA.map Row.event) Current535CoverageData.labels0 = Current535CoverageData.labels24 :=
  sparse_checkpoint Current535CoverageData.backwardA Current535CoverageData.labels0 (fun _ => (2 : FrameLabel 997))
    Current535CoverageData.support24 backward_support24 backward_touched24

theorem backward_B_labels_checked :
    labelRowsB Current535CoverageData.backwardB Current535CoverageData.labels24 = true := by decide +kernel

theorem backward_B_children_checked :
    childRowsB Current535CoverageData.data Current535CoverageData.backwardB = true := by decide +kernel

theorem backward_B_checked :
    checkRows Current535CoverageData.data Current535CoverageData.backwardB Current535CoverageData.labels24 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_B_labels_checked, backward_B_children_checked⟩

theorem backward_B_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535CoverageData.backwardB.map Row.event) Current535CoverageData.labels24 :=
  checkRows_wellLabelled Current535CoverageData.data Current535CoverageData.backwardB Current535CoverageData.labels24 backward_B_checked

theorem backward_support45 :
    (Current535CoverageData.backwardB.map Row.event).all (supportedB Current535CoverageData.support45) = true := by decide +kernel

theorem backward_touched45 :
    Current535CoverageData.support45.all (fun r =>
      LemmaG.Stream.labRun (Current535CoverageData.backwardB.map Row.event) Current535CoverageData.labels24 r ==
        (2 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint45 :
    LemmaG.Stream.labRun (Current535CoverageData.backwardB.map Row.event) Current535CoverageData.labels24 = Current535CoverageData.labels45 :=
  sparse_checkpoint Current535CoverageData.backwardB Current535CoverageData.labels24 (fun _ => (2 : FrameLabel 997))
    Current535CoverageData.support45 backward_support45 backward_touched45

theorem backward_composed_wellLabelled45 :
    LemmaG.Stream.WellLabelled ((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_A_wellLabelled, ?_⟩
  rw [backward_checkpoint24]
  exact backward_B_wellLabelled

theorem backward_composed_checkpoint45 :
    LemmaG.Stream.labRun ((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB).map Row.event) Current535CoverageData.labels0 = Current535CoverageData.labels45 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_checkpoint24]
  exact backward_checkpoint45

#print axioms current_table_shape
#print axioms exact_A_source_indices
#print axioms exact_B_source_indices
#print axioms forward_A_labels_checked
#print axioms forward_A_children_checked
#print axioms forward_A_checked
#print axioms forward_A_wellLabelled
#print axioms forward_support24
#print axioms forward_touched24
#print axioms forward_checkpoint24
#print axioms forward_B_labels_checked
#print axioms forward_B_children_checked
#print axioms forward_B_checked
#print axioms forward_B_wellLabelled
#print axioms forward_support45
#print axioms forward_touched45
#print axioms forward_checkpoint45
#print axioms forward_composed_wellLabelled45
#print axioms forward_composed_checkpoint45
#print axioms backward_A_labels_checked
#print axioms backward_A_children_checked
#print axioms backward_A_checked
#print axioms backward_A_wellLabelled
#print axioms backward_support24
#print axioms backward_touched24
#print axioms backward_checkpoint24
#print axioms backward_B_labels_checked
#print axioms backward_B_children_checked
#print axioms backward_B_checked
#print axioms backward_B_wellLabelled
#print axioms backward_support45
#print axioms backward_touched45
#print axioms backward_checkpoint45
#print axioms backward_composed_wellLabelled45
#print axioms backward_composed_checkpoint45
end CurrentMain.Current535CoverageCheck
