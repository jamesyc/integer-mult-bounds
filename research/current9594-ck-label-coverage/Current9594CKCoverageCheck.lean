/- Fresh current9594 CK canonical-frame checks for exactly raw9899..9931, both orientations.
The current1079-frame catalog and initializer are certified at this literal boundary.
No pre-A admissibility, omitted-adapter, scalar endpoint or operator conclusion. -/
import Current9594CKCoverageData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current9594CKCoverageCheck
open CurrentMain.CanonicalFrameCoverage


theorem current_table_shape :
    Current9594CKCoverageData.frameDimensions.size = 1079 ∧ Current9594CKCoverageData.initialOriginalLabels.size = 728 ∧
    Current9594CKCoverageData.children.size = 3017 := by decide +kernel

theorem exact_A_source_indices :
    Current9594CKCoverageData.forwardA.map Row.sourceIndex = List.range' 9899 24 ∧
    Current9594CKCoverageData.backwardA.map Row.sourceIndex = List.range' 9899 24 := by decide +kernel

theorem exact_B_source_indices :
    Current9594CKCoverageData.forwardB.map Row.sourceIndex = List.range' 9923 9 ∧
    Current9594CKCoverageData.backwardB.map Row.sourceIndex = List.range' 9923 9 := by decide +kernel

theorem forward_A_labels_checked :
    labelRowsB Current9594CKCoverageData.forwardA Current9594CKCoverageData.labels0 = true := by decide +kernel

theorem forward_A_children_checked :
    childRowsB Current9594CKCoverageData.data Current9594CKCoverageData.forwardA = true := by decide +kernel

theorem forward_A_checked :
    checkRows Current9594CKCoverageData.data Current9594CKCoverageData.forwardA Current9594CKCoverageData.labels0 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_A_labels_checked, forward_A_children_checked⟩

theorem forward_A_wellLabelled :
    LemmaG.Stream.WellLabelled (Current9594CKCoverageData.forwardA.map Row.event) Current9594CKCoverageData.labels0 :=
  checkRows_wellLabelled Current9594CKCoverageData.data Current9594CKCoverageData.forwardA Current9594CKCoverageData.labels0 forward_A_checked

theorem forward_support24 :
    (Current9594CKCoverageData.forwardA.map Row.event).all (supportedB Current9594CKCoverageData.support24) = true := by decide +kernel

theorem forward_touched24 :
    Current9594CKCoverageData.support24.all (fun r =>
      LemmaG.Stream.labRun (Current9594CKCoverageData.forwardA.map Row.event) Current9594CKCoverageData.labels0 r ==
        (2 : FrameLabel 1079)) = true := by decide +kernel

theorem forward_checkpoint24 :
    LemmaG.Stream.labRun (Current9594CKCoverageData.forwardA.map Row.event) Current9594CKCoverageData.labels0 = Current9594CKCoverageData.labels24 :=
  sparse_checkpoint Current9594CKCoverageData.forwardA Current9594CKCoverageData.labels0 (fun _ => (2 : FrameLabel 1079))
    Current9594CKCoverageData.support24 forward_support24 forward_touched24

theorem forward_B_labels_checked :
    labelRowsB Current9594CKCoverageData.forwardB Current9594CKCoverageData.labels24 = true := by decide +kernel

theorem forward_B_children_checked :
    childRowsB Current9594CKCoverageData.data Current9594CKCoverageData.forwardB = true := by decide +kernel

theorem forward_B_checked :
    checkRows Current9594CKCoverageData.data Current9594CKCoverageData.forwardB Current9594CKCoverageData.labels24 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_B_labels_checked, forward_B_children_checked⟩

theorem forward_B_wellLabelled :
    LemmaG.Stream.WellLabelled (Current9594CKCoverageData.forwardB.map Row.event) Current9594CKCoverageData.labels24 :=
  checkRows_wellLabelled Current9594CKCoverageData.data Current9594CKCoverageData.forwardB Current9594CKCoverageData.labels24 forward_B_checked

theorem forward_support33 :
    (Current9594CKCoverageData.forwardB.map Row.event).all (supportedB Current9594CKCoverageData.support33) = true := by decide +kernel

theorem forward_touched33 :
    Current9594CKCoverageData.support33.all (fun r =>
      LemmaG.Stream.labRun (Current9594CKCoverageData.forwardB.map Row.event) Current9594CKCoverageData.labels24 r ==
        (2 : FrameLabel 1079)) = true := by decide +kernel

theorem forward_checkpoint33 :
    LemmaG.Stream.labRun (Current9594CKCoverageData.forwardB.map Row.event) Current9594CKCoverageData.labels24 = Current9594CKCoverageData.labels33 :=
  sparse_checkpoint Current9594CKCoverageData.forwardB Current9594CKCoverageData.labels24 (fun _ => (2 : FrameLabel 1079))
    Current9594CKCoverageData.support33 forward_support33 forward_touched33

theorem forward_composed_wellLabelled33 :
    LemmaG.Stream.WellLabelled ((Current9594CKCoverageData.forwardA ++ Current9594CKCoverageData.forwardB).map Row.event) Current9594CKCoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_A_wellLabelled, ?_⟩
  rw [forward_checkpoint24]
  exact forward_B_wellLabelled

theorem forward_composed_checkpoint33 :
    LemmaG.Stream.labRun ((Current9594CKCoverageData.forwardA ++ Current9594CKCoverageData.forwardB).map Row.event) Current9594CKCoverageData.labels0 = Current9594CKCoverageData.labels33 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_checkpoint24]
  exact forward_checkpoint33

theorem backward_A_labels_checked :
    labelRowsB Current9594CKCoverageData.backwardA Current9594CKCoverageData.labels0 = true := by decide +kernel

theorem backward_A_children_checked :
    childRowsB Current9594CKCoverageData.data Current9594CKCoverageData.backwardA = true := by decide +kernel

theorem backward_A_checked :
    checkRows Current9594CKCoverageData.data Current9594CKCoverageData.backwardA Current9594CKCoverageData.labels0 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_A_labels_checked, backward_A_children_checked⟩

theorem backward_A_wellLabelled :
    LemmaG.Stream.WellLabelled (Current9594CKCoverageData.backwardA.map Row.event) Current9594CKCoverageData.labels0 :=
  checkRows_wellLabelled Current9594CKCoverageData.data Current9594CKCoverageData.backwardA Current9594CKCoverageData.labels0 backward_A_checked

theorem backward_support24 :
    (Current9594CKCoverageData.backwardA.map Row.event).all (supportedB Current9594CKCoverageData.support24) = true := by decide +kernel

theorem backward_touched24 :
    Current9594CKCoverageData.support24.all (fun r =>
      LemmaG.Stream.labRun (Current9594CKCoverageData.backwardA.map Row.event) Current9594CKCoverageData.labels0 r ==
        (2 : FrameLabel 1079)) = true := by decide +kernel

theorem backward_checkpoint24 :
    LemmaG.Stream.labRun (Current9594CKCoverageData.backwardA.map Row.event) Current9594CKCoverageData.labels0 = Current9594CKCoverageData.labels24 :=
  sparse_checkpoint Current9594CKCoverageData.backwardA Current9594CKCoverageData.labels0 (fun _ => (2 : FrameLabel 1079))
    Current9594CKCoverageData.support24 backward_support24 backward_touched24

theorem backward_B_labels_checked :
    labelRowsB Current9594CKCoverageData.backwardB Current9594CKCoverageData.labels24 = true := by decide +kernel

theorem backward_B_children_checked :
    childRowsB Current9594CKCoverageData.data Current9594CKCoverageData.backwardB = true := by decide +kernel

theorem backward_B_checked :
    checkRows Current9594CKCoverageData.data Current9594CKCoverageData.backwardB Current9594CKCoverageData.labels24 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_B_labels_checked, backward_B_children_checked⟩

theorem backward_B_wellLabelled :
    LemmaG.Stream.WellLabelled (Current9594CKCoverageData.backwardB.map Row.event) Current9594CKCoverageData.labels24 :=
  checkRows_wellLabelled Current9594CKCoverageData.data Current9594CKCoverageData.backwardB Current9594CKCoverageData.labels24 backward_B_checked

theorem backward_support33 :
    (Current9594CKCoverageData.backwardB.map Row.event).all (supportedB Current9594CKCoverageData.support33) = true := by decide +kernel

theorem backward_touched33 :
    Current9594CKCoverageData.support33.all (fun r =>
      LemmaG.Stream.labRun (Current9594CKCoverageData.backwardB.map Row.event) Current9594CKCoverageData.labels24 r ==
        (2 : FrameLabel 1079)) = true := by decide +kernel

theorem backward_checkpoint33 :
    LemmaG.Stream.labRun (Current9594CKCoverageData.backwardB.map Row.event) Current9594CKCoverageData.labels24 = Current9594CKCoverageData.labels33 :=
  sparse_checkpoint Current9594CKCoverageData.backwardB Current9594CKCoverageData.labels24 (fun _ => (2 : FrameLabel 1079))
    Current9594CKCoverageData.support33 backward_support33 backward_touched33

theorem backward_composed_wellLabelled33 :
    LemmaG.Stream.WellLabelled ((Current9594CKCoverageData.backwardA ++ Current9594CKCoverageData.backwardB).map Row.event) Current9594CKCoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_A_wellLabelled, ?_⟩
  rw [backward_checkpoint24]
  exact backward_B_wellLabelled

theorem backward_composed_checkpoint33 :
    LemmaG.Stream.labRun ((Current9594CKCoverageData.backwardA ++ Current9594CKCoverageData.backwardB).map Row.event) Current9594CKCoverageData.labels0 = Current9594CKCoverageData.labels33 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_checkpoint24]
  exact backward_checkpoint33

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
#print axioms forward_support33
#print axioms forward_touched33
#print axioms forward_checkpoint33
#print axioms forward_composed_wellLabelled33
#print axioms forward_composed_checkpoint33
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
#print axioms backward_support33
#print axioms backward_touched33
#print axioms backward_checkpoint33
#print axioms backward_composed_wellLabelled33
#print axioms backward_composed_checkpoint33
end CurrentMain.Current9594CKCoverageCheck
