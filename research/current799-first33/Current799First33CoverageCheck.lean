/- Fresh current799 canonical-frame checks for exactly raw9241..9273, both orientations.
The1005-frame dimensions,728 initial labels and first3 child keys are certified at this literal boundary.
Only ordinal2 old0/new4 is exercised. Actual pre-A execution remains a separate supplier.
No pre-A admissibility, omitted-adapter, scalar endpoint or operator conclusion. -/
import Current799First33CoverageData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799First33CoverageCheck
open CurrentMain.CanonicalFrameCoverage


theorem current_table_shape :
    Current799First33CoverageData.frameDimensions.size = 1005 ∧ Current799First33CoverageData.initialOriginalLabels.size = 728 ∧
    Current799First33CoverageData.children.size = 3 := by decide +kernel

theorem exact_A_source_indices :
    Current799First33CoverageData.forwardA.map Row.sourceIndex = List.range' 9241 24 ∧
    Current799First33CoverageData.backwardA.map Row.sourceIndex = List.range' 9241 24 := by decide +kernel

theorem exact_B_source_indices :
    Current799First33CoverageData.forwardB.map Row.sourceIndex = List.range' 9265 9 ∧
    Current799First33CoverageData.backwardB.map Row.sourceIndex = List.range' 9265 9 := by decide +kernel

theorem forward_A_labels_checked :
    labelRowsB Current799First33CoverageData.forwardA Current799First33CoverageData.labels0 = true := by decide +kernel

theorem forward_A_children_checked :
    childRowsB Current799First33CoverageData.data Current799First33CoverageData.forwardA = true := by decide +kernel

theorem forward_A_checked :
    checkRows Current799First33CoverageData.data Current799First33CoverageData.forwardA Current799First33CoverageData.labels0 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_A_labels_checked, forward_A_children_checked⟩

theorem forward_A_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799First33CoverageData.forwardA.map Row.event) Current799First33CoverageData.labels0 :=
  checkRows_wellLabelled Current799First33CoverageData.data Current799First33CoverageData.forwardA Current799First33CoverageData.labels0 forward_A_checked

theorem forward_support24 :
    (Current799First33CoverageData.forwardA.map Row.event).all (supportedB Current799First33CoverageData.support24) = true := by decide +kernel

theorem forward_touched24 :
    Current799First33CoverageData.support24.all (fun r =>
      LemmaG.Stream.labRun (Current799First33CoverageData.forwardA.map Row.event) Current799First33CoverageData.labels0 r ==
        (4 : FrameLabel 1005)) = true := by decide +kernel

theorem forward_checkpoint24 :
    LemmaG.Stream.labRun (Current799First33CoverageData.forwardA.map Row.event) Current799First33CoverageData.labels0 = Current799First33CoverageData.labels24 :=
  sparse_checkpoint Current799First33CoverageData.forwardA Current799First33CoverageData.labels0 (fun _ => (4 : FrameLabel 1005))
    Current799First33CoverageData.support24 forward_support24 forward_touched24

theorem forward_B_labels_checked :
    labelRowsB Current799First33CoverageData.forwardB Current799First33CoverageData.labels24 = true := by decide +kernel

theorem forward_B_children_checked :
    childRowsB Current799First33CoverageData.data Current799First33CoverageData.forwardB = true := by decide +kernel

theorem forward_B_checked :
    checkRows Current799First33CoverageData.data Current799First33CoverageData.forwardB Current799First33CoverageData.labels24 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_B_labels_checked, forward_B_children_checked⟩

theorem forward_B_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799First33CoverageData.forwardB.map Row.event) Current799First33CoverageData.labels24 :=
  checkRows_wellLabelled Current799First33CoverageData.data Current799First33CoverageData.forwardB Current799First33CoverageData.labels24 forward_B_checked

theorem forward_support33 :
    (Current799First33CoverageData.forwardB.map Row.event).all (supportedB Current799First33CoverageData.support33) = true := by decide +kernel

theorem forward_touched33 :
    Current799First33CoverageData.support33.all (fun r =>
      LemmaG.Stream.labRun (Current799First33CoverageData.forwardB.map Row.event) Current799First33CoverageData.labels24 r ==
        (4 : FrameLabel 1005)) = true := by decide +kernel

theorem forward_checkpoint33 :
    LemmaG.Stream.labRun (Current799First33CoverageData.forwardB.map Row.event) Current799First33CoverageData.labels24 = Current799First33CoverageData.labels33 :=
  sparse_checkpoint Current799First33CoverageData.forwardB Current799First33CoverageData.labels24 (fun _ => (4 : FrameLabel 1005))
    Current799First33CoverageData.support33 forward_support33 forward_touched33

theorem forward_composed_wellLabelled33 :
    LemmaG.Stream.WellLabelled ((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_A_wellLabelled, ?_⟩
  rw [forward_checkpoint24]
  exact forward_B_wellLabelled

theorem forward_composed_checkpoint33 :
    LemmaG.Stream.labRun ((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB).map Row.event) Current799First33CoverageData.labels0 = Current799First33CoverageData.labels33 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_checkpoint24]
  exact forward_checkpoint33

theorem backward_A_labels_checked :
    labelRowsB Current799First33CoverageData.backwardA Current799First33CoverageData.labels0 = true := by decide +kernel

theorem backward_A_children_checked :
    childRowsB Current799First33CoverageData.data Current799First33CoverageData.backwardA = true := by decide +kernel

theorem backward_A_checked :
    checkRows Current799First33CoverageData.data Current799First33CoverageData.backwardA Current799First33CoverageData.labels0 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_A_labels_checked, backward_A_children_checked⟩

theorem backward_A_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799First33CoverageData.backwardA.map Row.event) Current799First33CoverageData.labels0 :=
  checkRows_wellLabelled Current799First33CoverageData.data Current799First33CoverageData.backwardA Current799First33CoverageData.labels0 backward_A_checked

theorem backward_support24 :
    (Current799First33CoverageData.backwardA.map Row.event).all (supportedB Current799First33CoverageData.support24) = true := by decide +kernel

theorem backward_touched24 :
    Current799First33CoverageData.support24.all (fun r =>
      LemmaG.Stream.labRun (Current799First33CoverageData.backwardA.map Row.event) Current799First33CoverageData.labels0 r ==
        (4 : FrameLabel 1005)) = true := by decide +kernel

theorem backward_checkpoint24 :
    LemmaG.Stream.labRun (Current799First33CoverageData.backwardA.map Row.event) Current799First33CoverageData.labels0 = Current799First33CoverageData.labels24 :=
  sparse_checkpoint Current799First33CoverageData.backwardA Current799First33CoverageData.labels0 (fun _ => (4 : FrameLabel 1005))
    Current799First33CoverageData.support24 backward_support24 backward_touched24

theorem backward_B_labels_checked :
    labelRowsB Current799First33CoverageData.backwardB Current799First33CoverageData.labels24 = true := by decide +kernel

theorem backward_B_children_checked :
    childRowsB Current799First33CoverageData.data Current799First33CoverageData.backwardB = true := by decide +kernel

theorem backward_B_checked :
    checkRows Current799First33CoverageData.data Current799First33CoverageData.backwardB Current799First33CoverageData.labels24 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_B_labels_checked, backward_B_children_checked⟩

theorem backward_B_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799First33CoverageData.backwardB.map Row.event) Current799First33CoverageData.labels24 :=
  checkRows_wellLabelled Current799First33CoverageData.data Current799First33CoverageData.backwardB Current799First33CoverageData.labels24 backward_B_checked

theorem backward_support33 :
    (Current799First33CoverageData.backwardB.map Row.event).all (supportedB Current799First33CoverageData.support33) = true := by decide +kernel

theorem backward_touched33 :
    Current799First33CoverageData.support33.all (fun r =>
      LemmaG.Stream.labRun (Current799First33CoverageData.backwardB.map Row.event) Current799First33CoverageData.labels24 r ==
        (4 : FrameLabel 1005)) = true := by decide +kernel

theorem backward_checkpoint33 :
    LemmaG.Stream.labRun (Current799First33CoverageData.backwardB.map Row.event) Current799First33CoverageData.labels24 = Current799First33CoverageData.labels33 :=
  sparse_checkpoint Current799First33CoverageData.backwardB Current799First33CoverageData.labels24 (fun _ => (4 : FrameLabel 1005))
    Current799First33CoverageData.support33 backward_support33 backward_touched33

theorem backward_composed_wellLabelled33 :
    LemmaG.Stream.WellLabelled ((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_A_wellLabelled, ?_⟩
  rw [backward_checkpoint24]
  exact backward_B_wellLabelled

theorem backward_composed_checkpoint33 :
    LemmaG.Stream.labRun ((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB).map Row.event) Current799First33CoverageData.labels0 = Current799First33CoverageData.labels33 := by
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
end CurrentMain.Current799First33CoverageCheck
