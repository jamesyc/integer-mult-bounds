/- Exact45-row current535 extension, reusing the accepted45-row predicate and checkpoint.
Only canonical label and directed catalog coverage; physical/operator suppliers remain open. -/
import Current535Child003Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535Child003Check
open CurrentMain.CanonicalFrameCoverage

theorem exact_C_source_indices :
    Current535Child003Data.forwardC.map Row.sourceIndex = List.range' 10736 24 ∧
    Current535Child003Data.backwardC.map Row.sourceIndex = List.range' 10736 24 := by decide +kernel

theorem exact_D_source_indices :
    Current535Child003Data.forwardD.map Row.sourceIndex = List.range' 10760 21 ∧
    Current535Child003Data.backwardD.map Row.sourceIndex = List.range' 10760 21 := by decide +kernel

theorem forward_C_labels_checked :
    labelRowsB Current535Child003Data.forwardC Current535CoverageData.labels45 = true := by decide +kernel

theorem forward_C_children_checked :
    childRowsB Current535CoverageData.data Current535Child003Data.forwardC = true := by decide +kernel

theorem forward_C_checked :
    checkRows Current535CoverageData.data Current535Child003Data.forwardC Current535CoverageData.labels45 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_C_labels_checked, forward_C_children_checked⟩

theorem forward_C_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535Child003Data.forwardC.map Row.event) Current535CoverageData.labels45 :=
  checkRows_wellLabelled Current535CoverageData.data Current535Child003Data.forwardC Current535CoverageData.labels45 forward_C_checked

theorem forward_support69 :
    (Current535Child003Data.forwardC.map Row.event).all (supportedB Current535Child003Data.support69) = true := by decide +kernel

theorem forward_touched69 :
    Current535Child003Data.support69.all (fun r =>
      LemmaG.Stream.labRun (Current535Child003Data.forwardC.map Row.event) Current535CoverageData.labels45 r ==
        (3 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint69 :
    LemmaG.Stream.labRun (Current535Child003Data.forwardC.map Row.event) Current535CoverageData.labels45 = Current535Child003Data.labels69 :=
  sparse_checkpoint Current535Child003Data.forwardC Current535CoverageData.labels45 (fun _ => (3 : FrameLabel 997))
    Current535Child003Data.support69 forward_support69 forward_touched69

theorem forward_composed_wellLabelled69 :
    LemmaG.Stream.WellLabelled (((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535CoverageCheck.forward_composed_wellLabelled45, ?_⟩
  rw [Current535CoverageCheck.forward_composed_checkpoint45]
  exact forward_C_wellLabelled

theorem forward_composed_checkpoint69 :
    LemmaG.Stream.labRun (((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC).map Row.event) Current535CoverageData.labels0 = Current535Child003Data.labels69 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535CoverageCheck.forward_composed_checkpoint45]
  exact forward_checkpoint69

theorem forward_D_labels_checked :
    labelRowsB Current535Child003Data.forwardD Current535Child003Data.labels69 = true := by decide +kernel

theorem forward_D_children_checked :
    childRowsB Current535CoverageData.data Current535Child003Data.forwardD = true := by decide +kernel

theorem forward_D_checked :
    checkRows Current535CoverageData.data Current535Child003Data.forwardD Current535Child003Data.labels69 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_D_labels_checked, forward_D_children_checked⟩

theorem forward_D_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535Child003Data.forwardD.map Row.event) Current535Child003Data.labels69 :=
  checkRows_wellLabelled Current535CoverageData.data Current535Child003Data.forwardD Current535Child003Data.labels69 forward_D_checked

theorem forward_support90 :
    (Current535Child003Data.forwardD.map Row.event).all (supportedB Current535Child003Data.support90) = true := by decide +kernel

theorem forward_touched90 :
    Current535Child003Data.support90.all (fun r =>
      LemmaG.Stream.labRun (Current535Child003Data.forwardD.map Row.event) Current535Child003Data.labels69 r ==
        (3 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint90 :
    LemmaG.Stream.labRun (Current535Child003Data.forwardD.map Row.event) Current535Child003Data.labels69 = Current535Child003Data.labels90 :=
  sparse_checkpoint Current535Child003Data.forwardD Current535Child003Data.labels69 (fun _ => (3 : FrameLabel 997))
    Current535Child003Data.support90 forward_support90 forward_touched90

theorem forward_composed_wellLabelled90 :
    LemmaG.Stream.WellLabelled ((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled69, ?_⟩
  rw [forward_composed_checkpoint69]
  exact forward_D_wellLabelled

theorem forward_composed_checkpoint90 :
    LemmaG.Stream.labRun ((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD).map Row.event) Current535CoverageData.labels0 = Current535Child003Data.labels90 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint69]
  exact forward_checkpoint90

theorem backward_C_labels_checked :
    labelRowsB Current535Child003Data.backwardC Current535CoverageData.labels45 = true := by decide +kernel

theorem backward_C_children_checked :
    childRowsB Current535CoverageData.data Current535Child003Data.backwardC = true := by decide +kernel

theorem backward_C_checked :
    checkRows Current535CoverageData.data Current535Child003Data.backwardC Current535CoverageData.labels45 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_C_labels_checked, backward_C_children_checked⟩

theorem backward_C_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535Child003Data.backwardC.map Row.event) Current535CoverageData.labels45 :=
  checkRows_wellLabelled Current535CoverageData.data Current535Child003Data.backwardC Current535CoverageData.labels45 backward_C_checked

theorem backward_support69 :
    (Current535Child003Data.backwardC.map Row.event).all (supportedB Current535Child003Data.support69) = true := by decide +kernel

theorem backward_touched69 :
    Current535Child003Data.support69.all (fun r =>
      LemmaG.Stream.labRun (Current535Child003Data.backwardC.map Row.event) Current535CoverageData.labels45 r ==
        (3 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint69 :
    LemmaG.Stream.labRun (Current535Child003Data.backwardC.map Row.event) Current535CoverageData.labels45 = Current535Child003Data.labels69 :=
  sparse_checkpoint Current535Child003Data.backwardC Current535CoverageData.labels45 (fun _ => (3 : FrameLabel 997))
    Current535Child003Data.support69 backward_support69 backward_touched69

theorem backward_composed_wellLabelled69 :
    LemmaG.Stream.WellLabelled (((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535CoverageCheck.backward_composed_wellLabelled45, ?_⟩
  rw [Current535CoverageCheck.backward_composed_checkpoint45]
  exact backward_C_wellLabelled

theorem backward_composed_checkpoint69 :
    LemmaG.Stream.labRun (((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC).map Row.event) Current535CoverageData.labels0 = Current535Child003Data.labels69 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535CoverageCheck.backward_composed_checkpoint45]
  exact backward_checkpoint69

theorem backward_D_labels_checked :
    labelRowsB Current535Child003Data.backwardD Current535Child003Data.labels69 = true := by decide +kernel

theorem backward_D_children_checked :
    childRowsB Current535CoverageData.data Current535Child003Data.backwardD = true := by decide +kernel

theorem backward_D_checked :
    checkRows Current535CoverageData.data Current535Child003Data.backwardD Current535Child003Data.labels69 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_D_labels_checked, backward_D_children_checked⟩

theorem backward_D_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535Child003Data.backwardD.map Row.event) Current535Child003Data.labels69 :=
  checkRows_wellLabelled Current535CoverageData.data Current535Child003Data.backwardD Current535Child003Data.labels69 backward_D_checked

theorem backward_support90 :
    (Current535Child003Data.backwardD.map Row.event).all (supportedB Current535Child003Data.support90) = true := by decide +kernel

theorem backward_touched90 :
    Current535Child003Data.support90.all (fun r =>
      LemmaG.Stream.labRun (Current535Child003Data.backwardD.map Row.event) Current535Child003Data.labels69 r ==
        (3 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint90 :
    LemmaG.Stream.labRun (Current535Child003Data.backwardD.map Row.event) Current535Child003Data.labels69 = Current535Child003Data.labels90 :=
  sparse_checkpoint Current535Child003Data.backwardD Current535Child003Data.labels69 (fun _ => (3 : FrameLabel 997))
    Current535Child003Data.support90 backward_support90 backward_touched90

theorem backward_composed_wellLabelled90 :
    LemmaG.Stream.WellLabelled ((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled69, ?_⟩
  rw [backward_composed_checkpoint69]
  exact backward_D_wellLabelled

theorem backward_composed_checkpoint90 :
    LemmaG.Stream.labRun ((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD).map Row.event) Current535CoverageData.labels0 = Current535Child003Data.labels90 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint69]
  exact backward_checkpoint90

#print axioms exact_C_source_indices
#print axioms exact_D_source_indices
#print axioms forward_C_labels_checked
#print axioms forward_C_children_checked
#print axioms forward_C_checked
#print axioms forward_C_wellLabelled
#print axioms forward_support69
#print axioms forward_touched69
#print axioms forward_checkpoint69
#print axioms forward_composed_wellLabelled69
#print axioms forward_composed_checkpoint69
#print axioms forward_D_labels_checked
#print axioms forward_D_children_checked
#print axioms forward_D_checked
#print axioms forward_D_wellLabelled
#print axioms forward_support90
#print axioms forward_touched90
#print axioms forward_checkpoint90
#print axioms forward_composed_wellLabelled90
#print axioms forward_composed_checkpoint90
#print axioms backward_C_labels_checked
#print axioms backward_C_children_checked
#print axioms backward_C_checked
#print axioms backward_C_wellLabelled
#print axioms backward_support69
#print axioms backward_touched69
#print axioms backward_checkpoint69
#print axioms backward_composed_wellLabelled69
#print axioms backward_composed_checkpoint69
#print axioms backward_D_labels_checked
#print axioms backward_D_children_checked
#print axioms backward_D_checked
#print axioms backward_D_wellLabelled
#print axioms backward_support90
#print axioms backward_touched90
#print axioms backward_checkpoint90
#print axioms backward_composed_wellLabelled90
#print axioms backward_composed_checkpoint90
end CurrentMain.Current535Child003Check
