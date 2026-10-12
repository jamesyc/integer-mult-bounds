/- One measured synchronous90-row two-key batch, in four24/21 decisions.
All earlier90 rows are consumed by accepted theorems; no prefix check is replayed.
The conclusion remains current canonical labels/catalog, not operator or full physical execution. -/
import Current535TwoKeyData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535TwoKeyCheck
open CurrentMain.CanonicalFrameCoverage

theorem exact_E_source_indices :
    Current535TwoKeyData.forwardE.map Row.sourceIndex = List.range' 10781 24 ∧
    Current535TwoKeyData.backwardE.map Row.sourceIndex = List.range' 10781 24 := by decide +kernel

theorem exact_F_source_indices :
    Current535TwoKeyData.forwardF.map Row.sourceIndex = List.range' 10805 21 ∧
    Current535TwoKeyData.backwardF.map Row.sourceIndex = List.range' 10805 21 := by decide +kernel

theorem exact_G_source_indices :
    Current535TwoKeyData.forwardG.map Row.sourceIndex = List.range' 10826 24 ∧
    Current535TwoKeyData.backwardG.map Row.sourceIndex = List.range' 10826 24 := by decide +kernel

theorem exact_H_source_indices :
    Current535TwoKeyData.forwardH.map Row.sourceIndex = List.range' 10850 21 ∧
    Current535TwoKeyData.backwardH.map Row.sourceIndex = List.range' 10850 21 := by decide +kernel

theorem forward_E_labels_checked :
    labelRowsB Current535TwoKeyData.forwardE Current535Child003Data.labels90 = true := by decide +kernel

theorem forward_E_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.forwardE = true := by decide +kernel

theorem forward_E_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.forwardE Current535Child003Data.labels90 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_E_labels_checked, forward_E_children_checked⟩

theorem forward_E_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.forwardE.map Row.event) Current535Child003Data.labels90 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.forwardE Current535Child003Data.labels90 forward_E_checked

theorem forward_support114 :
    (Current535TwoKeyData.forwardE.map Row.event).all (supportedB Current535TwoKeyData.support114) = true := by decide +kernel

theorem forward_touched114 :
    Current535TwoKeyData.support114.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.forwardE.map Row.event) Current535Child003Data.labels90 r ==
        (4 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint114 :
    LemmaG.Stream.labRun (Current535TwoKeyData.forwardE.map Row.event) Current535Child003Data.labels90 = Current535TwoKeyData.labels114 :=
  sparse_checkpoint Current535TwoKeyData.forwardE Current535Child003Data.labels90 (fun _ => (4 : FrameLabel 997))
    Current535TwoKeyData.support114 forward_support114 forward_touched114

theorem forward_composed_wellLabelled114 :
    LemmaG.Stream.WellLabelled (((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535Child003Check.forward_composed_wellLabelled90, ?_⟩
  rw [Current535Child003Check.forward_composed_checkpoint90]
  exact forward_E_wellLabelled

theorem forward_composed_checkpoint114 :
    LemmaG.Stream.labRun (((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels114 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535Child003Check.forward_composed_checkpoint90]
  exact forward_checkpoint114

theorem forward_F_labels_checked :
    labelRowsB Current535TwoKeyData.forwardF Current535TwoKeyData.labels114 = true := by decide +kernel

theorem forward_F_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.forwardF = true := by decide +kernel

theorem forward_F_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.forwardF Current535TwoKeyData.labels114 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_F_labels_checked, forward_F_children_checked⟩

theorem forward_F_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.forwardF.map Row.event) Current535TwoKeyData.labels114 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.forwardF Current535TwoKeyData.labels114 forward_F_checked

theorem forward_support135 :
    (Current535TwoKeyData.forwardF.map Row.event).all (supportedB Current535TwoKeyData.support135) = true := by decide +kernel

theorem forward_touched135 :
    Current535TwoKeyData.support135.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.forwardF.map Row.event) Current535TwoKeyData.labels114 r ==
        (4 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint135 :
    LemmaG.Stream.labRun (Current535TwoKeyData.forwardF.map Row.event) Current535TwoKeyData.labels114 = Current535TwoKeyData.labels135 :=
  sparse_checkpoint Current535TwoKeyData.forwardF Current535TwoKeyData.labels114 (fun _ => (4 : FrameLabel 997))
    Current535TwoKeyData.support135 forward_support135 forward_touched135

theorem forward_composed_wellLabelled135 :
    LemmaG.Stream.WellLabelled ((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled114, ?_⟩
  rw [forward_composed_checkpoint114]
  exact forward_F_wellLabelled

theorem forward_composed_checkpoint135 :
    LemmaG.Stream.labRun ((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels135 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint114]
  exact forward_checkpoint135

theorem forward_G_labels_checked :
    labelRowsB Current535TwoKeyData.forwardG Current535TwoKeyData.labels135 = true := by decide +kernel

theorem forward_G_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.forwardG = true := by decide +kernel

theorem forward_G_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.forwardG Current535TwoKeyData.labels135 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_G_labels_checked, forward_G_children_checked⟩

theorem forward_G_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.forwardG.map Row.event) Current535TwoKeyData.labels135 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.forwardG Current535TwoKeyData.labels135 forward_G_checked

theorem forward_support159 :
    (Current535TwoKeyData.forwardG.map Row.event).all (supportedB Current535TwoKeyData.support159) = true := by decide +kernel

theorem forward_touched159 :
    Current535TwoKeyData.support159.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.forwardG.map Row.event) Current535TwoKeyData.labels135 r ==
        (5 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint159 :
    LemmaG.Stream.labRun (Current535TwoKeyData.forwardG.map Row.event) Current535TwoKeyData.labels135 = Current535TwoKeyData.labels159 :=
  sparse_checkpoint Current535TwoKeyData.forwardG Current535TwoKeyData.labels135 (fun _ => (5 : FrameLabel 997))
    Current535TwoKeyData.support159 forward_support159 forward_touched159

theorem forward_composed_wellLabelled159 :
    LemmaG.Stream.WellLabelled (((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled135, ?_⟩
  rw [forward_composed_checkpoint135]
  exact forward_G_wellLabelled

theorem forward_composed_checkpoint159 :
    LemmaG.Stream.labRun (((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels159 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint135]
  exact forward_checkpoint159

theorem forward_H_labels_checked :
    labelRowsB Current535TwoKeyData.forwardH Current535TwoKeyData.labels159 = true := by decide +kernel

theorem forward_H_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.forwardH = true := by decide +kernel

theorem forward_H_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.forwardH Current535TwoKeyData.labels159 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_H_labels_checked, forward_H_children_checked⟩

theorem forward_H_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.forwardH.map Row.event) Current535TwoKeyData.labels159 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.forwardH Current535TwoKeyData.labels159 forward_H_checked

theorem forward_support180 :
    (Current535TwoKeyData.forwardH.map Row.event).all (supportedB Current535TwoKeyData.support180) = true := by decide +kernel

theorem forward_touched180 :
    Current535TwoKeyData.support180.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.forwardH.map Row.event) Current535TwoKeyData.labels159 r ==
        (5 : FrameLabel 997)) = true := by decide +kernel

theorem forward_checkpoint180 :
    LemmaG.Stream.labRun (Current535TwoKeyData.forwardH.map Row.event) Current535TwoKeyData.labels159 = Current535TwoKeyData.labels180 :=
  sparse_checkpoint Current535TwoKeyData.forwardH Current535TwoKeyData.labels159 (fun _ => (5 : FrameLabel 997))
    Current535TwoKeyData.support180 forward_support180 forward_touched180

theorem forward_composed_wellLabelled180 :
    LemmaG.Stream.WellLabelled ((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled159, ?_⟩
  rw [forward_composed_checkpoint159]
  exact forward_H_wellLabelled

theorem forward_composed_checkpoint180 :
    LemmaG.Stream.labRun ((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels180 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint159]
  exact forward_checkpoint180

theorem backward_E_labels_checked :
    labelRowsB Current535TwoKeyData.backwardE Current535Child003Data.labels90 = true := by decide +kernel

theorem backward_E_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.backwardE = true := by decide +kernel

theorem backward_E_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.backwardE Current535Child003Data.labels90 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_E_labels_checked, backward_E_children_checked⟩

theorem backward_E_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.backwardE.map Row.event) Current535Child003Data.labels90 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.backwardE Current535Child003Data.labels90 backward_E_checked

theorem backward_support114 :
    (Current535TwoKeyData.backwardE.map Row.event).all (supportedB Current535TwoKeyData.support114) = true := by decide +kernel

theorem backward_touched114 :
    Current535TwoKeyData.support114.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.backwardE.map Row.event) Current535Child003Data.labels90 r ==
        (4 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint114 :
    LemmaG.Stream.labRun (Current535TwoKeyData.backwardE.map Row.event) Current535Child003Data.labels90 = Current535TwoKeyData.labels114 :=
  sparse_checkpoint Current535TwoKeyData.backwardE Current535Child003Data.labels90 (fun _ => (4 : FrameLabel 997))
    Current535TwoKeyData.support114 backward_support114 backward_touched114

theorem backward_composed_wellLabelled114 :
    LemmaG.Stream.WellLabelled (((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535Child003Check.backward_composed_wellLabelled90, ?_⟩
  rw [Current535Child003Check.backward_composed_checkpoint90]
  exact backward_E_wellLabelled

theorem backward_composed_checkpoint114 :
    LemmaG.Stream.labRun (((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels114 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535Child003Check.backward_composed_checkpoint90]
  exact backward_checkpoint114

theorem backward_F_labels_checked :
    labelRowsB Current535TwoKeyData.backwardF Current535TwoKeyData.labels114 = true := by decide +kernel

theorem backward_F_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.backwardF = true := by decide +kernel

theorem backward_F_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.backwardF Current535TwoKeyData.labels114 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_F_labels_checked, backward_F_children_checked⟩

theorem backward_F_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.backwardF.map Row.event) Current535TwoKeyData.labels114 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.backwardF Current535TwoKeyData.labels114 backward_F_checked

theorem backward_support135 :
    (Current535TwoKeyData.backwardF.map Row.event).all (supportedB Current535TwoKeyData.support135) = true := by decide +kernel

theorem backward_touched135 :
    Current535TwoKeyData.support135.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.backwardF.map Row.event) Current535TwoKeyData.labels114 r ==
        (4 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint135 :
    LemmaG.Stream.labRun (Current535TwoKeyData.backwardF.map Row.event) Current535TwoKeyData.labels114 = Current535TwoKeyData.labels135 :=
  sparse_checkpoint Current535TwoKeyData.backwardF Current535TwoKeyData.labels114 (fun _ => (4 : FrameLabel 997))
    Current535TwoKeyData.support135 backward_support135 backward_touched135

theorem backward_composed_wellLabelled135 :
    LemmaG.Stream.WellLabelled ((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled114, ?_⟩
  rw [backward_composed_checkpoint114]
  exact backward_F_wellLabelled

theorem backward_composed_checkpoint135 :
    LemmaG.Stream.labRun ((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels135 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint114]
  exact backward_checkpoint135

theorem backward_G_labels_checked :
    labelRowsB Current535TwoKeyData.backwardG Current535TwoKeyData.labels135 = true := by decide +kernel

theorem backward_G_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.backwardG = true := by decide +kernel

theorem backward_G_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.backwardG Current535TwoKeyData.labels135 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_G_labels_checked, backward_G_children_checked⟩

theorem backward_G_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.backwardG.map Row.event) Current535TwoKeyData.labels135 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.backwardG Current535TwoKeyData.labels135 backward_G_checked

theorem backward_support159 :
    (Current535TwoKeyData.backwardG.map Row.event).all (supportedB Current535TwoKeyData.support159) = true := by decide +kernel

theorem backward_touched159 :
    Current535TwoKeyData.support159.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.backwardG.map Row.event) Current535TwoKeyData.labels135 r ==
        (5 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint159 :
    LemmaG.Stream.labRun (Current535TwoKeyData.backwardG.map Row.event) Current535TwoKeyData.labels135 = Current535TwoKeyData.labels159 :=
  sparse_checkpoint Current535TwoKeyData.backwardG Current535TwoKeyData.labels135 (fun _ => (5 : FrameLabel 997))
    Current535TwoKeyData.support159 backward_support159 backward_touched159

theorem backward_composed_wellLabelled159 :
    LemmaG.Stream.WellLabelled (((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled135, ?_⟩
  rw [backward_composed_checkpoint135]
  exact backward_G_wellLabelled

theorem backward_composed_checkpoint159 :
    LemmaG.Stream.labRun (((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels159 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint135]
  exact backward_checkpoint159

theorem backward_H_labels_checked :
    labelRowsB Current535TwoKeyData.backwardH Current535TwoKeyData.labels159 = true := by decide +kernel

theorem backward_H_children_checked :
    childRowsB Current535CoverageData.data Current535TwoKeyData.backwardH = true := by decide +kernel

theorem backward_H_checked :
    checkRows Current535CoverageData.data Current535TwoKeyData.backwardH Current535TwoKeyData.labels159 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_H_labels_checked, backward_H_children_checked⟩

theorem backward_H_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535TwoKeyData.backwardH.map Row.event) Current535TwoKeyData.labels159 :=
  checkRows_wellLabelled Current535CoverageData.data Current535TwoKeyData.backwardH Current535TwoKeyData.labels159 backward_H_checked

theorem backward_support180 :
    (Current535TwoKeyData.backwardH.map Row.event).all (supportedB Current535TwoKeyData.support180) = true := by decide +kernel

theorem backward_touched180 :
    Current535TwoKeyData.support180.all (fun r =>
      LemmaG.Stream.labRun (Current535TwoKeyData.backwardH.map Row.event) Current535TwoKeyData.labels159 r ==
        (5 : FrameLabel 997)) = true := by decide +kernel

theorem backward_checkpoint180 :
    LemmaG.Stream.labRun (Current535TwoKeyData.backwardH.map Row.event) Current535TwoKeyData.labels159 = Current535TwoKeyData.labels180 :=
  sparse_checkpoint Current535TwoKeyData.backwardH Current535TwoKeyData.labels159 (fun _ => (5 : FrameLabel 997))
    Current535TwoKeyData.support180 backward_support180 backward_touched180

theorem backward_composed_wellLabelled180 :
    LemmaG.Stream.WellLabelled ((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled159, ?_⟩
  rw [backward_composed_checkpoint159]
  exact backward_H_wellLabelled

theorem backward_composed_checkpoint180 :
    LemmaG.Stream.labRun ((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH).map Row.event) Current535CoverageData.labels0 = Current535TwoKeyData.labels180 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint159]
  exact backward_checkpoint180

#print axioms exact_E_source_indices
#print axioms exact_F_source_indices
#print axioms exact_G_source_indices
#print axioms exact_H_source_indices
#print axioms forward_E_labels_checked
#print axioms forward_E_children_checked
#print axioms forward_E_checked
#print axioms forward_E_wellLabelled
#print axioms forward_support114
#print axioms forward_touched114
#print axioms forward_checkpoint114
#print axioms forward_composed_wellLabelled114
#print axioms forward_composed_checkpoint114
#print axioms forward_F_labels_checked
#print axioms forward_F_children_checked
#print axioms forward_F_checked
#print axioms forward_F_wellLabelled
#print axioms forward_support135
#print axioms forward_touched135
#print axioms forward_checkpoint135
#print axioms forward_composed_wellLabelled135
#print axioms forward_composed_checkpoint135
#print axioms forward_G_labels_checked
#print axioms forward_G_children_checked
#print axioms forward_G_checked
#print axioms forward_G_wellLabelled
#print axioms forward_support159
#print axioms forward_touched159
#print axioms forward_checkpoint159
#print axioms forward_composed_wellLabelled159
#print axioms forward_composed_checkpoint159
#print axioms forward_H_labels_checked
#print axioms forward_H_children_checked
#print axioms forward_H_checked
#print axioms forward_H_wellLabelled
#print axioms forward_support180
#print axioms forward_touched180
#print axioms forward_checkpoint180
#print axioms forward_composed_wellLabelled180
#print axioms forward_composed_checkpoint180
#print axioms backward_E_labels_checked
#print axioms backward_E_children_checked
#print axioms backward_E_checked
#print axioms backward_E_wellLabelled
#print axioms backward_support114
#print axioms backward_touched114
#print axioms backward_checkpoint114
#print axioms backward_composed_wellLabelled114
#print axioms backward_composed_checkpoint114
#print axioms backward_F_labels_checked
#print axioms backward_F_children_checked
#print axioms backward_F_checked
#print axioms backward_F_wellLabelled
#print axioms backward_support135
#print axioms backward_touched135
#print axioms backward_checkpoint135
#print axioms backward_composed_wellLabelled135
#print axioms backward_composed_checkpoint135
#print axioms backward_G_labels_checked
#print axioms backward_G_children_checked
#print axioms backward_G_checked
#print axioms backward_G_wellLabelled
#print axioms backward_support159
#print axioms backward_touched159
#print axioms backward_checkpoint159
#print axioms backward_composed_wellLabelled159
#print axioms backward_composed_checkpoint159
#print axioms backward_H_labels_checked
#print axioms backward_H_children_checked
#print axioms backward_H_checked
#print axioms backward_H_wellLabelled
#print axioms backward_support180
#print axioms backward_touched180
#print axioms backward_checkpoint180
#print axioms backward_composed_wellLabelled180
#print axioms backward_composed_checkpoint180
end CurrentMain.Current535TwoKeyCheck
