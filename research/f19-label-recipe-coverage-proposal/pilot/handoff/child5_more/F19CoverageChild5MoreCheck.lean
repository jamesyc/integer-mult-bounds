/- Scoped selected-source label/canonical-recipe coverage. No physical/operator claim. -/
import F19CoverageChild5MoreData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Child5MoreCheck
open CurrentMain.F19SelectedCoverage

theorem exact_K_source_indices :
    Child5MoreData.forwardK.map Row.sourceIndex = List.range' 11352 24 ∧
    Child5MoreData.backwardK.map Row.sourceIndex = List.range' 11352 24 := by
  decide +kernel

theorem exact_L_source_indices :
    Child5MoreData.forwardL.map Row.sourceIndex = List.range' 11376 24 ∧
    Child5MoreData.backwardL.map Row.sourceIndex = List.range' 11376 24 := by
  decide +kernel

theorem forward_K_labels_checked :
    CheckDecomposition.labelRowsB Child5MoreData.forwardK Child5BodyData.labels501 = true := by
  decide +kernel

theorem forward_K_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5MoreData.forwardK = true := by
  decide +kernel

theorem forward_K_checked :
    checkRows PilotData.data Child5MoreData.forwardK Child5BodyData.labels501 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_K_labels_checked, forward_K_children_checked⟩

theorem forward_K_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5MoreData.forwardK.map Row.event) Child5BodyData.labels501 :=
  checkRows_wellLabelled PilotData.data Child5MoreData.forwardK
    Child5BodyData.labels501 forward_K_checked

theorem forward_support525 :
    (Child5MoreData.forwardK.map Row.event).all
      (Boundary192.supportedB Child5MoreData.new525) = true := by decide +kernel

theorem forward_touched525 :
    Child5MoreData.new525.all (fun r =>
      LemmaG.Stream.labRun (Child5MoreData.forwardK.map Row.event) Child5BodyData.labels501 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint525 :
    LemmaG.Stream.labRun (Child5MoreData.forwardK.map Row.event) Child5BodyData.labels501 =
      Child5MoreData.labels525 :=
  SparseValues.sparse_checkpoint Child5MoreData.forwardK Child5BodyData.labels501
    (fun _ => (7 : FrameLabel)) Child5MoreData.new525 forward_support525 forward_touched525

theorem forward_composed_wellLabelled525 :
    LemmaG.Stream.WellLabelled (((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5BodyCheck.forward_composed_wellLabelled501, ?_⟩
  rw [Child5BodyCheck.forward_composed_checkpoint501]
  exact forward_K_wellLabelled

theorem forward_composed_checkpoint525 :
    LemmaG.Stream.labRun (((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK).map Row.event)
      (initialLabels PilotData.data) = Child5MoreData.labels525 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5BodyCheck.forward_composed_checkpoint501]
  exact forward_checkpoint525

theorem forward_L_labels_checked :
    CheckDecomposition.labelRowsB Child5MoreData.forwardL Child5MoreData.labels525 = true := by
  decide +kernel

theorem forward_L_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5MoreData.forwardL = true := by
  decide +kernel

theorem forward_L_checked :
    checkRows PilotData.data Child5MoreData.forwardL Child5MoreData.labels525 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_L_labels_checked, forward_L_children_checked⟩

theorem forward_L_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5MoreData.forwardL.map Row.event) Child5MoreData.labels525 :=
  checkRows_wellLabelled PilotData.data Child5MoreData.forwardL
    Child5MoreData.labels525 forward_L_checked

theorem forward_support549 :
    (Child5MoreData.forwardL.map Row.event).all
      (Boundary192.supportedB Child5MoreData.new549) = true := by decide +kernel

theorem forward_touched549 :
    Child5MoreData.new549.all (fun r =>
      LemmaG.Stream.labRun (Child5MoreData.forwardL.map Row.event) Child5MoreData.labels525 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint549 :
    LemmaG.Stream.labRun (Child5MoreData.forwardL.map Row.event) Child5MoreData.labels525 =
      Child5MoreData.labels549 :=
  SparseValues.sparse_checkpoint Child5MoreData.forwardL Child5MoreData.labels525
    (fun _ => (7 : FrameLabel)) Child5MoreData.new549 forward_support549 forward_touched549

theorem forward_composed_wellLabelled549 :
    LemmaG.Stream.WellLabelled ((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled525, ?_⟩
  rw [forward_composed_checkpoint525]
  exact forward_L_wellLabelled

theorem forward_composed_checkpoint549 :
    LemmaG.Stream.labRun ((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL).map Row.event)
      (initialLabels PilotData.data) = Child5MoreData.labels549 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint525]
  exact forward_checkpoint549

theorem backward_K_labels_checked :
    CheckDecomposition.labelRowsB Child5MoreData.backwardK Child5BodyData.labels501 = true := by
  decide +kernel

theorem backward_K_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5MoreData.backwardK = true := by
  decide +kernel

theorem backward_K_checked :
    checkRows PilotData.data Child5MoreData.backwardK Child5BodyData.labels501 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_K_labels_checked, backward_K_children_checked⟩

theorem backward_K_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5MoreData.backwardK.map Row.event) Child5BodyData.labels501 :=
  checkRows_wellLabelled PilotData.data Child5MoreData.backwardK
    Child5BodyData.labels501 backward_K_checked

theorem backward_support525 :
    (Child5MoreData.backwardK.map Row.event).all
      (Boundary192.supportedB Child5MoreData.new525) = true := by decide +kernel

theorem backward_touched525 :
    Child5MoreData.new525.all (fun r =>
      LemmaG.Stream.labRun (Child5MoreData.backwardK.map Row.event) Child5BodyData.labels501 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint525 :
    LemmaG.Stream.labRun (Child5MoreData.backwardK.map Row.event) Child5BodyData.labels501 =
      Child5MoreData.labels525 :=
  SparseValues.sparse_checkpoint Child5MoreData.backwardK Child5BodyData.labels501
    (fun _ => (7 : FrameLabel)) Child5MoreData.new525 backward_support525 backward_touched525

theorem backward_composed_wellLabelled525 :
    LemmaG.Stream.WellLabelled (((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5BodyCheck.backward_composed_wellLabelled501, ?_⟩
  rw [Child5BodyCheck.backward_composed_checkpoint501]
  exact backward_K_wellLabelled

theorem backward_composed_checkpoint525 :
    LemmaG.Stream.labRun (((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK).map Row.event)
      (initialLabels PilotData.data) = Child5MoreData.labels525 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5BodyCheck.backward_composed_checkpoint501]
  exact backward_checkpoint525

theorem backward_L_labels_checked :
    CheckDecomposition.labelRowsB Child5MoreData.backwardL Child5MoreData.labels525 = true := by
  decide +kernel

theorem backward_L_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5MoreData.backwardL = true := by
  decide +kernel

theorem backward_L_checked :
    checkRows PilotData.data Child5MoreData.backwardL Child5MoreData.labels525 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_L_labels_checked, backward_L_children_checked⟩

theorem backward_L_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5MoreData.backwardL.map Row.event) Child5MoreData.labels525 :=
  checkRows_wellLabelled PilotData.data Child5MoreData.backwardL
    Child5MoreData.labels525 backward_L_checked

theorem backward_support549 :
    (Child5MoreData.backwardL.map Row.event).all
      (Boundary192.supportedB Child5MoreData.new549) = true := by decide +kernel

theorem backward_touched549 :
    Child5MoreData.new549.all (fun r =>
      LemmaG.Stream.labRun (Child5MoreData.backwardL.map Row.event) Child5MoreData.labels525 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint549 :
    LemmaG.Stream.labRun (Child5MoreData.backwardL.map Row.event) Child5MoreData.labels525 =
      Child5MoreData.labels549 :=
  SparseValues.sparse_checkpoint Child5MoreData.backwardL Child5MoreData.labels525
    (fun _ => (7 : FrameLabel)) Child5MoreData.new549 backward_support549 backward_touched549

theorem backward_composed_wellLabelled549 :
    LemmaG.Stream.WellLabelled ((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled525, ?_⟩
  rw [backward_composed_checkpoint525]
  exact backward_L_wellLabelled

theorem backward_composed_checkpoint549 :
    LemmaG.Stream.labRun ((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL).map Row.event)
      (initialLabels PilotData.data) = Child5MoreData.labels549 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint525]
  exact backward_checkpoint549

#print axioms exact_K_source_indices
#print axioms exact_L_source_indices
#print axioms forward_K_labels_checked
#print axioms forward_K_children_checked
#print axioms forward_K_checked
#print axioms forward_K_wellLabelled
#print axioms forward_support525
#print axioms forward_touched525
#print axioms forward_checkpoint525
#print axioms forward_composed_wellLabelled525
#print axioms forward_composed_checkpoint525
#print axioms forward_L_labels_checked
#print axioms forward_L_children_checked
#print axioms forward_L_checked
#print axioms forward_L_wellLabelled
#print axioms forward_support549
#print axioms forward_touched549
#print axioms forward_checkpoint549
#print axioms forward_composed_wellLabelled549
#print axioms forward_composed_checkpoint549
#print axioms backward_K_labels_checked
#print axioms backward_K_children_checked
#print axioms backward_K_checked
#print axioms backward_K_wellLabelled
#print axioms backward_support525
#print axioms backward_touched525
#print axioms backward_checkpoint525
#print axioms backward_composed_wellLabelled525
#print axioms backward_composed_checkpoint525
#print axioms backward_L_labels_checked
#print axioms backward_L_children_checked
#print axioms backward_L_checked
#print axioms backward_L_wellLabelled
#print axioms backward_support549
#print axioms backward_touched549
#print axioms backward_checkpoint549
#print axioms backward_composed_wellLabelled549
#print axioms backward_composed_checkpoint549
end CurrentMain.F19SelectedCoverage.Child5MoreCheck
