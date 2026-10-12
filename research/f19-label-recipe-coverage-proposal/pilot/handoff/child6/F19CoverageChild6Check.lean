/- Scoped selected-source label/canonical-recipe coverage. No physical/operator claim. -/
import F19CoverageChild6Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Child6Check
open CurrentMain.F19SelectedCoverage

theorem exact_S_source_indices :
    Child6Data.forwardS.map Row.sourceIndex = List.range' 11546 24 ∧
    Child6Data.backwardS.map Row.sourceIndex = List.range' 11546 24 := by
  decide +kernel

theorem exact_T_source_indices :
    Child6Data.forwardT.map Row.sourceIndex = List.range' 11570 24 ∧
    Child6Data.backwardT.map Row.sourceIndex = List.range' 11570 24 := by
  decide +kernel

theorem forward_S_labels_checked :
    CheckDecomposition.labelRowsB Child6Data.forwardS StaticGapData.labels695 = true := by
  decide +kernel

theorem forward_S_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child6Data.forwardS = true := by
  decide +kernel

theorem forward_S_checked :
    checkRows PilotData.data Child6Data.forwardS StaticGapData.labels695 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_S_labels_checked, forward_S_children_checked⟩

theorem forward_S_wellLabelled :
    LemmaG.Stream.WellLabelled (Child6Data.forwardS.map Row.event) StaticGapData.labels695 :=
  checkRows_wellLabelled PilotData.data Child6Data.forwardS
    StaticGapData.labels695 forward_S_checked

theorem forward_support719 :
    (Child6Data.forwardS.map Row.event).all
      (Boundary192.supportedB Child6Data.new719) = true := by decide +kernel

theorem forward_touched719 :
    Child6Data.new719.all (fun r =>
      LemmaG.Stream.labRun (Child6Data.forwardS.map Row.event) StaticGapData.labels695 r ==
        (8 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint719 :
    LemmaG.Stream.labRun (Child6Data.forwardS.map Row.event) StaticGapData.labels695 =
      Child6Data.labels719 :=
  SparseValues.sparse_checkpoint Child6Data.forwardS StaticGapData.labels695
    (fun _ => (8 : FrameLabel)) Child6Data.new719 forward_support719 forward_touched719

theorem forward_composed_wellLabelled719 :
    LemmaG.Stream.WellLabelled (((((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ) ++ StaticGapData.forwardR) ++ Child6Data.forwardS).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨StaticGapCheckB.forward_composed_wellLabelled695, ?_⟩
  rw [StaticGapCheckB.forward_composed_checkpoint695]
  exact forward_S_wellLabelled

theorem forward_composed_checkpoint719 :
    LemmaG.Stream.labRun (((((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ) ++ StaticGapData.forwardR) ++ Child6Data.forwardS).map Row.event)
      (initialLabels PilotData.data) = Child6Data.labels719 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, StaticGapCheckB.forward_composed_checkpoint695]
  exact forward_checkpoint719

theorem forward_T_labels_checked :
    CheckDecomposition.labelRowsB Child6Data.forwardT Child6Data.labels719 = true := by
  decide +kernel

theorem forward_T_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child6Data.forwardT = true := by
  decide +kernel

theorem forward_T_checked :
    checkRows PilotData.data Child6Data.forwardT Child6Data.labels719 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_T_labels_checked, forward_T_children_checked⟩

theorem forward_T_wellLabelled :
    LemmaG.Stream.WellLabelled (Child6Data.forwardT.map Row.event) Child6Data.labels719 :=
  checkRows_wellLabelled PilotData.data Child6Data.forwardT
    Child6Data.labels719 forward_T_checked

theorem forward_support743 :
    (Child6Data.forwardT.map Row.event).all
      (Boundary192.supportedB Child6Data.new743) = true := by decide +kernel

theorem forward_touched743 :
    Child6Data.new743.all (fun r =>
      LemmaG.Stream.labRun (Child6Data.forwardT.map Row.event) Child6Data.labels719 r ==
        (8 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint743 :
    LemmaG.Stream.labRun (Child6Data.forwardT.map Row.event) Child6Data.labels719 =
      Child6Data.labels743 :=
  SparseValues.sparse_checkpoint Child6Data.forwardT Child6Data.labels719
    (fun _ => (8 : FrameLabel)) Child6Data.new743 forward_support743 forward_touched743

theorem forward_composed_wellLabelled743 :
    LemmaG.Stream.WellLabelled ((((((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ) ++ StaticGapData.forwardR) ++ Child6Data.forwardS) ++ Child6Data.forwardT).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled719, ?_⟩
  rw [forward_composed_checkpoint719]
  exact forward_T_wellLabelled

theorem forward_composed_checkpoint743 :
    LemmaG.Stream.labRun ((((((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ) ++ StaticGapData.forwardR) ++ Child6Data.forwardS) ++ Child6Data.forwardT).map Row.event)
      (initialLabels PilotData.data) = Child6Data.labels743 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint719]
  exact forward_checkpoint743

theorem backward_S_labels_checked :
    CheckDecomposition.labelRowsB Child6Data.backwardS StaticGapData.labels695 = true := by
  decide +kernel

theorem backward_S_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child6Data.backwardS = true := by
  decide +kernel

theorem backward_S_checked :
    checkRows PilotData.data Child6Data.backwardS StaticGapData.labels695 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_S_labels_checked, backward_S_children_checked⟩

theorem backward_S_wellLabelled :
    LemmaG.Stream.WellLabelled (Child6Data.backwardS.map Row.event) StaticGapData.labels695 :=
  checkRows_wellLabelled PilotData.data Child6Data.backwardS
    StaticGapData.labels695 backward_S_checked

theorem backward_support719 :
    (Child6Data.backwardS.map Row.event).all
      (Boundary192.supportedB Child6Data.new719) = true := by decide +kernel

theorem backward_touched719 :
    Child6Data.new719.all (fun r =>
      LemmaG.Stream.labRun (Child6Data.backwardS.map Row.event) StaticGapData.labels695 r ==
        (8 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint719 :
    LemmaG.Stream.labRun (Child6Data.backwardS.map Row.event) StaticGapData.labels695 =
      Child6Data.labels719 :=
  SparseValues.sparse_checkpoint Child6Data.backwardS StaticGapData.labels695
    (fun _ => (8 : FrameLabel)) Child6Data.new719 backward_support719 backward_touched719

theorem backward_composed_wellLabelled719 :
    LemmaG.Stream.WellLabelled (((((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ) ++ StaticGapData.backwardR) ++ Child6Data.backwardS).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨StaticGapCheckB.backward_composed_wellLabelled695, ?_⟩
  rw [StaticGapCheckB.backward_composed_checkpoint695]
  exact backward_S_wellLabelled

theorem backward_composed_checkpoint719 :
    LemmaG.Stream.labRun (((((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ) ++ StaticGapData.backwardR) ++ Child6Data.backwardS).map Row.event)
      (initialLabels PilotData.data) = Child6Data.labels719 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, StaticGapCheckB.backward_composed_checkpoint695]
  exact backward_checkpoint719

theorem backward_T_labels_checked :
    CheckDecomposition.labelRowsB Child6Data.backwardT Child6Data.labels719 = true := by
  decide +kernel

theorem backward_T_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child6Data.backwardT = true := by
  decide +kernel

theorem backward_T_checked :
    checkRows PilotData.data Child6Data.backwardT Child6Data.labels719 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_T_labels_checked, backward_T_children_checked⟩

theorem backward_T_wellLabelled :
    LemmaG.Stream.WellLabelled (Child6Data.backwardT.map Row.event) Child6Data.labels719 :=
  checkRows_wellLabelled PilotData.data Child6Data.backwardT
    Child6Data.labels719 backward_T_checked

theorem backward_support743 :
    (Child6Data.backwardT.map Row.event).all
      (Boundary192.supportedB Child6Data.new743) = true := by decide +kernel

theorem backward_touched743 :
    Child6Data.new743.all (fun r =>
      LemmaG.Stream.labRun (Child6Data.backwardT.map Row.event) Child6Data.labels719 r ==
        (8 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint743 :
    LemmaG.Stream.labRun (Child6Data.backwardT.map Row.event) Child6Data.labels719 =
      Child6Data.labels743 :=
  SparseValues.sparse_checkpoint Child6Data.backwardT Child6Data.labels719
    (fun _ => (8 : FrameLabel)) Child6Data.new743 backward_support743 backward_touched743

theorem backward_composed_wellLabelled743 :
    LemmaG.Stream.WellLabelled ((((((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ) ++ StaticGapData.backwardR) ++ Child6Data.backwardS) ++ Child6Data.backwardT).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled719, ?_⟩
  rw [backward_composed_checkpoint719]
  exact backward_T_wellLabelled

theorem backward_composed_checkpoint743 :
    LemmaG.Stream.labRun ((((((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ) ++ StaticGapData.backwardR) ++ Child6Data.backwardS) ++ Child6Data.backwardT).map Row.event)
      (initialLabels PilotData.data) = Child6Data.labels743 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint719]
  exact backward_checkpoint743

#print axioms exact_S_source_indices
#print axioms exact_T_source_indices
#print axioms forward_S_labels_checked
#print axioms forward_S_children_checked
#print axioms forward_S_checked
#print axioms forward_S_wellLabelled
#print axioms forward_support719
#print axioms forward_touched719
#print axioms forward_checkpoint719
#print axioms forward_composed_wellLabelled719
#print axioms forward_composed_checkpoint719
#print axioms forward_T_labels_checked
#print axioms forward_T_children_checked
#print axioms forward_T_checked
#print axioms forward_T_wellLabelled
#print axioms forward_support743
#print axioms forward_touched743
#print axioms forward_checkpoint743
#print axioms forward_composed_wellLabelled743
#print axioms forward_composed_checkpoint743
#print axioms backward_S_labels_checked
#print axioms backward_S_children_checked
#print axioms backward_S_checked
#print axioms backward_S_wellLabelled
#print axioms backward_support719
#print axioms backward_touched719
#print axioms backward_checkpoint719
#print axioms backward_composed_wellLabelled719
#print axioms backward_composed_checkpoint719
#print axioms backward_T_labels_checked
#print axioms backward_T_children_checked
#print axioms backward_T_checked
#print axioms backward_T_wellLabelled
#print axioms backward_support743
#print axioms backward_touched743
#print axioms backward_checkpoint743
#print axioms backward_composed_wellLabelled743
#print axioms backward_composed_checkpoint743
end CurrentMain.F19SelectedCoverage.Child6Check
