/- Scoped selected-source label/canonical-recipe coverage. No physical/operator claim. -/
import F19CoverageChild5BodyData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Child5BodyCheck
open CurrentMain.F19SelectedCoverage

theorem exact_I_source_indices :
    Child5BodyData.forwardI.map Row.sourceIndex = List.range' 11308 24 ∧
    Child5BodyData.backwardI.map Row.sourceIndex = List.range' 11308 24 := by
  decide +kernel

theorem exact_J_source_indices :
    Child5BodyData.forwardJ.map Row.sourceIndex = List.range' 11332 20 ∧
    Child5BodyData.backwardJ.map Row.sourceIndex = List.range' 11332 20 := by
  decide +kernel

theorem forward_I_labels_checked :
    CheckDecomposition.labelRowsB Child5BodyData.forwardI Child5TailData.labels457 = true := by
  decide +kernel

theorem forward_I_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5BodyData.forwardI = true := by
  decide +kernel

theorem forward_I_checked :
    checkRows PilotData.data Child5BodyData.forwardI Child5TailData.labels457 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_I_labels_checked, forward_I_children_checked⟩

theorem forward_I_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5BodyData.forwardI.map Row.event) Child5TailData.labels457 :=
  checkRows_wellLabelled PilotData.data Child5BodyData.forwardI
    Child5TailData.labels457 forward_I_checked

theorem forward_support481 :
    (Child5BodyData.forwardI.map Row.event).all
      (Boundary192.supportedB Child5BodyData.new481) = true := by decide +kernel

theorem forward_touched481 :
    Child5BodyData.new481.all (fun r =>
      LemmaG.Stream.labRun (Child5BodyData.forwardI.map Row.event) Child5TailData.labels457 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint481 :
    LemmaG.Stream.labRun (Child5BodyData.forwardI.map Row.event) Child5TailData.labels457 =
      Child5BodyData.labels481 :=
  SparseValues.sparse_checkpoint Child5BodyData.forwardI Child5TailData.labels457
    (fun _ => (7 : FrameLabel)) Child5BodyData.new481 forward_support481 forward_touched481

theorem forward_composed_wellLabelled481 :
    LemmaG.Stream.WellLabelled (((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5TailCheck.forward_composed_wellLabelled457, ?_⟩
  rw [Child5TailCheck.forward_composed_checkpoint457]
  exact forward_I_wellLabelled

theorem forward_composed_checkpoint481 :
    LemmaG.Stream.labRun (((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI).map Row.event)
      (initialLabels PilotData.data) = Child5BodyData.labels481 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5TailCheck.forward_composed_checkpoint457]
  exact forward_checkpoint481

theorem forward_J_labels_checked :
    CheckDecomposition.labelRowsB Child5BodyData.forwardJ Child5BodyData.labels481 = true := by
  decide +kernel

theorem forward_J_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5BodyData.forwardJ = true := by
  decide +kernel

theorem forward_J_checked :
    checkRows PilotData.data Child5BodyData.forwardJ Child5BodyData.labels481 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_J_labels_checked, forward_J_children_checked⟩

theorem forward_J_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5BodyData.forwardJ.map Row.event) Child5BodyData.labels481 :=
  checkRows_wellLabelled PilotData.data Child5BodyData.forwardJ
    Child5BodyData.labels481 forward_J_checked

theorem forward_support501 :
    (Child5BodyData.forwardJ.map Row.event).all
      (Boundary192.supportedB Child5BodyData.new501) = true := by decide +kernel

theorem forward_touched501 :
    Child5BodyData.new501.all (fun r =>
      LemmaG.Stream.labRun (Child5BodyData.forwardJ.map Row.event) Child5BodyData.labels481 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint501 :
    LemmaG.Stream.labRun (Child5BodyData.forwardJ.map Row.event) Child5BodyData.labels481 =
      Child5BodyData.labels501 :=
  SparseValues.sparse_checkpoint Child5BodyData.forwardJ Child5BodyData.labels481
    (fun _ => (7 : FrameLabel)) Child5BodyData.new501 forward_support501 forward_touched501

theorem forward_composed_wellLabelled501 :
    LemmaG.Stream.WellLabelled ((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled481, ?_⟩
  rw [forward_composed_checkpoint481]
  exact forward_J_wellLabelled

theorem forward_composed_checkpoint501 :
    LemmaG.Stream.labRun ((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ).map Row.event)
      (initialLabels PilotData.data) = Child5BodyData.labels501 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint481]
  exact forward_checkpoint501

theorem backward_I_labels_checked :
    CheckDecomposition.labelRowsB Child5BodyData.backwardI Child5TailData.labels457 = true := by
  decide +kernel

theorem backward_I_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5BodyData.backwardI = true := by
  decide +kernel

theorem backward_I_checked :
    checkRows PilotData.data Child5BodyData.backwardI Child5TailData.labels457 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_I_labels_checked, backward_I_children_checked⟩

theorem backward_I_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5BodyData.backwardI.map Row.event) Child5TailData.labels457 :=
  checkRows_wellLabelled PilotData.data Child5BodyData.backwardI
    Child5TailData.labels457 backward_I_checked

theorem backward_support481 :
    (Child5BodyData.backwardI.map Row.event).all
      (Boundary192.supportedB Child5BodyData.new481) = true := by decide +kernel

theorem backward_touched481 :
    Child5BodyData.new481.all (fun r =>
      LemmaG.Stream.labRun (Child5BodyData.backwardI.map Row.event) Child5TailData.labels457 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint481 :
    LemmaG.Stream.labRun (Child5BodyData.backwardI.map Row.event) Child5TailData.labels457 =
      Child5BodyData.labels481 :=
  SparseValues.sparse_checkpoint Child5BodyData.backwardI Child5TailData.labels457
    (fun _ => (7 : FrameLabel)) Child5BodyData.new481 backward_support481 backward_touched481

theorem backward_composed_wellLabelled481 :
    LemmaG.Stream.WellLabelled (((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5TailCheck.backward_composed_wellLabelled457, ?_⟩
  rw [Child5TailCheck.backward_composed_checkpoint457]
  exact backward_I_wellLabelled

theorem backward_composed_checkpoint481 :
    LemmaG.Stream.labRun (((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI).map Row.event)
      (initialLabels PilotData.data) = Child5BodyData.labels481 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5TailCheck.backward_composed_checkpoint457]
  exact backward_checkpoint481

theorem backward_J_labels_checked :
    CheckDecomposition.labelRowsB Child5BodyData.backwardJ Child5BodyData.labels481 = true := by
  decide +kernel

theorem backward_J_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5BodyData.backwardJ = true := by
  decide +kernel

theorem backward_J_checked :
    checkRows PilotData.data Child5BodyData.backwardJ Child5BodyData.labels481 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_J_labels_checked, backward_J_children_checked⟩

theorem backward_J_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5BodyData.backwardJ.map Row.event) Child5BodyData.labels481 :=
  checkRows_wellLabelled PilotData.data Child5BodyData.backwardJ
    Child5BodyData.labels481 backward_J_checked

theorem backward_support501 :
    (Child5BodyData.backwardJ.map Row.event).all
      (Boundary192.supportedB Child5BodyData.new501) = true := by decide +kernel

theorem backward_touched501 :
    Child5BodyData.new501.all (fun r =>
      LemmaG.Stream.labRun (Child5BodyData.backwardJ.map Row.event) Child5BodyData.labels481 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint501 :
    LemmaG.Stream.labRun (Child5BodyData.backwardJ.map Row.event) Child5BodyData.labels481 =
      Child5BodyData.labels501 :=
  SparseValues.sparse_checkpoint Child5BodyData.backwardJ Child5BodyData.labels481
    (fun _ => (7 : FrameLabel)) Child5BodyData.new501 backward_support501 backward_touched501

theorem backward_composed_wellLabelled501 :
    LemmaG.Stream.WellLabelled ((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled481, ?_⟩
  rw [backward_composed_checkpoint481]
  exact backward_J_wellLabelled

theorem backward_composed_checkpoint501 :
    LemmaG.Stream.labRun ((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ).map Row.event)
      (initialLabels PilotData.data) = Child5BodyData.labels501 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint481]
  exact backward_checkpoint501

#print axioms exact_I_source_indices
#print axioms exact_J_source_indices
#print axioms forward_I_labels_checked
#print axioms forward_I_children_checked
#print axioms forward_I_checked
#print axioms forward_I_wellLabelled
#print axioms forward_support481
#print axioms forward_touched481
#print axioms forward_checkpoint481
#print axioms forward_composed_wellLabelled481
#print axioms forward_composed_checkpoint481
#print axioms forward_J_labels_checked
#print axioms forward_J_children_checked
#print axioms forward_J_checked
#print axioms forward_J_wellLabelled
#print axioms forward_support501
#print axioms forward_touched501
#print axioms forward_checkpoint501
#print axioms forward_composed_wellLabelled501
#print axioms forward_composed_checkpoint501
#print axioms backward_I_labels_checked
#print axioms backward_I_children_checked
#print axioms backward_I_checked
#print axioms backward_I_wellLabelled
#print axioms backward_support481
#print axioms backward_touched481
#print axioms backward_checkpoint481
#print axioms backward_composed_wellLabelled481
#print axioms backward_composed_checkpoint481
#print axioms backward_J_labels_checked
#print axioms backward_J_children_checked
#print axioms backward_J_checked
#print axioms backward_J_wellLabelled
#print axioms backward_support501
#print axioms backward_touched501
#print axioms backward_checkpoint501
#print axioms backward_composed_wellLabelled501
#print axioms backward_composed_checkpoint501
end CurrentMain.F19SelectedCoverage.Child5BodyCheck
