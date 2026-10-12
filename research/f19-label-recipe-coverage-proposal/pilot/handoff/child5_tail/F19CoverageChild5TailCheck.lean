/- Scoped selected-source label/canonical-recipe coverage. No physical/operator claim. -/
import F19CoverageChild5TailData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Child5TailCheck
open CurrentMain.F19SelectedCoverage

theorem exact_G_source_indices :
    Child5TailData.forwardG.map Row.sourceIndex = List.range' 11260 24 ∧
    Child5TailData.backwardG.map Row.sourceIndex = List.range' 11260 24 := by
  decide +kernel

theorem exact_H_source_indices :
    Child5TailData.forwardH.map Row.sourceIndex = List.range' 11284 24 ∧
    Child5TailData.backwardH.map Row.sourceIndex = List.range' 11284 24 := by
  decide +kernel

theorem forward_G_labels_checked :
    CheckDecomposition.labelRowsB Child5TailData.forwardG Child5Data.labels409 = true := by
  decide +kernel

theorem forward_G_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5TailData.forwardG = true := by
  decide +kernel

theorem forward_G_checked :
    checkRows PilotData.data Child5TailData.forwardG Child5Data.labels409 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_G_labels_checked, forward_G_children_checked⟩

theorem forward_G_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5TailData.forwardG.map Row.event) Child5Data.labels409 :=
  checkRows_wellLabelled PilotData.data Child5TailData.forwardG
    Child5Data.labels409 forward_G_checked

theorem forward_support433 :
    (Child5TailData.forwardG.map Row.event).all
      (Boundary192.supportedB Child5TailData.new433) = true := by decide +kernel

theorem forward_touched433 :
    Child5TailData.new433.all (fun r =>
      LemmaG.Stream.labRun (Child5TailData.forwardG.map Row.event) Child5Data.labels409 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint433 :
    LemmaG.Stream.labRun (Child5TailData.forwardG.map Row.event) Child5Data.labels409 =
      Child5TailData.labels433 :=
  SparseValues.sparse_checkpoint Child5TailData.forwardG Child5Data.labels409
    (fun _ => (7 : FrameLabel)) Child5TailData.new433 forward_support433 forward_touched433

theorem forward_composed_wellLabelled433 :
    LemmaG.Stream.WellLabelled (((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5Check.forward_composed_wellLabelled409, ?_⟩
  rw [Child5Check.forward_composed_checkpoint409]
  exact forward_G_wellLabelled

theorem forward_composed_checkpoint433 :
    LemmaG.Stream.labRun (((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG).map Row.event)
      (initialLabels PilotData.data) = Child5TailData.labels433 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5Check.forward_composed_checkpoint409]
  exact forward_checkpoint433

theorem forward_H_labels_checked :
    CheckDecomposition.labelRowsB Child5TailData.forwardH Child5TailData.labels433 = true := by
  decide +kernel

theorem forward_H_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5TailData.forwardH = true := by
  decide +kernel

theorem forward_H_checked :
    checkRows PilotData.data Child5TailData.forwardH Child5TailData.labels433 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_H_labels_checked, forward_H_children_checked⟩

theorem forward_H_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5TailData.forwardH.map Row.event) Child5TailData.labels433 :=
  checkRows_wellLabelled PilotData.data Child5TailData.forwardH
    Child5TailData.labels433 forward_H_checked

theorem forward_support457 :
    (Child5TailData.forwardH.map Row.event).all
      (Boundary192.supportedB Child5TailData.new457) = true := by decide +kernel

theorem forward_touched457 :
    Child5TailData.new457.all (fun r =>
      LemmaG.Stream.labRun (Child5TailData.forwardH.map Row.event) Child5TailData.labels433 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint457 :
    LemmaG.Stream.labRun (Child5TailData.forwardH.map Row.event) Child5TailData.labels433 =
      Child5TailData.labels457 :=
  SparseValues.sparse_checkpoint Child5TailData.forwardH Child5TailData.labels433
    (fun _ => (7 : FrameLabel)) Child5TailData.new457 forward_support457 forward_touched457

theorem forward_composed_wellLabelled457 :
    LemmaG.Stream.WellLabelled ((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled433, ?_⟩
  rw [forward_composed_checkpoint433]
  exact forward_H_wellLabelled

theorem forward_composed_checkpoint457 :
    LemmaG.Stream.labRun ((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH).map Row.event)
      (initialLabels PilotData.data) = Child5TailData.labels457 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint433]
  exact forward_checkpoint457

theorem backward_G_labels_checked :
    CheckDecomposition.labelRowsB Child5TailData.backwardG Child5Data.labels409 = true := by
  decide +kernel

theorem backward_G_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5TailData.backwardG = true := by
  decide +kernel

theorem backward_G_checked :
    checkRows PilotData.data Child5TailData.backwardG Child5Data.labels409 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_G_labels_checked, backward_G_children_checked⟩

theorem backward_G_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5TailData.backwardG.map Row.event) Child5Data.labels409 :=
  checkRows_wellLabelled PilotData.data Child5TailData.backwardG
    Child5Data.labels409 backward_G_checked

theorem backward_support433 :
    (Child5TailData.backwardG.map Row.event).all
      (Boundary192.supportedB Child5TailData.new433) = true := by decide +kernel

theorem backward_touched433 :
    Child5TailData.new433.all (fun r =>
      LemmaG.Stream.labRun (Child5TailData.backwardG.map Row.event) Child5Data.labels409 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint433 :
    LemmaG.Stream.labRun (Child5TailData.backwardG.map Row.event) Child5Data.labels409 =
      Child5TailData.labels433 :=
  SparseValues.sparse_checkpoint Child5TailData.backwardG Child5Data.labels409
    (fun _ => (7 : FrameLabel)) Child5TailData.new433 backward_support433 backward_touched433

theorem backward_composed_wellLabelled433 :
    LemmaG.Stream.WellLabelled (((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5Check.backward_composed_wellLabelled409, ?_⟩
  rw [Child5Check.backward_composed_checkpoint409]
  exact backward_G_wellLabelled

theorem backward_composed_checkpoint433 :
    LemmaG.Stream.labRun (((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG).map Row.event)
      (initialLabels PilotData.data) = Child5TailData.labels433 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5Check.backward_composed_checkpoint409]
  exact backward_checkpoint433

theorem backward_H_labels_checked :
    CheckDecomposition.labelRowsB Child5TailData.backwardH Child5TailData.labels433 = true := by
  decide +kernel

theorem backward_H_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5TailData.backwardH = true := by
  decide +kernel

theorem backward_H_checked :
    checkRows PilotData.data Child5TailData.backwardH Child5TailData.labels433 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_H_labels_checked, backward_H_children_checked⟩

theorem backward_H_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5TailData.backwardH.map Row.event) Child5TailData.labels433 :=
  checkRows_wellLabelled PilotData.data Child5TailData.backwardH
    Child5TailData.labels433 backward_H_checked

theorem backward_support457 :
    (Child5TailData.backwardH.map Row.event).all
      (Boundary192.supportedB Child5TailData.new457) = true := by decide +kernel

theorem backward_touched457 :
    Child5TailData.new457.all (fun r =>
      LemmaG.Stream.labRun (Child5TailData.backwardH.map Row.event) Child5TailData.labels433 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint457 :
    LemmaG.Stream.labRun (Child5TailData.backwardH.map Row.event) Child5TailData.labels433 =
      Child5TailData.labels457 :=
  SparseValues.sparse_checkpoint Child5TailData.backwardH Child5TailData.labels433
    (fun _ => (7 : FrameLabel)) Child5TailData.new457 backward_support457 backward_touched457

theorem backward_composed_wellLabelled457 :
    LemmaG.Stream.WellLabelled ((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled433, ?_⟩
  rw [backward_composed_checkpoint433]
  exact backward_H_wellLabelled

theorem backward_composed_checkpoint457 :
    LemmaG.Stream.labRun ((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH).map Row.event)
      (initialLabels PilotData.data) = Child5TailData.labels457 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint433]
  exact backward_checkpoint457

#print axioms exact_G_source_indices
#print axioms exact_H_source_indices
#print axioms forward_G_labels_checked
#print axioms forward_G_children_checked
#print axioms forward_G_checked
#print axioms forward_G_wellLabelled
#print axioms forward_support433
#print axioms forward_touched433
#print axioms forward_checkpoint433
#print axioms forward_composed_wellLabelled433
#print axioms forward_composed_checkpoint433
#print axioms forward_H_labels_checked
#print axioms forward_H_children_checked
#print axioms forward_H_checked
#print axioms forward_H_wellLabelled
#print axioms forward_support457
#print axioms forward_touched457
#print axioms forward_checkpoint457
#print axioms forward_composed_wellLabelled457
#print axioms forward_composed_checkpoint457
#print axioms backward_G_labels_checked
#print axioms backward_G_children_checked
#print axioms backward_G_checked
#print axioms backward_G_wellLabelled
#print axioms backward_support433
#print axioms backward_touched433
#print axioms backward_checkpoint433
#print axioms backward_composed_wellLabelled433
#print axioms backward_composed_checkpoint433
#print axioms backward_H_labels_checked
#print axioms backward_H_children_checked
#print axioms backward_H_checked
#print axioms backward_H_wellLabelled
#print axioms backward_support457
#print axioms backward_touched457
#print axioms backward_checkpoint457
#print axioms backward_composed_wellLabelled457
#print axioms backward_composed_checkpoint457
end CurrentMain.F19SelectedCoverage.Child5TailCheck
