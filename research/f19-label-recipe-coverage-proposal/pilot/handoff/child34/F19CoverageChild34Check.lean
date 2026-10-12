/- Scoped selected-source label/canonical-recipe coverage; no operator or omitted-adapter claim. -/
import F19CoverageChild34Data
import F19CoverageSparseValues

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Child34Check
open CurrentMain.F19SelectedCoverage

theorem exact_C_source_indices :
    Child34Data.forwardC.map Row.sourceIndex = List.range' 11171 24 ∧
    Child34Data.backwardC.map Row.sourceIndex = List.range' 11171 24 := by
  decide +kernel

theorem exact_D_source_indices :
    Child34Data.forwardD.map Row.sourceIndex = List.range' 11195 20 ∧
    Child34Data.backwardD.map Row.sourceIndex = List.range' 11195 20 := by
  decide +kernel

theorem forward_support320 :
    (BatchData.forwardB.map Row.event).all
      (Boundary192.supportedB Child34Data.new320) = true := by decide +kernel

theorem forward_touched320 :
    Child34Data.new320.all (fun r =>
      LemmaG.Stream.labRun (BatchData.forwardB.map Row.event) BatchData.labels256 r ==
        Child34Data.values320 r) = true := by decide +kernel

theorem forward_checkpoint320 :
    LemmaG.Stream.labRun (BatchData.forwardB.map Row.event) BatchData.labels256 =
      Child34Data.labels320 :=
  SparseValues.sparse_checkpoint BatchData.forwardB BatchData.labels256
    Child34Data.values320 Child34Data.new320 forward_support320 forward_touched320

theorem forward_composed_checkpoint320 :
    LemmaG.Stream.labRun ((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB).map Row.event)
      (initialLabels PilotData.data) = Child34Data.labels320 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, ChunkA.forward_composed_checkpoint256]
  exact forward_checkpoint320

theorem forward_C_labels_checked :
    CheckDecomposition.labelRowsB Child34Data.forwardC Child34Data.labels320 = true := by
  decide +kernel

theorem forward_C_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child34Data.forwardC = true := by
  decide +kernel

theorem forward_C_checked :
    checkRows PilotData.data Child34Data.forwardC Child34Data.labels320 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_C_labels_checked, forward_C_children_checked⟩

theorem forward_C_wellLabelled :
    LemmaG.Stream.WellLabelled (Child34Data.forwardC.map Row.event) Child34Data.labels320 :=
  checkRows_wellLabelled PilotData.data Child34Data.forwardC
    Child34Data.labels320 forward_C_checked

theorem forward_support344 :
    (Child34Data.forwardC.map Row.event).all
      (Boundary192.supportedB Child34Data.new344) = true := by decide +kernel

theorem forward_touched344 :
    Child34Data.new344.all (fun r =>
      LemmaG.Stream.labRun (Child34Data.forwardC.map Row.event) Child34Data.labels320 r ==
        (5 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint344 :
    LemmaG.Stream.labRun (Child34Data.forwardC.map Row.event) Child34Data.labels320 =
      Child34Data.labels344 :=
  SparseValues.sparse_checkpoint Child34Data.forwardC Child34Data.labels320
    (fun _ => (5 : FrameLabel)) Child34Data.new344 forward_support344 forward_touched344

theorem forward_composed_wellLabelled344 :
    LemmaG.Stream.WellLabelled (((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨ChunkBSplit.forward_composed_wellLabelled, ?_⟩
  rw [forward_composed_checkpoint320]
  exact forward_C_wellLabelled

theorem forward_composed_checkpoint344 :
    LemmaG.Stream.labRun (((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC).map Row.event)
      (initialLabels PilotData.data) = Child34Data.labels344 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint320]
  exact forward_checkpoint344

theorem forward_D_labels_checked :
    CheckDecomposition.labelRowsB Child34Data.forwardD Child34Data.labels344 = true := by
  decide +kernel

theorem forward_D_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child34Data.forwardD = true := by
  decide +kernel

theorem forward_D_checked :
    checkRows PilotData.data Child34Data.forwardD Child34Data.labels344 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_D_labels_checked, forward_D_children_checked⟩

theorem forward_D_wellLabelled :
    LemmaG.Stream.WellLabelled (Child34Data.forwardD.map Row.event) Child34Data.labels344 :=
  checkRows_wellLabelled PilotData.data Child34Data.forwardD
    Child34Data.labels344 forward_D_checked

theorem forward_support364 :
    (Child34Data.forwardD.map Row.event).all
      (Boundary192.supportedB Child34Data.new364) = true := by decide +kernel

theorem forward_touched364 :
    Child34Data.new364.all (fun r =>
      LemmaG.Stream.labRun (Child34Data.forwardD.map Row.event) Child34Data.labels344 r ==
        (6 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint364 :
    LemmaG.Stream.labRun (Child34Data.forwardD.map Row.event) Child34Data.labels344 =
      Child34Data.labels364 :=
  SparseValues.sparse_checkpoint Child34Data.forwardD Child34Data.labels344
    (fun _ => (6 : FrameLabel)) Child34Data.new364 forward_support364 forward_touched364

theorem forward_composed_wellLabelled364 :
    LemmaG.Stream.WellLabelled ((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled344, ?_⟩
  rw [forward_composed_checkpoint344]
  exact forward_D_wellLabelled

theorem forward_composed_checkpoint364 :
    LemmaG.Stream.labRun ((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD).map Row.event)
      (initialLabels PilotData.data) = Child34Data.labels364 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint344]
  exact forward_checkpoint364

theorem backward_support320 :
    (BatchData.backwardB.map Row.event).all
      (Boundary192.supportedB Child34Data.new320) = true := by decide +kernel

theorem backward_touched320 :
    Child34Data.new320.all (fun r =>
      LemmaG.Stream.labRun (BatchData.backwardB.map Row.event) BatchData.labels256 r ==
        Child34Data.values320 r) = true := by decide +kernel

theorem backward_checkpoint320 :
    LemmaG.Stream.labRun (BatchData.backwardB.map Row.event) BatchData.labels256 =
      Child34Data.labels320 :=
  SparseValues.sparse_checkpoint BatchData.backwardB BatchData.labels256
    Child34Data.values320 Child34Data.new320 backward_support320 backward_touched320

theorem backward_composed_checkpoint320 :
    LemmaG.Stream.labRun ((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB).map Row.event)
      (initialLabels PilotData.data) = Child34Data.labels320 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, ChunkA.backward_composed_checkpoint256]
  exact backward_checkpoint320

theorem backward_C_labels_checked :
    CheckDecomposition.labelRowsB Child34Data.backwardC Child34Data.labels320 = true := by
  decide +kernel

theorem backward_C_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child34Data.backwardC = true := by
  decide +kernel

theorem backward_C_checked :
    checkRows PilotData.data Child34Data.backwardC Child34Data.labels320 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_C_labels_checked, backward_C_children_checked⟩

theorem backward_C_wellLabelled :
    LemmaG.Stream.WellLabelled (Child34Data.backwardC.map Row.event) Child34Data.labels320 :=
  checkRows_wellLabelled PilotData.data Child34Data.backwardC
    Child34Data.labels320 backward_C_checked

theorem backward_support344 :
    (Child34Data.backwardC.map Row.event).all
      (Boundary192.supportedB Child34Data.new344) = true := by decide +kernel

theorem backward_touched344 :
    Child34Data.new344.all (fun r =>
      LemmaG.Stream.labRun (Child34Data.backwardC.map Row.event) Child34Data.labels320 r ==
        (5 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint344 :
    LemmaG.Stream.labRun (Child34Data.backwardC.map Row.event) Child34Data.labels320 =
      Child34Data.labels344 :=
  SparseValues.sparse_checkpoint Child34Data.backwardC Child34Data.labels320
    (fun _ => (5 : FrameLabel)) Child34Data.new344 backward_support344 backward_touched344

theorem backward_composed_wellLabelled344 :
    LemmaG.Stream.WellLabelled (((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨ChunkBSplit.backward_composed_wellLabelled, ?_⟩
  rw [backward_composed_checkpoint320]
  exact backward_C_wellLabelled

theorem backward_composed_checkpoint344 :
    LemmaG.Stream.labRun (((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC).map Row.event)
      (initialLabels PilotData.data) = Child34Data.labels344 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint320]
  exact backward_checkpoint344

theorem backward_D_labels_checked :
    CheckDecomposition.labelRowsB Child34Data.backwardD Child34Data.labels344 = true := by
  decide +kernel

theorem backward_D_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child34Data.backwardD = true := by
  decide +kernel

theorem backward_D_checked :
    checkRows PilotData.data Child34Data.backwardD Child34Data.labels344 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_D_labels_checked, backward_D_children_checked⟩

theorem backward_D_wellLabelled :
    LemmaG.Stream.WellLabelled (Child34Data.backwardD.map Row.event) Child34Data.labels344 :=
  checkRows_wellLabelled PilotData.data Child34Data.backwardD
    Child34Data.labels344 backward_D_checked

theorem backward_support364 :
    (Child34Data.backwardD.map Row.event).all
      (Boundary192.supportedB Child34Data.new364) = true := by decide +kernel

theorem backward_touched364 :
    Child34Data.new364.all (fun r =>
      LemmaG.Stream.labRun (Child34Data.backwardD.map Row.event) Child34Data.labels344 r ==
        (6 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint364 :
    LemmaG.Stream.labRun (Child34Data.backwardD.map Row.event) Child34Data.labels344 =
      Child34Data.labels364 :=
  SparseValues.sparse_checkpoint Child34Data.backwardD Child34Data.labels344
    (fun _ => (6 : FrameLabel)) Child34Data.new364 backward_support364 backward_touched364

theorem backward_composed_wellLabelled364 :
    LemmaG.Stream.WellLabelled ((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled344, ?_⟩
  rw [backward_composed_checkpoint344]
  exact backward_D_wellLabelled

theorem backward_composed_checkpoint364 :
    LemmaG.Stream.labRun ((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD).map Row.event)
      (initialLabels PilotData.data) = Child34Data.labels364 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint344]
  exact backward_checkpoint364


#print axioms exact_C_source_indices
#print axioms exact_D_source_indices
#print axioms forward_support320
#print axioms forward_touched320
#print axioms forward_checkpoint320
#print axioms forward_composed_checkpoint320
#print axioms forward_C_labels_checked
#print axioms forward_C_children_checked
#print axioms forward_C_checked
#print axioms forward_C_wellLabelled
#print axioms forward_support344
#print axioms forward_touched344
#print axioms forward_checkpoint344
#print axioms forward_composed_wellLabelled344
#print axioms forward_composed_checkpoint344
#print axioms forward_D_labels_checked
#print axioms forward_D_children_checked
#print axioms forward_D_checked
#print axioms forward_D_wellLabelled
#print axioms forward_support364
#print axioms forward_touched364
#print axioms forward_checkpoint364
#print axioms forward_composed_wellLabelled364
#print axioms forward_composed_checkpoint364
#print axioms backward_support320
#print axioms backward_touched320
#print axioms backward_checkpoint320
#print axioms backward_composed_checkpoint320
#print axioms backward_C_labels_checked
#print axioms backward_C_children_checked
#print axioms backward_C_checked
#print axioms backward_C_wellLabelled
#print axioms backward_support344
#print axioms backward_touched344
#print axioms backward_checkpoint344
#print axioms backward_composed_wellLabelled344
#print axioms backward_composed_checkpoint344
#print axioms backward_D_labels_checked
#print axioms backward_D_children_checked
#print axioms backward_D_checked
#print axioms backward_D_wellLabelled
#print axioms backward_support364
#print axioms backward_touched364
#print axioms backward_checkpoint364
#print axioms backward_composed_wellLabelled364
#print axioms backward_composed_checkpoint364
end CurrentMain.F19SelectedCoverage.Child34Check
