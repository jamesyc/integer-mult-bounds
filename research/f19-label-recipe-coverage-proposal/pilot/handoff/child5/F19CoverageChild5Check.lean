/- Scoped selected-source label/canonical-recipe coverage. No physical/operator claim. -/
import F19CoverageChild5Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Child5Check
open CurrentMain.F19SelectedCoverage

theorem exact_E_source_indices :
    Child5Data.forwardE.map Row.sourceIndex = List.range' 11215 24 ∧
    Child5Data.backwardE.map Row.sourceIndex = List.range' 11215 24 := by
  decide +kernel

theorem exact_F_source_indices :
    Child5Data.forwardF.map Row.sourceIndex = List.range' 11239 21 ∧
    Child5Data.backwardF.map Row.sourceIndex = List.range' 11239 21 := by
  decide +kernel

theorem forward_E_labels_checked :
    CheckDecomposition.labelRowsB Child5Data.forwardE Child34Data.labels364 = true := by
  decide +kernel

theorem forward_E_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5Data.forwardE = true := by
  decide +kernel

theorem forward_E_checked :
    checkRows PilotData.data Child5Data.forwardE Child34Data.labels364 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_E_labels_checked, forward_E_children_checked⟩

theorem forward_E_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5Data.forwardE.map Row.event) Child34Data.labels364 :=
  checkRows_wellLabelled PilotData.data Child5Data.forwardE
    Child34Data.labels364 forward_E_checked

theorem forward_support388 :
    (Child5Data.forwardE.map Row.event).all
      (Boundary192.supportedB Child5Data.new388) = true := by decide +kernel

theorem forward_touched388 :
    Child5Data.new388.all (fun r =>
      LemmaG.Stream.labRun (Child5Data.forwardE.map Row.event) Child34Data.labels364 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint388 :
    LemmaG.Stream.labRun (Child5Data.forwardE.map Row.event) Child34Data.labels364 =
      Child5Data.labels388 :=
  SparseValues.sparse_checkpoint Child5Data.forwardE Child34Data.labels364
    (fun _ => (7 : FrameLabel)) Child5Data.new388 forward_support388 forward_touched388

theorem forward_composed_wellLabelled388 :
    LemmaG.Stream.WellLabelled ((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child34Check.forward_composed_wellLabelled364, ?_⟩
  rw [Child34Check.forward_composed_checkpoint364]
  exact forward_E_wellLabelled

theorem forward_composed_checkpoint388 :
    LemmaG.Stream.labRun ((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE).map Row.event)
      (initialLabels PilotData.data) = Child5Data.labels388 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child34Check.forward_composed_checkpoint364]
  exact forward_checkpoint388

theorem forward_F_labels_checked :
    CheckDecomposition.labelRowsB Child5Data.forwardF Child5Data.labels388 = true := by
  decide +kernel

theorem forward_F_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5Data.forwardF = true := by
  decide +kernel

theorem forward_F_checked :
    checkRows PilotData.data Child5Data.forwardF Child5Data.labels388 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_F_labels_checked, forward_F_children_checked⟩

theorem forward_F_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5Data.forwardF.map Row.event) Child5Data.labels388 :=
  checkRows_wellLabelled PilotData.data Child5Data.forwardF
    Child5Data.labels388 forward_F_checked

theorem forward_support409 :
    (Child5Data.forwardF.map Row.event).all
      (Boundary192.supportedB Child5Data.new409) = true := by decide +kernel

theorem forward_touched409 :
    Child5Data.new409.all (fun r =>
      LemmaG.Stream.labRun (Child5Data.forwardF.map Row.event) Child5Data.labels388 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem forward_checkpoint409 :
    LemmaG.Stream.labRun (Child5Data.forwardF.map Row.event) Child5Data.labels388 =
      Child5Data.labels409 :=
  SparseValues.sparse_checkpoint Child5Data.forwardF Child5Data.labels388
    (fun _ => (7 : FrameLabel)) Child5Data.new409 forward_support409 forward_touched409

theorem forward_composed_wellLabelled409 :
    LemmaG.Stream.WellLabelled (((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled388, ?_⟩
  rw [forward_composed_checkpoint388]
  exact forward_F_wellLabelled

theorem forward_composed_checkpoint409 :
    LemmaG.Stream.labRun (((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF).map Row.event)
      (initialLabels PilotData.data) = Child5Data.labels409 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint388]
  exact forward_checkpoint409

theorem backward_E_labels_checked :
    CheckDecomposition.labelRowsB Child5Data.backwardE Child34Data.labels364 = true := by
  decide +kernel

theorem backward_E_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5Data.backwardE = true := by
  decide +kernel

theorem backward_E_checked :
    checkRows PilotData.data Child5Data.backwardE Child34Data.labels364 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_E_labels_checked, backward_E_children_checked⟩

theorem backward_E_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5Data.backwardE.map Row.event) Child34Data.labels364 :=
  checkRows_wellLabelled PilotData.data Child5Data.backwardE
    Child34Data.labels364 backward_E_checked

theorem backward_support388 :
    (Child5Data.backwardE.map Row.event).all
      (Boundary192.supportedB Child5Data.new388) = true := by decide +kernel

theorem backward_touched388 :
    Child5Data.new388.all (fun r =>
      LemmaG.Stream.labRun (Child5Data.backwardE.map Row.event) Child34Data.labels364 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint388 :
    LemmaG.Stream.labRun (Child5Data.backwardE.map Row.event) Child34Data.labels364 =
      Child5Data.labels388 :=
  SparseValues.sparse_checkpoint Child5Data.backwardE Child34Data.labels364
    (fun _ => (7 : FrameLabel)) Child5Data.new388 backward_support388 backward_touched388

theorem backward_composed_wellLabelled388 :
    LemmaG.Stream.WellLabelled ((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child34Check.backward_composed_wellLabelled364, ?_⟩
  rw [Child34Check.backward_composed_checkpoint364]
  exact backward_E_wellLabelled

theorem backward_composed_checkpoint388 :
    LemmaG.Stream.labRun ((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE).map Row.event)
      (initialLabels PilotData.data) = Child5Data.labels388 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child34Check.backward_composed_checkpoint364]
  exact backward_checkpoint388

theorem backward_F_labels_checked :
    CheckDecomposition.labelRowsB Child5Data.backwardF Child5Data.labels388 = true := by
  decide +kernel

theorem backward_F_children_checked :
    CheckDecomposition.childRowsB PilotData.data Child5Data.backwardF = true := by
  decide +kernel

theorem backward_F_checked :
    checkRows PilotData.data Child5Data.backwardF Child5Data.labels388 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_F_labels_checked, backward_F_children_checked⟩

theorem backward_F_wellLabelled :
    LemmaG.Stream.WellLabelled (Child5Data.backwardF.map Row.event) Child5Data.labels388 :=
  checkRows_wellLabelled PilotData.data Child5Data.backwardF
    Child5Data.labels388 backward_F_checked

theorem backward_support409 :
    (Child5Data.backwardF.map Row.event).all
      (Boundary192.supportedB Child5Data.new409) = true := by decide +kernel

theorem backward_touched409 :
    Child5Data.new409.all (fun r =>
      LemmaG.Stream.labRun (Child5Data.backwardF.map Row.event) Child5Data.labels388 r ==
        (7 : FrameLabel)) = true := by decide +kernel

theorem backward_checkpoint409 :
    LemmaG.Stream.labRun (Child5Data.backwardF.map Row.event) Child5Data.labels388 =
      Child5Data.labels409 :=
  SparseValues.sparse_checkpoint Child5Data.backwardF Child5Data.labels388
    (fun _ => (7 : FrameLabel)) Child5Data.new409 backward_support409 backward_touched409

theorem backward_composed_wellLabelled409 :
    LemmaG.Stream.WellLabelled (((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled388, ?_⟩
  rw [backward_composed_checkpoint388]
  exact backward_F_wellLabelled

theorem backward_composed_checkpoint409 :
    LemmaG.Stream.labRun (((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF).map Row.event)
      (initialLabels PilotData.data) = Child5Data.labels409 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint388]
  exact backward_checkpoint409

#print axioms exact_E_source_indices
#print axioms exact_F_source_indices
#print axioms forward_E_labels_checked
#print axioms forward_E_children_checked
#print axioms forward_E_checked
#print axioms forward_E_wellLabelled
#print axioms forward_support388
#print axioms forward_touched388
#print axioms forward_checkpoint388
#print axioms forward_composed_wellLabelled388
#print axioms forward_composed_checkpoint388
#print axioms forward_F_labels_checked
#print axioms forward_F_children_checked
#print axioms forward_F_checked
#print axioms forward_F_wellLabelled
#print axioms forward_support409
#print axioms forward_touched409
#print axioms forward_checkpoint409
#print axioms forward_composed_wellLabelled409
#print axioms forward_composed_checkpoint409
#print axioms backward_E_labels_checked
#print axioms backward_E_children_checked
#print axioms backward_E_checked
#print axioms backward_E_wellLabelled
#print axioms backward_support388
#print axioms backward_touched388
#print axioms backward_checkpoint388
#print axioms backward_composed_wellLabelled388
#print axioms backward_composed_checkpoint388
#print axioms backward_F_labels_checked
#print axioms backward_F_children_checked
#print axioms backward_F_checked
#print axioms backward_F_wellLabelled
#print axioms backward_support409
#print axioms backward_touched409
#print axioms backward_checkpoint409
#print axioms backward_composed_wellLabelled409
#print axioms backward_composed_checkpoint409
end CurrentMain.F19SelectedCoverage.Child5Check
