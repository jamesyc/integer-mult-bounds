/- Two exact24-row chunks extend the accepted49-row selected current799 prefix.
Multivalue sparse checkpoints retain every736 label coordinate.
No operator realization or actual entrance execution is claimed. -/
import Current799Next48Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799Next48Check
open CurrentMain.CanonicalFrameCoverage

theorem catalog_prefix_shape : Current799Next48Data.children.size = 7 := by decide +kernel

theorem exact_source_indices :
    Current799Next48Data.forwardD.map Row.sourceIndex = List.range' 9290 24 ∧
    Current799Next48Data.forwardE.map Row.sourceIndex = List.range' 9314 24 ∧
    Current799Next48Data.backwardD.map Row.sourceIndex = List.range' 9290 24 ∧
    Current799Next48Data.backwardE.map Row.sourceIndex = List.range' 9314 24 := by decide +kernel

theorem forward_D_labels_checked : labelRowsB Current799Next48Data.forwardD Current799Next16Data.labels49 = true := by decide +kernel

theorem forward_D_children_checked : childRowsB Current799Next48Data.data Current799Next48Data.forwardD = true := by decide +kernel

theorem forward_D_checked : checkRows Current799Next48Data.data Current799Next48Data.forwardD Current799Next16Data.labels49 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_D_labels_checked, forward_D_children_checked⟩

theorem forward_D_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next48Data.forwardD.map Row.event) Current799Next16Data.labels49 :=
  checkRows_wellLabelled Current799Next48Data.data Current799Next48Data.forwardD Current799Next16Data.labels49 forward_D_checked

theorem forward_support73 :
    (Current799Next48Data.forwardD.map Row.event).all (supportedB Current799Next48Data.support73) = true := by decide +kernel

theorem forward_touched73 :
    Current799Next48Data.support73.all (fun r =>
      LemmaG.Stream.labRun (Current799Next48Data.forwardD.map Row.event) Current799Next16Data.labels49 r == Current799Next48Data.target73 r) = true := by decide +kernel

theorem forward_checkpoint73 :
    LemmaG.Stream.labRun (Current799Next48Data.forwardD.map Row.event) Current799Next16Data.labels49 = Current799Next48Data.labels73 :=
  sparse_checkpoint Current799Next48Data.forwardD Current799Next16Data.labels49 Current799Next48Data.target73
    Current799Next48Data.support73 forward_support73 forward_touched73

theorem forward_composed_wellLabelled73 :
    LemmaG.Stream.WellLabelled ((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799Next16Check.forward_composed_wellLabelled49, ?_⟩
  rw [Current799Next16Check.forward_composed_checkpoint49]
  exact forward_D_wellLabelled

theorem forward_composed_checkpoint73 :
    LemmaG.Stream.labRun ((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD).map Row.event) Current799First33CoverageData.labels0 = Current799Next48Data.labels73 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799Next16Check.forward_composed_checkpoint49]
  exact forward_checkpoint73

theorem forward_E_labels_checked : labelRowsB Current799Next48Data.forwardE Current799Next48Data.labels73 = true := by decide +kernel

theorem forward_E_children_checked : childRowsB Current799Next48Data.data Current799Next48Data.forwardE = true := by decide +kernel

theorem forward_E_checked : checkRows Current799Next48Data.data Current799Next48Data.forwardE Current799Next48Data.labels73 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_E_labels_checked, forward_E_children_checked⟩

theorem forward_E_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next48Data.forwardE.map Row.event) Current799Next48Data.labels73 :=
  checkRows_wellLabelled Current799Next48Data.data Current799Next48Data.forwardE Current799Next48Data.labels73 forward_E_checked

theorem forward_support97 :
    (Current799Next48Data.forwardE.map Row.event).all (supportedB Current799Next48Data.support97) = true := by decide +kernel

theorem forward_touched97 :
    Current799Next48Data.support97.all (fun r =>
      LemmaG.Stream.labRun (Current799Next48Data.forwardE.map Row.event) Current799Next48Data.labels73 r == Current799Next48Data.target97 r) = true := by decide +kernel

theorem forward_checkpoint97 :
    LemmaG.Stream.labRun (Current799Next48Data.forwardE.map Row.event) Current799Next48Data.labels73 = Current799Next48Data.labels97 :=
  sparse_checkpoint Current799Next48Data.forwardE Current799Next48Data.labels73 Current799Next48Data.target97
    Current799Next48Data.support97 forward_support97 forward_touched97

theorem forward_composed_wellLabelled97 :
    LemmaG.Stream.WellLabelled (((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled73, ?_⟩
  rw [forward_composed_checkpoint73]
  exact forward_E_wellLabelled

theorem forward_composed_checkpoint97 :
    LemmaG.Stream.labRun (((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE).map Row.event) Current799First33CoverageData.labels0 = Current799Next48Data.labels97 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint73]
  exact forward_checkpoint97

theorem backward_D_labels_checked : labelRowsB Current799Next48Data.backwardD Current799Next16Data.labels49 = true := by decide +kernel

theorem backward_D_children_checked : childRowsB Current799Next48Data.data Current799Next48Data.backwardD = true := by decide +kernel

theorem backward_D_checked : checkRows Current799Next48Data.data Current799Next48Data.backwardD Current799Next16Data.labels49 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_D_labels_checked, backward_D_children_checked⟩

theorem backward_D_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next48Data.backwardD.map Row.event) Current799Next16Data.labels49 :=
  checkRows_wellLabelled Current799Next48Data.data Current799Next48Data.backwardD Current799Next16Data.labels49 backward_D_checked

theorem backward_support73 :
    (Current799Next48Data.backwardD.map Row.event).all (supportedB Current799Next48Data.support73) = true := by decide +kernel

theorem backward_touched73 :
    Current799Next48Data.support73.all (fun r =>
      LemmaG.Stream.labRun (Current799Next48Data.backwardD.map Row.event) Current799Next16Data.labels49 r == Current799Next48Data.target73 r) = true := by decide +kernel

theorem backward_checkpoint73 :
    LemmaG.Stream.labRun (Current799Next48Data.backwardD.map Row.event) Current799Next16Data.labels49 = Current799Next48Data.labels73 :=
  sparse_checkpoint Current799Next48Data.backwardD Current799Next16Data.labels49 Current799Next48Data.target73
    Current799Next48Data.support73 backward_support73 backward_touched73

theorem backward_composed_wellLabelled73 :
    LemmaG.Stream.WellLabelled ((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799Next16Check.backward_composed_wellLabelled49, ?_⟩
  rw [Current799Next16Check.backward_composed_checkpoint49]
  exact backward_D_wellLabelled

theorem backward_composed_checkpoint73 :
    LemmaG.Stream.labRun ((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD).map Row.event) Current799First33CoverageData.labels0 = Current799Next48Data.labels73 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799Next16Check.backward_composed_checkpoint49]
  exact backward_checkpoint73

theorem backward_E_labels_checked : labelRowsB Current799Next48Data.backwardE Current799Next48Data.labels73 = true := by decide +kernel

theorem backward_E_children_checked : childRowsB Current799Next48Data.data Current799Next48Data.backwardE = true := by decide +kernel

theorem backward_E_checked : checkRows Current799Next48Data.data Current799Next48Data.backwardE Current799Next48Data.labels73 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_E_labels_checked, backward_E_children_checked⟩

theorem backward_E_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next48Data.backwardE.map Row.event) Current799Next48Data.labels73 :=
  checkRows_wellLabelled Current799Next48Data.data Current799Next48Data.backwardE Current799Next48Data.labels73 backward_E_checked

theorem backward_support97 :
    (Current799Next48Data.backwardE.map Row.event).all (supportedB Current799Next48Data.support97) = true := by decide +kernel

theorem backward_touched97 :
    Current799Next48Data.support97.all (fun r =>
      LemmaG.Stream.labRun (Current799Next48Data.backwardE.map Row.event) Current799Next48Data.labels73 r == Current799Next48Data.target97 r) = true := by decide +kernel

theorem backward_checkpoint97 :
    LemmaG.Stream.labRun (Current799Next48Data.backwardE.map Row.event) Current799Next48Data.labels73 = Current799Next48Data.labels97 :=
  sparse_checkpoint Current799Next48Data.backwardE Current799Next48Data.labels73 Current799Next48Data.target97
    Current799Next48Data.support97 backward_support97 backward_touched97

theorem backward_composed_wellLabelled97 :
    LemmaG.Stream.WellLabelled (((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled73, ?_⟩
  rw [backward_composed_checkpoint73]
  exact backward_E_wellLabelled

theorem backward_composed_checkpoint97 :
    LemmaG.Stream.labRun (((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE).map Row.event) Current799First33CoverageData.labels0 = Current799Next48Data.labels97 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint73]
  exact backward_checkpoint97

#print axioms catalog_prefix_shape
#print axioms exact_source_indices
#print axioms forward_D_labels_checked
#print axioms forward_D_children_checked
#print axioms forward_D_checked
#print axioms forward_D_wellLabelled
#print axioms forward_support73
#print axioms forward_touched73
#print axioms forward_checkpoint73
#print axioms forward_composed_wellLabelled73
#print axioms forward_composed_checkpoint73
#print axioms forward_E_labels_checked
#print axioms forward_E_children_checked
#print axioms forward_E_checked
#print axioms forward_E_wellLabelled
#print axioms forward_support97
#print axioms forward_touched97
#print axioms forward_checkpoint97
#print axioms forward_composed_wellLabelled97
#print axioms forward_composed_checkpoint97
#print axioms backward_D_labels_checked
#print axioms backward_D_children_checked
#print axioms backward_D_checked
#print axioms backward_D_wellLabelled
#print axioms backward_support73
#print axioms backward_touched73
#print axioms backward_checkpoint73
#print axioms backward_composed_wellLabelled73
#print axioms backward_composed_checkpoint73
#print axioms backward_E_labels_checked
#print axioms backward_E_children_checked
#print axioms backward_E_checked
#print axioms backward_E_wellLabelled
#print axioms backward_support97
#print axioms backward_touched97
#print axioms backward_checkpoint97
#print axioms backward_composed_wellLabelled97
#print axioms backward_composed_checkpoint97
end CurrentMain.Current799Next48Check
