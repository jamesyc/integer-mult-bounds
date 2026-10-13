/- Two exact24-row nonzero-old chunks extend the accepted129-row selected current799 prefix.
Multivalue sparse checkpoints retain every736 label coordinate.
No operator realization or actual entrance execution is claimed. -/
import Current799Nonzero48Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799Nonzero48Check
open CurrentMain.CanonicalFrameCoverage

theorem catalog_prefix_shape : Current799Nonzero48Data.children.size = 353 := by decide +kernel

theorem exact_source_indices :
    Current799Nonzero48Data.forwardH.map Row.sourceIndex = List.range' 9370 24 ∧
    Current799Nonzero48Data.forwardI.map Row.sourceIndex = List.range' 9394 24 ∧
    Current799Nonzero48Data.backwardH.map Row.sourceIndex = List.range' 9370 24 ∧
    Current799Nonzero48Data.backwardI.map Row.sourceIndex = List.range' 9394 24 := by decide +kernel

theorem forward_H_labels_checked : labelRowsB Current799Nonzero48Data.forwardH Current799Next32Data.labels129 = true := by decide +kernel

theorem forward_H_children_checked : childRowsB Current799Nonzero48Data.data Current799Nonzero48Data.forwardH = true := by decide +kernel

theorem forward_H_checked : checkRows Current799Nonzero48Data.data Current799Nonzero48Data.forwardH Current799Next32Data.labels129 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_H_labels_checked, forward_H_children_checked⟩

theorem forward_H_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Nonzero48Data.forwardH.map Row.event) Current799Next32Data.labels129 :=
  checkRows_wellLabelled Current799Nonzero48Data.data Current799Nonzero48Data.forwardH Current799Next32Data.labels129 forward_H_checked

theorem forward_support153 :
    (Current799Nonzero48Data.forwardH.map Row.event).all (supportedB Current799Nonzero48Data.support153) = true := by decide +kernel

theorem forward_touched153 :
    Current799Nonzero48Data.support153.all (fun r =>
      LemmaG.Stream.labRun (Current799Nonzero48Data.forwardH.map Row.event) Current799Next32Data.labels129 r == Current799Nonzero48Data.target153 r) = true := by decide +kernel

theorem forward_checkpoint153 :
    LemmaG.Stream.labRun (Current799Nonzero48Data.forwardH.map Row.event) Current799Next32Data.labels129 = Current799Nonzero48Data.labels153 :=
  sparse_checkpoint Current799Nonzero48Data.forwardH Current799Next32Data.labels129 Current799Nonzero48Data.target153
    Current799Nonzero48Data.support153 forward_support153 forward_touched153

theorem forward_composed_wellLabelled153 :
    LemmaG.Stream.WellLabelled ((((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF) ++ Current799Next32Data.forwardG) ++ Current799Nonzero48Data.forwardH).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799Next32Check.forward_composed_wellLabelled129, ?_⟩
  rw [Current799Next32Check.forward_composed_checkpoint129]
  exact forward_H_wellLabelled

theorem forward_composed_checkpoint153 :
    LemmaG.Stream.labRun ((((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF) ++ Current799Next32Data.forwardG) ++ Current799Nonzero48Data.forwardH).map Row.event) Current799First33CoverageData.labels0 = Current799Nonzero48Data.labels153 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799Next32Check.forward_composed_checkpoint129]
  exact forward_checkpoint153

theorem forward_I_labels_checked : labelRowsB Current799Nonzero48Data.forwardI Current799Nonzero48Data.labels153 = true := by decide +kernel

theorem forward_I_children_checked : childRowsB Current799Nonzero48Data.data Current799Nonzero48Data.forwardI = true := by decide +kernel

theorem forward_I_checked : checkRows Current799Nonzero48Data.data Current799Nonzero48Data.forwardI Current799Nonzero48Data.labels153 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_I_labels_checked, forward_I_children_checked⟩

theorem forward_I_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Nonzero48Data.forwardI.map Row.event) Current799Nonzero48Data.labels153 :=
  checkRows_wellLabelled Current799Nonzero48Data.data Current799Nonzero48Data.forwardI Current799Nonzero48Data.labels153 forward_I_checked

theorem forward_support177 :
    (Current799Nonzero48Data.forwardI.map Row.event).all (supportedB Current799Nonzero48Data.support177) = true := by decide +kernel

theorem forward_touched177 :
    Current799Nonzero48Data.support177.all (fun r =>
      LemmaG.Stream.labRun (Current799Nonzero48Data.forwardI.map Row.event) Current799Nonzero48Data.labels153 r == Current799Nonzero48Data.target177 r) = true := by decide +kernel

theorem forward_checkpoint177 :
    LemmaG.Stream.labRun (Current799Nonzero48Data.forwardI.map Row.event) Current799Nonzero48Data.labels153 = Current799Nonzero48Data.labels177 :=
  sparse_checkpoint Current799Nonzero48Data.forwardI Current799Nonzero48Data.labels153 Current799Nonzero48Data.target177
    Current799Nonzero48Data.support177 forward_support177 forward_touched177

theorem forward_composed_wellLabelled177 :
    LemmaG.Stream.WellLabelled (((((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF) ++ Current799Next32Data.forwardG) ++ Current799Nonzero48Data.forwardH) ++ Current799Nonzero48Data.forwardI).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled153, ?_⟩
  rw [forward_composed_checkpoint153]
  exact forward_I_wellLabelled

theorem forward_composed_checkpoint177 :
    LemmaG.Stream.labRun (((((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF) ++ Current799Next32Data.forwardG) ++ Current799Nonzero48Data.forwardH) ++ Current799Nonzero48Data.forwardI).map Row.event) Current799First33CoverageData.labels0 = Current799Nonzero48Data.labels177 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint153]
  exact forward_checkpoint177

theorem backward_H_labels_checked : labelRowsB Current799Nonzero48Data.backwardH Current799Next32Data.labels129 = true := by decide +kernel

theorem backward_H_children_checked : childRowsB Current799Nonzero48Data.data Current799Nonzero48Data.backwardH = true := by decide +kernel

theorem backward_H_checked : checkRows Current799Nonzero48Data.data Current799Nonzero48Data.backwardH Current799Next32Data.labels129 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_H_labels_checked, backward_H_children_checked⟩

theorem backward_H_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Nonzero48Data.backwardH.map Row.event) Current799Next32Data.labels129 :=
  checkRows_wellLabelled Current799Nonzero48Data.data Current799Nonzero48Data.backwardH Current799Next32Data.labels129 backward_H_checked

theorem backward_support153 :
    (Current799Nonzero48Data.backwardH.map Row.event).all (supportedB Current799Nonzero48Data.support153) = true := by decide +kernel

theorem backward_touched153 :
    Current799Nonzero48Data.support153.all (fun r =>
      LemmaG.Stream.labRun (Current799Nonzero48Data.backwardH.map Row.event) Current799Next32Data.labels129 r == Current799Nonzero48Data.target153 r) = true := by decide +kernel

theorem backward_checkpoint153 :
    LemmaG.Stream.labRun (Current799Nonzero48Data.backwardH.map Row.event) Current799Next32Data.labels129 = Current799Nonzero48Data.labels153 :=
  sparse_checkpoint Current799Nonzero48Data.backwardH Current799Next32Data.labels129 Current799Nonzero48Data.target153
    Current799Nonzero48Data.support153 backward_support153 backward_touched153

theorem backward_composed_wellLabelled153 :
    LemmaG.Stream.WellLabelled ((((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF) ++ Current799Next32Data.backwardG) ++ Current799Nonzero48Data.backwardH).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799Next32Check.backward_composed_wellLabelled129, ?_⟩
  rw [Current799Next32Check.backward_composed_checkpoint129]
  exact backward_H_wellLabelled

theorem backward_composed_checkpoint153 :
    LemmaG.Stream.labRun ((((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF) ++ Current799Next32Data.backwardG) ++ Current799Nonzero48Data.backwardH).map Row.event) Current799First33CoverageData.labels0 = Current799Nonzero48Data.labels153 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799Next32Check.backward_composed_checkpoint129]
  exact backward_checkpoint153

theorem backward_I_labels_checked : labelRowsB Current799Nonzero48Data.backwardI Current799Nonzero48Data.labels153 = true := by decide +kernel

theorem backward_I_children_checked : childRowsB Current799Nonzero48Data.data Current799Nonzero48Data.backwardI = true := by decide +kernel

theorem backward_I_checked : checkRows Current799Nonzero48Data.data Current799Nonzero48Data.backwardI Current799Nonzero48Data.labels153 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_I_labels_checked, backward_I_children_checked⟩

theorem backward_I_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Nonzero48Data.backwardI.map Row.event) Current799Nonzero48Data.labels153 :=
  checkRows_wellLabelled Current799Nonzero48Data.data Current799Nonzero48Data.backwardI Current799Nonzero48Data.labels153 backward_I_checked

theorem backward_support177 :
    (Current799Nonzero48Data.backwardI.map Row.event).all (supportedB Current799Nonzero48Data.support177) = true := by decide +kernel

theorem backward_touched177 :
    Current799Nonzero48Data.support177.all (fun r =>
      LemmaG.Stream.labRun (Current799Nonzero48Data.backwardI.map Row.event) Current799Nonzero48Data.labels153 r == Current799Nonzero48Data.target177 r) = true := by decide +kernel

theorem backward_checkpoint177 :
    LemmaG.Stream.labRun (Current799Nonzero48Data.backwardI.map Row.event) Current799Nonzero48Data.labels153 = Current799Nonzero48Data.labels177 :=
  sparse_checkpoint Current799Nonzero48Data.backwardI Current799Nonzero48Data.labels153 Current799Nonzero48Data.target177
    Current799Nonzero48Data.support177 backward_support177 backward_touched177

theorem backward_composed_wellLabelled177 :
    LemmaG.Stream.WellLabelled (((((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF) ++ Current799Next32Data.backwardG) ++ Current799Nonzero48Data.backwardH) ++ Current799Nonzero48Data.backwardI).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled153, ?_⟩
  rw [backward_composed_checkpoint153]
  exact backward_I_wellLabelled

theorem backward_composed_checkpoint177 :
    LemmaG.Stream.labRun (((((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF) ++ Current799Next32Data.backwardG) ++ Current799Nonzero48Data.backwardH) ++ Current799Nonzero48Data.backwardI).map Row.event) Current799First33CoverageData.labels0 = Current799Nonzero48Data.labels177 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint153]
  exact backward_checkpoint177

#print axioms catalog_prefix_shape
#print axioms exact_source_indices
#print axioms forward_H_labels_checked
#print axioms forward_H_children_checked
#print axioms forward_H_checked
#print axioms forward_H_wellLabelled
#print axioms forward_support153
#print axioms forward_touched153
#print axioms forward_checkpoint153
#print axioms forward_composed_wellLabelled153
#print axioms forward_composed_checkpoint153
#print axioms forward_I_labels_checked
#print axioms forward_I_children_checked
#print axioms forward_I_checked
#print axioms forward_I_wellLabelled
#print axioms forward_support177
#print axioms forward_touched177
#print axioms forward_checkpoint177
#print axioms forward_composed_wellLabelled177
#print axioms forward_composed_checkpoint177
#print axioms backward_H_labels_checked
#print axioms backward_H_children_checked
#print axioms backward_H_checked
#print axioms backward_H_wellLabelled
#print axioms backward_support153
#print axioms backward_touched153
#print axioms backward_checkpoint153
#print axioms backward_composed_wellLabelled153
#print axioms backward_composed_checkpoint153
#print axioms backward_I_labels_checked
#print axioms backward_I_children_checked
#print axioms backward_I_checked
#print axioms backward_I_wellLabelled
#print axioms backward_support177
#print axioms backward_touched177
#print axioms backward_checkpoint177
#print axioms backward_composed_wellLabelled177
#print axioms backward_composed_checkpoint177
end CurrentMain.Current799Nonzero48Check
