/- Exact24+8-row chunks extend the accepted97-row selected current799 prefix.
Multivalue sparse checkpoints retain every736 label coordinate.
No operator realization or actual entrance execution is claimed. -/
import Current799Next32Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799Next32Check
open CurrentMain.CanonicalFrameCoverage

theorem catalog_prefix_shape : Current799Next32Data.children.size = 15 := by decide +kernel

theorem exact_source_indices :
    Current799Next32Data.forwardF.map Row.sourceIndex = List.range' 9338 24 ∧
    Current799Next32Data.forwardG.map Row.sourceIndex = List.range' 9362 8 ∧
    Current799Next32Data.backwardF.map Row.sourceIndex = List.range' 9338 24 ∧
    Current799Next32Data.backwardG.map Row.sourceIndex = List.range' 9362 8 := by decide +kernel

theorem forward_F_labels_checked : labelRowsB Current799Next32Data.forwardF Current799Next48Data.labels97 = true := by decide +kernel

theorem forward_F_children_checked : childRowsB Current799Next32Data.data Current799Next32Data.forwardF = true := by decide +kernel

theorem forward_F_checked : checkRows Current799Next32Data.data Current799Next32Data.forwardF Current799Next48Data.labels97 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_F_labels_checked, forward_F_children_checked⟩

theorem forward_F_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next32Data.forwardF.map Row.event) Current799Next48Data.labels97 :=
  checkRows_wellLabelled Current799Next32Data.data Current799Next32Data.forwardF Current799Next48Data.labels97 forward_F_checked

theorem forward_support121 :
    (Current799Next32Data.forwardF.map Row.event).all (supportedB Current799Next32Data.support121) = true := by decide +kernel

theorem forward_touched121 :
    Current799Next32Data.support121.all (fun r =>
      LemmaG.Stream.labRun (Current799Next32Data.forwardF.map Row.event) Current799Next48Data.labels97 r == Current799Next32Data.target121 r) = true := by decide +kernel

theorem forward_checkpoint121 :
    LemmaG.Stream.labRun (Current799Next32Data.forwardF.map Row.event) Current799Next48Data.labels97 = Current799Next32Data.labels121 :=
  sparse_checkpoint Current799Next32Data.forwardF Current799Next48Data.labels97 Current799Next32Data.target121
    Current799Next32Data.support121 forward_support121 forward_touched121

theorem forward_composed_wellLabelled121 :
    LemmaG.Stream.WellLabelled ((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799Next48Check.forward_composed_wellLabelled97, ?_⟩
  rw [Current799Next48Check.forward_composed_checkpoint97]
  exact forward_F_wellLabelled

theorem forward_composed_checkpoint121 :
    LemmaG.Stream.labRun ((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF).map Row.event) Current799First33CoverageData.labels0 = Current799Next32Data.labels121 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799Next48Check.forward_composed_checkpoint97]
  exact forward_checkpoint121

theorem forward_G_labels_checked : labelRowsB Current799Next32Data.forwardG Current799Next32Data.labels121 = true := by decide +kernel

theorem forward_G_children_checked : childRowsB Current799Next32Data.data Current799Next32Data.forwardG = true := by decide +kernel

theorem forward_G_checked : checkRows Current799Next32Data.data Current799Next32Data.forwardG Current799Next32Data.labels121 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_G_labels_checked, forward_G_children_checked⟩

theorem forward_G_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next32Data.forwardG.map Row.event) Current799Next32Data.labels121 :=
  checkRows_wellLabelled Current799Next32Data.data Current799Next32Data.forwardG Current799Next32Data.labels121 forward_G_checked

theorem forward_support129 :
    (Current799Next32Data.forwardG.map Row.event).all (supportedB Current799Next32Data.support129) = true := by decide +kernel

theorem forward_touched129 :
    Current799Next32Data.support129.all (fun r =>
      LemmaG.Stream.labRun (Current799Next32Data.forwardG.map Row.event) Current799Next32Data.labels121 r == Current799Next32Data.target129 r) = true := by decide +kernel

theorem forward_checkpoint129 :
    LemmaG.Stream.labRun (Current799Next32Data.forwardG.map Row.event) Current799Next32Data.labels121 = Current799Next32Data.labels129 :=
  sparse_checkpoint Current799Next32Data.forwardG Current799Next32Data.labels121 Current799Next32Data.target129
    Current799Next32Data.support129 forward_support129 forward_touched129

theorem forward_composed_wellLabelled129 :
    LemmaG.Stream.WellLabelled (((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF) ++ Current799Next32Data.forwardG).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled121, ?_⟩
  rw [forward_composed_checkpoint121]
  exact forward_G_wellLabelled

theorem forward_composed_checkpoint129 :
    LemmaG.Stream.labRun (((((((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC) ++ Current799Next48Data.forwardD) ++ Current799Next48Data.forwardE) ++ Current799Next32Data.forwardF) ++ Current799Next32Data.forwardG).map Row.event) Current799First33CoverageData.labels0 = Current799Next32Data.labels129 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint121]
  exact forward_checkpoint129

theorem backward_F_labels_checked : labelRowsB Current799Next32Data.backwardF Current799Next48Data.labels97 = true := by decide +kernel

theorem backward_F_children_checked : childRowsB Current799Next32Data.data Current799Next32Data.backwardF = true := by decide +kernel

theorem backward_F_checked : checkRows Current799Next32Data.data Current799Next32Data.backwardF Current799Next48Data.labels97 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_F_labels_checked, backward_F_children_checked⟩

theorem backward_F_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next32Data.backwardF.map Row.event) Current799Next48Data.labels97 :=
  checkRows_wellLabelled Current799Next32Data.data Current799Next32Data.backwardF Current799Next48Data.labels97 backward_F_checked

theorem backward_support121 :
    (Current799Next32Data.backwardF.map Row.event).all (supportedB Current799Next32Data.support121) = true := by decide +kernel

theorem backward_touched121 :
    Current799Next32Data.support121.all (fun r =>
      LemmaG.Stream.labRun (Current799Next32Data.backwardF.map Row.event) Current799Next48Data.labels97 r == Current799Next32Data.target121 r) = true := by decide +kernel

theorem backward_checkpoint121 :
    LemmaG.Stream.labRun (Current799Next32Data.backwardF.map Row.event) Current799Next48Data.labels97 = Current799Next32Data.labels121 :=
  sparse_checkpoint Current799Next32Data.backwardF Current799Next48Data.labels97 Current799Next32Data.target121
    Current799Next32Data.support121 backward_support121 backward_touched121

theorem backward_composed_wellLabelled121 :
    LemmaG.Stream.WellLabelled ((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799Next48Check.backward_composed_wellLabelled97, ?_⟩
  rw [Current799Next48Check.backward_composed_checkpoint97]
  exact backward_F_wellLabelled

theorem backward_composed_checkpoint121 :
    LemmaG.Stream.labRun ((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF).map Row.event) Current799First33CoverageData.labels0 = Current799Next32Data.labels121 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799Next48Check.backward_composed_checkpoint97]
  exact backward_checkpoint121

theorem backward_G_labels_checked : labelRowsB Current799Next32Data.backwardG Current799Next32Data.labels121 = true := by decide +kernel

theorem backward_G_children_checked : childRowsB Current799Next32Data.data Current799Next32Data.backwardG = true := by decide +kernel

theorem backward_G_checked : checkRows Current799Next32Data.data Current799Next32Data.backwardG Current799Next32Data.labels121 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_G_labels_checked, backward_G_children_checked⟩

theorem backward_G_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next32Data.backwardG.map Row.event) Current799Next32Data.labels121 :=
  checkRows_wellLabelled Current799Next32Data.data Current799Next32Data.backwardG Current799Next32Data.labels121 backward_G_checked

theorem backward_support129 :
    (Current799Next32Data.backwardG.map Row.event).all (supportedB Current799Next32Data.support129) = true := by decide +kernel

theorem backward_touched129 :
    Current799Next32Data.support129.all (fun r =>
      LemmaG.Stream.labRun (Current799Next32Data.backwardG.map Row.event) Current799Next32Data.labels121 r == Current799Next32Data.target129 r) = true := by decide +kernel

theorem backward_checkpoint129 :
    LemmaG.Stream.labRun (Current799Next32Data.backwardG.map Row.event) Current799Next32Data.labels121 = Current799Next32Data.labels129 :=
  sparse_checkpoint Current799Next32Data.backwardG Current799Next32Data.labels121 Current799Next32Data.target129
    Current799Next32Data.support129 backward_support129 backward_touched129

theorem backward_composed_wellLabelled129 :
    LemmaG.Stream.WellLabelled (((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF) ++ Current799Next32Data.backwardG).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled121, ?_⟩
  rw [backward_composed_checkpoint121]
  exact backward_G_wellLabelled

theorem backward_composed_checkpoint129 :
    LemmaG.Stream.labRun (((((((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC) ++ Current799Next48Data.backwardD) ++ Current799Next48Data.backwardE) ++ Current799Next32Data.backwardF) ++ Current799Next32Data.backwardG).map Row.event) Current799First33CoverageData.labels0 = Current799Next32Data.labels129 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint121]
  exact backward_checkpoint129

#print axioms catalog_prefix_shape
#print axioms exact_source_indices
#print axioms forward_F_labels_checked
#print axioms forward_F_children_checked
#print axioms forward_F_checked
#print axioms forward_F_wellLabelled
#print axioms forward_support121
#print axioms forward_touched121
#print axioms forward_checkpoint121
#print axioms forward_composed_wellLabelled121
#print axioms forward_composed_checkpoint121
#print axioms forward_G_labels_checked
#print axioms forward_G_children_checked
#print axioms forward_G_checked
#print axioms forward_G_wellLabelled
#print axioms forward_support129
#print axioms forward_touched129
#print axioms forward_checkpoint129
#print axioms forward_composed_wellLabelled129
#print axioms forward_composed_checkpoint129
#print axioms backward_F_labels_checked
#print axioms backward_F_children_checked
#print axioms backward_F_checked
#print axioms backward_F_wellLabelled
#print axioms backward_support121
#print axioms backward_touched121
#print axioms backward_checkpoint121
#print axioms backward_composed_wellLabelled121
#print axioms backward_composed_checkpoint121
#print axioms backward_G_labels_checked
#print axioms backward_G_children_checked
#print axioms backward_G_checked
#print axioms backward_G_wellLabelled
#print axioms backward_support129
#print axioms backward_touched129
#print axioms backward_checkpoint129
#print axioms backward_composed_wellLabelled129
#print axioms backward_composed_checkpoint129
end CurrentMain.Current799Next32Check
