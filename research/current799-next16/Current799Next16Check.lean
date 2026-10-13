/- Fresh16-row directed0→5 extension of the accepted current799 first33.
The full sparse checkpoint and append use the accepted33 predicate without replay.
Only label/catalog/signed-denominator coverage; no operator or actual entrance execution. -/
import Current799Next16Data

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current799Next16Check
open CurrentMain.CanonicalFrameCoverage

theorem catalog_prefix_shape : Current799Next16Data.children.size = 4 := by decide +kernel

theorem exact_C_source_indices :
    Current799Next16Data.forwardC.map Row.sourceIndex = List.range' 9274 16 ∧
    Current799Next16Data.backwardC.map Row.sourceIndex = List.range' 9274 16 := by decide +kernel

theorem forward_C_labels_checked : labelRowsB Current799Next16Data.forwardC Current799First33CoverageData.labels33 = true := by decide +kernel

theorem forward_C_children_checked : childRowsB Current799Next16Data.data Current799Next16Data.forwardC = true := by decide +kernel

theorem forward_C_checked : checkRows Current799Next16Data.data Current799Next16Data.forwardC Current799First33CoverageData.labels33 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_C_labels_checked, forward_C_children_checked⟩

theorem forward_C_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next16Data.forwardC.map Row.event) Current799First33CoverageData.labels33 :=
  checkRows_wellLabelled Current799Next16Data.data Current799Next16Data.forwardC Current799First33CoverageData.labels33 forward_C_checked

theorem forward_support49 :
    (Current799Next16Data.forwardC.map Row.event).all (supportedB Current799Next16Data.support49) = true := by decide +kernel

theorem forward_touched49 :
    Current799Next16Data.support49.all (fun r =>
      LemmaG.Stream.labRun (Current799Next16Data.forwardC.map Row.event) Current799First33CoverageData.labels33 r ==
        (5 : FrameLabel 1005)) = true := by decide +kernel

theorem forward_checkpoint49 :
    LemmaG.Stream.labRun (Current799Next16Data.forwardC.map Row.event) Current799First33CoverageData.labels33 = Current799Next16Data.labels49 :=
  sparse_checkpoint Current799Next16Data.forwardC Current799First33CoverageData.labels33 (fun _ => (5 : FrameLabel 1005))
    Current799Next16Data.support49 forward_support49 forward_touched49

theorem forward_composed_wellLabelled49 :
    LemmaG.Stream.WellLabelled (((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799First33CoverageCheck.forward_composed_wellLabelled33, ?_⟩
  rw [Current799First33CoverageCheck.forward_composed_checkpoint33]
  exact forward_C_wellLabelled

theorem forward_composed_checkpoint49 :
    LemmaG.Stream.labRun (((Current799First33CoverageData.forwardA ++ Current799First33CoverageData.forwardB) ++ Current799Next16Data.forwardC).map Row.event) Current799First33CoverageData.labels0 = Current799Next16Data.labels49 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799First33CoverageCheck.forward_composed_checkpoint33]
  exact forward_checkpoint49

theorem backward_C_labels_checked : labelRowsB Current799Next16Data.backwardC Current799First33CoverageData.labels33 = true := by decide +kernel

theorem backward_C_children_checked : childRowsB Current799Next16Data.data Current799Next16Data.backwardC = true := by decide +kernel

theorem backward_C_checked : checkRows Current799Next16Data.data Current799Next16Data.backwardC Current799First33CoverageData.labels33 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_C_labels_checked, backward_C_children_checked⟩

theorem backward_C_wellLabelled :
    LemmaG.Stream.WellLabelled (Current799Next16Data.backwardC.map Row.event) Current799First33CoverageData.labels33 :=
  checkRows_wellLabelled Current799Next16Data.data Current799Next16Data.backwardC Current799First33CoverageData.labels33 backward_C_checked

theorem backward_support49 :
    (Current799Next16Data.backwardC.map Row.event).all (supportedB Current799Next16Data.support49) = true := by decide +kernel

theorem backward_touched49 :
    Current799Next16Data.support49.all (fun r =>
      LemmaG.Stream.labRun (Current799Next16Data.backwardC.map Row.event) Current799First33CoverageData.labels33 r ==
        (5 : FrameLabel 1005)) = true := by decide +kernel

theorem backward_checkpoint49 :
    LemmaG.Stream.labRun (Current799Next16Data.backwardC.map Row.event) Current799First33CoverageData.labels33 = Current799Next16Data.labels49 :=
  sparse_checkpoint Current799Next16Data.backwardC Current799First33CoverageData.labels33 (fun _ => (5 : FrameLabel 1005))
    Current799Next16Data.support49 backward_support49 backward_touched49

theorem backward_composed_wellLabelled49 :
    LemmaG.Stream.WellLabelled (((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC).map Row.event) Current799First33CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current799First33CoverageCheck.backward_composed_wellLabelled33, ?_⟩
  rw [Current799First33CoverageCheck.backward_composed_checkpoint33]
  exact backward_C_wellLabelled

theorem backward_composed_checkpoint49 :
    LemmaG.Stream.labRun (((Current799First33CoverageData.backwardA ++ Current799First33CoverageData.backwardB) ++ Current799Next16Data.backwardC).map Row.event) Current799First33CoverageData.labels0 = Current799Next16Data.labels49 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current799First33CoverageCheck.backward_composed_checkpoint33]
  exact backward_checkpoint49

#print axioms catalog_prefix_shape
#print axioms exact_C_source_indices
#print axioms forward_C_labels_checked
#print axioms forward_C_children_checked
#print axioms forward_C_checked
#print axioms forward_C_wellLabelled
#print axioms forward_support49
#print axioms forward_touched49
#print axioms forward_checkpoint49
#print axioms forward_composed_wellLabelled49
#print axioms forward_composed_checkpoint49
#print axioms backward_C_labels_checked
#print axioms backward_C_children_checked
#print axioms backward_C_checked
#print axioms backward_C_wellLabelled
#print axioms backward_support49
#print axioms backward_touched49
#print axioms backward_checkpoint49
#print axioms backward_composed_wellLabelled49
#print axioms backward_composed_checkpoint49
end CurrentMain.Current799Next16Check
