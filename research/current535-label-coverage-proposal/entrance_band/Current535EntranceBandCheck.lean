/- Two24+8 factored decisions with multivalue whole-register sparse handoffs.
The accepted180-row prefix is reused by append and checkpoint theorems.
Only label/catalog coverage; all eight operator suppliers are separate. -/
import Current535EntranceBandData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535EntranceBandCheck
open CurrentMain.CanonicalFrameCoverage

theorem exact_I_source_indices :
    Current535EntranceBandData.forwardI.map Row.sourceIndex = List.range' 10871 24 ∧
    Current535EntranceBandData.backwardI.map Row.sourceIndex = List.range' 10871 24 := by decide +kernel

theorem exact_J_source_indices :
    Current535EntranceBandData.forwardJ.map Row.sourceIndex = List.range' 10895 8 ∧
    Current535EntranceBandData.backwardJ.map Row.sourceIndex = List.range' 10895 8 := by decide +kernel

theorem forward_I_labels_checked :
    labelRowsB Current535EntranceBandData.forwardI Current535TwoKeyData.labels180 = true := by decide +kernel

theorem forward_I_children_checked :
    childRowsB Current535CoverageData.data Current535EntranceBandData.forwardI = true := by decide +kernel

theorem forward_I_checked :
    checkRows Current535CoverageData.data Current535EntranceBandData.forwardI Current535TwoKeyData.labels180 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_I_labels_checked, forward_I_children_checked⟩

theorem forward_I_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535EntranceBandData.forwardI.map Row.event) Current535TwoKeyData.labels180 :=
  checkRows_wellLabelled Current535CoverageData.data Current535EntranceBandData.forwardI Current535TwoKeyData.labels180 forward_I_checked

theorem forward_support204 :
    (Current535EntranceBandData.forwardI.map Row.event).all (supportedB Current535EntranceBandData.support204) = true := by decide +kernel

theorem forward_touched204 :
    Current535EntranceBandData.support204.all (fun r =>
      LemmaG.Stream.labRun (Current535EntranceBandData.forwardI.map Row.event) Current535TwoKeyData.labels180 r == Current535EntranceBandData.values204 r) = true := by decide +kernel

theorem forward_checkpoint204 :
    LemmaG.Stream.labRun (Current535EntranceBandData.forwardI.map Row.event) Current535TwoKeyData.labels180 = Current535EntranceBandData.labels204 :=
  sparse_checkpoint Current535EntranceBandData.forwardI Current535TwoKeyData.labels180 Current535EntranceBandData.values204
    Current535EntranceBandData.support204 forward_support204 forward_touched204

theorem forward_composed_wellLabelled204 :
    LemmaG.Stream.WellLabelled (((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535TwoKeyCheck.forward_composed_wellLabelled180, ?_⟩
  rw [Current535TwoKeyCheck.forward_composed_checkpoint180]
  exact forward_I_wellLabelled

theorem forward_composed_checkpoint204 :
    LemmaG.Stream.labRun (((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI).map Row.event) Current535CoverageData.labels0 = Current535EntranceBandData.labels204 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535TwoKeyCheck.forward_composed_checkpoint180]
  exact forward_checkpoint204

theorem forward_J_labels_checked :
    labelRowsB Current535EntranceBandData.forwardJ Current535EntranceBandData.labels204 = true := by decide +kernel

theorem forward_J_children_checked :
    childRowsB Current535CoverageData.data Current535EntranceBandData.forwardJ = true := by decide +kernel

theorem forward_J_checked :
    checkRows Current535CoverageData.data Current535EntranceBandData.forwardJ Current535EntranceBandData.labels204 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_J_labels_checked, forward_J_children_checked⟩

theorem forward_J_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535EntranceBandData.forwardJ.map Row.event) Current535EntranceBandData.labels204 :=
  checkRows_wellLabelled Current535CoverageData.data Current535EntranceBandData.forwardJ Current535EntranceBandData.labels204 forward_J_checked

theorem forward_support212 :
    (Current535EntranceBandData.forwardJ.map Row.event).all (supportedB Current535EntranceBandData.support212) = true := by decide +kernel

theorem forward_touched212 :
    Current535EntranceBandData.support212.all (fun r =>
      LemmaG.Stream.labRun (Current535EntranceBandData.forwardJ.map Row.event) Current535EntranceBandData.labels204 r == Current535EntranceBandData.values212 r) = true := by decide +kernel

theorem forward_checkpoint212 :
    LemmaG.Stream.labRun (Current535EntranceBandData.forwardJ.map Row.event) Current535EntranceBandData.labels204 = Current535EntranceBandData.labels212 :=
  sparse_checkpoint Current535EntranceBandData.forwardJ Current535EntranceBandData.labels204 Current535EntranceBandData.values212
    Current535EntranceBandData.support212 forward_support212 forward_touched212

theorem forward_composed_wellLabelled212 :
    LemmaG.Stream.WellLabelled ((((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI) ++ Current535EntranceBandData.forwardJ).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled204, ?_⟩
  rw [forward_composed_checkpoint204]
  exact forward_J_wellLabelled

theorem forward_composed_checkpoint212 :
    LemmaG.Stream.labRun ((((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI) ++ Current535EntranceBandData.forwardJ).map Row.event) Current535CoverageData.labels0 = Current535EntranceBandData.labels212 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint204]
  exact forward_checkpoint212

theorem backward_I_labels_checked :
    labelRowsB Current535EntranceBandData.backwardI Current535TwoKeyData.labels180 = true := by decide +kernel

theorem backward_I_children_checked :
    childRowsB Current535CoverageData.data Current535EntranceBandData.backwardI = true := by decide +kernel

theorem backward_I_checked :
    checkRows Current535CoverageData.data Current535EntranceBandData.backwardI Current535TwoKeyData.labels180 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_I_labels_checked, backward_I_children_checked⟩

theorem backward_I_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535EntranceBandData.backwardI.map Row.event) Current535TwoKeyData.labels180 :=
  checkRows_wellLabelled Current535CoverageData.data Current535EntranceBandData.backwardI Current535TwoKeyData.labels180 backward_I_checked

theorem backward_support204 :
    (Current535EntranceBandData.backwardI.map Row.event).all (supportedB Current535EntranceBandData.support204) = true := by decide +kernel

theorem backward_touched204 :
    Current535EntranceBandData.support204.all (fun r =>
      LemmaG.Stream.labRun (Current535EntranceBandData.backwardI.map Row.event) Current535TwoKeyData.labels180 r == Current535EntranceBandData.values204 r) = true := by decide +kernel

theorem backward_checkpoint204 :
    LemmaG.Stream.labRun (Current535EntranceBandData.backwardI.map Row.event) Current535TwoKeyData.labels180 = Current535EntranceBandData.labels204 :=
  sparse_checkpoint Current535EntranceBandData.backwardI Current535TwoKeyData.labels180 Current535EntranceBandData.values204
    Current535EntranceBandData.support204 backward_support204 backward_touched204

theorem backward_composed_wellLabelled204 :
    LemmaG.Stream.WellLabelled (((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535TwoKeyCheck.backward_composed_wellLabelled180, ?_⟩
  rw [Current535TwoKeyCheck.backward_composed_checkpoint180]
  exact backward_I_wellLabelled

theorem backward_composed_checkpoint204 :
    LemmaG.Stream.labRun (((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI).map Row.event) Current535CoverageData.labels0 = Current535EntranceBandData.labels204 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535TwoKeyCheck.backward_composed_checkpoint180]
  exact backward_checkpoint204

theorem backward_J_labels_checked :
    labelRowsB Current535EntranceBandData.backwardJ Current535EntranceBandData.labels204 = true := by decide +kernel

theorem backward_J_children_checked :
    childRowsB Current535CoverageData.data Current535EntranceBandData.backwardJ = true := by decide +kernel

theorem backward_J_checked :
    checkRows Current535CoverageData.data Current535EntranceBandData.backwardJ Current535EntranceBandData.labels204 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_J_labels_checked, backward_J_children_checked⟩

theorem backward_J_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535EntranceBandData.backwardJ.map Row.event) Current535EntranceBandData.labels204 :=
  checkRows_wellLabelled Current535CoverageData.data Current535EntranceBandData.backwardJ Current535EntranceBandData.labels204 backward_J_checked

theorem backward_support212 :
    (Current535EntranceBandData.backwardJ.map Row.event).all (supportedB Current535EntranceBandData.support212) = true := by decide +kernel

theorem backward_touched212 :
    Current535EntranceBandData.support212.all (fun r =>
      LemmaG.Stream.labRun (Current535EntranceBandData.backwardJ.map Row.event) Current535EntranceBandData.labels204 r == Current535EntranceBandData.values212 r) = true := by decide +kernel

theorem backward_checkpoint212 :
    LemmaG.Stream.labRun (Current535EntranceBandData.backwardJ.map Row.event) Current535EntranceBandData.labels204 = Current535EntranceBandData.labels212 :=
  sparse_checkpoint Current535EntranceBandData.backwardJ Current535EntranceBandData.labels204 Current535EntranceBandData.values212
    Current535EntranceBandData.support212 backward_support212 backward_touched212

theorem backward_composed_wellLabelled212 :
    LemmaG.Stream.WellLabelled ((((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI) ++ Current535EntranceBandData.backwardJ).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled204, ?_⟩
  rw [backward_composed_checkpoint204]
  exact backward_J_wellLabelled

theorem backward_composed_checkpoint212 :
    LemmaG.Stream.labRun ((((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI) ++ Current535EntranceBandData.backwardJ).map Row.event) Current535CoverageData.labels0 = Current535EntranceBandData.labels212 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint204]
  exact backward_checkpoint212

#print axioms exact_I_source_indices
#print axioms exact_J_source_indices
#print axioms forward_I_labels_checked
#print axioms forward_I_children_checked
#print axioms forward_I_checked
#print axioms forward_I_wellLabelled
#print axioms forward_support204
#print axioms forward_touched204
#print axioms forward_checkpoint204
#print axioms forward_composed_wellLabelled204
#print axioms forward_composed_checkpoint204
#print axioms forward_J_labels_checked
#print axioms forward_J_children_checked
#print axioms forward_J_checked
#print axioms forward_J_wellLabelled
#print axioms forward_support212
#print axioms forward_touched212
#print axioms forward_checkpoint212
#print axioms forward_composed_wellLabelled212
#print axioms forward_composed_checkpoint212
#print axioms backward_I_labels_checked
#print axioms backward_I_children_checked
#print axioms backward_I_checked
#print axioms backward_I_wellLabelled
#print axioms backward_support204
#print axioms backward_touched204
#print axioms backward_checkpoint204
#print axioms backward_composed_wellLabelled204
#print axioms backward_composed_checkpoint204
#print axioms backward_J_labels_checked
#print axioms backward_J_children_checked
#print axioms backward_J_checked
#print axioms backward_J_wellLabelled
#print axioms backward_support212
#print axioms backward_touched212
#print axioms backward_checkpoint212
#print axioms backward_composed_wellLabelled212
#print axioms backward_composed_checkpoint212
end CurrentMain.Current535EntranceBandCheck
