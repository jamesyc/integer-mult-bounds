/- Two24+24 factored decisions with multivalue whole-register sparse handoffs.
The accepted212-row prefix is reused by append and checkpoint theorems.
Only label/catalog coverage; all new operator suppliers are separate. -/
import Current535NonzeroBandData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current535NonzeroBandCheck
open CurrentMain.CanonicalFrameCoverage

theorem exact_K_source_indices :
    Current535NonzeroBandData.forwardK.map Row.sourceIndex = List.range' 10903 24 ∧
    Current535NonzeroBandData.backwardK.map Row.sourceIndex = List.range' 10903 24 := by decide +kernel

theorem exact_L_source_indices :
    Current535NonzeroBandData.forwardL.map Row.sourceIndex = List.range' 10927 24 ∧
    Current535NonzeroBandData.backwardL.map Row.sourceIndex = List.range' 10927 24 := by decide +kernel

theorem forward_K_labels_checked :
    labelRowsB Current535NonzeroBandData.forwardK Current535EntranceBandData.labels212 = true := by decide +kernel

theorem forward_K_children_checked :
    childRowsB Current535CoverageData.data Current535NonzeroBandData.forwardK = true := by decide +kernel

theorem forward_K_checked :
    checkRows Current535CoverageData.data Current535NonzeroBandData.forwardK Current535EntranceBandData.labels212 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_K_labels_checked, forward_K_children_checked⟩

theorem forward_K_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535NonzeroBandData.forwardK.map Row.event) Current535EntranceBandData.labels212 :=
  checkRows_wellLabelled Current535CoverageData.data Current535NonzeroBandData.forwardK Current535EntranceBandData.labels212 forward_K_checked

theorem forward_support236 :
    (Current535NonzeroBandData.forwardK.map Row.event).all (supportedB Current535NonzeroBandData.support236) = true := by decide +kernel

theorem forward_touched236 :
    Current535NonzeroBandData.support236.all (fun r =>
      LemmaG.Stream.labRun (Current535NonzeroBandData.forwardK.map Row.event) Current535EntranceBandData.labels212 r == Current535NonzeroBandData.values236 r) = true := by decide +kernel

theorem forward_checkpoint236 :
    LemmaG.Stream.labRun (Current535NonzeroBandData.forwardK.map Row.event) Current535EntranceBandData.labels212 = Current535NonzeroBandData.labels236 :=
  sparse_checkpoint Current535NonzeroBandData.forwardK Current535EntranceBandData.labels212 Current535NonzeroBandData.values236
    Current535NonzeroBandData.support236 forward_support236 forward_touched236

theorem forward_composed_wellLabelled236 :
    LemmaG.Stream.WellLabelled (((((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI) ++ Current535EntranceBandData.forwardJ) ++ Current535NonzeroBandData.forwardK).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535EntranceBandCheck.forward_composed_wellLabelled212, ?_⟩
  rw [Current535EntranceBandCheck.forward_composed_checkpoint212]
  exact forward_K_wellLabelled

theorem forward_composed_checkpoint236 :
    LemmaG.Stream.labRun (((((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI) ++ Current535EntranceBandData.forwardJ) ++ Current535NonzeroBandData.forwardK).map Row.event) Current535CoverageData.labels0 = Current535NonzeroBandData.labels236 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535EntranceBandCheck.forward_composed_checkpoint212]
  exact forward_checkpoint236

theorem forward_L_labels_checked :
    labelRowsB Current535NonzeroBandData.forwardL Current535NonzeroBandData.labels236 = true := by decide +kernel

theorem forward_L_children_checked :
    childRowsB Current535CoverageData.data Current535NonzeroBandData.forwardL = true := by decide +kernel

theorem forward_L_checked :
    checkRows Current535CoverageData.data Current535NonzeroBandData.forwardL Current535NonzeroBandData.labels236 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_L_labels_checked, forward_L_children_checked⟩

theorem forward_L_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535NonzeroBandData.forwardL.map Row.event) Current535NonzeroBandData.labels236 :=
  checkRows_wellLabelled Current535CoverageData.data Current535NonzeroBandData.forwardL Current535NonzeroBandData.labels236 forward_L_checked

theorem forward_support260 :
    (Current535NonzeroBandData.forwardL.map Row.event).all (supportedB Current535NonzeroBandData.support260) = true := by decide +kernel

theorem forward_touched260 :
    Current535NonzeroBandData.support260.all (fun r =>
      LemmaG.Stream.labRun (Current535NonzeroBandData.forwardL.map Row.event) Current535NonzeroBandData.labels236 r == Current535NonzeroBandData.values260 r) = true := by decide +kernel

theorem forward_checkpoint260 :
    LemmaG.Stream.labRun (Current535NonzeroBandData.forwardL.map Row.event) Current535NonzeroBandData.labels236 = Current535NonzeroBandData.labels260 :=
  sparse_checkpoint Current535NonzeroBandData.forwardL Current535NonzeroBandData.labels236 Current535NonzeroBandData.values260
    Current535NonzeroBandData.support260 forward_support260 forward_touched260

theorem forward_composed_wellLabelled260 :
    LemmaG.Stream.WellLabelled ((((((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI) ++ Current535EntranceBandData.forwardJ) ++ Current535NonzeroBandData.forwardK) ++ Current535NonzeroBandData.forwardL).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled236, ?_⟩
  rw [forward_composed_checkpoint236]
  exact forward_L_wellLabelled

theorem forward_composed_checkpoint260 :
    LemmaG.Stream.labRun ((((((((((((Current535CoverageData.forwardA ++ Current535CoverageData.forwardB) ++ Current535Child003Data.forwardC) ++ Current535Child003Data.forwardD) ++ Current535TwoKeyData.forwardE) ++ Current535TwoKeyData.forwardF) ++ Current535TwoKeyData.forwardG) ++ Current535TwoKeyData.forwardH) ++ Current535EntranceBandData.forwardI) ++ Current535EntranceBandData.forwardJ) ++ Current535NonzeroBandData.forwardK) ++ Current535NonzeroBandData.forwardL).map Row.event) Current535CoverageData.labels0 = Current535NonzeroBandData.labels260 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint236]
  exact forward_checkpoint260

theorem backward_K_labels_checked :
    labelRowsB Current535NonzeroBandData.backwardK Current535EntranceBandData.labels212 = true := by decide +kernel

theorem backward_K_children_checked :
    childRowsB Current535CoverageData.data Current535NonzeroBandData.backwardK = true := by decide +kernel

theorem backward_K_checked :
    checkRows Current535CoverageData.data Current535NonzeroBandData.backwardK Current535EntranceBandData.labels212 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_K_labels_checked, backward_K_children_checked⟩

theorem backward_K_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535NonzeroBandData.backwardK.map Row.event) Current535EntranceBandData.labels212 :=
  checkRows_wellLabelled Current535CoverageData.data Current535NonzeroBandData.backwardK Current535EntranceBandData.labels212 backward_K_checked

theorem backward_support236 :
    (Current535NonzeroBandData.backwardK.map Row.event).all (supportedB Current535NonzeroBandData.support236) = true := by decide +kernel

theorem backward_touched236 :
    Current535NonzeroBandData.support236.all (fun r =>
      LemmaG.Stream.labRun (Current535NonzeroBandData.backwardK.map Row.event) Current535EntranceBandData.labels212 r == Current535NonzeroBandData.values236 r) = true := by decide +kernel

theorem backward_checkpoint236 :
    LemmaG.Stream.labRun (Current535NonzeroBandData.backwardK.map Row.event) Current535EntranceBandData.labels212 = Current535NonzeroBandData.labels236 :=
  sparse_checkpoint Current535NonzeroBandData.backwardK Current535EntranceBandData.labels212 Current535NonzeroBandData.values236
    Current535NonzeroBandData.support236 backward_support236 backward_touched236

theorem backward_composed_wellLabelled236 :
    LemmaG.Stream.WellLabelled (((((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI) ++ Current535EntranceBandData.backwardJ) ++ Current535NonzeroBandData.backwardK).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Current535EntranceBandCheck.backward_composed_wellLabelled212, ?_⟩
  rw [Current535EntranceBandCheck.backward_composed_checkpoint212]
  exact backward_K_wellLabelled

theorem backward_composed_checkpoint236 :
    LemmaG.Stream.labRun (((((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI) ++ Current535EntranceBandData.backwardJ) ++ Current535NonzeroBandData.backwardK).map Row.event) Current535CoverageData.labels0 = Current535NonzeroBandData.labels236 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Current535EntranceBandCheck.backward_composed_checkpoint212]
  exact backward_checkpoint236

theorem backward_L_labels_checked :
    labelRowsB Current535NonzeroBandData.backwardL Current535NonzeroBandData.labels236 = true := by decide +kernel

theorem backward_L_children_checked :
    childRowsB Current535CoverageData.data Current535NonzeroBandData.backwardL = true := by decide +kernel

theorem backward_L_checked :
    checkRows Current535CoverageData.data Current535NonzeroBandData.backwardL Current535NonzeroBandData.labels236 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_L_labels_checked, backward_L_children_checked⟩

theorem backward_L_wellLabelled :
    LemmaG.Stream.WellLabelled (Current535NonzeroBandData.backwardL.map Row.event) Current535NonzeroBandData.labels236 :=
  checkRows_wellLabelled Current535CoverageData.data Current535NonzeroBandData.backwardL Current535NonzeroBandData.labels236 backward_L_checked

theorem backward_support260 :
    (Current535NonzeroBandData.backwardL.map Row.event).all (supportedB Current535NonzeroBandData.support260) = true := by decide +kernel

theorem backward_touched260 :
    Current535NonzeroBandData.support260.all (fun r =>
      LemmaG.Stream.labRun (Current535NonzeroBandData.backwardL.map Row.event) Current535NonzeroBandData.labels236 r == Current535NonzeroBandData.values260 r) = true := by decide +kernel

theorem backward_checkpoint260 :
    LemmaG.Stream.labRun (Current535NonzeroBandData.backwardL.map Row.event) Current535NonzeroBandData.labels236 = Current535NonzeroBandData.labels260 :=
  sparse_checkpoint Current535NonzeroBandData.backwardL Current535NonzeroBandData.labels236 Current535NonzeroBandData.values260
    Current535NonzeroBandData.support260 backward_support260 backward_touched260

theorem backward_composed_wellLabelled260 :
    LemmaG.Stream.WellLabelled ((((((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI) ++ Current535EntranceBandData.backwardJ) ++ Current535NonzeroBandData.backwardK) ++ Current535NonzeroBandData.backwardL).map Row.event) Current535CoverageData.labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled236, ?_⟩
  rw [backward_composed_checkpoint236]
  exact backward_L_wellLabelled

theorem backward_composed_checkpoint260 :
    LemmaG.Stream.labRun ((((((((((((Current535CoverageData.backwardA ++ Current535CoverageData.backwardB) ++ Current535Child003Data.backwardC) ++ Current535Child003Data.backwardD) ++ Current535TwoKeyData.backwardE) ++ Current535TwoKeyData.backwardF) ++ Current535TwoKeyData.backwardG) ++ Current535TwoKeyData.backwardH) ++ Current535EntranceBandData.backwardI) ++ Current535EntranceBandData.backwardJ) ++ Current535NonzeroBandData.backwardK) ++ Current535NonzeroBandData.backwardL).map Row.event) Current535CoverageData.labels0 = Current535NonzeroBandData.labels260 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint236]
  exact backward_checkpoint260

#print axioms exact_K_source_indices
#print axioms exact_L_source_indices
#print axioms forward_K_labels_checked
#print axioms forward_K_children_checked
#print axioms forward_K_checked
#print axioms forward_K_wellLabelled
#print axioms forward_support236
#print axioms forward_touched236
#print axioms forward_checkpoint236
#print axioms forward_composed_wellLabelled236
#print axioms forward_composed_checkpoint236
#print axioms forward_L_labels_checked
#print axioms forward_L_children_checked
#print axioms forward_L_checked
#print axioms forward_L_wellLabelled
#print axioms forward_support260
#print axioms forward_touched260
#print axioms forward_checkpoint260
#print axioms forward_composed_wellLabelled260
#print axioms forward_composed_checkpoint260
#print axioms backward_K_labels_checked
#print axioms backward_K_children_checked
#print axioms backward_K_checked
#print axioms backward_K_wellLabelled
#print axioms backward_support236
#print axioms backward_touched236
#print axioms backward_checkpoint236
#print axioms backward_composed_wellLabelled236
#print axioms backward_composed_checkpoint236
#print axioms backward_L_labels_checked
#print axioms backward_L_children_checked
#print axioms backward_L_checked
#print axioms backward_L_wellLabelled
#print axioms backward_support260
#print axioms backward_touched260
#print axioms backward_checkpoint260
#print axioms backward_composed_wellLabelled260
#print axioms backward_composed_checkpoint260
end CurrentMain.Current535NonzeroBandCheck
