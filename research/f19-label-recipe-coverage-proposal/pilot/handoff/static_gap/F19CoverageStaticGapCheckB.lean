/- Selected static-label gap: small factored decisions with empty-support boundaries.
Child lookup is vacuous because every new row is ADD. Accepted 549-row proofs are reused.
No omitted-adapter, scalar or physical/operator interpretation is asserted. -/
import F19CoverageStaticGapCheckA

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.StaticGapCheckB
open CurrentMain.F19SelectedCoverage

theorem exact_P_source_indices :
    StaticGapData.forwardP.map Row.sourceIndex = List.range' 11472 24 ∧
    StaticGapData.backwardP.map Row.sourceIndex = List.range' 11472 24 := by
  decide +kernel

theorem forward_P_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.forwardP StaticGapData.labels621 = true := by
  decide +kernel

theorem forward_P_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.forwardP = true := by
  decide +kernel

theorem forward_P_checked :
    checkRows PilotData.data StaticGapData.forwardP StaticGapData.labels621 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_P_labels_checked, forward_P_children_checked⟩

theorem forward_P_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.forwardP.map Row.event) StaticGapData.labels621 :=
  checkRows_wellLabelled PilotData.data StaticGapData.forwardP
    StaticGapData.labels621 forward_P_checked

theorem forward_support645 :
    (StaticGapData.forwardP.map Row.event).all (Boundary192.supportedB StaticGapData.new645) = true := by
  decide +kernel

theorem forward_touched645 :
    StaticGapData.new645.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.forwardP.map Row.event) StaticGapData.labels621 r == (7 : FrameLabel)) = true := by
  rfl

theorem forward_checkpoint645 :
    LemmaG.Stream.labRun (StaticGapData.forwardP.map Row.event) StaticGapData.labels621 = StaticGapData.labels645 :=
  SparseValues.sparse_checkpoint StaticGapData.forwardP StaticGapData.labels621
    (fun _ => (7 : FrameLabel)) StaticGapData.new645 forward_support645 forward_touched645

theorem forward_composed_wellLabelled645 :
    LemmaG.Stream.WellLabelled ((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨StaticGapCheckA.forward_composed_wellLabelled621, ?_⟩
  rw [StaticGapCheckA.forward_composed_checkpoint621]
  exact forward_P_wellLabelled

theorem forward_composed_checkpoint645 :
    LemmaG.Stream.labRun ((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels645 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, StaticGapCheckA.forward_composed_checkpoint621]
  exact forward_checkpoint645

theorem backward_P_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.backwardP StaticGapData.labels621 = true := by
  decide +kernel

theorem backward_P_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.backwardP = true := by
  decide +kernel

theorem backward_P_checked :
    checkRows PilotData.data StaticGapData.backwardP StaticGapData.labels621 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_P_labels_checked, backward_P_children_checked⟩

theorem backward_P_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.backwardP.map Row.event) StaticGapData.labels621 :=
  checkRows_wellLabelled PilotData.data StaticGapData.backwardP
    StaticGapData.labels621 backward_P_checked

theorem backward_support645 :
    (StaticGapData.backwardP.map Row.event).all (Boundary192.supportedB StaticGapData.new645) = true := by
  decide +kernel

theorem backward_touched645 :
    StaticGapData.new645.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.backwardP.map Row.event) StaticGapData.labels621 r == (7 : FrameLabel)) = true := by
  rfl

theorem backward_checkpoint645 :
    LemmaG.Stream.labRun (StaticGapData.backwardP.map Row.event) StaticGapData.labels621 = StaticGapData.labels645 :=
  SparseValues.sparse_checkpoint StaticGapData.backwardP StaticGapData.labels621
    (fun _ => (7 : FrameLabel)) StaticGapData.new645 backward_support645 backward_touched645

theorem backward_composed_wellLabelled645 :
    LemmaG.Stream.WellLabelled ((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨StaticGapCheckA.backward_composed_wellLabelled621, ?_⟩
  rw [StaticGapCheckA.backward_composed_checkpoint621]
  exact backward_P_wellLabelled

theorem backward_composed_checkpoint645 :
    LemmaG.Stream.labRun ((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels645 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, StaticGapCheckA.backward_composed_checkpoint621]
  exact backward_checkpoint645

theorem exact_Q_source_indices :
    StaticGapData.forwardQ.map Row.sourceIndex = List.range' 11496 24 ∧
    StaticGapData.backwardQ.map Row.sourceIndex = List.range' 11496 24 := by
  decide +kernel

theorem forward_Q_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.forwardQ StaticGapData.labels645 = true := by
  decide +kernel

theorem forward_Q_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.forwardQ = true := by
  decide +kernel

theorem forward_Q_checked :
    checkRows PilotData.data StaticGapData.forwardQ StaticGapData.labels645 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_Q_labels_checked, forward_Q_children_checked⟩

theorem forward_Q_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.forwardQ.map Row.event) StaticGapData.labels645 :=
  checkRows_wellLabelled PilotData.data StaticGapData.forwardQ
    StaticGapData.labels645 forward_Q_checked

theorem forward_support669 :
    (StaticGapData.forwardQ.map Row.event).all (Boundary192.supportedB StaticGapData.new669) = true := by
  decide +kernel

theorem forward_touched669 :
    StaticGapData.new669.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.forwardQ.map Row.event) StaticGapData.labels645 r == (7 : FrameLabel)) = true := by
  rfl

theorem forward_checkpoint669 :
    LemmaG.Stream.labRun (StaticGapData.forwardQ.map Row.event) StaticGapData.labels645 = StaticGapData.labels669 :=
  SparseValues.sparse_checkpoint StaticGapData.forwardQ StaticGapData.labels645
    (fun _ => (7 : FrameLabel)) StaticGapData.new669 forward_support669 forward_touched669

theorem forward_composed_wellLabelled669 :
    LemmaG.Stream.WellLabelled (((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled645, ?_⟩
  rw [forward_composed_checkpoint645]
  exact forward_Q_wellLabelled

theorem forward_composed_checkpoint669 :
    LemmaG.Stream.labRun (((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels669 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint645]
  exact forward_checkpoint669

theorem backward_Q_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.backwardQ StaticGapData.labels645 = true := by
  decide +kernel

theorem backward_Q_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.backwardQ = true := by
  decide +kernel

theorem backward_Q_checked :
    checkRows PilotData.data StaticGapData.backwardQ StaticGapData.labels645 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_Q_labels_checked, backward_Q_children_checked⟩

theorem backward_Q_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.backwardQ.map Row.event) StaticGapData.labels645 :=
  checkRows_wellLabelled PilotData.data StaticGapData.backwardQ
    StaticGapData.labels645 backward_Q_checked

theorem backward_support669 :
    (StaticGapData.backwardQ.map Row.event).all (Boundary192.supportedB StaticGapData.new669) = true := by
  decide +kernel

theorem backward_touched669 :
    StaticGapData.new669.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.backwardQ.map Row.event) StaticGapData.labels645 r == (7 : FrameLabel)) = true := by
  rfl

theorem backward_checkpoint669 :
    LemmaG.Stream.labRun (StaticGapData.backwardQ.map Row.event) StaticGapData.labels645 = StaticGapData.labels669 :=
  SparseValues.sparse_checkpoint StaticGapData.backwardQ StaticGapData.labels645
    (fun _ => (7 : FrameLabel)) StaticGapData.new669 backward_support669 backward_touched669

theorem backward_composed_wellLabelled669 :
    LemmaG.Stream.WellLabelled (((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled645, ?_⟩
  rw [backward_composed_checkpoint645]
  exact backward_Q_wellLabelled

theorem backward_composed_checkpoint669 :
    LemmaG.Stream.labRun (((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels669 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint645]
  exact backward_checkpoint669

theorem exact_R_source_indices :
    StaticGapData.forwardR.map Row.sourceIndex = List.range' 11520 26 ∧
    StaticGapData.backwardR.map Row.sourceIndex = List.range' 11520 26 := by
  decide +kernel

theorem forward_R_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.forwardR StaticGapData.labels669 = true := by
  decide +kernel

theorem forward_R_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.forwardR = true := by
  decide +kernel

theorem forward_R_checked :
    checkRows PilotData.data StaticGapData.forwardR StaticGapData.labels669 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_R_labels_checked, forward_R_children_checked⟩

theorem forward_R_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.forwardR.map Row.event) StaticGapData.labels669 :=
  checkRows_wellLabelled PilotData.data StaticGapData.forwardR
    StaticGapData.labels669 forward_R_checked

theorem forward_support695 :
    (StaticGapData.forwardR.map Row.event).all (Boundary192.supportedB StaticGapData.new695) = true := by
  decide +kernel

theorem forward_touched695 :
    StaticGapData.new695.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.forwardR.map Row.event) StaticGapData.labels669 r == (7 : FrameLabel)) = true := by
  rfl

theorem forward_checkpoint695 :
    LemmaG.Stream.labRun (StaticGapData.forwardR.map Row.event) StaticGapData.labels669 = StaticGapData.labels695 :=
  SparseValues.sparse_checkpoint StaticGapData.forwardR StaticGapData.labels669
    (fun _ => (7 : FrameLabel)) StaticGapData.new695 forward_support695 forward_touched695

theorem forward_composed_wellLabelled695 :
    LemmaG.Stream.WellLabelled ((((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ) ++ StaticGapData.forwardR).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled669, ?_⟩
  rw [forward_composed_checkpoint669]
  exact forward_R_wellLabelled

theorem forward_composed_checkpoint695 :
    LemmaG.Stream.labRun ((((((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO) ++ StaticGapData.forwardP) ++ StaticGapData.forwardQ) ++ StaticGapData.forwardR).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels695 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint669]
  exact forward_checkpoint695

theorem backward_R_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.backwardR StaticGapData.labels669 = true := by
  decide +kernel

theorem backward_R_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.backwardR = true := by
  decide +kernel

theorem backward_R_checked :
    checkRows PilotData.data StaticGapData.backwardR StaticGapData.labels669 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_R_labels_checked, backward_R_children_checked⟩

theorem backward_R_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.backwardR.map Row.event) StaticGapData.labels669 :=
  checkRows_wellLabelled PilotData.data StaticGapData.backwardR
    StaticGapData.labels669 backward_R_checked

theorem backward_support695 :
    (StaticGapData.backwardR.map Row.event).all (Boundary192.supportedB StaticGapData.new695) = true := by
  decide +kernel

theorem backward_touched695 :
    StaticGapData.new695.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.backwardR.map Row.event) StaticGapData.labels669 r == (7 : FrameLabel)) = true := by
  rfl

theorem backward_checkpoint695 :
    LemmaG.Stream.labRun (StaticGapData.backwardR.map Row.event) StaticGapData.labels669 = StaticGapData.labels695 :=
  SparseValues.sparse_checkpoint StaticGapData.backwardR StaticGapData.labels669
    (fun _ => (7 : FrameLabel)) StaticGapData.new695 backward_support695 backward_touched695

theorem backward_composed_wellLabelled695 :
    LemmaG.Stream.WellLabelled ((((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ) ++ StaticGapData.backwardR).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled669, ?_⟩
  rw [backward_composed_checkpoint669]
  exact backward_R_wellLabelled

theorem backward_composed_checkpoint695 :
    LemmaG.Stream.labRun ((((((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO) ++ StaticGapData.backwardP) ++ StaticGapData.backwardQ) ++ StaticGapData.backwardR).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels695 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint669]
  exact backward_checkpoint695

#print axioms exact_P_source_indices
#print axioms forward_P_labels_checked
#print axioms forward_P_children_checked
#print axioms forward_P_checked
#print axioms forward_P_wellLabelled
#print axioms forward_support645
#print axioms forward_touched645
#print axioms forward_checkpoint645
#print axioms forward_composed_wellLabelled645
#print axioms forward_composed_checkpoint645
#print axioms backward_P_labels_checked
#print axioms backward_P_children_checked
#print axioms backward_P_checked
#print axioms backward_P_wellLabelled
#print axioms backward_support645
#print axioms backward_touched645
#print axioms backward_checkpoint645
#print axioms backward_composed_wellLabelled645
#print axioms backward_composed_checkpoint645
#print axioms exact_Q_source_indices
#print axioms forward_Q_labels_checked
#print axioms forward_Q_children_checked
#print axioms forward_Q_checked
#print axioms forward_Q_wellLabelled
#print axioms forward_support669
#print axioms forward_touched669
#print axioms forward_checkpoint669
#print axioms forward_composed_wellLabelled669
#print axioms forward_composed_checkpoint669
#print axioms backward_Q_labels_checked
#print axioms backward_Q_children_checked
#print axioms backward_Q_checked
#print axioms backward_Q_wellLabelled
#print axioms backward_support669
#print axioms backward_touched669
#print axioms backward_checkpoint669
#print axioms backward_composed_wellLabelled669
#print axioms backward_composed_checkpoint669
#print axioms exact_R_source_indices
#print axioms forward_R_labels_checked
#print axioms forward_R_children_checked
#print axioms forward_R_checked
#print axioms forward_R_wellLabelled
#print axioms forward_support695
#print axioms forward_touched695
#print axioms forward_checkpoint695
#print axioms forward_composed_wellLabelled695
#print axioms forward_composed_checkpoint695
#print axioms backward_R_labels_checked
#print axioms backward_R_children_checked
#print axioms backward_R_checked
#print axioms backward_R_wellLabelled
#print axioms backward_support695
#print axioms backward_touched695
#print axioms backward_checkpoint695
#print axioms backward_composed_wellLabelled695
#print axioms backward_composed_checkpoint695
end CurrentMain.F19SelectedCoverage.StaticGapCheckB
