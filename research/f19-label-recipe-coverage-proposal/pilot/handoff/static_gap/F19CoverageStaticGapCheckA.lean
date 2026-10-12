/- Selected static-label gap: small factored decisions with empty-support boundaries.
Child lookup is vacuous because every new row is ADD. Accepted 549-row proofs are reused.
No omitted-adapter, scalar or physical/operator interpretation is asserted. -/
import F19CoverageStaticGapData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.StaticGapCheckA
open CurrentMain.F19SelectedCoverage

theorem exact_M_source_indices :
    StaticGapData.forwardM.map Row.sourceIndex = List.range' 11400 24 ∧
    StaticGapData.backwardM.map Row.sourceIndex = List.range' 11400 24 := by
  decide +kernel

theorem forward_M_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.forwardM Child5MoreData.labels549 = true := by
  decide +kernel

theorem forward_M_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.forwardM = true := by
  decide +kernel

theorem forward_M_checked :
    checkRows PilotData.data StaticGapData.forwardM Child5MoreData.labels549 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_M_labels_checked, forward_M_children_checked⟩

theorem forward_M_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.forwardM.map Row.event) Child5MoreData.labels549 :=
  checkRows_wellLabelled PilotData.data StaticGapData.forwardM
    Child5MoreData.labels549 forward_M_checked

theorem forward_support573 :
    (StaticGapData.forwardM.map Row.event).all (Boundary192.supportedB StaticGapData.new573) = true := by
  decide +kernel

theorem forward_touched573 :
    StaticGapData.new573.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.forwardM.map Row.event) Child5MoreData.labels549 r == (7 : FrameLabel)) = true := by
  rfl

theorem forward_checkpoint573 :
    LemmaG.Stream.labRun (StaticGapData.forwardM.map Row.event) Child5MoreData.labels549 = StaticGapData.labels573 :=
  SparseValues.sparse_checkpoint StaticGapData.forwardM Child5MoreData.labels549
    (fun _ => (7 : FrameLabel)) StaticGapData.new573 forward_support573 forward_touched573

theorem forward_composed_wellLabelled573 :
    LemmaG.Stream.WellLabelled (((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5MoreCheck.forward_composed_wellLabelled549, ?_⟩
  rw [Child5MoreCheck.forward_composed_checkpoint549]
  exact forward_M_wellLabelled

theorem forward_composed_checkpoint573 :
    LemmaG.Stream.labRun (((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels573 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5MoreCheck.forward_composed_checkpoint549]
  exact forward_checkpoint573

theorem backward_M_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.backwardM Child5MoreData.labels549 = true := by
  decide +kernel

theorem backward_M_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.backwardM = true := by
  decide +kernel

theorem backward_M_checked :
    checkRows PilotData.data StaticGapData.backwardM Child5MoreData.labels549 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_M_labels_checked, backward_M_children_checked⟩

theorem backward_M_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.backwardM.map Row.event) Child5MoreData.labels549 :=
  checkRows_wellLabelled PilotData.data StaticGapData.backwardM
    Child5MoreData.labels549 backward_M_checked

theorem backward_support573 :
    (StaticGapData.backwardM.map Row.event).all (Boundary192.supportedB StaticGapData.new573) = true := by
  decide +kernel

theorem backward_touched573 :
    StaticGapData.new573.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.backwardM.map Row.event) Child5MoreData.labels549 r == (7 : FrameLabel)) = true := by
  rfl

theorem backward_checkpoint573 :
    LemmaG.Stream.labRun (StaticGapData.backwardM.map Row.event) Child5MoreData.labels549 = StaticGapData.labels573 :=
  SparseValues.sparse_checkpoint StaticGapData.backwardM Child5MoreData.labels549
    (fun _ => (7 : FrameLabel)) StaticGapData.new573 backward_support573 backward_touched573

theorem backward_composed_wellLabelled573 :
    LemmaG.Stream.WellLabelled (((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨Child5MoreCheck.backward_composed_wellLabelled549, ?_⟩
  rw [Child5MoreCheck.backward_composed_checkpoint549]
  exact backward_M_wellLabelled

theorem backward_composed_checkpoint573 :
    LemmaG.Stream.labRun (((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels573 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, Child5MoreCheck.backward_composed_checkpoint549]
  exact backward_checkpoint573

theorem exact_N_source_indices :
    StaticGapData.forwardN.map Row.sourceIndex = List.range' 11424 24 ∧
    StaticGapData.backwardN.map Row.sourceIndex = List.range' 11424 24 := by
  decide +kernel

theorem forward_N_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.forwardN StaticGapData.labels573 = true := by
  decide +kernel

theorem forward_N_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.forwardN = true := by
  decide +kernel

theorem forward_N_checked :
    checkRows PilotData.data StaticGapData.forwardN StaticGapData.labels573 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_N_labels_checked, forward_N_children_checked⟩

theorem forward_N_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.forwardN.map Row.event) StaticGapData.labels573 :=
  checkRows_wellLabelled PilotData.data StaticGapData.forwardN
    StaticGapData.labels573 forward_N_checked

theorem forward_support597 :
    (StaticGapData.forwardN.map Row.event).all (Boundary192.supportedB StaticGapData.new597) = true := by
  decide +kernel

theorem forward_touched597 :
    StaticGapData.new597.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.forwardN.map Row.event) StaticGapData.labels573 r == (7 : FrameLabel)) = true := by
  rfl

theorem forward_checkpoint597 :
    LemmaG.Stream.labRun (StaticGapData.forwardN.map Row.event) StaticGapData.labels573 = StaticGapData.labels597 :=
  SparseValues.sparse_checkpoint StaticGapData.forwardN StaticGapData.labels573
    (fun _ => (7 : FrameLabel)) StaticGapData.new597 forward_support597 forward_touched597

theorem forward_composed_wellLabelled597 :
    LemmaG.Stream.WellLabelled ((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled573, ?_⟩
  rw [forward_composed_checkpoint573]
  exact forward_N_wellLabelled

theorem forward_composed_checkpoint597 :
    LemmaG.Stream.labRun ((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels597 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint573]
  exact forward_checkpoint597

theorem backward_N_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.backwardN StaticGapData.labels573 = true := by
  decide +kernel

theorem backward_N_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.backwardN = true := by
  decide +kernel

theorem backward_N_checked :
    checkRows PilotData.data StaticGapData.backwardN StaticGapData.labels573 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_N_labels_checked, backward_N_children_checked⟩

theorem backward_N_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.backwardN.map Row.event) StaticGapData.labels573 :=
  checkRows_wellLabelled PilotData.data StaticGapData.backwardN
    StaticGapData.labels573 backward_N_checked

theorem backward_support597 :
    (StaticGapData.backwardN.map Row.event).all (Boundary192.supportedB StaticGapData.new597) = true := by
  decide +kernel

theorem backward_touched597 :
    StaticGapData.new597.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.backwardN.map Row.event) StaticGapData.labels573 r == (7 : FrameLabel)) = true := by
  rfl

theorem backward_checkpoint597 :
    LemmaG.Stream.labRun (StaticGapData.backwardN.map Row.event) StaticGapData.labels573 = StaticGapData.labels597 :=
  SparseValues.sparse_checkpoint StaticGapData.backwardN StaticGapData.labels573
    (fun _ => (7 : FrameLabel)) StaticGapData.new597 backward_support597 backward_touched597

theorem backward_composed_wellLabelled597 :
    LemmaG.Stream.WellLabelled ((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled573, ?_⟩
  rw [backward_composed_checkpoint573]
  exact backward_N_wellLabelled

theorem backward_composed_checkpoint597 :
    LemmaG.Stream.labRun ((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels597 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint573]
  exact backward_checkpoint597

theorem exact_O_source_indices :
    StaticGapData.forwardO.map Row.sourceIndex = List.range' 11448 24 ∧
    StaticGapData.backwardO.map Row.sourceIndex = List.range' 11448 24 := by
  decide +kernel

theorem forward_O_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.forwardO StaticGapData.labels597 = true := by
  decide +kernel

theorem forward_O_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.forwardO = true := by
  decide +kernel

theorem forward_O_checked :
    checkRows PilotData.data StaticGapData.forwardO StaticGapData.labels597 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_O_labels_checked, forward_O_children_checked⟩

theorem forward_O_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.forwardO.map Row.event) StaticGapData.labels597 :=
  checkRows_wellLabelled PilotData.data StaticGapData.forwardO
    StaticGapData.labels597 forward_O_checked

theorem forward_support621 :
    (StaticGapData.forwardO.map Row.event).all (Boundary192.supportedB StaticGapData.new621) = true := by
  decide +kernel

theorem forward_touched621 :
    StaticGapData.new621.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.forwardO.map Row.event) StaticGapData.labels597 r == (7 : FrameLabel)) = true := by
  rfl

theorem forward_checkpoint621 :
    LemmaG.Stream.labRun (StaticGapData.forwardO.map Row.event) StaticGapData.labels597 = StaticGapData.labels621 :=
  SparseValues.sparse_checkpoint StaticGapData.forwardO StaticGapData.labels597
    (fun _ => (7 : FrameLabel)) StaticGapData.new621 forward_support621 forward_touched621

theorem forward_composed_wellLabelled621 :
    LemmaG.Stream.WellLabelled (((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_composed_wellLabelled597, ?_⟩
  rw [forward_composed_checkpoint597]
  exact forward_O_wellLabelled

theorem forward_composed_checkpoint621 :
    LemmaG.Stream.labRun (((((((((((((((((PilotData.forward ++ NextData.forward) ++ BatchData.forwardA) ++ BatchData.forwardB) ++ Child34Data.forwardC) ++ Child34Data.forwardD) ++ Child5Data.forwardE) ++ Child5Data.forwardF) ++ Child5TailData.forwardG) ++ Child5TailData.forwardH) ++ Child5BodyData.forwardI) ++ Child5BodyData.forwardJ) ++ Child5MoreData.forwardK) ++ Child5MoreData.forwardL) ++ StaticGapData.forwardM) ++ StaticGapData.forwardN) ++ StaticGapData.forwardO).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels621 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_composed_checkpoint597]
  exact forward_checkpoint621

theorem backward_O_labels_checked :
    CheckDecomposition.labelRowsB StaticGapData.backwardO StaticGapData.labels597 = true := by
  decide +kernel

theorem backward_O_children_checked :
    CheckDecomposition.childRowsB PilotData.data StaticGapData.backwardO = true := by
  decide +kernel

theorem backward_O_checked :
    checkRows PilotData.data StaticGapData.backwardO StaticGapData.labels597 = true := by
  rw [CheckDecomposition.checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_O_labels_checked, backward_O_children_checked⟩

theorem backward_O_wellLabelled :
    LemmaG.Stream.WellLabelled (StaticGapData.backwardO.map Row.event) StaticGapData.labels597 :=
  checkRows_wellLabelled PilotData.data StaticGapData.backwardO
    StaticGapData.labels597 backward_O_checked

theorem backward_support621 :
    (StaticGapData.backwardO.map Row.event).all (Boundary192.supportedB StaticGapData.new621) = true := by
  decide +kernel

theorem backward_touched621 :
    StaticGapData.new621.all (fun r =>
      LemmaG.Stream.labRun (StaticGapData.backwardO.map Row.event) StaticGapData.labels597 r == (7 : FrameLabel)) = true := by
  rfl

theorem backward_checkpoint621 :
    LemmaG.Stream.labRun (StaticGapData.backwardO.map Row.event) StaticGapData.labels597 = StaticGapData.labels621 :=
  SparseValues.sparse_checkpoint StaticGapData.backwardO StaticGapData.labels597
    (fun _ => (7 : FrameLabel)) StaticGapData.new621 backward_support621 backward_touched621

theorem backward_composed_wellLabelled621 :
    LemmaG.Stream.WellLabelled (((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO).map Row.event)
      (initialLabels PilotData.data) := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_composed_wellLabelled597, ?_⟩
  rw [backward_composed_checkpoint597]
  exact backward_O_wellLabelled

theorem backward_composed_checkpoint621 :
    LemmaG.Stream.labRun (((((((((((((((((PilotData.backward ++ NextData.backward) ++ BatchData.backwardA) ++ BatchData.backwardB) ++ Child34Data.backwardC) ++ Child34Data.backwardD) ++ Child5Data.backwardE) ++ Child5Data.backwardF) ++ Child5TailData.backwardG) ++ Child5TailData.backwardH) ++ Child5BodyData.backwardI) ++ Child5BodyData.backwardJ) ++ Child5MoreData.backwardK) ++ Child5MoreData.backwardL) ++ StaticGapData.backwardM) ++ StaticGapData.backwardN) ++ StaticGapData.backwardO).map Row.event)
      (initialLabels PilotData.data) = StaticGapData.labels621 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_composed_checkpoint597]
  exact backward_checkpoint621

#print axioms exact_M_source_indices
#print axioms forward_M_labels_checked
#print axioms forward_M_children_checked
#print axioms forward_M_checked
#print axioms forward_M_wellLabelled
#print axioms forward_support573
#print axioms forward_touched573
#print axioms forward_checkpoint573
#print axioms forward_composed_wellLabelled573
#print axioms forward_composed_checkpoint573
#print axioms backward_M_labels_checked
#print axioms backward_M_children_checked
#print axioms backward_M_checked
#print axioms backward_M_wellLabelled
#print axioms backward_support573
#print axioms backward_touched573
#print axioms backward_checkpoint573
#print axioms backward_composed_wellLabelled573
#print axioms backward_composed_checkpoint573
#print axioms exact_N_source_indices
#print axioms forward_N_labels_checked
#print axioms forward_N_children_checked
#print axioms forward_N_checked
#print axioms forward_N_wellLabelled
#print axioms forward_support597
#print axioms forward_touched597
#print axioms forward_checkpoint597
#print axioms forward_composed_wellLabelled597
#print axioms forward_composed_checkpoint597
#print axioms backward_N_labels_checked
#print axioms backward_N_children_checked
#print axioms backward_N_checked
#print axioms backward_N_wellLabelled
#print axioms backward_support597
#print axioms backward_touched597
#print axioms backward_checkpoint597
#print axioms backward_composed_wellLabelled597
#print axioms backward_composed_checkpoint597
#print axioms exact_O_source_indices
#print axioms forward_O_labels_checked
#print axioms forward_O_children_checked
#print axioms forward_O_checked
#print axioms forward_O_wellLabelled
#print axioms forward_support621
#print axioms forward_touched621
#print axioms forward_checkpoint621
#print axioms forward_composed_wellLabelled621
#print axioms forward_composed_checkpoint621
#print axioms backward_O_labels_checked
#print axioms backward_O_children_checked
#print axioms backward_O_checked
#print axioms backward_O_wellLabelled
#print axioms backward_support621
#print axioms backward_touched621
#print axioms backward_checkpoint621
#print axioms backward_composed_wellLabelled621
#print axioms backward_composed_checkpoint621
end CurrentMain.F19SelectedCoverage.StaticGapCheckA
