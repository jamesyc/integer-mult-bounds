import Current596CKFirst33Transport

/-! Exact current5996 CK raw9932..9939, both orientations. The eight new rows
exercise old0→3 and nonzero-old3→4, actual catalog ordinals1/173, rank1.
The lookup catalog is the exact first174 entries only, preserving original
ordinals. It is not a full3040-entry coverage claim. Current1082 dimensions
and728 initial labels reuse their source-equal predecessor prefix.
The accepted full33-row checkpoint is transported through the shared label map;
none of the accepted33 rows is decided again. All736 labels remain explicit.
Actual pre-A execution, omitted adapters, operators for both new keys, physical
packed execution and full work remain separate. Conditional source context
kappa=16127213726553/10000000000000000; no kappa theorem follows.
Apache-2.0; upstream PR509/588/596 and accepted checkpoint attribution retained.
Prepared with OpenAI assistance. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.Current596CKNext8
open CanonicalFrameCoverage FrameDomainTransport
open CurrentScalarCentreBand (ScalarEvent decodeRows)
namespace Old
abbrev data := Current9594CKCoverageData.data
end Old

/-- The register domain is unchanged. Only the value stored as a label is mapped. -/
theorem raw_mapEvent_lab {n m : Nat} (f : Fin n → Fin m)
    (e : LabelEvent n) (labels : Register → Fin n) :
    (mapEvent f e).lab (fun r => f (labels r)) = fun r => f (e.lab labels r) := by
  cases e with
  | relabel t a b =>
      funext r
      by_cases hr : r = t
      · subst r; simp [mapEvent, LemmaG.Event.lab]
      · simp [mapEvent, LemmaG.Event.lab, Function.update_of_ne hr]
  | add t s q => rfl
  | scale t q => rfl
  | copy t s a =>
      funext r
      by_cases hr : r = t
      · subst r; simp [mapEvent, LemmaG.Event.lab]
      · simp [mapEvent, LemmaG.Event.lab, Function.update_of_ne hr]
  | clear t a =>
      funext r
      by_cases hr : r = t
      · subst r; simp [mapEvent, LemmaG.Event.lab]
      · simp [mapEvent, LemmaG.Event.lab, Function.update_of_ne hr]

/-- Forward admissibility transport needs equality preservation, not an inverse. -/
theorem raw_mapEvent_admissible {n m : Nat} (f : Fin n → Fin m)
    (e : LabelEvent n) (labels : Register → Fin n) (h : e.Admissible labels) :
    (mapEvent f e).Admissible (fun r => f (labels r)) := by
  cases e with
  | relabel r a b => exact congrArg f h
  | add t s q => exact congrArg f h
  | scale t q => trivial
  | copy t s a => exact congrArg f h
  | clear t a => trivial

/-- This is label syntax transport, reusing the existing stream predicate. -/
theorem raw_wellLabelled_map {n m : Nat} (f : Fin n → Fin m)
    (es : List (LabelEvent n)) (labels : Register → Fin n)
    (h : LemmaG.Stream.WellLabelled es labels) :
    LemmaG.Stream.WellLabelled (es.map (mapEvent f)) (fun r => f (labels r)) := by
  induction es generalizing labels with
  | nil => trivial
  | cons e es ih =>
      change e.Admissible labels ∧ LemmaG.Stream.WellLabelled es (e.lab labels) at h
      change (mapEvent f e).Admissible (fun r => f (labels r)) ∧
        LemmaG.Stream.WellLabelled (es.map (mapEvent f))
          ((mapEvent f e).lab (fun r => f (labels r)))
      refine ⟨raw_mapEvent_admissible f e labels h.1, ?_⟩
      rw [raw_mapEvent_lab]
      exact ih (e.lab labels) h.2

/-- Coefficient syntax does not affect the label-state fold. -/
theorem raw_labRun_map {n m : Nat} (f : Fin n → Fin m)
    (es : List (LabelEvent n)) (labels : Register → Fin n) :
    LemmaG.Stream.labRun (es.map (mapEvent f)) (fun r => f (labels r)) =
      fun r => f (LemmaG.Stream.labRun es labels r) := by
  induction es generalizing labels with
  | nil => rfl
  | cons e es ih =>
      change LemmaG.Stream.labRun (es.map (mapEvent f))
        ((mapEvent f e).lab (fun r => f (labels r))) = _
      rw [raw_mapEvent_lab]
      exact ih (e.lab labels)

abbrev embed := Current596CKCentre.embed
abbrev labels0 := Current596CKFirst33Transport.labels0
def labels33 (r : Register) : Fin 1082 := embed (Current9594CKCoverageData.labels33 r)
def prefixForward : List (Row 1082) :=
  mapRows embed (Current9594CKCoverageData.forwardA ++ Current9594CKCoverageData.forwardB)
def prefixBackward : List (Row 1082) :=
  mapRows embed (Current9594CKCoverageData.backwardA ++ Current9594CKCoverageData.backwardB)

/-- A source-bound catalog prefix with actual ordinal positions, no filler keys. -/
def lookupData : SelectedData 1082 where
  frameDimensions := Current9594CKCoverageData.frameDimensions ++ #[8, 8, 8]
  initialOriginalLabels := Current9594CKCoverageData.initialOriginalLabels.map embed
  children := (Current9594CKCoverageData.children.extract 0 174).map
    (fun c => ⟨embed c.oldFrame, embed c.newFrame, c.rank⟩)
  forward := []
  backward := []

def forward : List (Row 1082) := [
  ⟨9932, .relabel 474 0 3, none, some (1, 1)⟩,
  ⟨9933, .add 474 464 ((-1), (1)), some 3, none⟩,
  ⟨9934, .relabel 474 3 4, none, some (173, 1)⟩,
  ⟨9935, .add 474 488 ((-1), (1)), some 4, none⟩,
  ⟨9936, .relabel 475 0 3, none, some (1, 1)⟩,
  ⟨9937, .add 475 464 ((-1), (1)), some 3, none⟩,
  ⟨9938, .relabel 475 3 4, none, some (173, 1)⟩,
  ⟨9939, .add 475 489 ((-1), (1)), some 4, none⟩
]

def backward : List (Row 1082) := [
  ⟨9932, .relabel 474 0 3, none, some (1, 1)⟩,
  ⟨9933, .add 464 474 ((1), (1)), some 3, none⟩,
  ⟨9934, .relabel 474 3 4, none, some (173, 1)⟩,
  ⟨9935, .add 488 474 ((1), (1)), some 4, none⟩,
  ⟨9936, .relabel 475 0 3, none, some (1, 1)⟩,
  ⟨9937, .add 464 475 ((1), (1)), some 3, none⟩,
  ⟨9938, .relabel 475 3 4, none, some (173, 1)⟩,
  ⟨9939, .add 489 475 ((1), (1)), some 4, none⟩
]

def support41 : List Register := [474, 475]
def labels41 (r : Register) : Fin 1082 := if r ∈ support41 then 4 else labels33 r

theorem exact_source_indices : forward.map Row.sourceIndex = List.range' 9932 8 ∧
    backward.map Row.sourceIndex = List.range' 9932 8 := by decide +kernel

theorem forward_prefix_checkpoint33 :
    LemmaG.Stream.labRun (prefixForward.map Row.event) labels0 = labels33 := by
  have h := raw_labRun_map embed ((Current9594CKCoverageData.forwardA ++ Current9594CKCoverageData.forwardB).map Row.event) Current9594CKCoverageData.labels0
  rw [Current9594CKCoverageCheck.forward_composed_checkpoint33] at h
  simpa only [prefixForward, mapRows, List.map_map, Function.comp_def, mapRow,
    labels0, Current596CKFirst33Transport.labels0, labels33] using h

theorem forward_prefix_wellLabelled33 :
    LemmaG.Stream.WellLabelled (prefixForward.map Row.event) labels0 := by
  have h := raw_wellLabelled_map embed ((Current9594CKCoverageData.forwardA ++ Current9594CKCoverageData.forwardB).map Row.event)
    Current9594CKCoverageData.labels0 Current9594CKCoverageCheck.forward_composed_wellLabelled33
  simpa only [prefixForward, mapRows, List.map_map, Function.comp_def, mapRow,
    labels0, Current596CKFirst33Transport.labels0] using h

theorem forward_labels_checked : labelRowsB forward labels33 = true := by decide +kernel

theorem forward_children_checked : childRowsB lookupData forward = true := by decide +kernel

theorem forward_checked : checkRows lookupData forward labels33 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨forward_labels_checked, forward_children_checked⟩

theorem forward_wellLabelled :
    LemmaG.Stream.WellLabelled (forward.map Row.event) labels33 :=
  checkRows_wellLabelled lookupData forward labels33 forward_checked

theorem forward_support41 :
    (forward.map Row.event).all (supportedB support41) = true := by decide +kernel

theorem forward_touched41 : support41.all (fun r =>
    LemmaG.Stream.labRun (forward.map Row.event) labels33 r == (4 : Fin 1082)) = true := by decide +kernel

theorem forward_checkpoint41 :
    LemmaG.Stream.labRun (forward.map Row.event) labels33 = labels41 :=
  sparse_checkpoint forward labels33 (fun _ => (4 : Fin 1082)) support41
    forward_support41 forward_touched41

theorem forward_composed_wellLabelled41 :
    LemmaG.Stream.WellLabelled ((prefixForward ++ forward).map Row.event) labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨forward_prefix_wellLabelled33, ?_⟩
  rw [forward_prefix_checkpoint33]
  exact forward_wellLabelled

theorem forward_composed_checkpoint41 :
    LemmaG.Stream.labRun ((prefixForward ++ forward).map Row.event) labels0 = labels41 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, forward_prefix_checkpoint33]
  exact forward_checkpoint41

/-- Denominator-aware ordered decoding reuses the accepted generic bridge. -/
theorem forward_decoded : ∃ es : List (ScalarEvent 1082),
    decodeRows forward = some es ∧ LemmaG.Stream.WellLabelled es labels33 ∧
    LemmaG.Stream.labRun es labels33 = labels41 := by
  obtain ⟨es, hd, hw, hl, _⟩ := CurrentCheckedScalarRows.checked_rows_sound
    (M := ℚ) lookupData forward labels33 forward_checked
  exact ⟨es, hd, hw, (hl labels33).trans forward_checkpoint41⟩

theorem backward_prefix_checkpoint33 :
    LemmaG.Stream.labRun (prefixBackward.map Row.event) labels0 = labels33 := by
  have h := raw_labRun_map embed ((Current9594CKCoverageData.backwardA ++ Current9594CKCoverageData.backwardB).map Row.event) Current9594CKCoverageData.labels0
  rw [Current9594CKCoverageCheck.backward_composed_checkpoint33] at h
  simpa only [prefixBackward, mapRows, List.map_map, Function.comp_def, mapRow,
    labels0, Current596CKFirst33Transport.labels0, labels33] using h

theorem backward_prefix_wellLabelled33 :
    LemmaG.Stream.WellLabelled (prefixBackward.map Row.event) labels0 := by
  have h := raw_wellLabelled_map embed ((Current9594CKCoverageData.backwardA ++ Current9594CKCoverageData.backwardB).map Row.event)
    Current9594CKCoverageData.labels0 Current9594CKCoverageCheck.backward_composed_wellLabelled33
  simpa only [prefixBackward, mapRows, List.map_map, Function.comp_def, mapRow,
    labels0, Current596CKFirst33Transport.labels0] using h

theorem backward_labels_checked : labelRowsB backward labels33 = true := by decide +kernel

theorem backward_children_checked : childRowsB lookupData backward = true := by decide +kernel

theorem backward_checked : checkRows lookupData backward labels33 = true := by
  rw [checkRows_factor]
  exact Bool.and_eq_true_iff.mpr ⟨backward_labels_checked, backward_children_checked⟩

theorem backward_wellLabelled :
    LemmaG.Stream.WellLabelled (backward.map Row.event) labels33 :=
  checkRows_wellLabelled lookupData backward labels33 backward_checked

theorem backward_support41 :
    (backward.map Row.event).all (supportedB support41) = true := by decide +kernel

theorem backward_touched41 : support41.all (fun r =>
    LemmaG.Stream.labRun (backward.map Row.event) labels33 r == (4 : Fin 1082)) = true := by decide +kernel

theorem backward_checkpoint41 :
    LemmaG.Stream.labRun (backward.map Row.event) labels33 = labels41 :=
  sparse_checkpoint backward labels33 (fun _ => (4 : Fin 1082)) support41
    backward_support41 backward_touched41

theorem backward_composed_wellLabelled41 :
    LemmaG.Stream.WellLabelled ((prefixBackward ++ backward).map Row.event) labels0 := by
  rw [List.map_append]
  apply (LemmaG.Stream.wellLabelled_append _ _ _).mpr
  refine ⟨backward_prefix_wellLabelled33, ?_⟩
  rw [backward_prefix_checkpoint33]
  exact backward_wellLabelled

theorem backward_composed_checkpoint41 :
    LemmaG.Stream.labRun ((prefixBackward ++ backward).map Row.event) labels0 = labels41 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, backward_prefix_checkpoint33]
  exact backward_checkpoint41

/-- Denominator-aware ordered decoding reuses the accepted generic bridge. -/
theorem backward_decoded : ∃ es : List (ScalarEvent 1082),
    decodeRows backward = some es ∧ LemmaG.Stream.WellLabelled es labels33 ∧
    LemmaG.Stream.labRun es labels33 = labels41 := by
  obtain ⟨es, hd, hw, hl, _⟩ := CurrentCheckedScalarRows.checked_rows_sound
    (M := ℚ) lookupData backward labels33 backward_checked
  exact ⟨es, hd, hw, (hl labels33).trans backward_checkpoint41⟩

end CurrentMain.Current596CKNext8

#print axioms CurrentMain.Current596CKNext8.raw_mapEvent_lab
#print axioms CurrentMain.Current596CKNext8.raw_mapEvent_admissible
#print axioms CurrentMain.Current596CKNext8.raw_wellLabelled_map
#print axioms CurrentMain.Current596CKNext8.raw_labRun_map
#print axioms CurrentMain.Current596CKNext8.exact_source_indices
#print axioms CurrentMain.Current596CKNext8.forward_prefix_checkpoint33
#print axioms CurrentMain.Current596CKNext8.forward_prefix_wellLabelled33
#print axioms CurrentMain.Current596CKNext8.forward_labels_checked
#print axioms CurrentMain.Current596CKNext8.forward_children_checked
#print axioms CurrentMain.Current596CKNext8.forward_checked
#print axioms CurrentMain.Current596CKNext8.forward_wellLabelled
#print axioms CurrentMain.Current596CKNext8.forward_support41
#print axioms CurrentMain.Current596CKNext8.forward_touched41
#print axioms CurrentMain.Current596CKNext8.forward_checkpoint41
#print axioms CurrentMain.Current596CKNext8.forward_composed_wellLabelled41
#print axioms CurrentMain.Current596CKNext8.forward_composed_checkpoint41
#print axioms CurrentMain.Current596CKNext8.forward_decoded
#print axioms CurrentMain.Current596CKNext8.backward_prefix_checkpoint33
#print axioms CurrentMain.Current596CKNext8.backward_prefix_wellLabelled33
#print axioms CurrentMain.Current596CKNext8.backward_labels_checked
#print axioms CurrentMain.Current596CKNext8.backward_children_checked
#print axioms CurrentMain.Current596CKNext8.backward_checked
#print axioms CurrentMain.Current596CKNext8.backward_wellLabelled
#print axioms CurrentMain.Current596CKNext8.backward_support41
#print axioms CurrentMain.Current596CKNext8.backward_touched41
#print axioms CurrentMain.Current596CKNext8.backward_checkpoint41
#print axioms CurrentMain.Current596CKNext8.backward_composed_wellLabelled41
#print axioms CurrentMain.Current596CKNext8.backward_composed_checkpoint41
#print axioms CurrentMain.Current596CKNext8.backward_decoded
