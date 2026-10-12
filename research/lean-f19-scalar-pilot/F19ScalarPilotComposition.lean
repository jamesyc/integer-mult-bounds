/-
Source proposal: composition of the accepted f19 scalar-event decoder on the
accepted bank's exact 128-row slices, raw indices10851..10978 in each direction.
This is an interpreted canonical-frame projection, not a physical full word.
Apache-2.0. OpenAI-assisted; PR509/selected supplier attribution is in SOURCE_SCOPE.
-/
import F19ScalarEventInterpretation
import F19CoveragePilotCheck

namespace CurrentMain.F19ScalarPilotComposition

open F19SelectedCoverage F19ScalarEventInterpretation

/-- A checked scalar annotation supplies the actual event denominator condition;
WellLabelled alone would not supply this fact. -/
private theorem annotation_decodes (row : Row) (labels : Register → FrameLabel)
    (h : scalarAnnotationB row labels = true) :
    ∃ decoded, decodeEvent row.event = some decoded := by
  cases he : row.event with
  | relabel r a b => exact ⟨.relabel r a b, by simp [he, decodeEvent]⟩
  | add t s q =>
      by_cases hz : q.2 = 0
      · simp [scalarAnnotationB, he, hz] at h
      · exact ⟨.add t s ((q.1 : ℚ) / (q.2 : ℚ)),
          by simp [he, decodeEvent, decodeCoefficient, hz]⟩
  | scale t q =>
      by_cases hz : q.2 = 0
      · simp [scalarAnnotationB, he, hz] at h
      · exact ⟨.scale t ((q.1 : ℚ) / (q.2 : ℚ)),
          by simp [he, decodeEvent, decodeCoefficient, hz]⟩
  | copy t s f => exact ⟨.copy t s f, by simp [he, decodeEvent]⟩
  | clear t f => exact ⟨.clear t f, by simp [he, decodeEvent]⟩

/-- Changing coefficient syntax to its rational value preserves admissibility. -/
theorem decoded_admissible (e : LabelEvent) (decoded : ScalarEvent)
    (hdecode : decodeEvent e = some decoded) (labels : Register → FrameLabel) :
    decoded.Admissible labels ↔ e.Admissible labels := by
  cases e with
  | relabel r a b =>
      simp_all [decodeEvent, LemmaG.Event.Admissible] <;> subst decoded <;> rfl
  | add t s q =>
      by_cases hd : q.2 = 0 <;>
        simp_all [decodeEvent, decodeCoefficient, hd, LemmaG.Event.Admissible] <;>
        subst decoded <;> rfl
  | scale t q =>
      by_cases hd : q.2 = 0 <;>
        simp_all [decodeEvent, decodeCoefficient, hd, LemmaG.Event.Admissible] <;>
        subst decoded <;> exact True.intro
  | copy t s f =>
      simp_all [decodeEvent, LemmaG.Event.Admissible] <;> subst decoded <;> rfl
  | clear t f =>
      simp_all [decodeEvent, LemmaG.Event.Admissible] <;> subst decoded <;> exact True.intro

section ScalarRun
variable {M : Type*} [AddCommMonoid M] [Module ℚ M]

/-- Sequential source macro updates, with the same denominator rejection as the
one-event decoder. All initial register values, including centres, are arbitrary. -/
def rawRowsRun : List Row → (Register → M) → Option (Register → M)
  | [], h => some h
  | row :: rows, h => (rawScalarStep row.event h).bind (rawRowsRun rows)

/-- Decoder composition only. Reuses the accepted event scalar/label equations and
the existing PR509 run and WellLabelled definitions; no conjugation is reproved. -/
theorem checked_rows_sound (p : SelectedData) (rows : List Row)
    (labels : Register → FrameLabel) (hcheck : checkRows p rows labels = true) :
    ∃ es : List ScalarEvent,
      decodeRows rows = some es ∧
      LemmaG.Stream.WellLabelled es labels ∧
      (∀ l, LemmaG.Stream.labRun es l = LemmaG.Stream.labRun (rows.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun rows h = some (LemmaG.Stream.scalRun es h)) := by
  induction rows generalizing labels with
  | nil =>
      refine ⟨[], ?_, trivial, ?_, ?_⟩
      · simp [decodeRows]
      · intro l; rfl
      · intro h; rfl
  | cons row rows ih =>
      change (admissibleB row.event labels && (scalarAnnotationB row labels &&
        (childReferenceB p row && checkRows p rows (row.event.lab labels)))) = true at hcheck
      have ha := (Bool.and_eq_true_iff.mp hcheck).1
      have hrest := (Bool.and_eq_true_iff.mp hcheck).2
      have hs := (Bool.and_eq_true_iff.mp hrest).1
      have ht := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hrest).2).2
      obtain ⟨decoded, hd⟩ := annotation_decodes row labels hs
      obtain ⟨es, he, hw, hl, hr⟩ := ih (row.event.lab labels) ht
      refine ⟨decoded :: es, ?_, ?_, ?_, ?_⟩
      · have hm : rows.mapM (fun r => decodeEvent r.event) = some es := he
        simp [decodeRows, List.mapM_cons, hd, hm]
      · change decoded.Admissible labels ∧ LemmaG.Stream.WellLabelled es (decoded.lab labels)
        refine ⟨(decoded_admissible row.event decoded hd labels).2
          (admissibleB_sound row.event labels ha), ?_⟩
        rw [decoded_labels row.event decoded hd labels]
        exact hw
      · intro l
        change LemmaG.Stream.labRun es (decoded.lab l) =
          LemmaG.Stream.labRun (rows.map Row.event) (row.event.lab l)
        rw [decoded_labels row.event decoded hd l]
        exact hl _
      · intro h
        change (rawScalarStep row.event h).bind (rawRowsRun rows) =
          some (LemmaG.Stream.scalRun es (decoded.scal h))
        rw [decoded_step row.event decoded hd h]
        exact hr _

/-- Exact accepted forward slice; no repeated finite arithmetic or label check. -/
theorem selected_forward_slice :
    ∃ es : List ScalarEvent,
      decodeRows PilotData.data.forward = some es ∧
      LemmaG.Stream.WellLabelled es (initialLabels PilotData.data) ∧
      (∀ l, LemmaG.Stream.labRun es l =
        LemmaG.Stream.labRun (PilotData.data.forward.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun PilotData.data.forward h =
        some (LemmaG.Stream.scalRun es h)) := by
  apply checked_rows_sound (M := M)
  exact (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp PilotCheck.selected_pilot_checked).2).1

/-- Exact accepted backward slice with the same arbitrary-input convention. -/
theorem selected_backward_slice :
    ∃ es : List ScalarEvent,
      decodeRows PilotData.data.backward = some es ∧
      LemmaG.Stream.WellLabelled es (initialLabels PilotData.data) ∧
      (∀ l, LemmaG.Stream.labRun es l =
        LemmaG.Stream.labRun (PilotData.data.backward.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun PilotData.data.backward h =
        some (LemmaG.Stream.scalRun es h)) := by
  apply checked_rows_sound (M := M)
  exact (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp PilotCheck.selected_pilot_checked).2).2
end ScalarRun

/-- Source-index identity is the accepted literal supplier, not a new decoder run. -/
theorem selected_source_indices :
    PilotData.data.forward.map Row.sourceIndex = List.range' 10851 128 ∧
    PilotData.data.backward.map Row.sourceIndex = List.range' 10851 128 :=
  PilotCheck.exact_source_indices

end CurrentMain.F19ScalarPilotComposition

#print axioms CurrentMain.F19ScalarPilotComposition.decoded_admissible
#print axioms CurrentMain.F19ScalarPilotComposition.checked_rows_sound
#print axioms CurrentMain.F19ScalarPilotComposition.selected_forward_slice
#print axioms CurrentMain.F19ScalarPilotComposition.selected_backward_slice
#print axioms CurrentMain.F19ScalarPilotComposition.selected_source_indices
