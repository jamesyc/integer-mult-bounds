import CurrentScalarCentreBand
import Current535CoverageCheck

/-!
Current997 coefficient-decoder bridge for the accepted current45 coverage blocks.
The accepted denominator-aware checkRows facts are premises; no finite slice is
reevaluated. The already accepted current centre decoder/run transport is reused.
PR509 RecipesExact, current packed execution, canonical operator interpretation,
omitted adapters and physical work remain explicit downstream obligations.
Conditional source kappa=1584931111785787/1000000000000000000.
Apache-2.0; PR509 and source notices remain applicable. OpenAI-assisted.
-/
namespace CurrentMain.CurrentCheckedScalarRows
open CanonicalFrameCoverage
open CurrentScalarCentreBand (ScalarEvent decodeEvent decodeRows decoded_labels
  decoded_rows_run rawRowsRun)
open F19ScalarEventInterpretation (decodeCoefficient)
variable {frameCount : Nat}

/-- A checked scalar annotation supplies the actual event denominator condition;
WellLabelled alone would not supply this fact. -/
private theorem annotation_decodes (row : Row frameCount) (labels : Register → FrameLabel frameCount)
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
theorem decoded_admissible (e : LabelEvent frameCount) (decoded : ScalarEvent frameCount)
    (hdecode : decodeEvent e = some decoded) (labels : Register → FrameLabel frameCount) :
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

private theorem checked_rows_labels (p : SelectedData frameCount) (rows : List (Row frameCount))
    (labels : Register → FrameLabel frameCount) (hcheck : checkRows p rows labels = true) :
    ∃ es : List (ScalarEvent frameCount),
      decodeRows rows = some es ∧
      LemmaG.Stream.WellLabelled es labels ∧
      (∀ l, LemmaG.Stream.labRun es l = LemmaG.Stream.labRun (rows.map Row.event) l) := by
  induction rows generalizing labels with
  | nil =>
      refine ⟨[], ?_, trivial, ?_⟩
      · simp [decodeRows]
      · intro l; rfl
  | cons row rows ih =>
      change (admissibleB row.event labels && (scalarAnnotationB row labels &&
        (childReferenceB p row && checkRows p rows (row.event.lab labels)))) = true at hcheck
      have ha := (Bool.and_eq_true_iff.mp hcheck).1
      have hrest := (Bool.and_eq_true_iff.mp hcheck).2
      have hs := (Bool.and_eq_true_iff.mp hrest).1
      have ht := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hrest).2).2
      obtain ⟨decoded, hd⟩ := annotation_decodes row labels hs
      obtain ⟨es, he, hw, hl⟩ := ih (row.event.lab labels) ht
      refine ⟨decoded :: es, ?_, ?_, ?_⟩
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

/-- Exact ordered rational decoding, unchanged current labels/admissibility, and
raw scalar run equality. This is syntax transport, not a new conjugation proof. -/
theorem checked_rows_sound {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (p : SelectedData frameCount) (rows : List (Row frameCount))
    (labels : Register → FrameLabel frameCount)
    (hc : checkRows p rows labels = true) :
    ∃ es : List (ScalarEvent frameCount), decodeRows rows = some es ∧
      LemmaG.Stream.WellLabelled es labels ∧
      (∀ l, LemmaG.Stream.labRun es l = LemmaG.Stream.labRun (rows.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun rows h = some (LemmaG.Stream.scalRun es h)) := by
  obtain ⟨es, hd, hw, hl⟩ := checked_rows_labels p rows labels hc
  exact ⟨es, hd, hw, hl, fun h => decoded_rows_run rows es hd h⟩

theorem selected_forward_A {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 997),
      decodeRows Current535CoverageData.forwardA = some es ∧
      LemmaG.Stream.WellLabelled es Current535CoverageData.labels0 ∧
      (∀ l, LemmaG.Stream.labRun es l =
        LemmaG.Stream.labRun (Current535CoverageData.forwardA.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun Current535CoverageData.forwardA h =
        some (LemmaG.Stream.scalRun es h)) :=
  checked_rows_sound (M := M) Current535CoverageData.data _ _
    Current535CoverageCheck.forward_A_checked

theorem selected_forward_B {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 997),
      decodeRows Current535CoverageData.forwardB = some es ∧
      LemmaG.Stream.WellLabelled es Current535CoverageData.labels24 ∧
      (∀ l, LemmaG.Stream.labRun es l =
        LemmaG.Stream.labRun (Current535CoverageData.forwardB.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun Current535CoverageData.forwardB h =
        some (LemmaG.Stream.scalRun es h)) :=
  checked_rows_sound (M := M) Current535CoverageData.data _ _
    Current535CoverageCheck.forward_B_checked

theorem selected_backward_A {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 997),
      decodeRows Current535CoverageData.backwardA = some es ∧
      LemmaG.Stream.WellLabelled es Current535CoverageData.labels0 ∧
      (∀ l, LemmaG.Stream.labRun es l =
        LemmaG.Stream.labRun (Current535CoverageData.backwardA.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun Current535CoverageData.backwardA h =
        some (LemmaG.Stream.scalRun es h)) :=
  checked_rows_sound (M := M) Current535CoverageData.data _ _
    Current535CoverageCheck.backward_A_checked

theorem selected_backward_B {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 997),
      decodeRows Current535CoverageData.backwardB = some es ∧
      LemmaG.Stream.WellLabelled es Current535CoverageData.labels24 ∧
      (∀ l, LemmaG.Stream.labRun es l =
        LemmaG.Stream.labRun (Current535CoverageData.backwardB.map Row.event) l) ∧
      (∀ h : Register → M, rawRowsRun Current535CoverageData.backwardB h =
        some (LemmaG.Stream.scalRun es h)) :=
  checked_rows_sound (M := M) Current535CoverageData.data _ _
    Current535CoverageCheck.backward_B_checked

end CurrentMain.CurrentCheckedScalarRows

#print axioms CurrentMain.CurrentCheckedScalarRows.decoded_admissible
#print axioms CurrentMain.CurrentCheckedScalarRows.checked_rows_sound
#print axioms CurrentMain.CurrentCheckedScalarRows.selected_forward_A
#print axioms CurrentMain.CurrentCheckedScalarRows.selected_forward_B
#print axioms CurrentMain.CurrentCheckedScalarRows.selected_backward_A
#print axioms CurrentMain.CurrentCheckedScalarRows.selected_backward_B
