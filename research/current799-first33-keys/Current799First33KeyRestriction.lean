/- First33 current799 gauge44 relabel-key restriction. Existing exact lists and checked
   labels/catalog predicates are reused without a new finite decision. The
   rational decoder changes coefficients only. This supplies a local key premise
   for PR509 RecipesExact; actual recipes, charts and physical execution remain
   separate. PR509 Stream: DreamingOfClouds (Claude-assisted), unchanged pin.
   Author-checked conditional source kappa = 1661634653669567/1000000000000000000.
   Apache-2.0. OpenAI-assisted. -/
import CurrentCheckedScalarRows
import Current799First33CoverageCheck

set_option Elab.async false
namespace CurrentMain.Current799First33KeyRestriction
open CanonicalFrameCoverage
open CurrentScalarCentreBand (ScalarEvent decodeEvent decodeRows)
open F19ScalarEventInterpretation (decodeCoefficient)

/-- This projection reads only a relabel's ordered old/new labels. -/
private def eventKey {n : Nat} {K : Type*} (old new : Fin n) :
    LemmaG.Event Register (Fin n) K → Prop
  | .relabel _ a b => a = old ∧ b = new
  | .add .. => True
  | .scale .. => True
  | .copy .. => True
  | .clear .. => True

private theorem decoded_event_key {n : Nat} (old new : Fin n)
    (e : LabelEvent n) (d : ScalarEvent n)
    (hd : decodeEvent e = some d) (hk : eventKey old new e) :
    eventKey old new d := by
  cases e with
  | relabel r a b =>
      have he : LemmaG.Event.relabel r a b = d := Option.some.inj hd
      subst d
      exact hk
  | add t s q =>
      cases hq : decodeCoefficient q with
      | none => simp [decodeEvent, hq] at hd
      | some c =>
          have he : LemmaG.Event.add t s c = d := by simpa [decodeEvent, hq] using hd
          subst d
          trivial
  | scale t q =>
      cases hq : decodeCoefficient q with
      | none => simp [decodeEvent, hq] at hd
      | some c =>
          have he : LemmaG.Event.scale t c = d := by simpa [decodeEvent, hq] using hd
          subst d
          trivial
  | copy t s f =>
      have he : LemmaG.Event.copy t s f = d := Option.some.inj hd
      subst d
      trivial
  | clear t f =>
      have he : LemmaG.Event.clear t f = d := Option.some.inj hd
      subst d
      trivial

/-- Membership transport for this existing Option decoder. No scalar-run or
    physical-conjugation induction is repeated. -/
private theorem decoded_keys {n : Nat} (old new : Fin n)
    (rows : List (Row n)) (es : List (ScalarEvent n))
    (hd : decodeRows rows = some es)
    (hk : ∀ row ∈ rows, eventKey old new row.event) :
    ∀ e ∈ es, eventKey old new e := by
  induction rows generalizing es with
  | nil =>
      have he : es = [] := by simpa [decodeRows] using hd.symm
      subst es
      simp
  | cons row rows ih =>
      cases he : decodeEvent row.event with
      | none => simp [decodeRows, List.mapM_cons, he] at hd
      | some d =>
          cases ht : decodeRows rows with
          | none =>
              have hm : rows.mapM (fun r => decodeEvent r.event) = none := ht
              simp [decodeRows, List.mapM_cons, he, hm] at hd
          | some ds =>
              have hm : rows.mapM (fun r => decodeEvent r.event) = some ds := ht
              have hs : d :: ds = es := by
                simpa [decodeRows, List.mapM_cons, he, hm] using hd
              subst es
              intro e hem
              rcases List.mem_cons.mp hem with hhead | htail
              · subst e
                exact decoded_event_key old new row.event d he (hk row (by simp))
              · exact ih ds ht (fun r hr => hk r (by simp [hr])) e htail

/-- Only an ordered relabel-key premise. It makes no claim about recipe values. -/
def RelabelsUse {n : Nat} (old new : Fin n) (es : List (ScalarEvent n)) : Prop :=
  ∀ r a b, LemmaG.Event.relabel r a b ∈ es → a = old ∧ b = new

/-- The exact selected lists, decoder and labels remain visible to callers. -/
def KeyedDecoded {n : Nat} (old new : Fin n) (rows : List (Row n))
    (labels : Register → Fin n) : Prop :=
  ∃ es : List (ScalarEvent n), decodeRows rows = some es ∧
    LemmaG.Stream.WellLabelled es labels ∧ RelabelsUse old new es

private theorem checked_keyed {n : Nat} (p : SelectedData n)
    (rows : List (Row n)) (labels : Register → Fin n) (old new : Fin n)
    (hc : checkRows p rows labels = true)
    (hk : ∀ row ∈ rows, eventKey old new row.event) :
    KeyedDecoded old new rows labels := by
  obtain ⟨es, hd, hw, _, _⟩ :=
    CurrentCheckedScalarRows.checked_rows_sound (M := ℚ) p rows labels hc
  refine ⟨es, hd, hw, ?_⟩
  intro r a b hm
  exact decoded_keys old new rows es hd hk (.relabel r a b) hm

/- Each key-only projection below unfolds the already accepted literal list.
   It does not reevaluate checkRows, labels, dimensions or the child catalog. -/
private theorem forward_A_keys :
    ∀ row ∈ Current799First33CoverageData.forwardA, eventKey (0 : Fin 1005) 4 row.event := by
  simp [Current799First33CoverageData.forwardA, eventKey]

private theorem forward_B_keys :
    ∀ row ∈ Current799First33CoverageData.forwardB, eventKey (0 : Fin 1005) 4 row.event := by
  simp [Current799First33CoverageData.forwardB, eventKey]

private theorem backward_A_keys :
    ∀ row ∈ Current799First33CoverageData.backwardA, eventKey (0 : Fin 1005) 4 row.event := by
  simp [Current799First33CoverageData.backwardA, eventKey]

private theorem backward_B_keys :
    ∀ row ∈ Current799First33CoverageData.backwardB, eventKey (0 : Fin 1005) 4 row.event := by
  simp [Current799First33CoverageData.backwardB, eventKey]

/-- Every rational-decoded relabel in raw9241..9264 uses current key0→4. -/
theorem selected_forward_A :
    KeyedDecoded 0 4 Current799First33CoverageData.forwardA Current799First33CoverageData.labels0 :=
  checked_keyed Current799First33CoverageData.data _ _ _ _
    Current799First33CoverageCheck.forward_A_checked forward_A_keys

/-- Every rational-decoded relabel in raw9265..9273 uses current key0→4. -/
theorem selected_forward_B :
    KeyedDecoded 0 4 Current799First33CoverageData.forwardB Current799First33CoverageData.labels24 :=
  checked_keyed Current799First33CoverageData.data _ _ _ _
    Current799First33CoverageCheck.forward_B_checked forward_B_keys

theorem selected_backward_A :
    KeyedDecoded 0 4 Current799First33CoverageData.backwardA Current799First33CoverageData.labels0 :=
  checked_keyed Current799First33CoverageData.data _ _ _ _
    Current799First33CoverageCheck.backward_A_checked backward_A_keys

theorem selected_backward_B :
    KeyedDecoded 0 4 Current799First33CoverageData.backwardB Current799First33CoverageData.labels24 :=
  checked_keyed Current799First33CoverageData.data _ _ _ _
    Current799First33CoverageCheck.backward_B_checked backward_B_keys

end CurrentMain.Current799First33KeyRestriction

#print axioms CurrentMain.Current799First33KeyRestriction.selected_forward_A
#print axioms CurrentMain.Current799First33KeyRestriction.selected_forward_B
#print axioms CurrentMain.Current799First33KeyRestriction.selected_backward_A
#print axioms CurrentMain.Current799First33KeyRestriction.selected_backward_B
