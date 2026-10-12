import Current596CKCentre
import Current9594CKFirst33KeyRestriction

/-! Current PR596 CK first33, exact selected main5996. The emitted raw rows and
starting labels agree with the accepted predecessor, while the label domain is
now Fin1082. This module consumes the shared frame-domain map and transports
ordered decoding, WellLabelled and the sole relabel key0→2; no row or catalog
predicate is reevaluated. Current source equality is pinned by external literal
readback. Actual recipes/charts, omitted adapters and packed execution remain
separate. Author-checked conditional kappa=16127213726553/10000000000000000.
Apache-2.0; PR509, PR588/596 and accepted predecessor attribution retained.
Prepared with OpenAI assistance. -/
set_option Elab.async false
namespace CurrentMain.Current596CKFirst33Transport
open CanonicalFrameCoverage
open CurrentScalarCentreBand (ScalarEvent decodeRows)
open FrameDomainTransport
open Current9594CKFirst33KeyRestriction (RelabelsUse KeyedDecoded)

/-- The register domain is unchanged. Only the value stored as a label is mapped. -/
theorem mapEvent_lab {n m : Nat} (f : Fin n → Fin m)
    (e : ScalarEvent n) (labels : Register → Fin n) :
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
theorem mapEvent_admissible {n m : Nat} (f : Fin n → Fin m)
    (e : ScalarEvent n) (labels : Register → Fin n) (h : e.Admissible labels) :
    (mapEvent f e).Admissible (fun r => f (labels r)) := by
  cases e with
  | relabel r a b => exact congrArg f h
  | add t s q => exact congrArg f h
  | scale t q => trivial
  | copy t s a => exact congrArg f h
  | clear t a => trivial

/-- This is label syntax transport, reusing the existing stream predicate. -/
theorem wellLabelled_map {n m : Nat} (f : Fin n → Fin m)
    (es : List (ScalarEvent n)) (labels : Register → Fin n)
    (h : LemmaG.Stream.WellLabelled es labels) :
    LemmaG.Stream.WellLabelled (es.map (mapEvent f)) (fun r => f (labels r)) := by
  induction es generalizing labels with
  | nil => trivial
  | cons e es ih =>
      change e.Admissible labels ∧ LemmaG.Stream.WellLabelled es (e.lab labels) at h
      change (mapEvent f e).Admissible (fun r => f (labels r)) ∧
        LemmaG.Stream.WellLabelled (es.map (mapEvent f))
          ((mapEvent f e).lab (fun r => f (labels r)))
      refine ⟨mapEvent_admissible f e labels h.1, ?_⟩
      rw [mapEvent_lab]
      exact ih (e.lab labels) h.2

/-- Ordered membership and the relabel constructor preserve the selected key. -/
theorem relabelsUse_map {n m : Nat} (f : Fin n → Fin m)
    (old new : Fin n) (es : List (ScalarEvent n)) (h : RelabelsUse old new es) :
    RelabelsUse (f old) (f new) (es.map (mapEvent f)) := by
  intro r a b hm
  obtain ⟨e, he, eq⟩ := List.mem_map.mp hm
  cases e with
  | relabel r' a' b' =>
      change LemmaG.Event.relabel r' (f a') (f b') = LemmaG.Event.relabel r a b at eq
      cases eq
      exact ⟨congrArg f (h r' a' b' he).1, congrArg f (h r' a' b' he).2⟩
  | add t s q => cases eq
  | scale t q => cases eq
  | copy t s a => cases eq
  | clear t a => cases eq

/-- Reuse the accepted denominator-aware decoder witness without a new decision. -/
theorem keyedDecoded_map {n m : Nat} (f : Fin n → Fin m)
    (old new : Fin n) (rows : List (Row n)) (labels : Register → Fin n)
    (h : KeyedDecoded old new rows labels) :
    KeyedDecoded (f old) (f new) (mapRows f rows) (fun r => f (labels r)) := by
  obtain ⟨es, hd, hw, hk⟩ := h
  refine ⟨es.map (mapEvent f), ?_, wellLabelled_map f es labels hw,
    relabelsUse_map f old new es hk⟩
  rw [decodeRows_map, hd]
  rfl

abbrev embed := Current596CKCentre.embed

def forwardA : List (Row 1082) := mapRows embed Current9594CKCoverageData.forwardA
def forwardB : List (Row 1082) := mapRows embed Current9594CKCoverageData.forwardB
def backwardA : List (Row 1082) := mapRows embed Current9594CKCoverageData.backwardA
def backwardB : List (Row 1082) := mapRows embed Current9594CKCoverageData.backwardB
def labels0 : Register → Fin 1082 := fun r => embed (Current9594CKCoverageData.labels0 r)
def labels24 : Register → Fin 1082 := fun r => embed (Current9594CKCoverageData.labels24 r)

/-- Current raw9899..9922: 24 exact rows at the mapped initial labels. -/
theorem selected_forward_A : KeyedDecoded 0 2 forwardA labels0 :=
  keyedDecoded_map embed 0 2 _ _ Current9594CKFirst33KeyRestriction.selected_forward_A

/-- Current raw9923..9931: 9 exact rows at the mapped accepted checkpoint. -/
theorem selected_forward_B : KeyedDecoded 0 2 forwardB labels24 :=
  keyedDecoded_map embed 0 2 _ _ Current9594CKFirst33KeyRestriction.selected_forward_B

theorem selected_backward_A : KeyedDecoded 0 2 backwardA labels0 :=
  keyedDecoded_map embed 0 2 _ _ Current9594CKFirst33KeyRestriction.selected_backward_A

theorem selected_backward_B : KeyedDecoded 0 2 backwardB labels24 :=
  keyedDecoded_map embed 0 2 _ _ Current9594CKFirst33KeyRestriction.selected_backward_B

end CurrentMain.Current596CKFirst33Transport

#print axioms CurrentMain.Current596CKFirst33Transport.mapEvent_lab
#print axioms CurrentMain.Current596CKFirst33Transport.mapEvent_admissible
#print axioms CurrentMain.Current596CKFirst33Transport.wellLabelled_map
#print axioms CurrentMain.Current596CKFirst33Transport.relabelsUse_map
#print axioms CurrentMain.Current596CKFirst33Transport.keyedDecoded_map
#print axioms CurrentMain.Current596CKFirst33Transport.selected_forward_A
#print axioms CurrentMain.Current596CKFirst33Transport.selected_forward_B
#print axioms CurrentMain.Current596CKFirst33Transport.selected_backward_A
#print axioms CurrentMain.Current596CKFirst33Transport.selected_backward_B
