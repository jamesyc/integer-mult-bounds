import Current9594CKCentre

/-!
PR596 CK centre, pinned main5996. The selected source retains exactly the
historical 256 rows in each direction, while the frame table grows1079→1082.
The generic map below changes only the label type and keeps coefficient syntax,
registers, row indices, annotation values and child references. The current
source binding is external evidence, not a full selected-stream theorem.
Dirty COPY/CLEAR semantics and arbitrary incoming centres are retained.
Conditional source context kappa=16127213726553/10000000000000000.
Apache-2.0; PR509, accepted scalar proofs, PR588/596 attribution retained.
Prepared with OpenAI assistance. No finite band predicate is reevaluated.
-/
set_option Elab.async false
namespace CurrentMain.FrameDomainTransport
open CurrentScalarCentreBand

/-- Change only event labels; coefficients and register occurrences are exact. -/
def mapEvent {ι Λ Λ' K : Type*} (f : Λ → Λ') :
    LemmaG.Event ι Λ K → LemmaG.Event ι Λ' K
  | .relabel r a b => .relabel r (f a) (f b)
  | .add t s q => .add t s q
  | .scale t q => .scale t q
  | .copy t s a => .copy t s (f a)
  | .clear t a => .clear t (f a)

def mapRow {n m : Nat} (f : Fin n → Fin m) (row : Row n) : Row m :=
  ⟨row.sourceIndex, mapEvent f row.event, row.scalarFrame.map f, row.childRef⟩

def mapRows {n m : Nat} (f : Fin n → Fin m) (rows : List (Row n)) : List (Row m) :=
  rows.map (mapRow f)

theorem decodeEvent_map {n m : Nat} (f : Fin n → Fin m) (e : RawEvent n) :
    decodeEvent (mapEvent f e) = (decodeEvent e).map (mapEvent f) := by
  cases e with
  | relabel r a b => rfl
  | add t s q =>
      simp only [mapEvent, decodeEvent]
      cases F19ScalarEventInterpretation.decodeCoefficient q <;> rfl
  | scale t q =>
      simp only [mapEvent, decodeEvent]
      cases F19ScalarEventInterpretation.decodeCoefficient q <;> rfl
  | copy t s a => rfl
  | clear t a => rfl

private theorem decodeRows_cons {n : Nat} (row : Row n) (rows : List (Row n)) :
    decodeRows (row :: rows) =
      (decodeEvent row.event).bind (fun e => (decodeRows rows).map (fun es => e :: es)) := by
  simp [decodeRows, List.mapM_cons]
  cases decodeEvent row.event <;>
    cases rows.mapM (fun row => decodeEvent row.event) <;> rfl

/-- Ordered rational decoding commutes with the label map, including failure. -/
theorem decodeRows_map {n m : Nat} (f : Fin n → Fin m) (rows : List (Row n)) :
    decodeRows (mapRows f rows) = (decodeRows rows).map (List.map (mapEvent f)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change decodeRows (mapRow f row :: mapRows f rows) =
        (decodeRows (row :: rows)).map (List.map (mapEvent f))
      rw [decodeRows_cons, decodeRows_cons]
      change (decodeEvent (mapEvent f row.event)).bind
        (fun e => (decodeRows (mapRows f rows)).map (fun es => e :: es)) = _
      rw [decodeEvent_map, ih]
      cases decodeEvent row.event <;> cases decodeRows rows <;> rfl

theorem projectRow_map {n m : Nat} (f : Fin n → Fin m) (row : Row n) :
    projectRow (mapRow f row) = projectRow row := by
  rcases row with ⟨idx, e, annotation, child⟩
  cases e <;> cases annotation <;> rfl

theorem projectRows_map {n m : Nat} (f : Fin n → Fin m) (rows : List (Row n)) :
    projectRows (mapRows f rows) = projectRows rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      change projectRow (mapRow f row) :: projectRows (mapRows f rows) =
        projectRow row :: projectRows rows
      rw [projectRow_map, ih]

theorem sourceIndices_map {n m : Nat} (f : Fin n → Fin m) (rows : List (Row n)) :
    (mapRows f rows).map CanonicalFrameCoverage.Row.sourceIndex =
      rows.map CanonicalFrameCoverage.Row.sourceIndex := by
  simp [mapRows, mapRow, List.map_map]

section Semantics
variable {n m : Nat} {M : Type*} [AddCommMonoid M] [Module ℚ M]

theorem rawRowsRun_map (f : Fin n → Fin m) (rows : List (Row n)) (h : Register → M) :
    rawRowsRun (mapRows f rows) h = rawRowsRun rows h := by
  unfold rawRowsRun
  rw [projectRows_map]

/-- Scalar equality follows from the accepted raw/decoded-run bridge, with no
new scalar execution or independence induction. -/
theorem decoded_map_run (f : Fin n → Fin m) (rows : List (Row n))
    (es : List (ScalarEvent n)) (hd : decodeRows rows = some es) (h : Register → M) :
    LemmaG.Stream.scalRun (es.map (mapEvent f)) h = LemmaG.Stream.scalRun es h := by
  have hm : decodeRows (mapRows f rows) = some (es.map (mapEvent f)) := by
    rw [decodeRows_map, hd]; rfl
  have hn := decoded_rows_run (mapRows f rows) (es.map (mapEvent f)) hm h
  rw [rawRowsRun_map, decoded_rows_run rows es hd h] at hn
  exact (Option.some.inj hn).symm
end Semantics
end CurrentMain.FrameDomainTransport

namespace CurrentMain.Current596CKCentre
open CurrentScalarCentreBand FrameDomainTransport

def embed : Fin 1079 → Fin 1082 := Fin.castLE (by decide)

theorem embed_value (f : Fin 1079) : (embed f).val = f.val := rfl

def forward : List (Row 1082) := mapRows embed Current9594CKCentre.forward
def backward : List (Row 1082) := mapRows embed Current9594CKCentre.backward

theorem exact_source_indices :
    forward.map CanonicalFrameCoverage.Row.sourceIndex = List.range' 12927 256 ∧
    backward.map CanonicalFrameCoverage.Row.sourceIndex = List.range' 12927 256 := by
  simpa only [forward, backward, sourceIndices_map] using Current9594CKCentre.exact_source_indices

section Semantics
variable {M : Type*} [AddCommMonoid M] [Module ℚ M]

theorem forward_run_eq (h : Register → M) :
    rawRowsRun forward h = rawRowsRun Current9594CKCentre.forward h :=
  rawRowsRun_map embed Current9594CKCentre.forward h

theorem backward_run_eq (h : Register → M) :
    rawRowsRun backward h = rawRowsRun Current9594CKCentre.backward h :=
  rawRowsRun_map embed Current9594CKCentre.backward h

theorem forward_independent (h h' : Register → M)
    (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun forward h = some out ∧ rawRowsRun forward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) := by
  simpa only [forward_run_eq] using Current9594CKCentre.forward_independent h h' hL

theorem backward_independent (h h' : Register → M)
    (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun backward h = some out ∧ rawRowsRun backward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) := by
  simpa only [backward_run_eq] using Current9594CKCentre.backward_independent h h' hL

theorem forward_interpreted :
    ∃ es : List (ScalarEvent 1082), decodeRows forward = some es ∧
      ∀ h h' : Register → M, (∀ r, r.val < 728 → h r = h' r) →
        LemmaG.Stream.scalRun es h = LemmaG.Stream.scalRun es h' ∧
        (∀ k : Fin 8, LemmaG.Stream.scalRun es h (F19CentreBand.centre k) = 0) := by
  obtain ⟨es, hd, hs⟩ := Current9594CKCentre.forward_interpreted (M := M)
  refine ⟨es.map (mapEvent embed), ?_, ?_⟩
  · change decodeRows (mapRows embed Current9594CKCentre.forward) = _
    rw [decodeRows_map, hd]; rfl
  · intro h h' hL
    simpa only [decoded_map_run embed Current9594CKCentre.forward es hd] using hs h h' hL

theorem backward_interpreted :
    ∃ es : List (ScalarEvent 1082), decodeRows backward = some es ∧
      ∀ h h' : Register → M, (∀ r, r.val < 728 → h r = h' r) →
        LemmaG.Stream.scalRun es h = LemmaG.Stream.scalRun es h' ∧
        (∀ k : Fin 8, LemmaG.Stream.scalRun es h (F19CentreBand.centre k) = 0) := by
  obtain ⟨es, hd, hs⟩ := Current9594CKCentre.backward_interpreted (M := M)
  refine ⟨es.map (mapEvent embed), ?_, ?_⟩
  · change decodeRows (mapRows embed Current9594CKCentre.backward) = _
    rw [decodeRows_map, hd]; rfl
  · intro h h' hL
    simpa only [decoded_map_run embed Current9594CKCentre.backward es hd] using hs h h' hL
end Semantics
end CurrentMain.Current596CKCentre

#print axioms CurrentMain.FrameDomainTransport.decodeEvent_map
#print axioms CurrentMain.FrameDomainTransport.decodeRows_map
#print axioms CurrentMain.FrameDomainTransport.projectRows_map
#print axioms CurrentMain.FrameDomainTransport.rawRowsRun_map
#print axioms CurrentMain.FrameDomainTransport.decoded_map_run
#print axioms CurrentMain.Current596CKCentre.embed_value
#print axioms CurrentMain.Current596CKCentre.exact_source_indices
#print axioms CurrentMain.Current596CKCentre.forward_run_eq
#print axioms CurrentMain.Current596CKCentre.backward_run_eq
#print axioms CurrentMain.Current596CKCentre.forward_independent
#print axioms CurrentMain.Current596CKCentre.backward_independent
#print axioms CurrentMain.Current596CKCentre.forward_interpreted
#print axioms CurrentMain.Current596CKCentre.backward_interpreted
