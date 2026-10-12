import F19CentreBandComposition

/-!
Current main535 source-bound first64 scalar rows, raw indices1..64 in each
orientation. These ordered rows are byte-value identical to the historical
f19 slice, but their current selection/program hashes are pinned separately.
This supplies only signed-denominator-valid L-only typed decoding. Raw index0
is a phase precondition and is excluded. No full prefix/suffix, centre-band
transfer, frame admissibility, omitted adapter or physical endpoint is proved.
The reused Register/FrameLabel types are an embedding for these L112..219,
frame0 records, not a claim about the complete current register/frame domain.
Current conditional kappa context: 1584931111785787/1000000000000000000
= 0.001584931111785787; this finite slice proves no kappa or multiplier theorem.
PR509/selected supplier attribution retained; Apache-2.0. OpenAI-assisted.
-/
set_option Elab.async false
namespace CurrentMain.CurrentScalarFirst64
open F19SelectedCoverage F19ScalarEventInterpretation F19CentreComposition

/-- Constructor-wise test, retaining signed denominator syntax. -/
def eventLOnlyB : LabelEvent → Bool
  | .relabel r _ _ => decide (r.val < 728)
  | .add t s q => decide (t.val < 728 ∧ s.val < 728 ∧ q.2 ≠ 0)
  | .scale t q => decide (t.val < 728 ∧ q.2 ≠ 0)
  | .copy t s _ => decide (t.val < 728 ∧ s.val < 728)
  | .clear t _ => decide (t.val < 728)

def rowsLOnlyB (rows : List Row) : Bool :=
  rows.all (fun row => eventLOnlyB row.event)

private theorem eventLOnlyB_sound (e : LabelEvent) (h : eventLOnlyB e = true) :
    LOnlyEvent e := by
  cases e <;> unfold LOnlyEvent <;> exact of_decide_eq_true h

/-- Generic finite certificate soundness; no full-word scalar execution. -/
theorem rowsLOnlyB_sound (rows : List Row) (h : rowsLOnlyB rows = true) :
    LOnlyRows rows := by
  change rows.all (fun row => eventLOnlyB row.event) = true at h
  intro row hr
  exact eventLOnlyB_sound row.event ((List.all_eq_true.mp h) row hr)

private theorem lonly_event_decodes (e : LabelEvent) (h : LOnlyEvent e) :
    ∃ decoded, decodeEvent e = some decoded := by
  cases e with
  | relabel r a b => exact ⟨.relabel r a b, rfl⟩
  | add t s q =>
      exact ⟨.add t s ((q.1 : ℚ) / (q.2 : ℚ)),
        by simp [decodeEvent, decodeCoefficient, h.2.2]⟩
  | scale t q =>
      exact ⟨.scale t ((q.1 : ℚ) / (q.2 : ℚ)),
        by simp [decodeEvent, decodeCoefficient, h.2]⟩
  | copy t s f => exact ⟨.copy t s f, rfl⟩
  | clear t f => exact ⟨.clear t f, rfl⟩

/-- Ordered decoding succeeds from the denominator-bearing L-only premise.
This is list-decoder totality, not a new scalar or frame run induction. -/
theorem lonly_rows_decode (rows : List Row) (h : LOnlyRows rows) :
    ∃ es : List ScalarEvent, decodeRows rows = some es := by
  induction rows with
  | nil => exact ⟨[], rfl⟩
  | cons row rows ih =>
      obtain ⟨decoded, hd⟩ := lonly_event_decodes row.event (h row (by simp))
      obtain ⟨es, he⟩ := ih (fun r hr => h r (by simp [hr]))
      refine ⟨decoded :: es, ?_⟩
      have hm : rows.mapM (fun r => decodeEvent r.event) = some es := he
      simp [decodeRows, List.mapM_cons, hd, hm]

def forward : List Row := [
  ⟨1, .scale 119 ((-1), (2)), some 0, none⟩,
  ⟨2, .add 119 169 ((1), (2)), some 0, none⟩,
  ⟨3, .add 169 119 ((-1), (1)), some 0, none⟩,
  ⟨4, .scale 139 ((-1), (2)), some 0, none⟩,
  ⟨5, .add 139 112 ((1), (2)), some 0, none⟩,
  ⟨6, .add 112 139 ((-1), (1)), some 0, none⟩,
  ⟨7, .scale 193 ((-1), (2)), some 0, none⟩,
  ⟨8, .add 193 204 ((1), (2)), some 0, none⟩,
  ⟨9, .add 204 193 ((-1), (1)), some 0, none⟩,
  ⟨10, .scale 199 ((-1), (2)), some 0, none⟩,
  ⟨11, .add 199 188 ((1), (2)), some 0, none⟩,
  ⟨12, .add 188 199 ((-1), (1)), some 0, none⟩,
  ⟨13, .scale 122 ((-1), (2)), some 0, none⟩,
  ⟨14, .add 122 174 ((1), (2)), some 0, none⟩,
  ⟨15, .add 174 122 ((-1), (1)), some 0, none⟩,
  ⟨16, .scale 203 ((-1), (2)), some 0, none⟩,
  ⟨17, .add 203 182 ((1), (2)), some 0, none⟩,
  ⟨18, .add 182 203 ((-1), (1)), some 0, none⟩,
  ⟨19, .scale 123 ((-1), (2)), some 0, none⟩,
  ⟨20, .add 123 175 ((1), (2)), some 0, none⟩,
  ⟨21, .add 175 123 ((-1), (1)), some 0, none⟩,
  ⟨22, .scale 202 ((-1), (2)), some 0, none⟩,
  ⟨23, .add 202 183 ((1), (2)), some 0, none⟩,
  ⟨24, .add 183 202 ((-1), (1)), some 0, none⟩,
  ⟨25, .scale 191 ((-1), (2)), some 0, none⟩,
  ⟨26, .add 191 206 ((1), (2)), some 0, none⟩,
  ⟨27, .add 206 191 ((-1), (1)), some 0, none⟩,
  ⟨28, .scale 201 ((-1), (2)), some 0, none⟩,
  ⟨29, .add 201 184 ((1), (2)), some 0, none⟩,
  ⟨30, .add 184 201 ((-1), (1)), some 0, none⟩,
  ⟨31, .scale 121 ((-1), (2)), some 0, none⟩,
  ⟨32, .add 121 173 ((1), (2)), some 0, none⟩,
  ⟨33, .add 173 121 ((-1), (1)), some 0, none⟩,
  ⟨34, .scale 137 ((-1), (2)), some 0, none⟩,
  ⟨35, .add 137 114 ((1), (2)), some 0, none⟩,
  ⟨36, .add 114 137 ((-1), (1)), some 0, none⟩,
  ⟨37, .scale 150 ((-1), (2)), some 0, none⟩,
  ⟨38, .add 150 129 ((1), (2)), some 0, none⟩,
  ⟨39, .add 129 150 ((-1), (1)), some 0, none⟩,
  ⟨40, .scale 143 ((-1), (2)), some 0, none⟩,
  ⟨41, .add 143 124 ((1), (2)), some 0, none⟩,
  ⟨42, .add 124 143 ((-1), (1)), some 0, none⟩,
  ⟨43, .scale 189 ((-1), (2)), some 0, none⟩,
  ⟨44, .add 189 215 ((1), (2)), some 0, none⟩,
  ⟨45, .add 215 189 ((-1), (1)), some 0, none⟩,
  ⟨46, .scale 168 ((-1), (2)), some 0, none⟩,
  ⟨47, .add 168 212 ((1), (2)), some 0, none⟩,
  ⟨48, .add 212 168 ((-1), (1)), some 0, none⟩,
  ⟨49, .scale 131 ((-1), (2)), some 0, none⟩,
  ⟨50, .add 131 152 ((1), (2)), some 0, none⟩,
  ⟨51, .add 152 131 ((-1), (1)), some 0, none⟩,
  ⟨52, .scale 167 ((-1), (2)), some 0, none⟩,
  ⟨53, .add 167 213 ((1), (2)), some 0, none⟩,
  ⟨54, .add 213 167 ((-1), (1)), some 0, none⟩,
  ⟨55, .scale 151 ((-1), (2)), some 0, none⟩,
  ⟨56, .add 151 130 ((1), (2)), some 0, none⟩,
  ⟨57, .add 130 151 ((-1), (1)), some 0, none⟩,
  ⟨58, .scale 214 ((-1), (2)), some 0, none⟩,
  ⟨59, .add 214 166 ((1), (2)), some 0, none⟩,
  ⟨60, .add 166 214 ((-1), (1)), some 0, none⟩,
  ⟨61, .scale 136 ((-1), (2)), some 0, none⟩,
  ⟨62, .add 136 219 ((1), (2)), some 0, none⟩,
  ⟨63, .add 219 136 ((-1), (1)), some 0, none⟩,
  ⟨64, .scale 197 ((-1), (2)), some 0, none⟩
]

def backward : List Row := [
  ⟨1, .scale 119 ((2), (-1)), some 0, none⟩,
  ⟨2, .add 169 119 ((-1), (2)), some 0, none⟩,
  ⟨3, .add 119 169 ((1), (1)), some 0, none⟩,
  ⟨4, .scale 139 ((2), (-1)), some 0, none⟩,
  ⟨5, .add 112 139 ((-1), (2)), some 0, none⟩,
  ⟨6, .add 139 112 ((1), (1)), some 0, none⟩,
  ⟨7, .scale 193 ((2), (-1)), some 0, none⟩,
  ⟨8, .add 204 193 ((-1), (2)), some 0, none⟩,
  ⟨9, .add 193 204 ((1), (1)), some 0, none⟩,
  ⟨10, .scale 199 ((2), (-1)), some 0, none⟩,
  ⟨11, .add 188 199 ((-1), (2)), some 0, none⟩,
  ⟨12, .add 199 188 ((1), (1)), some 0, none⟩,
  ⟨13, .scale 122 ((2), (-1)), some 0, none⟩,
  ⟨14, .add 174 122 ((-1), (2)), some 0, none⟩,
  ⟨15, .add 122 174 ((1), (1)), some 0, none⟩,
  ⟨16, .scale 203 ((2), (-1)), some 0, none⟩,
  ⟨17, .add 182 203 ((-1), (2)), some 0, none⟩,
  ⟨18, .add 203 182 ((1), (1)), some 0, none⟩,
  ⟨19, .scale 123 ((2), (-1)), some 0, none⟩,
  ⟨20, .add 175 123 ((-1), (2)), some 0, none⟩,
  ⟨21, .add 123 175 ((1), (1)), some 0, none⟩,
  ⟨22, .scale 202 ((2), (-1)), some 0, none⟩,
  ⟨23, .add 183 202 ((-1), (2)), some 0, none⟩,
  ⟨24, .add 202 183 ((1), (1)), some 0, none⟩,
  ⟨25, .scale 191 ((2), (-1)), some 0, none⟩,
  ⟨26, .add 206 191 ((-1), (2)), some 0, none⟩,
  ⟨27, .add 191 206 ((1), (1)), some 0, none⟩,
  ⟨28, .scale 201 ((2), (-1)), some 0, none⟩,
  ⟨29, .add 184 201 ((-1), (2)), some 0, none⟩,
  ⟨30, .add 201 184 ((1), (1)), some 0, none⟩,
  ⟨31, .scale 121 ((2), (-1)), some 0, none⟩,
  ⟨32, .add 173 121 ((-1), (2)), some 0, none⟩,
  ⟨33, .add 121 173 ((1), (1)), some 0, none⟩,
  ⟨34, .scale 137 ((2), (-1)), some 0, none⟩,
  ⟨35, .add 114 137 ((-1), (2)), some 0, none⟩,
  ⟨36, .add 137 114 ((1), (1)), some 0, none⟩,
  ⟨37, .scale 150 ((2), (-1)), some 0, none⟩,
  ⟨38, .add 129 150 ((-1), (2)), some 0, none⟩,
  ⟨39, .add 150 129 ((1), (1)), some 0, none⟩,
  ⟨40, .scale 143 ((2), (-1)), some 0, none⟩,
  ⟨41, .add 124 143 ((-1), (2)), some 0, none⟩,
  ⟨42, .add 143 124 ((1), (1)), some 0, none⟩,
  ⟨43, .scale 189 ((2), (-1)), some 0, none⟩,
  ⟨44, .add 215 189 ((-1), (2)), some 0, none⟩,
  ⟨45, .add 189 215 ((1), (1)), some 0, none⟩,
  ⟨46, .scale 168 ((2), (-1)), some 0, none⟩,
  ⟨47, .add 212 168 ((-1), (2)), some 0, none⟩,
  ⟨48, .add 168 212 ((1), (1)), some 0, none⟩,
  ⟨49, .scale 131 ((2), (-1)), some 0, none⟩,
  ⟨50, .add 152 131 ((-1), (2)), some 0, none⟩,
  ⟨51, .add 131 152 ((1), (1)), some 0, none⟩,
  ⟨52, .scale 167 ((2), (-1)), some 0, none⟩,
  ⟨53, .add 213 167 ((-1), (2)), some 0, none⟩,
  ⟨54, .add 167 213 ((1), (1)), some 0, none⟩,
  ⟨55, .scale 151 ((2), (-1)), some 0, none⟩,
  ⟨56, .add 130 151 ((-1), (2)), some 0, none⟩,
  ⟨57, .add 151 130 ((1), (1)), some 0, none⟩,
  ⟨58, .scale 214 ((2), (-1)), some 0, none⟩,
  ⟨59, .add 166 214 ((-1), (2)), some 0, none⟩,
  ⟨60, .add 214 166 ((1), (1)), some 0, none⟩,
  ⟨61, .scale 136 ((2), (-1)), some 0, none⟩,
  ⟨62, .add 219 136 ((-1), (2)), some 0, none⟩,
  ⟨63, .add 136 219 ((1), (1)), some 0, none⟩,
  ⟨64, .scale 197 ((2), (-1)), some 0, none⟩
]

private theorem forward_checked : rowsLOnlyB forward = true := by decide +kernel
private theorem backward_checked : rowsLOnlyB backward = true := by decide +kernel

theorem forward_lonly : LOnlyRows forward := rowsLOnlyB_sound forward forward_checked
theorem backward_lonly : LOnlyRows backward := rowsLOnlyB_sound backward backward_checked

theorem exact_source_indices :
    forward.map Row.sourceIndex = List.range' 1 64 ∧
    backward.map Row.sourceIndex = List.range' 1 64 := by decide +kernel

theorem forward_decodes : ∃ es : List ScalarEvent, decodeRows forward = some es :=
  lonly_rows_decode forward forward_lonly

theorem backward_decodes : ∃ es : List ScalarEvent, decodeRows backward = some es :=
  lonly_rows_decode backward backward_lonly

end CurrentMain.CurrentScalarFirst64
#print axioms CurrentMain.CurrentScalarFirst64.rowsLOnlyB_sound
#print axioms CurrentMain.CurrentScalarFirst64.lonly_rows_decode
#print axioms CurrentMain.CurrentScalarFirst64.forward_lonly
#print axioms CurrentMain.CurrentScalarFirst64.backward_lonly
#print axioms CurrentMain.CurrentScalarFirst64.exact_source_indices
#print axioms CurrentMain.CurrentScalarFirst64.forward_decodes
#print axioms CurrentMain.CurrentScalarFirst64.backward_decodes
