import F19CentreBandIndependence

/-!
Conditional scalar composition around the exact accepted f19 centre bands.
No full prefix/suffix typed supplier has been accepted. In each direction,
1,617 raw phase/adapter/residual entries lie outside the scalar projection.
The LOnlyRows premises below must be supplied for the actual typed words;
read-only inspection of compressed JSON does not discharge them in Lean.
Physical adapters, complete scalar matrix identity and physical endpoints
remain separate. Apache-2.0; prepared with OpenAI assistance.
-/
set_option Elab.async false
namespace CurrentMain.F19CentreComposition
open F19SelectedCoverage F19ScalarEventInterpretation F19ScalarPilotComposition F19CentreBand

/-- Signed denominators are nonzero; no positivity or clean-target condition. -/
def LOnlyEvent : LabelEvent → Prop
  | .relabel r _ _ => r.val < 728
  | .add t s q => t.val < 728 ∧ s.val < 728 ∧ q.2 ≠ 0
  | .scale t q => t.val < 728 ∧ q.2 ≠ 0
  | .copy t s _ => t.val < 728 ∧ s.val < 728
  | .clear t _ => t.val < 728

def LOnlyRows (rows : List Row) : Prop := ∀ row ∈ rows, LOnlyEvent row.event
private def KnownL (f : Flags) : Prop := ∀ r : Register, r.val < 728 → f.known r = true

private theorem step_known (e : LabelEvent) (f : Flags) (r : Register)
    (h : f.known r = true) : (stepFlags e f).known r = true := by
  cases e <;> simp_all [stepFlags, mark, Function.update_apply]

private theorem end_known (rows : List Row) (f : Flags) (r : Register)
    (h : f.known r = true) : (endFlags rows f).known r = true := by
  induction rows generalizing f with
  | nil => exact h
  | cons row rows ih => exact ih _ (step_known row.event f r h)

private theorem lonly_step_safe (e : LabelEvent) (he : LOnlyEvent e)
    (f : Flags) (hf : KnownL f) : safeStep e f = true := by
  cases e with
  | relabel r a b => rfl
  | add t s q =>
      apply decide_eq_true
      exact ⟨hf t he.1, hf s he.2.1, he.2.2⟩
  | scale t q =>
      apply decide_eq_true
      exact ⟨hf t he.1, he.2⟩
  | copy t s label => exact hf s he.2
  | clear t label => rfl

/-- Reuse of the accepted safety relation, without interpreting omitted adapters. -/
theorem lonly_rows_safe (rows : List Row) (hl : LOnlyRows rows)
    (f : Flags) (hf : ∀ r : Register, r.val < 728 → f.known r = true) :
    safeRows rows f = true := by
  induction rows generalizing f with
  | nil => rfl
  | cons row rows ih =>
      apply Bool.and_eq_true_iff.mpr
      refine ⟨lonly_step_safe row.event (hl row (by simp)) f hf, ?_⟩
      apply ih (fun x hx => hl x (by simp [hx]))
      intro r hr
      exact step_known row.event f r (hf r hr)

private theorem step_zero_centre (e : LabelEvent) (he : LOnlyEvent e)
    (f : Flags) (k : Fin 8) :
    (stepFlags e f).zeroed (centre k) = f.zeroed (centre k) := by
  have hne (t : Register) (ht : t.val < 728) : centre k ≠ t := by
    intro h
    have hv := congrArg Fin.val h
    simp only [centre] at hv
    omega
  cases e with
  | relabel r a b => rfl
  | add t s q => simp [stepFlags, mark, Function.update_of_ne (hne t he.1)]
  | scale t q => simp [stepFlags, mark, Function.update_of_ne (hne t he.1)]
  | copy t s label => simp [stepFlags, mark, Function.update_of_ne (hne t he.1)]
  | clear t label => simp [stepFlags, mark, Function.update_of_ne (hne t he)]

private theorem end_zero_centre (rows : List Row) (hl : LOnlyRows rows)
    (f : Flags) (k : Fin 8) :
    (endFlags rows f).zeroed (centre k) = f.zeroed (centre k) := by
  induction rows generalizing f with
  | nil => rfl
  | cons row rows ih =>
      change (endFlags rows (stepFlags row.event f)).zeroed (centre k) = _
      rw [ih (fun x hx => hl x (by simp [hx])),
        step_zero_centre row.event (hl row (by simp))]

section Semantics
variable {M : Type*} [AddCommMonoid M] [Module ℚ M]

/-- Exact list composition for the already accepted Option-valued raw interpreter. -/
theorem rawRowsRun_append (xs ys : List Row) (h : Register → M) :
    rawRowsRun (xs ++ ys) h = (rawRowsRun xs h).bind (rawRowsRun ys) := by
  induction xs generalizing h with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.cons_append, rawRowsRun, ih, Option.bind_assoc]

/-- L-only prefixes can depend on dirty L values, but never on incoming centres. -/
theorem lonly_prefix_agreement (rows : List Row) (hl : LOnlyRows rows)
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ a b, rawRowsRun rows h = some a ∧ rawRowsRun rows h' = some b ∧
      (∀ r, r.val < 728 → a r = b r) := by
  have hi : Related initialFlags h h' := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr; exact hL r (of_decide_eq_true hr)
    · intro r hr; cases hr
    · intro r hr; cases hr
  have hs := lonly_rows_safe rows hl initialFlags (by
    intro r hr; exact decide_eq_true hr)
  obtain ⟨a, b, ha, hb, hab⟩ := safe_run_related rows initialFlags hs h h' hi
  refine ⟨a, b, ha, hb, ?_⟩
  intro r hr
  exact hab.1 r (end_known rows initialFlags r (decide_eq_true hr))

private def clearedFlags : Flags := ⟨fun _ => true, fun r => decide (728 ≤ r.val)⟩

/-- A signed-denominator-valid L-only suffix is total and keeps all centres zero. -/
theorem lonly_suffix_zero (rows : List Row) (hl : LOnlyRows rows)
    (h : Register → M) (h0 : ∀ k : Fin 8, h (centre k) = 0) :
    ∃ out, rawRowsRun rows h = some out ∧ (∀ k : Fin 8, out (centre k) = 0) := by
  have hz : ∀ r : Register, clearedFlags.zeroed r = true → h r = 0 := by
    intro r hr
    have hlo : 728 ≤ r.val := of_decide_eq_true hr
    let k : Fin 8 := ⟨r.val - 728, by omega⟩
    have hk : centre k = r := by apply Fin.ext; simp [centre, k]; omega
    rw [← hk]
    exact h0 k
  have hi : Related clearedFlags h h := ⟨fun _ _ => rfl, hz, hz⟩
  have hs := lonly_rows_safe rows hl clearedFlags (fun _ _ => rfl)
  obtain ⟨a, b, ha, hb, hab⟩ := safe_run_related rows clearedFlags hs h h hi
  refine ⟨a, ha, ?_⟩
  intro k
  apply hab.2.1
  rw [end_zero_centre rows hl]
  simp [clearedFlags, centre]

/-- Conditional whole projected-word independence around a certified band.
No equality of a projected word with the full raw physical program is assumed. -/
theorem sandwich_independent (prefix band suffix : List Row)
    (hp : LOnlyRows prefix) (hb : bandCertificate band = true)
    (hs : LOnlyRows suffix) (h h' : Register → M)
    (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out, rawRowsRun ((prefix ++ band) ++ suffix) h = some out ∧
      rawRowsRun ((prefix ++ band) ++ suffix) h' = some out ∧
      (∀ k : Fin 8, out (centre k) = 0) := by
  obtain ⟨p, p', hrp, hrp', he⟩ := lonly_prefix_agreement prefix hp h h' hL
  obtain ⟨b, b', hrb, hrb', hbb, hzero⟩ := certified_band_independent band hb p p' he
  subst b'
  obtain ⟨out, hrs, hz⟩ := lonly_suffix_zero suffix hs b hzero
  refine ⟨out, ?_, ?_, hz⟩
  · simp only [rawRowsRun_append, hrp, Option.bind_some, hrb, hrs]
  · simp only [rawRowsRun_append, hrp', Option.bind_some, hrb', hrs]

/-- Exact selected forward centre band; actual prefix/suffix suppliers remain premises. -/
theorem selected_forward_sandwich (prefix suffix : List Row)
    (hp : LOnlyRows prefix) (hs : LOnlyRows suffix)
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out, rawRowsRun ((prefix ++ forward) ++ suffix) h = some out ∧
      rawRowsRun ((prefix ++ forward) ++ suffix) h' = some out ∧
      (∀ k : Fin 8, out (centre k) = 0) :=
  sandwich_independent prefix forward suffix hp forward_checked hs h h' hL

theorem selected_backward_sandwich (prefix suffix : List Row)
    (hp : LOnlyRows prefix) (hs : LOnlyRows suffix)
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out, rawRowsRun ((prefix ++ backward) ++ suffix) h = some out ∧
      rawRowsRun ((prefix ++ backward) ++ suffix) h' = some out ∧
      (∀ k : Fin 8, out (centre k) = 0) :=
  sandwich_independent prefix backward suffix hp backward_checked hs h h' hL
end Semantics
end CurrentMain.F19CentreComposition

#print axioms CurrentMain.F19CentreComposition.lonly_rows_safe
#print axioms CurrentMain.F19CentreComposition.rawRowsRun_append
#print axioms CurrentMain.F19CentreComposition.lonly_prefix_agreement
#print axioms CurrentMain.F19CentreComposition.lonly_suffix_zero
#print axioms CurrentMain.F19CentreComposition.sandwich_independent
#print axioms CurrentMain.F19CentreComposition.selected_forward_sandwich
#print axioms CurrentMain.F19CentreComposition.selected_backward_sandwich
