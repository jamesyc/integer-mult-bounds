import F19ScalarPilotComposition

/-!
Source-bound scalar independence of the exact f19 centre band.
The 264 rows in each direction are raw indices 14768 through 15031.
No physical adapter, Clifford operator, or full-word identity is asserted.
Apache-2.0. Prepared with OpenAI assistance; see SOURCE_SCOPE.json.
-/
set_option Elab.async false

namespace CurrentMain.F19CentreBand
open F19SelectedCoverage F19ScalarEventInterpretation F19ScalarPilotComposition

structure Flags where
  known : Register → Bool
  zeroed : Register → Bool

def safeStep (e : LabelEvent) (f : Flags) : Bool :=
  match e with
  | .relabel .. => true
  | .add t s q => decide (f.known t = true ∧ f.known s = true ∧ q.2 ≠ 0)
  | .scale t q => decide (f.known t = true ∧ q.2 ≠ 0)
  | .copy _ s _ => f.known s
  | .clear .. => true

def mark (f : Flags) (t : Register) (z : Bool) : Flags :=
  ⟨Function.update f.known t true, Function.update f.zeroed t z⟩

def stepFlags (e : LabelEvent) (f : Flags) : Flags :=
  match e with
  | .relabel .. => f
  | .add t _ _ | .scale t _ | .copy t _ _ => mark f t false
  | .clear t _ => mark f t true

def endFlags : List Row → Flags → Flags
  | [], f => f
  | r :: rs, f => endFlags rs (stepFlags r.event f)

def safeRows : List Row → Flags → Bool
  | [], _ => true
  | r :: rs, f => safeStep r.event f && safeRows rs (stepFlags r.event f)

def initialFlags : Flags := ⟨fun r => decide (r.val < 728), fun _ => false⟩
def centre (k : Fin 8) : Register := ⟨728 + k.val, by omega⟩

/-- Eight final work locations are checked, without enumerating 736 input states. -/
def bandCertificate (rows : List Row) : Bool :=
  safeRows rows initialFlags &&
    (List.finRange 8).all (fun k =>
      (endFlags rows initialFlags).known (centre k) &&
      (endFlags rows initialFlags).zeroed (centre k))

section Semantics
variable {M : Type*} [AddCommMonoid M] [Module ℚ M]

def Related (f : Flags) (h h' : Register → M) : Prop :=
  (∀ r, f.known r = true → h r = h' r) ∧
  (∀ r, f.zeroed r = true → h r = 0) ∧
  (∀ r, f.zeroed r = true → h' r = 0)

private theorem related_update (f : Flags) (h h' : Register → M)
    (hr : Related f h h') (t : Register) (a b : M) (z : Bool)
    (hab : a = b) (hz : z = true → a = 0 ∧ b = 0) :
    Related (mark f t z) (Function.update h t a) (Function.update h' t b) := by
  rcases hr with ⟨he, h0, h0'⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r hk
    by_cases ht : r = t
    · subst r; simpa [mark] using hab
    · simpa [mark, Function.update_of_ne ht] using he r (by simpa [mark, ht] using hk)
  · intro r hk
    by_cases ht : r = t
    · subst r
      have hz' : z = true := by simpa [mark] using hk
      simpa [mark] using (hz hz').1
    · simpa [mark, Function.update_of_ne ht] using h0 r (by simpa [mark, ht] using hk)
  · intro r hk
    by_cases ht : r = t
    · subst r
      have hz' : z = true := by simpa [mark] using hk
      simpa [mark] using (hz hz').2
    · simpa [mark, Function.update_of_ne ht] using h0' r (by simpa [mark, ht] using hk)

private theorem step_related (e : LabelEvent) (f : Flags)
    (hs : safeStep e f = true) (h h' : Register → M) (hr : Related f h h') :
    ∃ a b, rawScalarStep e h = some a ∧ rawScalarStep e h' = some b ∧
      Related (stepFlags e f) a b := by
  cases e with
  | relabel r x y => exact ⟨h, h', rfl, rfl, hr⟩
  | add t s q =>
      have hsafe : f.known t = true ∧ f.known s = true ∧ q.2 ≠ 0 := of_decide_eq_true hs
      let c : ℚ := (q.1 : ℚ) / (q.2 : ℚ)
      refine ⟨Function.update h t (h t + c • h s),
        Function.update h' t (h' t + c • h' s), ?_, ?_, ?_⟩
      · simp [rawScalarStep, decodeCoefficient, hsafe.2.2, c]
      · simp [rawScalarStep, decodeCoefficient, hsafe.2.2, c]
      · apply related_update f h h' hr t _ _ false
        · rw [hr.1 t hsafe.1, hr.1 s hsafe.2.1]
        · intro hn; cases hn
  | scale t q =>
      have hsafe : f.known t = true ∧ q.2 ≠ 0 := of_decide_eq_true hs
      let c : ℚ := (q.1 : ℚ) / (q.2 : ℚ)
      refine ⟨Function.update h t (c • h t), Function.update h' t (c • h' t), ?_, ?_, ?_⟩
      · simp [rawScalarStep, decodeCoefficient, hsafe.2, c]
      · simp [rawScalarStep, decodeCoefficient, hsafe.2, c]
      · apply related_update f h h' hr t _ _ false
        · rw [hr.1 t hsafe.1]
        · intro hn; cases hn
  | copy t s frame =>
      refine ⟨Function.update h t (h s), Function.update h' t (h' s), rfl, rfl, ?_⟩
      apply related_update f h h' hr t _ _ false
      · exact hr.1 s hs
      · intro hn; cases hn
  | clear t frame =>
      refine ⟨Function.update h t 0, Function.update h' t 0, rfl, rfl, ?_⟩
      exact related_update f h h' hr t 0 0 true rfl (fun _ => ⟨rfl, rfl⟩)

/-- A local scalar state relation, reusing the accepted rawRowsRun interpreter. -/
theorem safe_run_related (rows : List Row) (f : Flags)
    (hs : safeRows rows f = true) (h h' : Register → M) (hr : Related f h h') :
    ∃ a b, rawRowsRun rows h = some a ∧ rawRowsRun rows h' = some b ∧
      Related (endFlags rows f) a b := by
  induction rows generalizing f h h' with
  | nil => exact ⟨h, h', rfl, rfl, hr⟩
  | cons row rows ih =>
      have hb := Bool.and_eq_true_iff.mp hs
      obtain ⟨x, y, hx, hy, hr'⟩ := step_related row.event f hb.1 h h' hr
      obtain ⟨a, b, ha, hb', hab⟩ := ih (stepFlags row.event f) hb.2 x y hr'
      refine ⟨a, b, ?_, ?_, hab⟩
      · simp only [rawRowsRun, hx, Option.bind_some]; exact ha
      · simp only [rawRowsRun, hy, Option.bind_some]; exact hb'
end Semantics

private theorem step_known_mono (e : LabelEvent) (f : Flags) (r : Register)
    (h : f.known r = true) : (stepFlags e f).known r = true := by
  cases e <;> simp_all [stepFlags, mark, Function.update_apply]

private theorem end_known_mono (rows : List Row) (f : Flags) (r : Register)
    (h : f.known r = true) : (endFlags rows f).known r = true := by
  induction rows generalizing f with
  | nil => exact h
  | cons row rows ih => exact ih _ (step_known_mono row.event f r h)

/-- Agreement on the 728 original registers suffices; all eight initial centre
values may be arbitrary and different. The conclusion includes every register. -/
theorem certified_band_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (rows : List Row) (hc : bandCertificate rows = true)
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun rows h = some out ∧ rawRowsRun rows h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (centre k) = 0) := by
  have hb := Bool.and_eq_true_iff.mp hc
  have hcentres : ∀ k : Fin 8,
      (endFlags rows initialFlags).known (centre k) = true ∧
      (endFlags rows initialFlags).zeroed (centre k) = true := by
    intro k
    exact Bool.and_eq_true_iff.mp ((List.all_eq_true.mp hb.2) k (List.mem_finRange k))
  have hi : Related initialFlags h h' := by
    refine ⟨?_, ?_, ?_⟩
    · intro r hr; exact hL r (of_decide_eq_true hr)
    · intro r hr; cases hr
    · intro r hr; cases hr
  obtain ⟨out, out', ho, ho', hr⟩ := safe_run_related rows initialFlags hb.1 h h' hi
  refine ⟨out, out', ho, ho', ?_, fun k => hr.2.1 _ (hcentres k).2⟩
  funext r
  apply hr.1 r
  by_cases hlow : r.val < 728
  · exact end_known_mono rows initialFlags r (by simpa [initialFlags] using hlow)
  · let k : Fin 8 := ⟨r.val - 728, by omega⟩
    have hk : centre k = r := by apply Fin.ext; simp [centre, k]; omega
    rw [← hk]
    exact (hcentres k).1

def forward : List Row := [
  ⟨14768, .clear 728 415, some 415, none⟩,
  ⟨14769, .copy 728 229 415, some 415, none⟩,
  ⟨14770, .relabel 728 415 2, none, some (1668, 7)⟩,
  ⟨14771, .add 184 728 (1, 4), some 2, none⟩,
  ⟨14772, .add 114 728 (1, 4), some 2, none⟩,
  ⟨14773, .add 173 728 (1, 4), some 2, none⟩,
  ⟨14774, .add 206 728 (1, 4), some 2, none⟩,
  ⟨14775, .add 182 728 (1, 4), some 2, none⟩,
  ⟨14776, .add 183 728 (1, 4), some 2, none⟩,
  ⟨14777, .add 175 728 (1, 4), some 2, none⟩,
  ⟨14778, .add 112 728 (1, 4), some 2, none⟩,
  ⟨14779, .add 188 728 (1, 4), some 2, none⟩,
  ⟨14780, .add 204 728 (1, 4), some 2, none⟩,
  ⟨14781, .add 169 728 (1, 4), some 2, none⟩,
  ⟨14782, .relabel 728 2 0, none, some (207, 1)⟩,
  ⟨14783, .add 124 728 (1, 4), some 0, none⟩,
  ⟨14784, .add 212 728 (1, 4), some 0, none⟩,
  ⟨14785, .add 215 728 (1, 4), some 0, none⟩,
  ⟨14786, .add 129 728 (1, 4), some 0, none⟩,
  ⟨14787, .add 174 728 (1, 4), some 0, none⟩,
  ⟨14788, .add 213 728 (1, 4), some 0, none⟩,
  ⟨14789, .add 166 728 (1, 4), some 0, none⟩,
  ⟨14790, .add 130 728 (1, 4), some 0, none⟩,
  ⟨14791, .add 152 728 (1, 4), some 0, none⟩,
  ⟨14792, .add 210 728 (1, 4), some 0, none⟩,
  ⟨14793, .add 160 728 (1, 4), some 0, none⟩,
  ⟨14794, .add 157 728 (1, 4), some 0, none⟩,
  ⟨14795, .add 219 728 (1, 4), some 0, none⟩,
  ⟨14796, .add 161 728 (1, 4), some 0, none⟩,
  ⟨14797, .add 146 728 (1, 4), some 0, none⟩,
  ⟨14798, .add 220 728 (1, 4), some 0, none⟩,
  ⟨14799, .add 134 728 (1, 4), some 0, none⟩,
  ⟨14800, .clear 728 0, some 0, none⟩,
  ⟨14801, .clear 729 416, some 416, none⟩,
  ⟨14802, .copy 729 224 416, some 416, none⟩,
  ⟨14803, .relabel 729 416 2, none, some (1671, 7)⟩,
  ⟨14804, .add 184 729 (1, 4), some 2, none⟩,
  ⟨14805, .add 114 729 (1, 4), some 2, none⟩,
  ⟨14806, .add 173 729 (-1, 4), some 2, none⟩,
  ⟨14807, .add 206 729 (-1, 4), some 2, none⟩,
  ⟨14808, .add 182 729 (1, 4), some 2, none⟩,
  ⟨14809, .add 183 729 (1, 4), some 2, none⟩,
  ⟨14810, .add 175 729 (-1, 4), some 2, none⟩,
  ⟨14811, .add 112 729 (1, 4), some 2, none⟩,
  ⟨14812, .add 188 729 (1, 4), some 2, none⟩,
  ⟨14813, .add 204 729 (-1, 4), some 2, none⟩,
  ⟨14814, .add 169 729 (-1, 4), some 2, none⟩,
  ⟨14815, .relabel 729 2 0, none, some (207, 1)⟩,
  ⟨14816, .add 118 729 (1, 4), some 0, none⟩,
  ⟨14817, .add 194 729 (1, 4), some 0, none⟩,
  ⟨14818, .add 205 729 (1, 4), some 0, none⟩,
  ⟨14819, .add 170 729 (1, 4), some 0, none⟩,
  ⟨14820, .add 174 729 (-1, 4), some 0, none⟩,
  ⟨14821, .add 195 729 (1, 4), some 0, none⟩,
  ⟨14822, .add 185 729 (1, 4), some 0, none⟩,
  ⟨14823, .add 171 729 (1, 4), some 0, none⟩,
  ⟨14824, .add 142 729 (1, 4), some 0, none⟩,
  ⟨14825, .add 192 729 (1, 4), some 0, none⟩,
  ⟨14826, .add 179 729 (1, 4), some 0, none⟩,
  ⟨14827, .add 120 729 (1, 4), some 0, none⟩,
  ⟨14828, .add 207 729 (1, 4), some 0, none⟩,
  ⟨14829, .add 180 729 (1, 4), some 0, none⟩,
  ⟨14830, .add 117 729 (1, 4), some 0, none⟩,
  ⟨14831, .add 208 729 (1, 4), some 0, none⟩,
  ⟨14832, .add 176 729 (1, 4), some 0, none⟩,
  ⟨14833, .clear 729 0, some 0, none⟩,
  ⟨14834, .clear 730 417, some 417, none⟩,
  ⟨14835, .copy 730 227 417, some 417, none⟩,
  ⟨14836, .relabel 730 417 2, none, some (1674, 7)⟩,
  ⟨14837, .add 199 730 (1, 4), some 2, none⟩,
  ⟨14838, .add 139 730 (1, 4), some 2, none⟩,
  ⟨14839, .add 119 730 (1, 4), some 2, none⟩,
  ⟨14840, .add 193 730 (1, 4), some 2, none⟩,
  ⟨14841, .add 125 730 (1, 4), some 2, none⟩,
  ⟨14842, .add 190 730 (1, 4), some 2, none⟩,
  ⟨14843, .add 155 730 (1, 4), some 2, none⟩,
  ⟨14844, .add 128 730 (1, 4), some 2, none⟩,
  ⟨14845, .add 127 730 (1, 4), some 2, none⟩,
  ⟨14846, .add 126 730 (1, 4), some 2, none⟩,
  ⟨14847, .add 153 730 (1, 4), some 2, none⟩,
  ⟨14848, .relabel 730 2 0, none, some (207, 1)⟩,
  ⟨14849, .add 118 730 (1, 4), some 0, none⟩,
  ⟨14850, .add 194 730 (1, 4), some 0, none⟩,
  ⟨14851, .add 205 730 (-1, 4), some 0, none⟩,
  ⟨14852, .add 170 730 (-1, 4), some 0, none⟩,
  ⟨14853, .add 124 730 (1, 4), some 0, none⟩,
  ⟨14854, .add 212 730 (1, 4), some 0, none⟩,
  ⟨14855, .add 215 730 (-1, 4), some 0, none⟩,
  ⟨14856, .add 129 730 (-1, 4), some 0, none⟩,
  ⟨14857, .add 213 730 (1, 4), some 0, none⟩,
  ⟨14858, .add 166 730 (1, 4), some 0, none⟩,
  ⟨14859, .add 130 730 (-1, 4), some 0, none⟩,
  ⟨14860, .add 152 730 (-1, 4), some 0, none⟩,
  ⟨14861, .add 195 730 (1, 4), some 0, none⟩,
  ⟨14862, .add 185 730 (1, 4), some 0, none⟩,
  ⟨14863, .add 171 730 (-1, 4), some 0, none⟩,
  ⟨14864, .add 142 730 (-1, 4), some 0, none⟩,
  ⟨14865, .add 154 730 (1, 4), some 0, none⟩,
  ⟨14866, .clear 730 0, some 0, none⟩,
  ⟨14867, .clear 731 418, some 418, none⟩,
  ⟨14868, .copy 731 225 418, some 418, none⟩,
  ⟨14869, .relabel 731 418 2, none, some (1677, 7)⟩,
  ⟨14870, .add 199 731 (-1, 4), some 2, none⟩,
  ⟨14871, .add 139 731 (1, 4), some 2, none⟩,
  ⟨14872, .add 119 731 (-1, 4), some 2, none⟩,
  ⟨14873, .add 193 731 (1, 4), some 2, none⟩,
  ⟨14874, .add 125 731 (1, 4), some 2, none⟩,
  ⟨14875, .add 190 731 (1, 4), some 2, none⟩,
  ⟨14876, .add 155 731 (-1, 4), some 2, none⟩,
  ⟨14877, .add 128 731 (-1, 4), some 2, none⟩,
  ⟨14878, .add 127 731 (1, 4), some 2, none⟩,
  ⟨14879, .add 126 731 (1, 4), some 2, none⟩,
  ⟨14880, .add 153 731 (-1, 4), some 2, none⟩,
  ⟨14881, .relabel 731 2 0, none, some (207, 1)⟩,
  ⟨14882, .add 210 731 (1, 4), some 0, none⟩,
  ⟨14883, .add 160 731 (1, 4), some 0, none⟩,
  ⟨14884, .add 157 731 (-1, 4), some 0, none⟩,
  ⟨14885, .add 219 731 (-1, 4), some 0, none⟩,
  ⟨14886, .add 192 731 (1, 4), some 0, none⟩,
  ⟨14887, .add 179 731 (1, 4), some 0, none⟩,
  ⟨14888, .add 120 731 (-1, 4), some 0, none⟩,
  ⟨14889, .add 207 731 (-1, 4), some 0, none⟩,
  ⟨14890, .add 154 731 (-1, 4), some 0, none⟩,
  ⟨14891, .add 180 731 (1, 4), some 0, none⟩,
  ⟨14892, .add 117 731 (1, 4), some 0, none⟩,
  ⟨14893, .add 208 731 (-1, 4), some 0, none⟩,
  ⟨14894, .add 176 731 (-1, 4), some 0, none⟩,
  ⟨14895, .add 161 731 (1, 4), some 0, none⟩,
  ⟨14896, .add 146 731 (1, 4), some 0, none⟩,
  ⟨14897, .add 220 731 (-1, 4), some 0, none⟩,
  ⟨14898, .add 134 731 (-1, 4), some 0, none⟩,
  ⟨14899, .clear 731 0, some 0, none⟩,
  ⟨14900, .clear 732 419, some 419, none⟩,
  ⟨14901, .copy 732 243 419, some 419, none⟩,
  ⟨14902, .relabel 732 419 2, none, some (1680, 7)⟩,
  ⟨14903, .add 202 732 (1, 4), some 2, none⟩,
  ⟨14904, .add 203 732 (1, 4), some 2, none⟩,
  ⟨14905, .add 122 732 (1, 4), some 2, none⟩,
  ⟨14906, .add 123 732 (1, 4), some 2, none⟩,
  ⟨14907, .add 148 732 (1, 4), some 2, none⟩,
  ⟨14908, .add 133 732 (1, 4), some 2, none⟩,
  ⟨14909, .add 149 732 (1, 4), some 2, none⟩,
  ⟨14910, .add 132 732 (1, 4), some 2, none⟩,
  ⟨14911, .add 164 732 (1, 4), some 2, none⟩,
  ⟨14912, .add 165 732 (1, 4), some 2, none⟩,
  ⟨14913, .add 218 732 (1, 4), some 2, none⟩,
  ⟨14914, .relabel 732 2 0, none, some (207, 1)⟩,
  ⟨14915, .add 187 732 (1, 4), some 0, none⟩,
  ⟨14916, .add 113 732 (1, 4), some 0, none⟩,
  ⟨14917, .add 140 732 (1, 4), some 0, none⟩,
  ⟨14918, .add 198 732 (1, 4), some 0, none⟩,
  ⟨14919, .add 168 732 (1, 4), some 0, none⟩,
  ⟨14920, .add 143 732 (1, 4), some 0, none⟩,
  ⟨14921, .add 150 732 (1, 4), some 0, none⟩,
  ⟨14922, .add 189 732 (1, 4), some 0, none⟩,
  ⟨14923, .add 144 732 (1, 4), some 0, none⟩,
  ⟨14924, .add 197 732 (1, 4), some 0, none⟩,
  ⟨14925, .add 136 732 (1, 4), some 0, none⟩,
  ⟨14926, .add 147 732 (1, 4), some 0, none⟩,
  ⟨14927, .add 115 732 (1, 4), some 0, none⟩,
  ⟨14928, .add 200 732 (1, 4), some 0, none⟩,
  ⟨14929, .add 178 732 (1, 4), some 0, none⟩,
  ⟨14930, .add 138 732 (1, 4), some 0, none⟩,
  ⟨14931, .add 217 732 (1, 4), some 0, none⟩,
  ⟨14932, .clear 732 0, some 0, none⟩,
  ⟨14933, .clear 733 420, some 420, none⟩,
  ⟨14934, .copy 733 241 420, some 420, none⟩,
  ⟨14935, .relabel 733 420 2, none, some (1683, 7)⟩,
  ⟨14936, .add 202 733 (-1, 4), some 2, none⟩,
  ⟨14937, .add 203 733 (1, 4), some 2, none⟩,
  ⟨14938, .add 122 733 (-1, 4), some 2, none⟩,
  ⟨14939, .add 123 733 (1, 4), some 2, none⟩,
  ⟨14940, .add 148 733 (1, 4), some 2, none⟩,
  ⟨14941, .add 133 733 (1, 4), some 2, none⟩,
  ⟨14942, .add 149 733 (-1, 4), some 2, none⟩,
  ⟨14943, .add 132 733 (-1, 4), some 2, none⟩,
  ⟨14944, .add 164 733 (-1, 4), some 2, none⟩,
  ⟨14945, .add 165 733 (1, 4), some 2, none⟩,
  ⟨14946, .add 218 733 (1, 4), some 2, none⟩,
  ⟨14947, .relabel 733 2 0, none, some (207, 1)⟩,
  ⟨14948, .add 214 733 (1, 4), some 0, none⟩,
  ⟨14949, .add 167 733 (1, 4), some 0, none⟩,
  ⟨14950, .add 131 733 (1, 4), some 0, none⟩,
  ⟨14951, .add 151 733 (1, 4), some 0, none⟩,
  ⟨14952, .add 196 733 (1, 4), some 0, none⟩,
  ⟨14953, .add 186 733 (1, 4), some 0, none⟩,
  ⟨14954, .add 172 733 (1, 4), some 0, none⟩,
  ⟨14955, .add 141 733 (1, 4), some 0, none⟩,
  ⟨14956, .add 217 733 (-1, 4), some 0, none⟩,
  ⟨14957, .add 181 733 (1, 4), some 0, none⟩,
  ⟨14958, .add 116 733 (1, 4), some 0, none⟩,
  ⟨14959, .add 209 733 (1, 4), some 0, none⟩,
  ⟨14960, .add 177 733 (1, 4), some 0, none⟩,
  ⟨14961, .add 162 733 (1, 4), some 0, none⟩,
  ⟨14962, .add 145 733 (1, 4), some 0, none⟩,
  ⟨14963, .add 221 733 (1, 4), some 0, none⟩,
  ⟨14964, .add 135 733 (1, 4), some 0, none⟩,
  ⟨14965, .clear 733 0, some 0, none⟩,
  ⟨14966, .clear 734 421, some 421, none⟩,
  ⟨14967, .copy 734 259 421, some 421, none⟩,
  ⟨14968, .relabel 734 421 2, none, some (1686, 7)⟩,
  ⟨14969, .add 137 734 (1, 4), some 2, none⟩,
  ⟨14970, .add 201 734 (1, 4), some 2, none⟩,
  ⟨14971, .add 191 734 (1, 4), some 2, none⟩,
  ⟨14972, .add 121 734 (1, 4), some 2, none⟩,
  ⟨14973, .add 159 734 (1, 4), some 2, none⟩,
  ⟨14974, .add 223 734 (1, 4), some 2, none⟩,
  ⟨14975, .add 158 734 (1, 4), some 2, none⟩,
  ⟨14976, .add 222 734 (1, 4), some 2, none⟩,
  ⟨14977, .add 211 734 (1, 4), some 2, none⟩,
  ⟨14978, .add 163 734 (1, 4), some 2, none⟩,
  ⟨14979, .add 216 734 (1, 4), some 2, none⟩,
  ⟨14980, .relabel 734 2 0, none, some (207, 1)⟩,
  ⟨14981, .add 168 734 (-1, 4), some 0, none⟩,
  ⟨14982, .add 143 734 (1, 4), some 0, none⟩,
  ⟨14983, .add 150 734 (-1, 4), some 0, none⟩,
  ⟨14984, .add 189 734 (1, 4), some 0, none⟩,
  ⟨14985, .add 196 734 (-1, 4), some 0, none⟩,
  ⟨14986, .add 186 734 (1, 4), some 0, none⟩,
  ⟨14987, .add 172 734 (-1, 4), some 0, none⟩,
  ⟨14988, .add 141 734 (1, 4), some 0, none⟩,
  ⟨14989, .add 115 734 (-1, 4), some 0, none⟩,
  ⟨14990, .add 200 734 (1, 4), some 0, none⟩,
  ⟨14991, .add 178 734 (-1, 4), some 0, none⟩,
  ⟨14992, .add 138 734 (1, 4), some 0, none⟩,
  ⟨14993, .add 156 734 (1, 4), some 0, none⟩,
  ⟨14994, .add 162 734 (-1, 4), some 0, none⟩,
  ⟨14995, .add 145 734 (1, 4), some 0, none⟩,
  ⟨14996, .add 221 734 (-1, 4), some 0, none⟩,
  ⟨14997, .add 135 734 (1, 4), some 0, none⟩,
  ⟨14998, .clear 734 0, some 0, none⟩,
  ⟨14999, .clear 735 422, some 422, none⟩,
  ⟨15000, .copy 735 257 422, some 422, none⟩,
  ⟨15001, .relabel 735 422 2, none, some (1689, 7)⟩,
  ⟨15002, .add 137 735 (-1, 4), some 2, none⟩,
  ⟨15003, .add 201 735 (1, 4), some 2, none⟩,
  ⟨15004, .add 191 735 (-1, 4), some 2, none⟩,
  ⟨15005, .add 121 735 (1, 4), some 2, none⟩,
  ⟨15006, .add 159 735 (-1, 4), some 2, none⟩,
  ⟨15007, .add 223 735 (1, 4), some 2, none⟩,
  ⟨15008, .add 158 735 (-1, 4), some 2, none⟩,
  ⟨15009, .add 222 735 (1, 4), some 2, none⟩,
  ⟨15010, .add 211 735 (-1, 4), some 2, none⟩,
  ⟨15011, .add 163 735 (1, 4), some 2, none⟩,
  ⟨15012, .add 216 735 (1, 4), some 2, none⟩,
  ⟨15013, .relabel 735 2 0, none, some (207, 1)⟩,
  ⟨15014, .add 187 735 (-1, 4), some 0, none⟩,
  ⟨15015, .add 113 735 (1, 4), some 0, none⟩,
  ⟨15016, .add 140 735 (-1, 4), some 0, none⟩,
  ⟨15017, .add 198 735 (1, 4), some 0, none⟩,
  ⟨15018, .add 214 735 (-1, 4), some 0, none⟩,
  ⟨15019, .add 167 735 (1, 4), some 0, none⟩,
  ⟨15020, .add 131 735 (-1, 4), some 0, none⟩,
  ⟨15021, .add 151 735 (1, 4), some 0, none⟩,
  ⟨15022, .add 144 735 (-1, 4), some 0, none⟩,
  ⟨15023, .add 197 735 (1, 4), some 0, none⟩,
  ⟨15024, .add 136 735 (-1, 4), some 0, none⟩,
  ⟨15025, .add 147 735 (1, 4), some 0, none⟩,
  ⟨15026, .add 156 735 (-1, 4), some 0, none⟩,
  ⟨15027, .add 181 735 (-1, 4), some 0, none⟩,
  ⟨15028, .add 116 735 (1, 4), some 0, none⟩,
  ⟨15029, .add 209 735 (-1, 4), some 0, none⟩,
  ⟨15030, .add 177 735 (1, 4), some 0, none⟩,
  ⟨15031, .clear 735 0, some 0, none⟩
]

def backward : List Row := [
  ⟨14768, .clear 728 0, some 0, none⟩,
  ⟨14769, .add 728 124 (1, 4), some 0, none⟩,
  ⟨14770, .add 728 212 (1, 4), some 0, none⟩,
  ⟨14771, .add 728 215 (1, 4), some 0, none⟩,
  ⟨14772, .add 728 129 (1, 4), some 0, none⟩,
  ⟨14773, .add 728 174 (1, 4), some 0, none⟩,
  ⟨14774, .add 728 213 (1, 4), some 0, none⟩,
  ⟨14775, .add 728 166 (1, 4), some 0, none⟩,
  ⟨14776, .add 728 130 (1, 4), some 0, none⟩,
  ⟨14777, .add 728 152 (1, 4), some 0, none⟩,
  ⟨14778, .add 728 210 (1, 4), some 0, none⟩,
  ⟨14779, .add 728 160 (1, 4), some 0, none⟩,
  ⟨14780, .add 728 157 (1, 4), some 0, none⟩,
  ⟨14781, .add 728 219 (1, 4), some 0, none⟩,
  ⟨14782, .add 728 161 (1, 4), some 0, none⟩,
  ⟨14783, .add 728 146 (1, 4), some 0, none⟩,
  ⟨14784, .add 728 220 (1, 4), some 0, none⟩,
  ⟨14785, .add 728 134 (1, 4), some 0, none⟩,
  ⟨14786, .relabel 728 0 2, none, some (0, 1)⟩,
  ⟨14787, .add 728 184 (1, 4), some 2, none⟩,
  ⟨14788, .add 728 114 (1, 4), some 2, none⟩,
  ⟨14789, .add 728 173 (1, 4), some 2, none⟩,
  ⟨14790, .add 728 206 (1, 4), some 2, none⟩,
  ⟨14791, .add 728 182 (1, 4), some 2, none⟩,
  ⟨14792, .add 728 183 (1, 4), some 2, none⟩,
  ⟨14793, .add 728 175 (1, 4), some 2, none⟩,
  ⟨14794, .add 728 112 (1, 4), some 2, none⟩,
  ⟨14795, .add 728 188 (1, 4), some 2, none⟩,
  ⟨14796, .add 728 204 (1, 4), some 2, none⟩,
  ⟨14797, .add 728 169 (1, 4), some 2, none⟩,
  ⟨14798, .relabel 728 2 415, none, some (232, 7)⟩,
  ⟨14799, .add 229 728 (-1, 1), some 415, none⟩,
  ⟨14800, .clear 728 415, some 415, none⟩,
  ⟨14801, .clear 729 0, some 0, none⟩,
  ⟨14802, .add 729 118 (1, 4), some 0, none⟩,
  ⟨14803, .add 729 194 (1, 4), some 0, none⟩,
  ⟨14804, .add 729 205 (1, 4), some 0, none⟩,
  ⟨14805, .add 729 170 (1, 4), some 0, none⟩,
  ⟨14806, .add 729 174 (-1, 4), some 0, none⟩,
  ⟨14807, .add 729 195 (1, 4), some 0, none⟩,
  ⟨14808, .add 729 185 (1, 4), some 0, none⟩,
  ⟨14809, .add 729 171 (1, 4), some 0, none⟩,
  ⟨14810, .add 729 142 (1, 4), some 0, none⟩,
  ⟨14811, .add 729 192 (1, 4), some 0, none⟩,
  ⟨14812, .add 729 179 (1, 4), some 0, none⟩,
  ⟨14813, .add 729 120 (1, 4), some 0, none⟩,
  ⟨14814, .add 729 207 (1, 4), some 0, none⟩,
  ⟨14815, .add 729 180 (1, 4), some 0, none⟩,
  ⟨14816, .add 729 117 (1, 4), some 0, none⟩,
  ⟨14817, .add 729 208 (1, 4), some 0, none⟩,
  ⟨14818, .add 729 176 (1, 4), some 0, none⟩,
  ⟨14819, .relabel 729 0 2, none, some (0, 1)⟩,
  ⟨14820, .add 729 184 (1, 4), some 2, none⟩,
  ⟨14821, .add 729 114 (1, 4), some 2, none⟩,
  ⟨14822, .add 729 173 (-1, 4), some 2, none⟩,
  ⟨14823, .add 729 206 (-1, 4), some 2, none⟩,
  ⟨14824, .add 729 182 (1, 4), some 2, none⟩,
  ⟨14825, .add 729 183 (1, 4), some 2, none⟩,
  ⟨14826, .add 729 175 (-1, 4), some 2, none⟩,
  ⟨14827, .add 729 112 (1, 4), some 2, none⟩,
  ⟨14828, .add 729 188 (1, 4), some 2, none⟩,
  ⟨14829, .add 729 204 (-1, 4), some 2, none⟩,
  ⟨14830, .add 729 169 (-1, 4), some 2, none⟩,
  ⟨14831, .relabel 729 2 416, none, some (233, 7)⟩,
  ⟨14832, .add 224 729 (-1, 1), some 416, none⟩,
  ⟨14833, .clear 729 416, some 416, none⟩,
  ⟨14834, .clear 730 0, some 0, none⟩,
  ⟨14835, .add 730 118 (1, 4), some 0, none⟩,
  ⟨14836, .add 730 194 (1, 4), some 0, none⟩,
  ⟨14837, .add 730 205 (-1, 4), some 0, none⟩,
  ⟨14838, .add 730 170 (-1, 4), some 0, none⟩,
  ⟨14839, .add 730 124 (1, 4), some 0, none⟩,
  ⟨14840, .add 730 212 (1, 4), some 0, none⟩,
  ⟨14841, .add 730 215 (-1, 4), some 0, none⟩,
  ⟨14842, .add 730 129 (-1, 4), some 0, none⟩,
  ⟨14843, .add 730 213 (1, 4), some 0, none⟩,
  ⟨14844, .add 730 166 (1, 4), some 0, none⟩,
  ⟨14845, .add 730 130 (-1, 4), some 0, none⟩,
  ⟨14846, .add 730 152 (-1, 4), some 0, none⟩,
  ⟨14847, .add 730 195 (1, 4), some 0, none⟩,
  ⟨14848, .add 730 185 (1, 4), some 0, none⟩,
  ⟨14849, .add 730 171 (-1, 4), some 0, none⟩,
  ⟨14850, .add 730 142 (-1, 4), some 0, none⟩,
  ⟨14851, .add 730 154 (1, 4), some 0, none⟩,
  ⟨14852, .relabel 730 0 2, none, some (0, 1)⟩,
  ⟨14853, .add 730 199 (1, 4), some 2, none⟩,
  ⟨14854, .add 730 139 (1, 4), some 2, none⟩,
  ⟨14855, .add 730 119 (1, 4), some 2, none⟩,
  ⟨14856, .add 730 193 (1, 4), some 2, none⟩,
  ⟨14857, .add 730 125 (1, 4), some 2, none⟩,
  ⟨14858, .add 730 190 (1, 4), some 2, none⟩,
  ⟨14859, .add 730 155 (1, 4), some 2, none⟩,
  ⟨14860, .add 730 128 (1, 4), some 2, none⟩,
  ⟨14861, .add 730 127 (1, 4), some 2, none⟩,
  ⟨14862, .add 730 126 (1, 4), some 2, none⟩,
  ⟨14863, .add 730 153 (1, 4), some 2, none⟩,
  ⟨14864, .relabel 730 2 417, none, some (234, 7)⟩,
  ⟨14865, .add 227 730 (-1, 1), some 417, none⟩,
  ⟨14866, .clear 730 417, some 417, none⟩,
  ⟨14867, .clear 731 0, some 0, none⟩,
  ⟨14868, .add 731 210 (1, 4), some 0, none⟩,
  ⟨14869, .add 731 160 (1, 4), some 0, none⟩,
  ⟨14870, .add 731 157 (-1, 4), some 0, none⟩,
  ⟨14871, .add 731 219 (-1, 4), some 0, none⟩,
  ⟨14872, .add 731 192 (1, 4), some 0, none⟩,
  ⟨14873, .add 731 179 (1, 4), some 0, none⟩,
  ⟨14874, .add 731 120 (-1, 4), some 0, none⟩,
  ⟨14875, .add 731 207 (-1, 4), some 0, none⟩,
  ⟨14876, .add 731 154 (-1, 4), some 0, none⟩,
  ⟨14877, .add 731 180 (1, 4), some 0, none⟩,
  ⟨14878, .add 731 117 (1, 4), some 0, none⟩,
  ⟨14879, .add 731 208 (-1, 4), some 0, none⟩,
  ⟨14880, .add 731 176 (-1, 4), some 0, none⟩,
  ⟨14881, .add 731 161 (1, 4), some 0, none⟩,
  ⟨14882, .add 731 146 (1, 4), some 0, none⟩,
  ⟨14883, .add 731 220 (-1, 4), some 0, none⟩,
  ⟨14884, .add 731 134 (-1, 4), some 0, none⟩,
  ⟨14885, .relabel 731 0 2, none, some (0, 1)⟩,
  ⟨14886, .add 731 199 (-1, 4), some 2, none⟩,
  ⟨14887, .add 731 139 (1, 4), some 2, none⟩,
  ⟨14888, .add 731 119 (-1, 4), some 2, none⟩,
  ⟨14889, .add 731 193 (1, 4), some 2, none⟩,
  ⟨14890, .add 731 125 (1, 4), some 2, none⟩,
  ⟨14891, .add 731 190 (1, 4), some 2, none⟩,
  ⟨14892, .add 731 155 (-1, 4), some 2, none⟩,
  ⟨14893, .add 731 128 (-1, 4), some 2, none⟩,
  ⟨14894, .add 731 127 (1, 4), some 2, none⟩,
  ⟨14895, .add 731 126 (1, 4), some 2, none⟩,
  ⟨14896, .add 731 153 (-1, 4), some 2, none⟩,
  ⟨14897, .relabel 731 2 418, none, some (235, 7)⟩,
  ⟨14898, .add 225 731 (-1, 1), some 418, none⟩,
  ⟨14899, .clear 731 418, some 418, none⟩,
  ⟨14900, .clear 732 0, some 0, none⟩,
  ⟨14901, .add 732 187 (1, 4), some 0, none⟩,
  ⟨14902, .add 732 113 (1, 4), some 0, none⟩,
  ⟨14903, .add 732 140 (1, 4), some 0, none⟩,
  ⟨14904, .add 732 198 (1, 4), some 0, none⟩,
  ⟨14905, .add 732 168 (1, 4), some 0, none⟩,
  ⟨14906, .add 732 143 (1, 4), some 0, none⟩,
  ⟨14907, .add 732 150 (1, 4), some 0, none⟩,
  ⟨14908, .add 732 189 (1, 4), some 0, none⟩,
  ⟨14909, .add 732 144 (1, 4), some 0, none⟩,
  ⟨14910, .add 732 197 (1, 4), some 0, none⟩,
  ⟨14911, .add 732 136 (1, 4), some 0, none⟩,
  ⟨14912, .add 732 147 (1, 4), some 0, none⟩,
  ⟨14913, .add 732 115 (1, 4), some 0, none⟩,
  ⟨14914, .add 732 200 (1, 4), some 0, none⟩,
  ⟨14915, .add 732 178 (1, 4), some 0, none⟩,
  ⟨14916, .add 732 138 (1, 4), some 0, none⟩,
  ⟨14917, .add 732 217 (1, 4), some 0, none⟩,
  ⟨14918, .relabel 732 0 2, none, some (0, 1)⟩,
  ⟨14919, .add 732 202 (1, 4), some 2, none⟩,
  ⟨14920, .add 732 203 (1, 4), some 2, none⟩,
  ⟨14921, .add 732 122 (1, 4), some 2, none⟩,
  ⟨14922, .add 732 123 (1, 4), some 2, none⟩,
  ⟨14923, .add 732 148 (1, 4), some 2, none⟩,
  ⟨14924, .add 732 133 (1, 4), some 2, none⟩,
  ⟨14925, .add 732 149 (1, 4), some 2, none⟩,
  ⟨14926, .add 732 132 (1, 4), some 2, none⟩,
  ⟨14927, .add 732 164 (1, 4), some 2, none⟩,
  ⟨14928, .add 732 165 (1, 4), some 2, none⟩,
  ⟨14929, .add 732 218 (1, 4), some 2, none⟩,
  ⟨14930, .relabel 732 2 419, none, some (236, 7)⟩,
  ⟨14931, .add 243 732 (-1, 1), some 419, none⟩,
  ⟨14932, .clear 732 419, some 419, none⟩,
  ⟨14933, .clear 733 0, some 0, none⟩,
  ⟨14934, .add 733 214 (1, 4), some 0, none⟩,
  ⟨14935, .add 733 167 (1, 4), some 0, none⟩,
  ⟨14936, .add 733 131 (1, 4), some 0, none⟩,
  ⟨14937, .add 733 151 (1, 4), some 0, none⟩,
  ⟨14938, .add 733 196 (1, 4), some 0, none⟩,
  ⟨14939, .add 733 186 (1, 4), some 0, none⟩,
  ⟨14940, .add 733 172 (1, 4), some 0, none⟩,
  ⟨14941, .add 733 141 (1, 4), some 0, none⟩,
  ⟨14942, .add 733 217 (-1, 4), some 0, none⟩,
  ⟨14943, .add 733 181 (1, 4), some 0, none⟩,
  ⟨14944, .add 733 116 (1, 4), some 0, none⟩,
  ⟨14945, .add 733 209 (1, 4), some 0, none⟩,
  ⟨14946, .add 733 177 (1, 4), some 0, none⟩,
  ⟨14947, .add 733 162 (1, 4), some 0, none⟩,
  ⟨14948, .add 733 145 (1, 4), some 0, none⟩,
  ⟨14949, .add 733 221 (1, 4), some 0, none⟩,
  ⟨14950, .add 733 135 (1, 4), some 0, none⟩,
  ⟨14951, .relabel 733 0 2, none, some (0, 1)⟩,
  ⟨14952, .add 733 202 (-1, 4), some 2, none⟩,
  ⟨14953, .add 733 203 (1, 4), some 2, none⟩,
  ⟨14954, .add 733 122 (-1, 4), some 2, none⟩,
  ⟨14955, .add 733 123 (1, 4), some 2, none⟩,
  ⟨14956, .add 733 148 (1, 4), some 2, none⟩,
  ⟨14957, .add 733 133 (1, 4), some 2, none⟩,
  ⟨14958, .add 733 149 (-1, 4), some 2, none⟩,
  ⟨14959, .add 733 132 (-1, 4), some 2, none⟩,
  ⟨14960, .add 733 164 (-1, 4), some 2, none⟩,
  ⟨14961, .add 733 165 (1, 4), some 2, none⟩,
  ⟨14962, .add 733 218 (1, 4), some 2, none⟩,
  ⟨14963, .relabel 733 2 420, none, some (237, 7)⟩,
  ⟨14964, .add 241 733 (-1, 1), some 420, none⟩,
  ⟨14965, .clear 733 420, some 420, none⟩,
  ⟨14966, .clear 734 0, some 0, none⟩,
  ⟨14967, .add 734 168 (-1, 4), some 0, none⟩,
  ⟨14968, .add 734 143 (1, 4), some 0, none⟩,
  ⟨14969, .add 734 150 (-1, 4), some 0, none⟩,
  ⟨14970, .add 734 189 (1, 4), some 0, none⟩,
  ⟨14971, .add 734 196 (-1, 4), some 0, none⟩,
  ⟨14972, .add 734 186 (1, 4), some 0, none⟩,
  ⟨14973, .add 734 172 (-1, 4), some 0, none⟩,
  ⟨14974, .add 734 141 (1, 4), some 0, none⟩,
  ⟨14975, .add 734 115 (-1, 4), some 0, none⟩,
  ⟨14976, .add 734 200 (1, 4), some 0, none⟩,
  ⟨14977, .add 734 178 (-1, 4), some 0, none⟩,
  ⟨14978, .add 734 138 (1, 4), some 0, none⟩,
  ⟨14979, .add 734 156 (1, 4), some 0, none⟩,
  ⟨14980, .add 734 162 (-1, 4), some 0, none⟩,
  ⟨14981, .add 734 145 (1, 4), some 0, none⟩,
  ⟨14982, .add 734 221 (-1, 4), some 0, none⟩,
  ⟨14983, .add 734 135 (1, 4), some 0, none⟩,
  ⟨14984, .relabel 734 0 2, none, some (0, 1)⟩,
  ⟨14985, .add 734 137 (1, 4), some 2, none⟩,
  ⟨14986, .add 734 201 (1, 4), some 2, none⟩,
  ⟨14987, .add 734 191 (1, 4), some 2, none⟩,
  ⟨14988, .add 734 121 (1, 4), some 2, none⟩,
  ⟨14989, .add 734 159 (1, 4), some 2, none⟩,
  ⟨14990, .add 734 223 (1, 4), some 2, none⟩,
  ⟨14991, .add 734 158 (1, 4), some 2, none⟩,
  ⟨14992, .add 734 222 (1, 4), some 2, none⟩,
  ⟨14993, .add 734 211 (1, 4), some 2, none⟩,
  ⟨14994, .add 734 163 (1, 4), some 2, none⟩,
  ⟨14995, .add 734 216 (1, 4), some 2, none⟩,
  ⟨14996, .relabel 734 2 421, none, some (238, 7)⟩,
  ⟨14997, .add 259 734 (-1, 1), some 421, none⟩,
  ⟨14998, .clear 734 421, some 421, none⟩,
  ⟨14999, .clear 735 0, some 0, none⟩,
  ⟨15000, .add 735 187 (-1, 4), some 0, none⟩,
  ⟨15001, .add 735 113 (1, 4), some 0, none⟩,
  ⟨15002, .add 735 140 (-1, 4), some 0, none⟩,
  ⟨15003, .add 735 198 (1, 4), some 0, none⟩,
  ⟨15004, .add 735 214 (-1, 4), some 0, none⟩,
  ⟨15005, .add 735 167 (1, 4), some 0, none⟩,
  ⟨15006, .add 735 131 (-1, 4), some 0, none⟩,
  ⟨15007, .add 735 151 (1, 4), some 0, none⟩,
  ⟨15008, .add 735 144 (-1, 4), some 0, none⟩,
  ⟨15009, .add 735 197 (1, 4), some 0, none⟩,
  ⟨15010, .add 735 136 (-1, 4), some 0, none⟩,
  ⟨15011, .add 735 147 (1, 4), some 0, none⟩,
  ⟨15012, .add 735 156 (-1, 4), some 0, none⟩,
  ⟨15013, .add 735 181 (-1, 4), some 0, none⟩,
  ⟨15014, .add 735 116 (1, 4), some 0, none⟩,
  ⟨15015, .add 735 209 (-1, 4), some 0, none⟩,
  ⟨15016, .add 735 177 (1, 4), some 0, none⟩,
  ⟨15017, .relabel 735 0 2, none, some (0, 1)⟩,
  ⟨15018, .add 735 137 (-1, 4), some 2, none⟩,
  ⟨15019, .add 735 201 (1, 4), some 2, none⟩,
  ⟨15020, .add 735 191 (-1, 4), some 2, none⟩,
  ⟨15021, .add 735 121 (1, 4), some 2, none⟩,
  ⟨15022, .add 735 159 (-1, 4), some 2, none⟩,
  ⟨15023, .add 735 223 (1, 4), some 2, none⟩,
  ⟨15024, .add 735 158 (-1, 4), some 2, none⟩,
  ⟨15025, .add 735 222 (1, 4), some 2, none⟩,
  ⟨15026, .add 735 211 (-1, 4), some 2, none⟩,
  ⟨15027, .add 735 163 (1, 4), some 2, none⟩,
  ⟨15028, .add 735 216 (1, 4), some 2, none⟩,
  ⟨15029, .relabel 735 2 422, none, some (239, 7)⟩,
  ⟨15030, .add 257 735 (-1, 1), some 422, none⟩,
  ⟨15031, .clear 735 422, some 422, none⟩
]

theorem forward_checked : bandCertificate forward = true := by decide +kernel
theorem backward_checked : bandCertificate backward = true := by decide +kernel

theorem exact_band_indices :
    forward.map Row.sourceIndex = List.range' 14768 264 ∧
    backward.map Row.sourceIndex = List.range' 14768 264 := by decide +kernel

/-- All 736 outputs agree, including the eight cleared work registers. -/
theorem forward_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun forward h = some out ∧ rawRowsRun forward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (centre k) = 0) :=
  certified_band_independent forward forward_checked h h' hL

theorem backward_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun backward h = some out ∧ rawRowsRun backward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (centre k) = 0) :=
  certified_band_independent backward backward_checked h h' hL

end CurrentMain.F19CentreBand

#print axioms CurrentMain.F19CentreBand.safe_run_related
#print axioms CurrentMain.F19CentreBand.certified_band_independent
#print axioms CurrentMain.F19CentreBand.forward_checked
#print axioms CurrentMain.F19CentreBand.backward_checked
#print axioms CurrentMain.F19CentreBand.exact_band_indices
#print axioms CurrentMain.F19CentreBand.forward_independent
#print axioms CurrentMain.F19CentreBand.backward_independent
