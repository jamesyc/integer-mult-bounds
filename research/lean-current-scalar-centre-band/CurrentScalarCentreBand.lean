import F19CentreBandIndependence
import CanonicalFrameCoverage

/-!
Current535 scalar centre band at immutable 7dfa22b. Current rows use all 997
frame labels. The frame-erasing map below is used only for scalar semantics,
where relabel is identity; it does not identify current and historical frames.
The actual current labels and directed child references remain in each Row997.
The accepted generic dirty-COPY/CLEAR and independence theorem are reused.
No physical recipe, omitted adapter, prefix/suffix or whole-word supplier follows.
Conditional source kappa = 1584931111785787/1000000000000000000.
Apache-2.0; PR509 and selected source attribution retained. OpenAI-assisted.
-/
set_option Elab.async false
namespace CurrentMain.CurrentScalarCentreBand

abbrev Register := CanonicalFrameCoverage.Register
abbrev Row (n : Nat) := CanonicalFrameCoverage.Row n
abbrev RawEvent (n : Nat) := CanonicalFrameCoverage.LabelEvent n
abbrev ScalarEvent (n : Nat) := LemmaG.Event Register (Fin n) ℚ

/-- Scalar evaluation ignores frame annotations, but preserves all registers and
signed coefficients. This is not a label-domain embedding. -/
def scalarProjection {n : Nat} : RawEvent n → F19SelectedCoverage.LabelEvent
  | .relabel r _ _ => .relabel r 0 0
  | .add t s q => .add t s q
  | .scale t q => .scale t q
  | .copy t s _ => .copy t s 0
  | .clear t _ => .clear t 0

def projectRow {n : Nat} (row : Row n) : F19SelectedCoverage.Row :=
  ⟨row.sourceIndex, scalarProjection row.event,
    row.scalarFrame.map (fun _ => 0), row.childRef⟩

def projectRows {n : Nat} (rows : List (Row n)) : List F19SelectedCoverage.Row :=
  rows.map projectRow

/-- The actual current frame labels are preserved by this coefficient decoder. -/
def decodeEvent {n : Nat} : RawEvent n → Option (ScalarEvent n)
  | .relabel r a b => some (.relabel r a b)
  | .add t s q => (F19ScalarEventInterpretation.decodeCoefficient q).map
      (fun c => .add t s c)
  | .scale t q => (F19ScalarEventInterpretation.decodeCoefficient q).map
      (fun c => .scale t c)
  | .copy t s f => some (.copy t s f)
  | .clear t f => some (.clear t f)

def decodeRows {n : Nat} (rows : List (Row n)) : Option (List (ScalarEvent n)) :=
  rows.mapM (fun row => decodeEvent row.event)

def validDenominator {n : Nat} : RawEvent n → Bool
  | .add _ _ q | .scale _ q => decide (q.2 ≠ 0)
  | _ => true

private theorem event_decodes {n : Nat} (e : RawEvent n)
    (hd : validDenominator e = true) : ∃ d, decodeEvent e = some d := by
  cases e with
  | relabel r a b => exact ⟨.relabel r a b, rfl⟩
  | add t s q =>
      have hq : q.2 ≠ 0 := of_decide_eq_true hd
      exact ⟨.add t s ((q.1 : ℚ) / (q.2 : ℚ)), by
        simp [decodeEvent, F19ScalarEventInterpretation.decodeCoefficient, hq]⟩
  | scale t q =>
      have hq : q.2 ≠ 0 := of_decide_eq_true hd
      exact ⟨.scale t ((q.1 : ℚ) / (q.2 : ℚ)), by
        simp [decodeEvent, F19ScalarEventInterpretation.decodeCoefficient, hq]⟩
  | copy t s f => exact ⟨.copy t s f, rfl⟩
  | clear t f => exact ⟨.clear t f, rfl⟩

theorem rows_decode {n : Nat} (rows : List (Row n))
    (hd : rows.all (fun r => validDenominator r.event) = true) :
    ∃ es, decodeRows rows = some es := by
  induction rows with
  | nil => exact ⟨[], rfl⟩
  | cons row rows ih =>
      have hh := Bool.and_eq_true_iff.mp hd
      obtain ⟨d, he⟩ := event_decodes row.event hh.1
      obtain ⟨es, ht⟩ := ih hh.2
      refine ⟨d :: es, ?_⟩
      have hm : rows.mapM (fun r => decodeEvent r.event) = some es := ht
      simp [decodeRows, List.mapM_cons, he, hm]

section Semantics
variable {n : Nat} {M : Type*} [AddCommMonoid M] [Module ℚ M]

/-- The accepted scalar interpreter after an explicit frame-only projection. -/
def rawRowsRun (rows : List (Row n)) (h : Register → M) : Option (Register → M) :=
  F19ScalarPilotComposition.rawRowsRun (projectRows rows) h

theorem decoded_step (e : RawEvent n) (d : ScalarEvent n)
    (hd : decodeEvent e = some d) (h : Register → M) :
    F19ScalarEventInterpretation.rawScalarStep (scalarProjection e) h =
      some (d.scal h) := by
  cases e with
  | relabel r a b =>
      simp_all [decodeEvent, scalarProjection, F19ScalarEventInterpretation.rawScalarStep,
        LemmaG.Event.scal, LemmaG.Event.phys] <;> subst d <;> rfl
  | add t s q =>
      by_cases hz : q.2 = 0 <;>
        simp_all [decodeEvent, scalarProjection, F19ScalarEventInterpretation.decodeCoefficient,
          F19ScalarEventInterpretation.rawScalarStep, hz,
          LemmaG.Event.scal, LemmaG.Event.phys] <;> subst d <;> rfl
  | scale t q =>
      by_cases hz : q.2 = 0 <;>
        simp_all [decodeEvent, scalarProjection, F19ScalarEventInterpretation.decodeCoefficient,
          F19ScalarEventInterpretation.rawScalarStep, hz,
          LemmaG.Event.scal, LemmaG.Event.phys] <;> subst d <;> rfl
  | copy t s f =>
      simp_all [decodeEvent, scalarProjection, F19ScalarEventInterpretation.rawScalarStep,
        LemmaG.Event.scal, LemmaG.Event.phys] <;> subst d <;> rfl
  | clear t f =>
      simp_all [decodeEvent, scalarProjection, F19ScalarEventInterpretation.rawScalarStep,
        LemmaG.Event.scal, LemmaG.Event.phys] <;> subst d <;> rfl

/-- Ordered decoder composition, using the accepted raw interpreter and PR509
scalar run. This induction only transports coefficient/label syntax. -/
theorem decoded_rows_run (rows : List (Row n)) (es : List (ScalarEvent n))
    (hd : decodeRows rows = some es) (h : Register → M) :
    rawRowsRun rows h = some (LemmaG.Stream.scalRun es h) := by
  induction rows generalizing es h with
  | nil =>
      have he : es = [] := by simpa [decodeRows] using hd.symm
      subst es; rfl
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
              change (F19ScalarEventInterpretation.rawScalarStep
                (scalarProjection row.event) h).bind
                (F19ScalarPilotComposition.rawRowsRun (projectRows rows)) =
                some (LemmaG.Stream.scalRun ds (d.scal h))
              rw [decoded_step row.event d he h]
              exact ih ds ht (d.scal h)
end Semantics

/-- Decoding rational coefficients preserves current997 labels exactly. -/
theorem decoded_labels {n : Nat} (e : RawEvent n) (d : ScalarEvent n)
    (hd : decodeEvent e = some d) (l : Register → Fin n) :
    d.lab l = e.lab l := by
  cases e with
  | relabel r a b => simp_all [decodeEvent, LemmaG.Event.lab] <;> subst d <;> rfl
  | add t s q =>
      by_cases hz : q.2 = 0 <;>
        simp_all [decodeEvent, F19ScalarEventInterpretation.decodeCoefficient,
          hz, LemmaG.Event.lab] <;> subst d <;> rfl
  | scale t q =>
      by_cases hz : q.2 = 0 <;>
        simp_all [decodeEvent, F19ScalarEventInterpretation.decodeCoefficient,
          hz, LemmaG.Event.lab] <;> subst d <;> rfl
  | copy t s f => simp_all [decodeEvent, LemmaG.Event.lab] <;> subst d <;> rfl
  | clear t f => simp_all [decodeEvent, LemmaG.Event.lab] <;> subst d <;> rfl

/-- Reuse the already checked arbitrary-centre state relation through the explicit
scalar projection. No new independence or stream-conjugation induction. -/
theorem certified_current_band {n : Nat} {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (rows : List (Row n))
    (hc : F19CentreBand.bandCertificate (projectRows rows) = true)
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun rows h = some out ∧ rawRowsRun rows h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) :=
  F19CentreBand.certified_band_independent (projectRows rows) hc h h' hL

def forward : List (Row 997) := [
  ⟨13762, .clear 728 412, some 412, none⟩,
  ⟨13763, .copy 728 229 412, some 412, none⟩,
  ⟨13764, .relabel 728 412 0, none, some (1443, 8)⟩,
  ⟨13765, .add 124 728 (1, 4), some 0, none⟩,
  ⟨13766, .add 212 728 (1, 4), some 0, none⟩,
  ⟨13767, .add 215 728 (1, 4), some 0, none⟩,
  ⟨13768, .add 129 728 (1, 4), some 0, none⟩,
  ⟨13769, .add 184 728 (1, 4), some 0, none⟩,
  ⟨13770, .add 114 728 (1, 4), some 0, none⟩,
  ⟨13771, .add 173 728 (1, 4), some 0, none⟩,
  ⟨13772, .add 206 728 (1, 4), some 0, none⟩,
  ⟨13773, .add 182 728 (1, 4), some 0, none⟩,
  ⟨13774, .add 183 728 (1, 4), some 0, none⟩,
  ⟨13775, .add 175 728 (1, 4), some 0, none⟩,
  ⟨13776, .add 174 728 (1, 4), some 0, none⟩,
  ⟨13777, .add 213 728 (1, 4), some 0, none⟩,
  ⟨13778, .add 166 728 (1, 4), some 0, none⟩,
  ⟨13779, .add 130 728 (1, 4), some 0, none⟩,
  ⟨13780, .add 152 728 (1, 4), some 0, none⟩,
  ⟨13781, .add 112 728 (1, 4), some 0, none⟩,
  ⟨13782, .add 188 728 (1, 4), some 0, none⟩,
  ⟨13783, .add 204 728 (1, 4), some 0, none⟩,
  ⟨13784, .add 169 728 (1, 4), some 0, none⟩,
  ⟨13785, .add 210 728 (1, 4), some 0, none⟩,
  ⟨13786, .add 160 728 (1, 4), some 0, none⟩,
  ⟨13787, .add 157 728 (1, 4), some 0, none⟩,
  ⟨13788, .add 219 728 (1, 4), some 0, none⟩,
  ⟨13789, .add 161 728 (1, 4), some 0, none⟩,
  ⟨13790, .add 146 728 (1, 4), some 0, none⟩,
  ⟨13791, .add 220 728 (1, 4), some 0, none⟩,
  ⟨13792, .add 134 728 (1, 4), some 0, none⟩,
  ⟨13793, .clear 728 0, some 0, none⟩,
  ⟨13794, .clear 729 413, some 413, none⟩,
  ⟨13795, .copy 729 224 413, some 413, none⟩,
  ⟨13796, .relabel 729 413 0, none, some (1445, 8)⟩,
  ⟨13797, .add 118 729 (1, 4), some 0, none⟩,
  ⟨13798, .add 194 729 (1, 4), some 0, none⟩,
  ⟨13799, .add 205 729 (1, 4), some 0, none⟩,
  ⟨13800, .add 170 729 (1, 4), some 0, none⟩,
  ⟨13801, .add 184 729 (1, 4), some 0, none⟩,
  ⟨13802, .add 114 729 (1, 4), some 0, none⟩,
  ⟨13803, .add 173 729 (-1, 4), some 0, none⟩,
  ⟨13804, .add 206 729 (-1, 4), some 0, none⟩,
  ⟨13805, .add 182 729 (1, 4), some 0, none⟩,
  ⟨13806, .add 183 729 (1, 4), some 0, none⟩,
  ⟨13807, .add 175 729 (-1, 4), some 0, none⟩,
  ⟨13808, .add 174 729 (-1, 4), some 0, none⟩,
  ⟨13809, .add 195 729 (1, 4), some 0, none⟩,
  ⟨13810, .add 185 729 (1, 4), some 0, none⟩,
  ⟨13811, .add 171 729 (1, 4), some 0, none⟩,
  ⟨13812, .add 142 729 (1, 4), some 0, none⟩,
  ⟨13813, .add 112 729 (1, 4), some 0, none⟩,
  ⟨13814, .add 188 729 (1, 4), some 0, none⟩,
  ⟨13815, .add 204 729 (-1, 4), some 0, none⟩,
  ⟨13816, .add 169 729 (-1, 4), some 0, none⟩,
  ⟨13817, .add 192 729 (1, 4), some 0, none⟩,
  ⟨13818, .add 179 729 (1, 4), some 0, none⟩,
  ⟨13819, .add 120 729 (1, 4), some 0, none⟩,
  ⟨13820, .add 207 729 (1, 4), some 0, none⟩,
  ⟨13821, .add 180 729 (1, 4), some 0, none⟩,
  ⟨13822, .add 117 729 (1, 4), some 0, none⟩,
  ⟨13823, .add 208 729 (1, 4), some 0, none⟩,
  ⟨13824, .add 176 729 (1, 4), some 0, none⟩,
  ⟨13825, .clear 729 0, some 0, none⟩,
  ⟨13826, .clear 730 414, some 414, none⟩,
  ⟨13827, .copy 730 227 414, some 414, none⟩,
  ⟨13828, .relabel 730 414 0, none, some (1447, 8)⟩,
  ⟨13829, .add 118 730 (1, 4), some 0, none⟩,
  ⟨13830, .add 194 730 (1, 4), some 0, none⟩,
  ⟨13831, .add 205 730 (-1, 4), some 0, none⟩,
  ⟨13832, .add 170 730 (-1, 4), some 0, none⟩,
  ⟨13833, .add 124 730 (1, 4), some 0, none⟩,
  ⟨13834, .add 212 730 (1, 4), some 0, none⟩,
  ⟨13835, .add 215 730 (-1, 4), some 0, none⟩,
  ⟨13836, .add 129 730 (-1, 4), some 0, none⟩,
  ⟨13837, .add 213 730 (1, 4), some 0, none⟩,
  ⟨13838, .add 166 730 (1, 4), some 0, none⟩,
  ⟨13839, .add 130 730 (-1, 4), some 0, none⟩,
  ⟨13840, .add 152 730 (-1, 4), some 0, none⟩,
  ⟨13841, .add 195 730 (1, 4), some 0, none⟩,
  ⟨13842, .add 185 730 (1, 4), some 0, none⟩,
  ⟨13843, .add 171 730 (-1, 4), some 0, none⟩,
  ⟨13844, .add 142 730 (-1, 4), some 0, none⟩,
  ⟨13845, .add 199 730 (1, 4), some 0, none⟩,
  ⟨13846, .add 139 730 (1, 4), some 0, none⟩,
  ⟨13847, .add 119 730 (1, 4), some 0, none⟩,
  ⟨13848, .add 193 730 (1, 4), some 0, none⟩,
  ⟨13849, .add 125 730 (1, 4), some 0, none⟩,
  ⟨13850, .add 190 730 (1, 4), some 0, none⟩,
  ⟨13851, .add 155 730 (1, 4), some 0, none⟩,
  ⟨13852, .add 128 730 (1, 4), some 0, none⟩,
  ⟨13853, .add 127 730 (1, 4), some 0, none⟩,
  ⟨13854, .add 126 730 (1, 4), some 0, none⟩,
  ⟨13855, .add 153 730 (1, 4), some 0, none⟩,
  ⟨13856, .add 154 730 (1, 4), some 0, none⟩,
  ⟨13857, .clear 730 0, some 0, none⟩,
  ⟨13858, .clear 731 415, some 415, none⟩,
  ⟨13859, .copy 731 225 415, some 415, none⟩,
  ⟨13860, .relabel 731 415 0, none, some (1449, 8)⟩,
  ⟨13861, .add 199 731 (-1, 4), some 0, none⟩,
  ⟨13862, .add 139 731 (1, 4), some 0, none⟩,
  ⟨13863, .add 119 731 (-1, 4), some 0, none⟩,
  ⟨13864, .add 193 731 (1, 4), some 0, none⟩,
  ⟨13865, .add 210 731 (1, 4), some 0, none⟩,
  ⟨13866, .add 160 731 (1, 4), some 0, none⟩,
  ⟨13867, .add 157 731 (-1, 4), some 0, none⟩,
  ⟨13868, .add 219 731 (-1, 4), some 0, none⟩,
  ⟨13869, .add 192 731 (1, 4), some 0, none⟩,
  ⟨13870, .add 179 731 (1, 4), some 0, none⟩,
  ⟨13871, .add 120 731 (-1, 4), some 0, none⟩,
  ⟨13872, .add 207 731 (-1, 4), some 0, none⟩,
  ⟨13873, .add 125 731 (1, 4), some 0, none⟩,
  ⟨13874, .add 190 731 (1, 4), some 0, none⟩,
  ⟨13875, .add 155 731 (-1, 4), some 0, none⟩,
  ⟨13876, .add 128 731 (-1, 4), some 0, none⟩,
  ⟨13877, .add 127 731 (1, 4), some 0, none⟩,
  ⟨13878, .add 126 731 (1, 4), some 0, none⟩,
  ⟨13879, .add 153 731 (-1, 4), some 0, none⟩,
  ⟨13880, .add 154 731 (-1, 4), some 0, none⟩,
  ⟨13881, .add 180 731 (1, 4), some 0, none⟩,
  ⟨13882, .add 117 731 (1, 4), some 0, none⟩,
  ⟨13883, .add 208 731 (-1, 4), some 0, none⟩,
  ⟨13884, .add 176 731 (-1, 4), some 0, none⟩,
  ⟨13885, .add 161 731 (1, 4), some 0, none⟩,
  ⟨13886, .add 146 731 (1, 4), some 0, none⟩,
  ⟨13887, .add 220 731 (-1, 4), some 0, none⟩,
  ⟨13888, .add 134 731 (-1, 4), some 0, none⟩,
  ⟨13889, .clear 731 0, some 0, none⟩,
  ⟨13890, .clear 732 416, some 416, none⟩,
  ⟨13891, .copy 732 243 416, some 416, none⟩,
  ⟨13892, .relabel 732 416 0, none, some (1451, 8)⟩,
  ⟨13893, .add 187 732 (1, 4), some 0, none⟩,
  ⟨13894, .add 113 732 (1, 4), some 0, none⟩,
  ⟨13895, .add 140 732 (1, 4), some 0, none⟩,
  ⟨13896, .add 198 732 (1, 4), some 0, none⟩,
  ⟨13897, .add 168 732 (1, 4), some 0, none⟩,
  ⟨13898, .add 143 732 (1, 4), some 0, none⟩,
  ⟨13899, .add 150 732 (1, 4), some 0, none⟩,
  ⟨13900, .add 189 732 (1, 4), some 0, none⟩,
  ⟨13901, .add 202 732 (1, 4), some 0, none⟩,
  ⟨13902, .add 203 732 (1, 4), some 0, none⟩,
  ⟨13903, .add 122 732 (1, 4), some 0, none⟩,
  ⟨13904, .add 123 732 (1, 4), some 0, none⟩,
  ⟨13905, .add 148 732 (1, 4), some 0, none⟩,
  ⟨13906, .add 133 732 (1, 4), some 0, none⟩,
  ⟨13907, .add 149 732 (1, 4), some 0, none⟩,
  ⟨13908, .add 132 732 (1, 4), some 0, none⟩,
  ⟨13909, .add 144 732 (1, 4), some 0, none⟩,
  ⟨13910, .add 197 732 (1, 4), some 0, none⟩,
  ⟨13911, .add 136 732 (1, 4), some 0, none⟩,
  ⟨13912, .add 147 732 (1, 4), some 0, none⟩,
  ⟨13913, .add 115 732 (1, 4), some 0, none⟩,
  ⟨13914, .add 200 732 (1, 4), some 0, none⟩,
  ⟨13915, .add 178 732 (1, 4), some 0, none⟩,
  ⟨13916, .add 138 732 (1, 4), some 0, none⟩,
  ⟨13917, .add 164 732 (1, 4), some 0, none⟩,
  ⟨13918, .add 165 732 (1, 4), some 0, none⟩,
  ⟨13919, .add 217 732 (1, 4), some 0, none⟩,
  ⟨13920, .add 218 732 (1, 4), some 0, none⟩,
  ⟨13921, .clear 732 0, some 0, none⟩,
  ⟨13922, .clear 733 417, some 417, none⟩,
  ⟨13923, .copy 733 241 417, some 417, none⟩,
  ⟨13924, .relabel 733 417 0, none, some (1453, 8)⟩,
  ⟨13925, .add 202 733 (-1, 4), some 0, none⟩,
  ⟨13926, .add 203 733 (1, 4), some 0, none⟩,
  ⟨13927, .add 122 733 (-1, 4), some 0, none⟩,
  ⟨13928, .add 123 733 (1, 4), some 0, none⟩,
  ⟨13929, .add 214 733 (1, 4), some 0, none⟩,
  ⟨13930, .add 167 733 (1, 4), some 0, none⟩,
  ⟨13931, .add 131 733 (1, 4), some 0, none⟩,
  ⟨13932, .add 151 733 (1, 4), some 0, none⟩,
  ⟨13933, .add 196 733 (1, 4), some 0, none⟩,
  ⟨13934, .add 186 733 (1, 4), some 0, none⟩,
  ⟨13935, .add 172 733 (1, 4), some 0, none⟩,
  ⟨13936, .add 141 733 (1, 4), some 0, none⟩,
  ⟨13937, .add 148 733 (1, 4), some 0, none⟩,
  ⟨13938, .add 133 733 (1, 4), some 0, none⟩,
  ⟨13939, .add 149 733 (-1, 4), some 0, none⟩,
  ⟨13940, .add 132 733 (-1, 4), some 0, none⟩,
  ⟨13941, .add 164 733 (-1, 4), some 0, none⟩,
  ⟨13942, .add 165 733 (1, 4), some 0, none⟩,
  ⟨13943, .add 217 733 (-1, 4), some 0, none⟩,
  ⟨13944, .add 218 733 (1, 4), some 0, none⟩,
  ⟨13945, .add 181 733 (1, 4), some 0, none⟩,
  ⟨13946, .add 116 733 (1, 4), some 0, none⟩,
  ⟨13947, .add 209 733 (1, 4), some 0, none⟩,
  ⟨13948, .add 177 733 (1, 4), some 0, none⟩,
  ⟨13949, .add 162 733 (1, 4), some 0, none⟩,
  ⟨13950, .add 145 733 (1, 4), some 0, none⟩,
  ⟨13951, .add 221 733 (1, 4), some 0, none⟩,
  ⟨13952, .add 135 733 (1, 4), some 0, none⟩,
  ⟨13953, .clear 733 0, some 0, none⟩,
  ⟨13954, .clear 734 418, some 418, none⟩,
  ⟨13955, .copy 734 259 418, some 418, none⟩,
  ⟨13956, .relabel 734 418 0, none, some (1455, 8)⟩,
  ⟨13957, .add 168 734 (-1, 4), some 0, none⟩,
  ⟨13958, .add 143 734 (1, 4), some 0, none⟩,
  ⟨13959, .add 150 734 (-1, 4), some 0, none⟩,
  ⟨13960, .add 189 734 (1, 4), some 0, none⟩,
  ⟨13961, .add 137 734 (1, 4), some 0, none⟩,
  ⟨13962, .add 201 734 (1, 4), some 0, none⟩,
  ⟨13963, .add 191 734 (1, 4), some 0, none⟩,
  ⟨13964, .add 121 734 (1, 4), some 0, none⟩,
  ⟨13965, .add 196 734 (-1, 4), some 0, none⟩,
  ⟨13966, .add 186 734 (1, 4), some 0, none⟩,
  ⟨13967, .add 172 734 (-1, 4), some 0, none⟩,
  ⟨13968, .add 141 734 (1, 4), some 0, none⟩,
  ⟨13969, .add 159 734 (1, 4), some 0, none⟩,
  ⟨13970, .add 223 734 (1, 4), some 0, none⟩,
  ⟨13971, .add 158 734 (1, 4), some 0, none⟩,
  ⟨13972, .add 222 734 (1, 4), some 0, none⟩,
  ⟨13973, .add 115 734 (-1, 4), some 0, none⟩,
  ⟨13974, .add 200 734 (1, 4), some 0, none⟩,
  ⟨13975, .add 178 734 (-1, 4), some 0, none⟩,
  ⟨13976, .add 138 734 (1, 4), some 0, none⟩,
  ⟨13977, .add 211 734 (1, 4), some 0, none⟩,
  ⟨13978, .add 163 734 (1, 4), some 0, none⟩,
  ⟨13979, .add 156 734 (1, 4), some 0, none⟩,
  ⟨13980, .add 216 734 (1, 4), some 0, none⟩,
  ⟨13981, .add 162 734 (-1, 4), some 0, none⟩,
  ⟨13982, .add 145 734 (1, 4), some 0, none⟩,
  ⟨13983, .add 221 734 (-1, 4), some 0, none⟩,
  ⟨13984, .add 135 734 (1, 4), some 0, none⟩,
  ⟨13985, .clear 734 0, some 0, none⟩,
  ⟨13986, .clear 735 419, some 419, none⟩,
  ⟨13987, .copy 735 257 419, some 419, none⟩,
  ⟨13988, .relabel 735 419 0, none, some (1457, 8)⟩,
  ⟨13989, .add 187 735 (-1, 4), some 0, none⟩,
  ⟨13990, .add 113 735 (1, 4), some 0, none⟩,
  ⟨13991, .add 140 735 (-1, 4), some 0, none⟩,
  ⟨13992, .add 198 735 (1, 4), some 0, none⟩,
  ⟨13993, .add 137 735 (-1, 4), some 0, none⟩,
  ⟨13994, .add 201 735 (1, 4), some 0, none⟩,
  ⟨13995, .add 191 735 (-1, 4), some 0, none⟩,
  ⟨13996, .add 121 735 (1, 4), some 0, none⟩,
  ⟨13997, .add 214 735 (-1, 4), some 0, none⟩,
  ⟨13998, .add 167 735 (1, 4), some 0, none⟩,
  ⟨13999, .add 131 735 (-1, 4), some 0, none⟩,
  ⟨14000, .add 151 735 (1, 4), some 0, none⟩,
  ⟨14001, .add 159 735 (-1, 4), some 0, none⟩,
  ⟨14002, .add 223 735 (1, 4), some 0, none⟩,
  ⟨14003, .add 158 735 (-1, 4), some 0, none⟩,
  ⟨14004, .add 222 735 (1, 4), some 0, none⟩,
  ⟨14005, .add 144 735 (-1, 4), some 0, none⟩,
  ⟨14006, .add 197 735 (1, 4), some 0, none⟩,
  ⟨14007, .add 136 735 (-1, 4), some 0, none⟩,
  ⟨14008, .add 147 735 (1, 4), some 0, none⟩,
  ⟨14009, .add 211 735 (-1, 4), some 0, none⟩,
  ⟨14010, .add 163 735 (1, 4), some 0, none⟩,
  ⟨14011, .add 156 735 (-1, 4), some 0, none⟩,
  ⟨14012, .add 216 735 (1, 4), some 0, none⟩,
  ⟨14013, .add 181 735 (-1, 4), some 0, none⟩,
  ⟨14014, .add 116 735 (1, 4), some 0, none⟩,
  ⟨14015, .add 209 735 (-1, 4), some 0, none⟩,
  ⟨14016, .add 177 735 (1, 4), some 0, none⟩,
  ⟨14017, .clear 735 0, some 0, none⟩
]

def backward : List (Row 997) := [
  ⟨13762, .clear 728 0, some 0, none⟩,
  ⟨13763, .add 728 124 (1, 4), some 0, none⟩,
  ⟨13764, .add 728 212 (1, 4), some 0, none⟩,
  ⟨13765, .add 728 215 (1, 4), some 0, none⟩,
  ⟨13766, .add 728 129 (1, 4), some 0, none⟩,
  ⟨13767, .add 728 184 (1, 4), some 0, none⟩,
  ⟨13768, .add 728 114 (1, 4), some 0, none⟩,
  ⟨13769, .add 728 173 (1, 4), some 0, none⟩,
  ⟨13770, .add 728 206 (1, 4), some 0, none⟩,
  ⟨13771, .add 728 182 (1, 4), some 0, none⟩,
  ⟨13772, .add 728 183 (1, 4), some 0, none⟩,
  ⟨13773, .add 728 175 (1, 4), some 0, none⟩,
  ⟨13774, .add 728 174 (1, 4), some 0, none⟩,
  ⟨13775, .add 728 213 (1, 4), some 0, none⟩,
  ⟨13776, .add 728 166 (1, 4), some 0, none⟩,
  ⟨13777, .add 728 130 (1, 4), some 0, none⟩,
  ⟨13778, .add 728 152 (1, 4), some 0, none⟩,
  ⟨13779, .add 728 112 (1, 4), some 0, none⟩,
  ⟨13780, .add 728 188 (1, 4), some 0, none⟩,
  ⟨13781, .add 728 204 (1, 4), some 0, none⟩,
  ⟨13782, .add 728 169 (1, 4), some 0, none⟩,
  ⟨13783, .add 728 210 (1, 4), some 0, none⟩,
  ⟨13784, .add 728 160 (1, 4), some 0, none⟩,
  ⟨13785, .add 728 157 (1, 4), some 0, none⟩,
  ⟨13786, .add 728 219 (1, 4), some 0, none⟩,
  ⟨13787, .add 728 161 (1, 4), some 0, none⟩,
  ⟨13788, .add 728 146 (1, 4), some 0, none⟩,
  ⟨13789, .add 728 220 (1, 4), some 0, none⟩,
  ⟨13790, .add 728 134 (1, 4), some 0, none⟩,
  ⟨13791, .relabel 728 0 412, none, some (130, 8)⟩,
  ⟨13792, .add 229 728 (-1, 1), some 412, none⟩,
  ⟨13793, .clear 728 412, some 412, none⟩,
  ⟨13794, .clear 729 0, some 0, none⟩,
  ⟨13795, .add 729 118 (1, 4), some 0, none⟩,
  ⟨13796, .add 729 194 (1, 4), some 0, none⟩,
  ⟨13797, .add 729 205 (1, 4), some 0, none⟩,
  ⟨13798, .add 729 170 (1, 4), some 0, none⟩,
  ⟨13799, .add 729 184 (1, 4), some 0, none⟩,
  ⟨13800, .add 729 114 (1, 4), some 0, none⟩,
  ⟨13801, .add 729 173 (-1, 4), some 0, none⟩,
  ⟨13802, .add 729 206 (-1, 4), some 0, none⟩,
  ⟨13803, .add 729 182 (1, 4), some 0, none⟩,
  ⟨13804, .add 729 183 (1, 4), some 0, none⟩,
  ⟨13805, .add 729 175 (-1, 4), some 0, none⟩,
  ⟨13806, .add 729 174 (-1, 4), some 0, none⟩,
  ⟨13807, .add 729 195 (1, 4), some 0, none⟩,
  ⟨13808, .add 729 185 (1, 4), some 0, none⟩,
  ⟨13809, .add 729 171 (1, 4), some 0, none⟩,
  ⟨13810, .add 729 142 (1, 4), some 0, none⟩,
  ⟨13811, .add 729 112 (1, 4), some 0, none⟩,
  ⟨13812, .add 729 188 (1, 4), some 0, none⟩,
  ⟨13813, .add 729 204 (-1, 4), some 0, none⟩,
  ⟨13814, .add 729 169 (-1, 4), some 0, none⟩,
  ⟨13815, .add 729 192 (1, 4), some 0, none⟩,
  ⟨13816, .add 729 179 (1, 4), some 0, none⟩,
  ⟨13817, .add 729 120 (1, 4), some 0, none⟩,
  ⟨13818, .add 729 207 (1, 4), some 0, none⟩,
  ⟨13819, .add 729 180 (1, 4), some 0, none⟩,
  ⟨13820, .add 729 117 (1, 4), some 0, none⟩,
  ⟨13821, .add 729 208 (1, 4), some 0, none⟩,
  ⟨13822, .add 729 176 (1, 4), some 0, none⟩,
  ⟨13823, .relabel 729 0 413, none, some (131, 8)⟩,
  ⟨13824, .add 224 729 (-1, 1), some 413, none⟩,
  ⟨13825, .clear 729 413, some 413, none⟩,
  ⟨13826, .clear 730 0, some 0, none⟩,
  ⟨13827, .add 730 118 (1, 4), some 0, none⟩,
  ⟨13828, .add 730 194 (1, 4), some 0, none⟩,
  ⟨13829, .add 730 205 (-1, 4), some 0, none⟩,
  ⟨13830, .add 730 170 (-1, 4), some 0, none⟩,
  ⟨13831, .add 730 124 (1, 4), some 0, none⟩,
  ⟨13832, .add 730 212 (1, 4), some 0, none⟩,
  ⟨13833, .add 730 215 (-1, 4), some 0, none⟩,
  ⟨13834, .add 730 129 (-1, 4), some 0, none⟩,
  ⟨13835, .add 730 213 (1, 4), some 0, none⟩,
  ⟨13836, .add 730 166 (1, 4), some 0, none⟩,
  ⟨13837, .add 730 130 (-1, 4), some 0, none⟩,
  ⟨13838, .add 730 152 (-1, 4), some 0, none⟩,
  ⟨13839, .add 730 195 (1, 4), some 0, none⟩,
  ⟨13840, .add 730 185 (1, 4), some 0, none⟩,
  ⟨13841, .add 730 171 (-1, 4), some 0, none⟩,
  ⟨13842, .add 730 142 (-1, 4), some 0, none⟩,
  ⟨13843, .add 730 199 (1, 4), some 0, none⟩,
  ⟨13844, .add 730 139 (1, 4), some 0, none⟩,
  ⟨13845, .add 730 119 (1, 4), some 0, none⟩,
  ⟨13846, .add 730 193 (1, 4), some 0, none⟩,
  ⟨13847, .add 730 125 (1, 4), some 0, none⟩,
  ⟨13848, .add 730 190 (1, 4), some 0, none⟩,
  ⟨13849, .add 730 155 (1, 4), some 0, none⟩,
  ⟨13850, .add 730 128 (1, 4), some 0, none⟩,
  ⟨13851, .add 730 127 (1, 4), some 0, none⟩,
  ⟨13852, .add 730 126 (1, 4), some 0, none⟩,
  ⟨13853, .add 730 153 (1, 4), some 0, none⟩,
  ⟨13854, .add 730 154 (1, 4), some 0, none⟩,
  ⟨13855, .relabel 730 0 414, none, some (132, 8)⟩,
  ⟨13856, .add 227 730 (-1, 1), some 414, none⟩,
  ⟨13857, .clear 730 414, some 414, none⟩,
  ⟨13858, .clear 731 0, some 0, none⟩,
  ⟨13859, .add 731 199 (-1, 4), some 0, none⟩,
  ⟨13860, .add 731 139 (1, 4), some 0, none⟩,
  ⟨13861, .add 731 119 (-1, 4), some 0, none⟩,
  ⟨13862, .add 731 193 (1, 4), some 0, none⟩,
  ⟨13863, .add 731 210 (1, 4), some 0, none⟩,
  ⟨13864, .add 731 160 (1, 4), some 0, none⟩,
  ⟨13865, .add 731 157 (-1, 4), some 0, none⟩,
  ⟨13866, .add 731 219 (-1, 4), some 0, none⟩,
  ⟨13867, .add 731 192 (1, 4), some 0, none⟩,
  ⟨13868, .add 731 179 (1, 4), some 0, none⟩,
  ⟨13869, .add 731 120 (-1, 4), some 0, none⟩,
  ⟨13870, .add 731 207 (-1, 4), some 0, none⟩,
  ⟨13871, .add 731 125 (1, 4), some 0, none⟩,
  ⟨13872, .add 731 190 (1, 4), some 0, none⟩,
  ⟨13873, .add 731 155 (-1, 4), some 0, none⟩,
  ⟨13874, .add 731 128 (-1, 4), some 0, none⟩,
  ⟨13875, .add 731 127 (1, 4), some 0, none⟩,
  ⟨13876, .add 731 126 (1, 4), some 0, none⟩,
  ⟨13877, .add 731 153 (-1, 4), some 0, none⟩,
  ⟨13878, .add 731 154 (-1, 4), some 0, none⟩,
  ⟨13879, .add 731 180 (1, 4), some 0, none⟩,
  ⟨13880, .add 731 117 (1, 4), some 0, none⟩,
  ⟨13881, .add 731 208 (-1, 4), some 0, none⟩,
  ⟨13882, .add 731 176 (-1, 4), some 0, none⟩,
  ⟨13883, .add 731 161 (1, 4), some 0, none⟩,
  ⟨13884, .add 731 146 (1, 4), some 0, none⟩,
  ⟨13885, .add 731 220 (-1, 4), some 0, none⟩,
  ⟨13886, .add 731 134 (-1, 4), some 0, none⟩,
  ⟨13887, .relabel 731 0 415, none, some (133, 8)⟩,
  ⟨13888, .add 225 731 (-1, 1), some 415, none⟩,
  ⟨13889, .clear 731 415, some 415, none⟩,
  ⟨13890, .clear 732 0, some 0, none⟩,
  ⟨13891, .add 732 187 (1, 4), some 0, none⟩,
  ⟨13892, .add 732 113 (1, 4), some 0, none⟩,
  ⟨13893, .add 732 140 (1, 4), some 0, none⟩,
  ⟨13894, .add 732 198 (1, 4), some 0, none⟩,
  ⟨13895, .add 732 168 (1, 4), some 0, none⟩,
  ⟨13896, .add 732 143 (1, 4), some 0, none⟩,
  ⟨13897, .add 732 150 (1, 4), some 0, none⟩,
  ⟨13898, .add 732 189 (1, 4), some 0, none⟩,
  ⟨13899, .add 732 202 (1, 4), some 0, none⟩,
  ⟨13900, .add 732 203 (1, 4), some 0, none⟩,
  ⟨13901, .add 732 122 (1, 4), some 0, none⟩,
  ⟨13902, .add 732 123 (1, 4), some 0, none⟩,
  ⟨13903, .add 732 148 (1, 4), some 0, none⟩,
  ⟨13904, .add 732 133 (1, 4), some 0, none⟩,
  ⟨13905, .add 732 149 (1, 4), some 0, none⟩,
  ⟨13906, .add 732 132 (1, 4), some 0, none⟩,
  ⟨13907, .add 732 144 (1, 4), some 0, none⟩,
  ⟨13908, .add 732 197 (1, 4), some 0, none⟩,
  ⟨13909, .add 732 136 (1, 4), some 0, none⟩,
  ⟨13910, .add 732 147 (1, 4), some 0, none⟩,
  ⟨13911, .add 732 115 (1, 4), some 0, none⟩,
  ⟨13912, .add 732 200 (1, 4), some 0, none⟩,
  ⟨13913, .add 732 178 (1, 4), some 0, none⟩,
  ⟨13914, .add 732 138 (1, 4), some 0, none⟩,
  ⟨13915, .add 732 164 (1, 4), some 0, none⟩,
  ⟨13916, .add 732 165 (1, 4), some 0, none⟩,
  ⟨13917, .add 732 217 (1, 4), some 0, none⟩,
  ⟨13918, .add 732 218 (1, 4), some 0, none⟩,
  ⟨13919, .relabel 732 0 416, none, some (134, 8)⟩,
  ⟨13920, .add 243 732 (-1, 1), some 416, none⟩,
  ⟨13921, .clear 732 416, some 416, none⟩,
  ⟨13922, .clear 733 0, some 0, none⟩,
  ⟨13923, .add 733 202 (-1, 4), some 0, none⟩,
  ⟨13924, .add 733 203 (1, 4), some 0, none⟩,
  ⟨13925, .add 733 122 (-1, 4), some 0, none⟩,
  ⟨13926, .add 733 123 (1, 4), some 0, none⟩,
  ⟨13927, .add 733 214 (1, 4), some 0, none⟩,
  ⟨13928, .add 733 167 (1, 4), some 0, none⟩,
  ⟨13929, .add 733 131 (1, 4), some 0, none⟩,
  ⟨13930, .add 733 151 (1, 4), some 0, none⟩,
  ⟨13931, .add 733 196 (1, 4), some 0, none⟩,
  ⟨13932, .add 733 186 (1, 4), some 0, none⟩,
  ⟨13933, .add 733 172 (1, 4), some 0, none⟩,
  ⟨13934, .add 733 141 (1, 4), some 0, none⟩,
  ⟨13935, .add 733 148 (1, 4), some 0, none⟩,
  ⟨13936, .add 733 133 (1, 4), some 0, none⟩,
  ⟨13937, .add 733 149 (-1, 4), some 0, none⟩,
  ⟨13938, .add 733 132 (-1, 4), some 0, none⟩,
  ⟨13939, .add 733 164 (-1, 4), some 0, none⟩,
  ⟨13940, .add 733 165 (1, 4), some 0, none⟩,
  ⟨13941, .add 733 217 (-1, 4), some 0, none⟩,
  ⟨13942, .add 733 218 (1, 4), some 0, none⟩,
  ⟨13943, .add 733 181 (1, 4), some 0, none⟩,
  ⟨13944, .add 733 116 (1, 4), some 0, none⟩,
  ⟨13945, .add 733 209 (1, 4), some 0, none⟩,
  ⟨13946, .add 733 177 (1, 4), some 0, none⟩,
  ⟨13947, .add 733 162 (1, 4), some 0, none⟩,
  ⟨13948, .add 733 145 (1, 4), some 0, none⟩,
  ⟨13949, .add 733 221 (1, 4), some 0, none⟩,
  ⟨13950, .add 733 135 (1, 4), some 0, none⟩,
  ⟨13951, .relabel 733 0 417, none, some (135, 8)⟩,
  ⟨13952, .add 241 733 (-1, 1), some 417, none⟩,
  ⟨13953, .clear 733 417, some 417, none⟩,
  ⟨13954, .clear 734 0, some 0, none⟩,
  ⟨13955, .add 734 168 (-1, 4), some 0, none⟩,
  ⟨13956, .add 734 143 (1, 4), some 0, none⟩,
  ⟨13957, .add 734 150 (-1, 4), some 0, none⟩,
  ⟨13958, .add 734 189 (1, 4), some 0, none⟩,
  ⟨13959, .add 734 137 (1, 4), some 0, none⟩,
  ⟨13960, .add 734 201 (1, 4), some 0, none⟩,
  ⟨13961, .add 734 191 (1, 4), some 0, none⟩,
  ⟨13962, .add 734 121 (1, 4), some 0, none⟩,
  ⟨13963, .add 734 196 (-1, 4), some 0, none⟩,
  ⟨13964, .add 734 186 (1, 4), some 0, none⟩,
  ⟨13965, .add 734 172 (-1, 4), some 0, none⟩,
  ⟨13966, .add 734 141 (1, 4), some 0, none⟩,
  ⟨13967, .add 734 159 (1, 4), some 0, none⟩,
  ⟨13968, .add 734 223 (1, 4), some 0, none⟩,
  ⟨13969, .add 734 158 (1, 4), some 0, none⟩,
  ⟨13970, .add 734 222 (1, 4), some 0, none⟩,
  ⟨13971, .add 734 115 (-1, 4), some 0, none⟩,
  ⟨13972, .add 734 200 (1, 4), some 0, none⟩,
  ⟨13973, .add 734 178 (-1, 4), some 0, none⟩,
  ⟨13974, .add 734 138 (1, 4), some 0, none⟩,
  ⟨13975, .add 734 211 (1, 4), some 0, none⟩,
  ⟨13976, .add 734 163 (1, 4), some 0, none⟩,
  ⟨13977, .add 734 156 (1, 4), some 0, none⟩,
  ⟨13978, .add 734 216 (1, 4), some 0, none⟩,
  ⟨13979, .add 734 162 (-1, 4), some 0, none⟩,
  ⟨13980, .add 734 145 (1, 4), some 0, none⟩,
  ⟨13981, .add 734 221 (-1, 4), some 0, none⟩,
  ⟨13982, .add 734 135 (1, 4), some 0, none⟩,
  ⟨13983, .relabel 734 0 418, none, some (136, 8)⟩,
  ⟨13984, .add 259 734 (-1, 1), some 418, none⟩,
  ⟨13985, .clear 734 418, some 418, none⟩,
  ⟨13986, .clear 735 0, some 0, none⟩,
  ⟨13987, .add 735 187 (-1, 4), some 0, none⟩,
  ⟨13988, .add 735 113 (1, 4), some 0, none⟩,
  ⟨13989, .add 735 140 (-1, 4), some 0, none⟩,
  ⟨13990, .add 735 198 (1, 4), some 0, none⟩,
  ⟨13991, .add 735 137 (-1, 4), some 0, none⟩,
  ⟨13992, .add 735 201 (1, 4), some 0, none⟩,
  ⟨13993, .add 735 191 (-1, 4), some 0, none⟩,
  ⟨13994, .add 735 121 (1, 4), some 0, none⟩,
  ⟨13995, .add 735 214 (-1, 4), some 0, none⟩,
  ⟨13996, .add 735 167 (1, 4), some 0, none⟩,
  ⟨13997, .add 735 131 (-1, 4), some 0, none⟩,
  ⟨13998, .add 735 151 (1, 4), some 0, none⟩,
  ⟨13999, .add 735 159 (-1, 4), some 0, none⟩,
  ⟨14000, .add 735 223 (1, 4), some 0, none⟩,
  ⟨14001, .add 735 158 (-1, 4), some 0, none⟩,
  ⟨14002, .add 735 222 (1, 4), some 0, none⟩,
  ⟨14003, .add 735 144 (-1, 4), some 0, none⟩,
  ⟨14004, .add 735 197 (1, 4), some 0, none⟩,
  ⟨14005, .add 735 136 (-1, 4), some 0, none⟩,
  ⟨14006, .add 735 147 (1, 4), some 0, none⟩,
  ⟨14007, .add 735 211 (-1, 4), some 0, none⟩,
  ⟨14008, .add 735 163 (1, 4), some 0, none⟩,
  ⟨14009, .add 735 156 (-1, 4), some 0, none⟩,
  ⟨14010, .add 735 216 (1, 4), some 0, none⟩,
  ⟨14011, .add 735 181 (-1, 4), some 0, none⟩,
  ⟨14012, .add 735 116 (1, 4), some 0, none⟩,
  ⟨14013, .add 735 209 (-1, 4), some 0, none⟩,
  ⟨14014, .add 735 177 (1, 4), some 0, none⟩,
  ⟨14015, .relabel 735 0 419, none, some (137, 8)⟩,
  ⟨14016, .add 257 735 (-1, 1), some 419, none⟩,
  ⟨14017, .clear 735 419, some 419, none⟩
]

private theorem forward_certificate :
    F19CentreBand.bandCertificate (projectRows forward) = true := by decide +kernel

private theorem forward_denominators :
    forward.all (fun r => validDenominator r.event) = true := by decide +kernel

theorem forward_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun forward h = some out ∧ rawRowsRun forward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) :=
  certified_current_band forward forward_certificate h h' hL

theorem forward_interpreted {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 997), decodeRows forward = some es ∧
      ∀ h h' : Register → M, (∀ r, r.val < 728 → h r = h' r) →
        LemmaG.Stream.scalRun es h = LemmaG.Stream.scalRun es h' ∧
        (∀ k : Fin 8, LemmaG.Stream.scalRun es h (F19CentreBand.centre k) = 0) := by
  obtain ⟨es, hd⟩ := rows_decode forward forward_denominators
  refine ⟨es, hd, ?_⟩
  intro h h' hL
  obtain ⟨out, out', ho, ho', he, hz⟩ := forward_independent h h' hL
  rw [decoded_rows_run forward es hd h] at ho
  rw [decoded_rows_run forward es hd h'] at ho'
  have eo := Option.some.inj ho
  have eo' := Option.some.inj ho'
  exact ⟨eo.trans (he.trans eo'.symm), fun k => by rw [eo]; exact hz k⟩

private theorem backward_certificate :
    F19CentreBand.bandCertificate (projectRows backward) = true := by decide +kernel

private theorem backward_denominators :
    backward.all (fun r => validDenominator r.event) = true := by decide +kernel

theorem backward_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun backward h = some out ∧ rawRowsRun backward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) :=
  certified_current_band backward backward_certificate h h' hL

theorem backward_interpreted {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 997), decodeRows backward = some es ∧
      ∀ h h' : Register → M, (∀ r, r.val < 728 → h r = h' r) →
        LemmaG.Stream.scalRun es h = LemmaG.Stream.scalRun es h' ∧
        (∀ k : Fin 8, LemmaG.Stream.scalRun es h (F19CentreBand.centre k) = 0) := by
  obtain ⟨es, hd⟩ := rows_decode backward backward_denominators
  refine ⟨es, hd, ?_⟩
  intro h h' hL
  obtain ⟨out, out', ho, ho', he, hz⟩ := backward_independent h h' hL
  rw [decoded_rows_run backward es hd h] at ho
  rw [decoded_rows_run backward es hd h'] at ho'
  have eo := Option.some.inj ho
  have eo' := Option.some.inj ho'
  exact ⟨eo.trans (he.trans eo'.symm), fun k => by rw [eo]; exact hz k⟩

theorem exact_source_indices :
    forward.map CanonicalFrameCoverage.Row.sourceIndex = List.range' 13762 256 ∧
    backward.map CanonicalFrameCoverage.Row.sourceIndex = List.range' 13762 256 := by
  constructor <;> decide +kernel

end CurrentMain.CurrentScalarCentreBand

#print axioms CurrentMain.CurrentScalarCentreBand.rows_decode
#print axioms CurrentMain.CurrentScalarCentreBand.decoded_step
#print axioms CurrentMain.CurrentScalarCentreBand.decoded_rows_run
#print axioms CurrentMain.CurrentScalarCentreBand.decoded_labels
#print axioms CurrentMain.CurrentScalarCentreBand.certified_current_band
#print axioms CurrentMain.CurrentScalarCentreBand.forward_independent
#print axioms CurrentMain.CurrentScalarCentreBand.forward_interpreted
#print axioms CurrentMain.CurrentScalarCentreBand.backward_independent
#print axioms CurrentMain.CurrentScalarCentreBand.backward_interpreted
#print axioms CurrentMain.CurrentScalarCentreBand.exact_source_indices
