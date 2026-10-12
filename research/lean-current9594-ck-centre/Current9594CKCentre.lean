import CurrentScalarCentreBand

/-!
Selected9594 CK centre supplier from the independently materialized exact provider.
Both 256-event bands are raw zero-based indices12927..13182. The complete Row1079
annotations remain explicit. Scalar-event equality reuses the accepted historical
band only after frame erasure, preserving dirty COPY/CLEAR and signed coefficients.
No historical frame-domain, omitted adapter, prefix/suffix, packed executor, physical
work endpoint, provider-mixture or all-size conclusion is asserted.
Author-checked source context kappa=400569730495803/250000000000000000.
Apache-2.0; PR509, accepted scalar proofs and PR588 provider attribution retained.
Prepared with OpenAI assistance. See SOURCE_SCOPE.json for immutable bindings.
-/
set_option Elab.async false
namespace CurrentMain.Current9594CKCentre
open CurrentScalarCentreBand

/-- Row metadata does not enter the scalar interpreter. This transports equality
of the ordered projected events; it does not identify any frame labels. -/
theorem raw_run_congr_events {n m : Nat} {M : Type*}
    [AddCommMonoid M] [Module ℚ M]
    (rows : List (Row n)) (other : List (Row m))
    (he : (projectRows rows).map F19SelectedCoverage.Row.event =
      (projectRows other).map F19SelectedCoverage.Row.event) (h : Register → M) :
    rawRowsRun rows h = rawRowsRun other h := by
  have aux (xs ys : List F19SelectedCoverage.Row)
      (hx : xs.map F19SelectedCoverage.Row.event = ys.map F19SelectedCoverage.Row.event) :
      ∀ state : Register → M,
        F19ScalarPilotComposition.rawRowsRun xs state =
        F19ScalarPilotComposition.rawRowsRun ys state := by
    induction xs generalizing ys with
    | nil =>
        cases ys with
        | nil => intro state; rfl
        | cons y ys => simp at hx
    | cons x xs ih =>
        cases ys with
        | nil => simp at hx
        | cons y ys =>
            have hh : x.event = y.event ∧
                xs.map F19SelectedCoverage.Row.event = ys.map F19SelectedCoverage.Row.event := by
              simpa only [List.map_cons, List.cons.injEq] using hx
            intro state
            change (F19ScalarEventInterpretation.rawScalarStep x.event state).bind
              (F19ScalarPilotComposition.rawRowsRun xs) =
                (F19ScalarEventInterpretation.rawScalarStep y.event state).bind
                  (F19ScalarPilotComposition.rawRowsRun ys)
            rw [hh.1]
            have ht : (F19ScalarPilotComposition.rawRowsRun xs :
                (Register → M) → Option (Register → M)) =
                  F19ScalarPilotComposition.rawRowsRun ys := funext (ih ys hh.2)
            rw [ht]
  exact aux (projectRows rows) (projectRows other) he h

def forward : List (Row 1079) := [
  ⟨12927, .clear 728 429, some 429, none⟩,
  ⟨12928, .copy 728 229 429, some 429, none⟩,
  ⟨12929, .relabel 728 429 0, none, some (1379, 8)⟩,
  ⟨12930, .add 124 728 (1, 4), some 0, none⟩,
  ⟨12931, .add 212 728 (1, 4), some 0, none⟩,
  ⟨12932, .add 215 728 (1, 4), some 0, none⟩,
  ⟨12933, .add 129 728 (1, 4), some 0, none⟩,
  ⟨12934, .add 184 728 (1, 4), some 0, none⟩,
  ⟨12935, .add 114 728 (1, 4), some 0, none⟩,
  ⟨12936, .add 173 728 (1, 4), some 0, none⟩,
  ⟨12937, .add 206 728 (1, 4), some 0, none⟩,
  ⟨12938, .add 182 728 (1, 4), some 0, none⟩,
  ⟨12939, .add 183 728 (1, 4), some 0, none⟩,
  ⟨12940, .add 175 728 (1, 4), some 0, none⟩,
  ⟨12941, .add 174 728 (1, 4), some 0, none⟩,
  ⟨12942, .add 213 728 (1, 4), some 0, none⟩,
  ⟨12943, .add 166 728 (1, 4), some 0, none⟩,
  ⟨12944, .add 130 728 (1, 4), some 0, none⟩,
  ⟨12945, .add 152 728 (1, 4), some 0, none⟩,
  ⟨12946, .add 112 728 (1, 4), some 0, none⟩,
  ⟨12947, .add 188 728 (1, 4), some 0, none⟩,
  ⟨12948, .add 204 728 (1, 4), some 0, none⟩,
  ⟨12949, .add 169 728 (1, 4), some 0, none⟩,
  ⟨12950, .add 210 728 (1, 4), some 0, none⟩,
  ⟨12951, .add 160 728 (1, 4), some 0, none⟩,
  ⟨12952, .add 157 728 (1, 4), some 0, none⟩,
  ⟨12953, .add 219 728 (1, 4), some 0, none⟩,
  ⟨12954, .add 161 728 (1, 4), some 0, none⟩,
  ⟨12955, .add 146 728 (1, 4), some 0, none⟩,
  ⟨12956, .add 220 728 (1, 4), some 0, none⟩,
  ⟨12957, .add 134 728 (1, 4), some 0, none⟩,
  ⟨12958, .clear 728 0, some 0, none⟩,
  ⟨12959, .clear 729 430, some 430, none⟩,
  ⟨12960, .copy 729 224 430, some 430, none⟩,
  ⟨12961, .relabel 729 430 0, none, some (1381, 8)⟩,
  ⟨12962, .add 118 729 (1, 4), some 0, none⟩,
  ⟨12963, .add 194 729 (1, 4), some 0, none⟩,
  ⟨12964, .add 205 729 (1, 4), some 0, none⟩,
  ⟨12965, .add 170 729 (1, 4), some 0, none⟩,
  ⟨12966, .add 184 729 (1, 4), some 0, none⟩,
  ⟨12967, .add 114 729 (1, 4), some 0, none⟩,
  ⟨12968, .add 173 729 (-1, 4), some 0, none⟩,
  ⟨12969, .add 206 729 (-1, 4), some 0, none⟩,
  ⟨12970, .add 182 729 (1, 4), some 0, none⟩,
  ⟨12971, .add 183 729 (1, 4), some 0, none⟩,
  ⟨12972, .add 175 729 (-1, 4), some 0, none⟩,
  ⟨12973, .add 174 729 (-1, 4), some 0, none⟩,
  ⟨12974, .add 195 729 (1, 4), some 0, none⟩,
  ⟨12975, .add 185 729 (1, 4), some 0, none⟩,
  ⟨12976, .add 171 729 (1, 4), some 0, none⟩,
  ⟨12977, .add 142 729 (1, 4), some 0, none⟩,
  ⟨12978, .add 112 729 (1, 4), some 0, none⟩,
  ⟨12979, .add 188 729 (1, 4), some 0, none⟩,
  ⟨12980, .add 204 729 (-1, 4), some 0, none⟩,
  ⟨12981, .add 169 729 (-1, 4), some 0, none⟩,
  ⟨12982, .add 192 729 (1, 4), some 0, none⟩,
  ⟨12983, .add 179 729 (1, 4), some 0, none⟩,
  ⟨12984, .add 120 729 (1, 4), some 0, none⟩,
  ⟨12985, .add 207 729 (1, 4), some 0, none⟩,
  ⟨12986, .add 180 729 (1, 4), some 0, none⟩,
  ⟨12987, .add 117 729 (1, 4), some 0, none⟩,
  ⟨12988, .add 208 729 (1, 4), some 0, none⟩,
  ⟨12989, .add 176 729 (1, 4), some 0, none⟩,
  ⟨12990, .clear 729 0, some 0, none⟩,
  ⟨12991, .clear 730 431, some 431, none⟩,
  ⟨12992, .copy 730 227 431, some 431, none⟩,
  ⟨12993, .relabel 730 431 0, none, some (1383, 8)⟩,
  ⟨12994, .add 118 730 (1, 4), some 0, none⟩,
  ⟨12995, .add 194 730 (1, 4), some 0, none⟩,
  ⟨12996, .add 205 730 (-1, 4), some 0, none⟩,
  ⟨12997, .add 170 730 (-1, 4), some 0, none⟩,
  ⟨12998, .add 124 730 (1, 4), some 0, none⟩,
  ⟨12999, .add 212 730 (1, 4), some 0, none⟩,
  ⟨13000, .add 215 730 (-1, 4), some 0, none⟩,
  ⟨13001, .add 129 730 (-1, 4), some 0, none⟩,
  ⟨13002, .add 213 730 (1, 4), some 0, none⟩,
  ⟨13003, .add 166 730 (1, 4), some 0, none⟩,
  ⟨13004, .add 130 730 (-1, 4), some 0, none⟩,
  ⟨13005, .add 152 730 (-1, 4), some 0, none⟩,
  ⟨13006, .add 195 730 (1, 4), some 0, none⟩,
  ⟨13007, .add 185 730 (1, 4), some 0, none⟩,
  ⟨13008, .add 171 730 (-1, 4), some 0, none⟩,
  ⟨13009, .add 142 730 (-1, 4), some 0, none⟩,
  ⟨13010, .add 199 730 (1, 4), some 0, none⟩,
  ⟨13011, .add 139 730 (1, 4), some 0, none⟩,
  ⟨13012, .add 119 730 (1, 4), some 0, none⟩,
  ⟨13013, .add 193 730 (1, 4), some 0, none⟩,
  ⟨13014, .add 125 730 (1, 4), some 0, none⟩,
  ⟨13015, .add 190 730 (1, 4), some 0, none⟩,
  ⟨13016, .add 155 730 (1, 4), some 0, none⟩,
  ⟨13017, .add 128 730 (1, 4), some 0, none⟩,
  ⟨13018, .add 127 730 (1, 4), some 0, none⟩,
  ⟨13019, .add 126 730 (1, 4), some 0, none⟩,
  ⟨13020, .add 153 730 (1, 4), some 0, none⟩,
  ⟨13021, .add 154 730 (1, 4), some 0, none⟩,
  ⟨13022, .clear 730 0, some 0, none⟩,
  ⟨13023, .clear 731 432, some 432, none⟩,
  ⟨13024, .copy 731 225 432, some 432, none⟩,
  ⟨13025, .relabel 731 432 0, none, some (1385, 8)⟩,
  ⟨13026, .add 199 731 (-1, 4), some 0, none⟩,
  ⟨13027, .add 139 731 (1, 4), some 0, none⟩,
  ⟨13028, .add 119 731 (-1, 4), some 0, none⟩,
  ⟨13029, .add 193 731 (1, 4), some 0, none⟩,
  ⟨13030, .add 210 731 (1, 4), some 0, none⟩,
  ⟨13031, .add 160 731 (1, 4), some 0, none⟩,
  ⟨13032, .add 157 731 (-1, 4), some 0, none⟩,
  ⟨13033, .add 219 731 (-1, 4), some 0, none⟩,
  ⟨13034, .add 192 731 (1, 4), some 0, none⟩,
  ⟨13035, .add 179 731 (1, 4), some 0, none⟩,
  ⟨13036, .add 120 731 (-1, 4), some 0, none⟩,
  ⟨13037, .add 207 731 (-1, 4), some 0, none⟩,
  ⟨13038, .add 125 731 (1, 4), some 0, none⟩,
  ⟨13039, .add 190 731 (1, 4), some 0, none⟩,
  ⟨13040, .add 155 731 (-1, 4), some 0, none⟩,
  ⟨13041, .add 128 731 (-1, 4), some 0, none⟩,
  ⟨13042, .add 127 731 (1, 4), some 0, none⟩,
  ⟨13043, .add 126 731 (1, 4), some 0, none⟩,
  ⟨13044, .add 153 731 (-1, 4), some 0, none⟩,
  ⟨13045, .add 154 731 (-1, 4), some 0, none⟩,
  ⟨13046, .add 180 731 (1, 4), some 0, none⟩,
  ⟨13047, .add 117 731 (1, 4), some 0, none⟩,
  ⟨13048, .add 208 731 (-1, 4), some 0, none⟩,
  ⟨13049, .add 176 731 (-1, 4), some 0, none⟩,
  ⟨13050, .add 161 731 (1, 4), some 0, none⟩,
  ⟨13051, .add 146 731 (1, 4), some 0, none⟩,
  ⟨13052, .add 220 731 (-1, 4), some 0, none⟩,
  ⟨13053, .add 134 731 (-1, 4), some 0, none⟩,
  ⟨13054, .clear 731 0, some 0, none⟩,
  ⟨13055, .clear 732 433, some 433, none⟩,
  ⟨13056, .copy 732 243 433, some 433, none⟩,
  ⟨13057, .relabel 732 433 0, none, some (1387, 8)⟩,
  ⟨13058, .add 187 732 (1, 4), some 0, none⟩,
  ⟨13059, .add 113 732 (1, 4), some 0, none⟩,
  ⟨13060, .add 140 732 (1, 4), some 0, none⟩,
  ⟨13061, .add 198 732 (1, 4), some 0, none⟩,
  ⟨13062, .add 168 732 (1, 4), some 0, none⟩,
  ⟨13063, .add 143 732 (1, 4), some 0, none⟩,
  ⟨13064, .add 150 732 (1, 4), some 0, none⟩,
  ⟨13065, .add 189 732 (1, 4), some 0, none⟩,
  ⟨13066, .add 202 732 (1, 4), some 0, none⟩,
  ⟨13067, .add 203 732 (1, 4), some 0, none⟩,
  ⟨13068, .add 122 732 (1, 4), some 0, none⟩,
  ⟨13069, .add 123 732 (1, 4), some 0, none⟩,
  ⟨13070, .add 148 732 (1, 4), some 0, none⟩,
  ⟨13071, .add 133 732 (1, 4), some 0, none⟩,
  ⟨13072, .add 149 732 (1, 4), some 0, none⟩,
  ⟨13073, .add 132 732 (1, 4), some 0, none⟩,
  ⟨13074, .add 144 732 (1, 4), some 0, none⟩,
  ⟨13075, .add 197 732 (1, 4), some 0, none⟩,
  ⟨13076, .add 136 732 (1, 4), some 0, none⟩,
  ⟨13077, .add 147 732 (1, 4), some 0, none⟩,
  ⟨13078, .add 115 732 (1, 4), some 0, none⟩,
  ⟨13079, .add 200 732 (1, 4), some 0, none⟩,
  ⟨13080, .add 178 732 (1, 4), some 0, none⟩,
  ⟨13081, .add 138 732 (1, 4), some 0, none⟩,
  ⟨13082, .add 164 732 (1, 4), some 0, none⟩,
  ⟨13083, .add 165 732 (1, 4), some 0, none⟩,
  ⟨13084, .add 217 732 (1, 4), some 0, none⟩,
  ⟨13085, .add 218 732 (1, 4), some 0, none⟩,
  ⟨13086, .clear 732 0, some 0, none⟩,
  ⟨13087, .clear 733 434, some 434, none⟩,
  ⟨13088, .copy 733 241 434, some 434, none⟩,
  ⟨13089, .relabel 733 434 0, none, some (1389, 8)⟩,
  ⟨13090, .add 202 733 (-1, 4), some 0, none⟩,
  ⟨13091, .add 203 733 (1, 4), some 0, none⟩,
  ⟨13092, .add 122 733 (-1, 4), some 0, none⟩,
  ⟨13093, .add 123 733 (1, 4), some 0, none⟩,
  ⟨13094, .add 214 733 (1, 4), some 0, none⟩,
  ⟨13095, .add 167 733 (1, 4), some 0, none⟩,
  ⟨13096, .add 131 733 (1, 4), some 0, none⟩,
  ⟨13097, .add 151 733 (1, 4), some 0, none⟩,
  ⟨13098, .add 196 733 (1, 4), some 0, none⟩,
  ⟨13099, .add 186 733 (1, 4), some 0, none⟩,
  ⟨13100, .add 172 733 (1, 4), some 0, none⟩,
  ⟨13101, .add 141 733 (1, 4), some 0, none⟩,
  ⟨13102, .add 148 733 (1, 4), some 0, none⟩,
  ⟨13103, .add 133 733 (1, 4), some 0, none⟩,
  ⟨13104, .add 149 733 (-1, 4), some 0, none⟩,
  ⟨13105, .add 132 733 (-1, 4), some 0, none⟩,
  ⟨13106, .add 164 733 (-1, 4), some 0, none⟩,
  ⟨13107, .add 165 733 (1, 4), some 0, none⟩,
  ⟨13108, .add 217 733 (-1, 4), some 0, none⟩,
  ⟨13109, .add 218 733 (1, 4), some 0, none⟩,
  ⟨13110, .add 181 733 (1, 4), some 0, none⟩,
  ⟨13111, .add 116 733 (1, 4), some 0, none⟩,
  ⟨13112, .add 209 733 (1, 4), some 0, none⟩,
  ⟨13113, .add 177 733 (1, 4), some 0, none⟩,
  ⟨13114, .add 162 733 (1, 4), some 0, none⟩,
  ⟨13115, .add 145 733 (1, 4), some 0, none⟩,
  ⟨13116, .add 221 733 (1, 4), some 0, none⟩,
  ⟨13117, .add 135 733 (1, 4), some 0, none⟩,
  ⟨13118, .clear 733 0, some 0, none⟩,
  ⟨13119, .clear 734 435, some 435, none⟩,
  ⟨13120, .copy 734 259 435, some 435, none⟩,
  ⟨13121, .relabel 734 435 0, none, some (1391, 8)⟩,
  ⟨13122, .add 168 734 (-1, 4), some 0, none⟩,
  ⟨13123, .add 143 734 (1, 4), some 0, none⟩,
  ⟨13124, .add 150 734 (-1, 4), some 0, none⟩,
  ⟨13125, .add 189 734 (1, 4), some 0, none⟩,
  ⟨13126, .add 137 734 (1, 4), some 0, none⟩,
  ⟨13127, .add 201 734 (1, 4), some 0, none⟩,
  ⟨13128, .add 191 734 (1, 4), some 0, none⟩,
  ⟨13129, .add 121 734 (1, 4), some 0, none⟩,
  ⟨13130, .add 196 734 (-1, 4), some 0, none⟩,
  ⟨13131, .add 186 734 (1, 4), some 0, none⟩,
  ⟨13132, .add 172 734 (-1, 4), some 0, none⟩,
  ⟨13133, .add 141 734 (1, 4), some 0, none⟩,
  ⟨13134, .add 159 734 (1, 4), some 0, none⟩,
  ⟨13135, .add 223 734 (1, 4), some 0, none⟩,
  ⟨13136, .add 158 734 (1, 4), some 0, none⟩,
  ⟨13137, .add 222 734 (1, 4), some 0, none⟩,
  ⟨13138, .add 115 734 (-1, 4), some 0, none⟩,
  ⟨13139, .add 200 734 (1, 4), some 0, none⟩,
  ⟨13140, .add 178 734 (-1, 4), some 0, none⟩,
  ⟨13141, .add 138 734 (1, 4), some 0, none⟩,
  ⟨13142, .add 211 734 (1, 4), some 0, none⟩,
  ⟨13143, .add 163 734 (1, 4), some 0, none⟩,
  ⟨13144, .add 156 734 (1, 4), some 0, none⟩,
  ⟨13145, .add 216 734 (1, 4), some 0, none⟩,
  ⟨13146, .add 162 734 (-1, 4), some 0, none⟩,
  ⟨13147, .add 145 734 (1, 4), some 0, none⟩,
  ⟨13148, .add 221 734 (-1, 4), some 0, none⟩,
  ⟨13149, .add 135 734 (1, 4), some 0, none⟩,
  ⟨13150, .clear 734 0, some 0, none⟩,
  ⟨13151, .clear 735 436, some 436, none⟩,
  ⟨13152, .copy 735 257 436, some 436, none⟩,
  ⟨13153, .relabel 735 436 0, none, some (1393, 8)⟩,
  ⟨13154, .add 187 735 (-1, 4), some 0, none⟩,
  ⟨13155, .add 113 735 (1, 4), some 0, none⟩,
  ⟨13156, .add 140 735 (-1, 4), some 0, none⟩,
  ⟨13157, .add 198 735 (1, 4), some 0, none⟩,
  ⟨13158, .add 137 735 (-1, 4), some 0, none⟩,
  ⟨13159, .add 201 735 (1, 4), some 0, none⟩,
  ⟨13160, .add 191 735 (-1, 4), some 0, none⟩,
  ⟨13161, .add 121 735 (1, 4), some 0, none⟩,
  ⟨13162, .add 214 735 (-1, 4), some 0, none⟩,
  ⟨13163, .add 167 735 (1, 4), some 0, none⟩,
  ⟨13164, .add 131 735 (-1, 4), some 0, none⟩,
  ⟨13165, .add 151 735 (1, 4), some 0, none⟩,
  ⟨13166, .add 159 735 (-1, 4), some 0, none⟩,
  ⟨13167, .add 223 735 (1, 4), some 0, none⟩,
  ⟨13168, .add 158 735 (-1, 4), some 0, none⟩,
  ⟨13169, .add 222 735 (1, 4), some 0, none⟩,
  ⟨13170, .add 144 735 (-1, 4), some 0, none⟩,
  ⟨13171, .add 197 735 (1, 4), some 0, none⟩,
  ⟨13172, .add 136 735 (-1, 4), some 0, none⟩,
  ⟨13173, .add 147 735 (1, 4), some 0, none⟩,
  ⟨13174, .add 211 735 (-1, 4), some 0, none⟩,
  ⟨13175, .add 163 735 (1, 4), some 0, none⟩,
  ⟨13176, .add 156 735 (-1, 4), some 0, none⟩,
  ⟨13177, .add 216 735 (1, 4), some 0, none⟩,
  ⟨13178, .add 181 735 (-1, 4), some 0, none⟩,
  ⟨13179, .add 116 735 (1, 4), some 0, none⟩,
  ⟨13180, .add 209 735 (-1, 4), some 0, none⟩,
  ⟨13181, .add 177 735 (1, 4), some 0, none⟩,
  ⟨13182, .clear 735 0, some 0, none⟩
]

def backward : List (Row 1079) := [
  ⟨12927, .clear 728 0, some 0, none⟩,
  ⟨12928, .add 728 124 (1, 4), some 0, none⟩,
  ⟨12929, .add 728 212 (1, 4), some 0, none⟩,
  ⟨12930, .add 728 215 (1, 4), some 0, none⟩,
  ⟨12931, .add 728 129 (1, 4), some 0, none⟩,
  ⟨12932, .add 728 184 (1, 4), some 0, none⟩,
  ⟨12933, .add 728 114 (1, 4), some 0, none⟩,
  ⟨12934, .add 728 173 (1, 4), some 0, none⟩,
  ⟨12935, .add 728 206 (1, 4), some 0, none⟩,
  ⟨12936, .add 728 182 (1, 4), some 0, none⟩,
  ⟨12937, .add 728 183 (1, 4), some 0, none⟩,
  ⟨12938, .add 728 175 (1, 4), some 0, none⟩,
  ⟨12939, .add 728 174 (1, 4), some 0, none⟩,
  ⟨12940, .add 728 213 (1, 4), some 0, none⟩,
  ⟨12941, .add 728 166 (1, 4), some 0, none⟩,
  ⟨12942, .add 728 130 (1, 4), some 0, none⟩,
  ⟨12943, .add 728 152 (1, 4), some 0, none⟩,
  ⟨12944, .add 728 112 (1, 4), some 0, none⟩,
  ⟨12945, .add 728 188 (1, 4), some 0, none⟩,
  ⟨12946, .add 728 204 (1, 4), some 0, none⟩,
  ⟨12947, .add 728 169 (1, 4), some 0, none⟩,
  ⟨12948, .add 728 210 (1, 4), some 0, none⟩,
  ⟨12949, .add 728 160 (1, 4), some 0, none⟩,
  ⟨12950, .add 728 157 (1, 4), some 0, none⟩,
  ⟨12951, .add 728 219 (1, 4), some 0, none⟩,
  ⟨12952, .add 728 161 (1, 4), some 0, none⟩,
  ⟨12953, .add 728 146 (1, 4), some 0, none⟩,
  ⟨12954, .add 728 220 (1, 4), some 0, none⟩,
  ⟨12955, .add 728 134 (1, 4), some 0, none⟩,
  ⟨12956, .relabel 728 0 429, none, some (137, 8)⟩,
  ⟨12957, .add 229 728 (-1, 1), some 429, none⟩,
  ⟨12958, .clear 728 429, some 429, none⟩,
  ⟨12959, .clear 729 0, some 0, none⟩,
  ⟨12960, .add 729 118 (1, 4), some 0, none⟩,
  ⟨12961, .add 729 194 (1, 4), some 0, none⟩,
  ⟨12962, .add 729 205 (1, 4), some 0, none⟩,
  ⟨12963, .add 729 170 (1, 4), some 0, none⟩,
  ⟨12964, .add 729 184 (1, 4), some 0, none⟩,
  ⟨12965, .add 729 114 (1, 4), some 0, none⟩,
  ⟨12966, .add 729 173 (-1, 4), some 0, none⟩,
  ⟨12967, .add 729 206 (-1, 4), some 0, none⟩,
  ⟨12968, .add 729 182 (1, 4), some 0, none⟩,
  ⟨12969, .add 729 183 (1, 4), some 0, none⟩,
  ⟨12970, .add 729 175 (-1, 4), some 0, none⟩,
  ⟨12971, .add 729 174 (-1, 4), some 0, none⟩,
  ⟨12972, .add 729 195 (1, 4), some 0, none⟩,
  ⟨12973, .add 729 185 (1, 4), some 0, none⟩,
  ⟨12974, .add 729 171 (1, 4), some 0, none⟩,
  ⟨12975, .add 729 142 (1, 4), some 0, none⟩,
  ⟨12976, .add 729 112 (1, 4), some 0, none⟩,
  ⟨12977, .add 729 188 (1, 4), some 0, none⟩,
  ⟨12978, .add 729 204 (-1, 4), some 0, none⟩,
  ⟨12979, .add 729 169 (-1, 4), some 0, none⟩,
  ⟨12980, .add 729 192 (1, 4), some 0, none⟩,
  ⟨12981, .add 729 179 (1, 4), some 0, none⟩,
  ⟨12982, .add 729 120 (1, 4), some 0, none⟩,
  ⟨12983, .add 729 207 (1, 4), some 0, none⟩,
  ⟨12984, .add 729 180 (1, 4), some 0, none⟩,
  ⟨12985, .add 729 117 (1, 4), some 0, none⟩,
  ⟨12986, .add 729 208 (1, 4), some 0, none⟩,
  ⟨12987, .add 729 176 (1, 4), some 0, none⟩,
  ⟨12988, .relabel 729 0 430, none, some (138, 8)⟩,
  ⟨12989, .add 224 729 (-1, 1), some 430, none⟩,
  ⟨12990, .clear 729 430, some 430, none⟩,
  ⟨12991, .clear 730 0, some 0, none⟩,
  ⟨12992, .add 730 118 (1, 4), some 0, none⟩,
  ⟨12993, .add 730 194 (1, 4), some 0, none⟩,
  ⟨12994, .add 730 205 (-1, 4), some 0, none⟩,
  ⟨12995, .add 730 170 (-1, 4), some 0, none⟩,
  ⟨12996, .add 730 124 (1, 4), some 0, none⟩,
  ⟨12997, .add 730 212 (1, 4), some 0, none⟩,
  ⟨12998, .add 730 215 (-1, 4), some 0, none⟩,
  ⟨12999, .add 730 129 (-1, 4), some 0, none⟩,
  ⟨13000, .add 730 213 (1, 4), some 0, none⟩,
  ⟨13001, .add 730 166 (1, 4), some 0, none⟩,
  ⟨13002, .add 730 130 (-1, 4), some 0, none⟩,
  ⟨13003, .add 730 152 (-1, 4), some 0, none⟩,
  ⟨13004, .add 730 195 (1, 4), some 0, none⟩,
  ⟨13005, .add 730 185 (1, 4), some 0, none⟩,
  ⟨13006, .add 730 171 (-1, 4), some 0, none⟩,
  ⟨13007, .add 730 142 (-1, 4), some 0, none⟩,
  ⟨13008, .add 730 199 (1, 4), some 0, none⟩,
  ⟨13009, .add 730 139 (1, 4), some 0, none⟩,
  ⟨13010, .add 730 119 (1, 4), some 0, none⟩,
  ⟨13011, .add 730 193 (1, 4), some 0, none⟩,
  ⟨13012, .add 730 125 (1, 4), some 0, none⟩,
  ⟨13013, .add 730 190 (1, 4), some 0, none⟩,
  ⟨13014, .add 730 155 (1, 4), some 0, none⟩,
  ⟨13015, .add 730 128 (1, 4), some 0, none⟩,
  ⟨13016, .add 730 127 (1, 4), some 0, none⟩,
  ⟨13017, .add 730 126 (1, 4), some 0, none⟩,
  ⟨13018, .add 730 153 (1, 4), some 0, none⟩,
  ⟨13019, .add 730 154 (1, 4), some 0, none⟩,
  ⟨13020, .relabel 730 0 431, none, some (139, 8)⟩,
  ⟨13021, .add 227 730 (-1, 1), some 431, none⟩,
  ⟨13022, .clear 730 431, some 431, none⟩,
  ⟨13023, .clear 731 0, some 0, none⟩,
  ⟨13024, .add 731 199 (-1, 4), some 0, none⟩,
  ⟨13025, .add 731 139 (1, 4), some 0, none⟩,
  ⟨13026, .add 731 119 (-1, 4), some 0, none⟩,
  ⟨13027, .add 731 193 (1, 4), some 0, none⟩,
  ⟨13028, .add 731 210 (1, 4), some 0, none⟩,
  ⟨13029, .add 731 160 (1, 4), some 0, none⟩,
  ⟨13030, .add 731 157 (-1, 4), some 0, none⟩,
  ⟨13031, .add 731 219 (-1, 4), some 0, none⟩,
  ⟨13032, .add 731 192 (1, 4), some 0, none⟩,
  ⟨13033, .add 731 179 (1, 4), some 0, none⟩,
  ⟨13034, .add 731 120 (-1, 4), some 0, none⟩,
  ⟨13035, .add 731 207 (-1, 4), some 0, none⟩,
  ⟨13036, .add 731 125 (1, 4), some 0, none⟩,
  ⟨13037, .add 731 190 (1, 4), some 0, none⟩,
  ⟨13038, .add 731 155 (-1, 4), some 0, none⟩,
  ⟨13039, .add 731 128 (-1, 4), some 0, none⟩,
  ⟨13040, .add 731 127 (1, 4), some 0, none⟩,
  ⟨13041, .add 731 126 (1, 4), some 0, none⟩,
  ⟨13042, .add 731 153 (-1, 4), some 0, none⟩,
  ⟨13043, .add 731 154 (-1, 4), some 0, none⟩,
  ⟨13044, .add 731 180 (1, 4), some 0, none⟩,
  ⟨13045, .add 731 117 (1, 4), some 0, none⟩,
  ⟨13046, .add 731 208 (-1, 4), some 0, none⟩,
  ⟨13047, .add 731 176 (-1, 4), some 0, none⟩,
  ⟨13048, .add 731 161 (1, 4), some 0, none⟩,
  ⟨13049, .add 731 146 (1, 4), some 0, none⟩,
  ⟨13050, .add 731 220 (-1, 4), some 0, none⟩,
  ⟨13051, .add 731 134 (-1, 4), some 0, none⟩,
  ⟨13052, .relabel 731 0 432, none, some (140, 8)⟩,
  ⟨13053, .add 225 731 (-1, 1), some 432, none⟩,
  ⟨13054, .clear 731 432, some 432, none⟩,
  ⟨13055, .clear 732 0, some 0, none⟩,
  ⟨13056, .add 732 187 (1, 4), some 0, none⟩,
  ⟨13057, .add 732 113 (1, 4), some 0, none⟩,
  ⟨13058, .add 732 140 (1, 4), some 0, none⟩,
  ⟨13059, .add 732 198 (1, 4), some 0, none⟩,
  ⟨13060, .add 732 168 (1, 4), some 0, none⟩,
  ⟨13061, .add 732 143 (1, 4), some 0, none⟩,
  ⟨13062, .add 732 150 (1, 4), some 0, none⟩,
  ⟨13063, .add 732 189 (1, 4), some 0, none⟩,
  ⟨13064, .add 732 202 (1, 4), some 0, none⟩,
  ⟨13065, .add 732 203 (1, 4), some 0, none⟩,
  ⟨13066, .add 732 122 (1, 4), some 0, none⟩,
  ⟨13067, .add 732 123 (1, 4), some 0, none⟩,
  ⟨13068, .add 732 148 (1, 4), some 0, none⟩,
  ⟨13069, .add 732 133 (1, 4), some 0, none⟩,
  ⟨13070, .add 732 149 (1, 4), some 0, none⟩,
  ⟨13071, .add 732 132 (1, 4), some 0, none⟩,
  ⟨13072, .add 732 144 (1, 4), some 0, none⟩,
  ⟨13073, .add 732 197 (1, 4), some 0, none⟩,
  ⟨13074, .add 732 136 (1, 4), some 0, none⟩,
  ⟨13075, .add 732 147 (1, 4), some 0, none⟩,
  ⟨13076, .add 732 115 (1, 4), some 0, none⟩,
  ⟨13077, .add 732 200 (1, 4), some 0, none⟩,
  ⟨13078, .add 732 178 (1, 4), some 0, none⟩,
  ⟨13079, .add 732 138 (1, 4), some 0, none⟩,
  ⟨13080, .add 732 164 (1, 4), some 0, none⟩,
  ⟨13081, .add 732 165 (1, 4), some 0, none⟩,
  ⟨13082, .add 732 217 (1, 4), some 0, none⟩,
  ⟨13083, .add 732 218 (1, 4), some 0, none⟩,
  ⟨13084, .relabel 732 0 433, none, some (141, 8)⟩,
  ⟨13085, .add 243 732 (-1, 1), some 433, none⟩,
  ⟨13086, .clear 732 433, some 433, none⟩,
  ⟨13087, .clear 733 0, some 0, none⟩,
  ⟨13088, .add 733 202 (-1, 4), some 0, none⟩,
  ⟨13089, .add 733 203 (1, 4), some 0, none⟩,
  ⟨13090, .add 733 122 (-1, 4), some 0, none⟩,
  ⟨13091, .add 733 123 (1, 4), some 0, none⟩,
  ⟨13092, .add 733 214 (1, 4), some 0, none⟩,
  ⟨13093, .add 733 167 (1, 4), some 0, none⟩,
  ⟨13094, .add 733 131 (1, 4), some 0, none⟩,
  ⟨13095, .add 733 151 (1, 4), some 0, none⟩,
  ⟨13096, .add 733 196 (1, 4), some 0, none⟩,
  ⟨13097, .add 733 186 (1, 4), some 0, none⟩,
  ⟨13098, .add 733 172 (1, 4), some 0, none⟩,
  ⟨13099, .add 733 141 (1, 4), some 0, none⟩,
  ⟨13100, .add 733 148 (1, 4), some 0, none⟩,
  ⟨13101, .add 733 133 (1, 4), some 0, none⟩,
  ⟨13102, .add 733 149 (-1, 4), some 0, none⟩,
  ⟨13103, .add 733 132 (-1, 4), some 0, none⟩,
  ⟨13104, .add 733 164 (-1, 4), some 0, none⟩,
  ⟨13105, .add 733 165 (1, 4), some 0, none⟩,
  ⟨13106, .add 733 217 (-1, 4), some 0, none⟩,
  ⟨13107, .add 733 218 (1, 4), some 0, none⟩,
  ⟨13108, .add 733 181 (1, 4), some 0, none⟩,
  ⟨13109, .add 733 116 (1, 4), some 0, none⟩,
  ⟨13110, .add 733 209 (1, 4), some 0, none⟩,
  ⟨13111, .add 733 177 (1, 4), some 0, none⟩,
  ⟨13112, .add 733 162 (1, 4), some 0, none⟩,
  ⟨13113, .add 733 145 (1, 4), some 0, none⟩,
  ⟨13114, .add 733 221 (1, 4), some 0, none⟩,
  ⟨13115, .add 733 135 (1, 4), some 0, none⟩,
  ⟨13116, .relabel 733 0 434, none, some (142, 8)⟩,
  ⟨13117, .add 241 733 (-1, 1), some 434, none⟩,
  ⟨13118, .clear 733 434, some 434, none⟩,
  ⟨13119, .clear 734 0, some 0, none⟩,
  ⟨13120, .add 734 168 (-1, 4), some 0, none⟩,
  ⟨13121, .add 734 143 (1, 4), some 0, none⟩,
  ⟨13122, .add 734 150 (-1, 4), some 0, none⟩,
  ⟨13123, .add 734 189 (1, 4), some 0, none⟩,
  ⟨13124, .add 734 137 (1, 4), some 0, none⟩,
  ⟨13125, .add 734 201 (1, 4), some 0, none⟩,
  ⟨13126, .add 734 191 (1, 4), some 0, none⟩,
  ⟨13127, .add 734 121 (1, 4), some 0, none⟩,
  ⟨13128, .add 734 196 (-1, 4), some 0, none⟩,
  ⟨13129, .add 734 186 (1, 4), some 0, none⟩,
  ⟨13130, .add 734 172 (-1, 4), some 0, none⟩,
  ⟨13131, .add 734 141 (1, 4), some 0, none⟩,
  ⟨13132, .add 734 159 (1, 4), some 0, none⟩,
  ⟨13133, .add 734 223 (1, 4), some 0, none⟩,
  ⟨13134, .add 734 158 (1, 4), some 0, none⟩,
  ⟨13135, .add 734 222 (1, 4), some 0, none⟩,
  ⟨13136, .add 734 115 (-1, 4), some 0, none⟩,
  ⟨13137, .add 734 200 (1, 4), some 0, none⟩,
  ⟨13138, .add 734 178 (-1, 4), some 0, none⟩,
  ⟨13139, .add 734 138 (1, 4), some 0, none⟩,
  ⟨13140, .add 734 211 (1, 4), some 0, none⟩,
  ⟨13141, .add 734 163 (1, 4), some 0, none⟩,
  ⟨13142, .add 734 156 (1, 4), some 0, none⟩,
  ⟨13143, .add 734 216 (1, 4), some 0, none⟩,
  ⟨13144, .add 734 162 (-1, 4), some 0, none⟩,
  ⟨13145, .add 734 145 (1, 4), some 0, none⟩,
  ⟨13146, .add 734 221 (-1, 4), some 0, none⟩,
  ⟨13147, .add 734 135 (1, 4), some 0, none⟩,
  ⟨13148, .relabel 734 0 435, none, some (143, 8)⟩,
  ⟨13149, .add 259 734 (-1, 1), some 435, none⟩,
  ⟨13150, .clear 734 435, some 435, none⟩,
  ⟨13151, .clear 735 0, some 0, none⟩,
  ⟨13152, .add 735 187 (-1, 4), some 0, none⟩,
  ⟨13153, .add 735 113 (1, 4), some 0, none⟩,
  ⟨13154, .add 735 140 (-1, 4), some 0, none⟩,
  ⟨13155, .add 735 198 (1, 4), some 0, none⟩,
  ⟨13156, .add 735 137 (-1, 4), some 0, none⟩,
  ⟨13157, .add 735 201 (1, 4), some 0, none⟩,
  ⟨13158, .add 735 191 (-1, 4), some 0, none⟩,
  ⟨13159, .add 735 121 (1, 4), some 0, none⟩,
  ⟨13160, .add 735 214 (-1, 4), some 0, none⟩,
  ⟨13161, .add 735 167 (1, 4), some 0, none⟩,
  ⟨13162, .add 735 131 (-1, 4), some 0, none⟩,
  ⟨13163, .add 735 151 (1, 4), some 0, none⟩,
  ⟨13164, .add 735 159 (-1, 4), some 0, none⟩,
  ⟨13165, .add 735 223 (1, 4), some 0, none⟩,
  ⟨13166, .add 735 158 (-1, 4), some 0, none⟩,
  ⟨13167, .add 735 222 (1, 4), some 0, none⟩,
  ⟨13168, .add 735 144 (-1, 4), some 0, none⟩,
  ⟨13169, .add 735 197 (1, 4), some 0, none⟩,
  ⟨13170, .add 735 136 (-1, 4), some 0, none⟩,
  ⟨13171, .add 735 147 (1, 4), some 0, none⟩,
  ⟨13172, .add 735 211 (-1, 4), some 0, none⟩,
  ⟨13173, .add 735 163 (1, 4), some 0, none⟩,
  ⟨13174, .add 735 156 (-1, 4), some 0, none⟩,
  ⟨13175, .add 735 216 (1, 4), some 0, none⟩,
  ⟨13176, .add 735 181 (-1, 4), some 0, none⟩,
  ⟨13177, .add 735 116 (1, 4), some 0, none⟩,
  ⟨13178, .add 735 209 (-1, 4), some 0, none⟩,
  ⟨13179, .add 735 177 (1, 4), some 0, none⟩,
  ⟨13180, .relabel 735 0 436, none, some (144, 8)⟩,
  ⟨13181, .add 257 735 (-1, 1), some 436, none⟩,
  ⟨13182, .clear 735 436, some 436, none⟩
]

theorem forward_scalar_events :
    (projectRows forward).map F19SelectedCoverage.Row.event =
      (projectRows CurrentScalarCentreBand.forward).map F19SelectedCoverage.Row.event := by
  simp only [projectRows, List.map_map]
  rfl

theorem forward_run_eq {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h : Register → M) :
    rawRowsRun forward h = rawRowsRun CurrentScalarCentreBand.forward h :=
  raw_run_congr_events forward CurrentScalarCentreBand.forward forward_scalar_events h

theorem forward_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun forward h = some out ∧ rawRowsRun forward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) := by
  simpa only [forward_run_eq] using CurrentScalarCentreBand.forward_independent h h' hL

private theorem forward_denominators :
    forward.all (fun r => validDenominator r.event) = true := by decide +kernel

theorem forward_interpreted {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 1079), decodeRows forward = some es ∧
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

theorem backward_scalar_events :
    (projectRows backward).map F19SelectedCoverage.Row.event =
      (projectRows CurrentScalarCentreBand.backward).map F19SelectedCoverage.Row.event := by
  simp only [projectRows, List.map_map]
  rfl

theorem backward_run_eq {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h : Register → M) :
    rawRowsRun backward h = rawRowsRun CurrentScalarCentreBand.backward h :=
  raw_run_congr_events backward CurrentScalarCentreBand.backward backward_scalar_events h

theorem backward_independent {M : Type*} [AddCommMonoid M] [Module ℚ M]
    (h h' : Register → M) (hL : ∀ r, r.val < 728 → h r = h' r) :
    ∃ out out', rawRowsRun backward h = some out ∧ rawRowsRun backward h' = some out' ∧
      out = out' ∧ (∀ k : Fin 8, out (F19CentreBand.centre k) = 0) := by
  simpa only [backward_run_eq] using CurrentScalarCentreBand.backward_independent h h' hL

private theorem backward_denominators :
    backward.all (fun r => validDenominator r.event) = true := by decide +kernel

theorem backward_interpreted {M : Type*} [AddCommMonoid M] [Module ℚ M] :
    ∃ es : List (ScalarEvent 1079), decodeRows backward = some es ∧
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
    forward.map CanonicalFrameCoverage.Row.sourceIndex = List.range' 12927 256 ∧
    backward.map CanonicalFrameCoverage.Row.sourceIndex = List.range' 12927 256 := by
  constructor <;> decide +kernel

end CurrentMain.Current9594CKCentre

#print axioms CurrentMain.Current9594CKCentre.raw_run_congr_events
#print axioms CurrentMain.Current9594CKCentre.forward_scalar_events
#print axioms CurrentMain.Current9594CKCentre.backward_scalar_events
#print axioms CurrentMain.Current9594CKCentre.forward_run_eq
#print axioms CurrentMain.Current9594CKCentre.backward_run_eq
#print axioms CurrentMain.Current9594CKCentre.forward_independent
#print axioms CurrentMain.Current9594CKCentre.forward_interpreted
#print axioms CurrentMain.Current9594CKCentre.backward_independent
#print axioms CurrentMain.Current9594CKCentre.backward_interpreted
#print axioms CurrentMain.Current9594CKCentre.exact_source_indices
