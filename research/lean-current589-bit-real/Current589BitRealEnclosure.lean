import Current589BitUpperAggregate
import SelectedMomentExpEnclosure
import SelectedRoundedLogEnclosure
import CurrentBitLogRealEnclosure
import Current543LogRealEnclosure

/-!
Current PR589 bit Real moment as loaded by selected PR799 mainf567884.
The eight whole weight-times-exponential terms retain exact source order,
dimension64, live28416 and the current supplied bit saving. The dimension64
binary domain permits its reduced unit to equal2. Accepted Real units and the
generic exp enclosure feed two independent outward ceilings: ordinary first,
rank-one fallback separately, followed by the exact10^-16 fallback factor.

Author-checked conditional current source context:
kappa=1661634653669567/1000000000000000000=0.001661634653669567.
The native complex no-fallback convention is not used for this bit branch.
Bit supplier/profile/operator realization, recurrence saving interpretation,
bootstrap/outer interpretation and physical/all-size selected-kappa transfer
remain separate. No new numeric checkpoint is re-proved in this bridge.
Attribution: cited PR589 supplier, PR799 assembler, inherited PR361 engine,
accepted rational/Real certificates and Mathlib. OpenAI-assisted preparation.
-/
namespace CurrentMain.Current589BitRealEnclosure
open Current589BitUpperAggregate SelectedMomentUpperAggregate SelectedMomentExpEnclosure
open SelectedMomentLogCheckpoints SelectedMomentLogUnitEnclosure
open SelectedRoundedLogEnclosure CurrentBitLogRealEnclosure Current543LogRealEnclosure
set_option Elab.async false

private theorem rounded_from_domain (rank count k n d : Nat)
    (hd : bitLogDomain rank count k n d)
    (hu : Real.log (((d+n : Nat) : ℝ) / ((d-n : Nat) : ℝ)) ≤
      (unitUpper n d : ℝ)) :
    Real.log ((64 : ℝ)/(rank : ℝ)) ≤ (roundedLog k n d : ℝ) := by
  rcases hd with ⟨hr, _, _, he, hlo, _⟩
  have hp : (0 : ℝ) < ((2^k : Nat) : ℝ) := by
    exact_mod_cast Nat.two_pow_pos k
  have hq : (0 : ℝ) < ((d+n : Nat) : ℝ) / ((d-n : Nat) : ℝ) := by
    have hh : (1 : ℝ) < ((d+n : Nat) : ℝ) / ((d-n : Nat) : ℝ) := by
      have hc : ((1 : Rat) : ℝ) <
          ((((d+n : Nat) : Rat) / ((d-n : Nat) : Rat)) : ℝ) := by
        exact_mod_cast hlo
      simpa only [Rat.cast_one, Rat.cast_div, Rat.cast_natCast] using hc
    linarith
  have heR : (64 : ℝ)/(rank : ℝ)/((2^k : Nat) : ℝ) =
      ((d+n : Nat) : ℝ)/((d-n : Nat) : ℝ) := by
    have hc := congrArg (fun q : Rat => (q : ℝ)) he
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hc
  have hx := (div_eq_iff (ne_of_gt hp)).mp heR
  have htw := mul_le_mul_of_nonneg_left log_two_upper
    (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))
  have hout := ceilGrid_outward (unitUpper n d + (k : Rat) * unitUpper 1 3)
  have hcast : ((unitUpper n d + (k : Rat) * unitUpper 1 3 : Rat) : ℝ) ≤
      (ceilGrid (unitUpper n d + (k : Rat) * unitUpper 1 3) : ℝ) := by
    exact_mod_cast hout
  have hrounded : (unitUpper n d : ℝ) + (k : ℝ) * (unitUpper 1 3 : ℝ) ≤
      (roundedLog k n d : ℝ) := by
    simpa only [roundedLog, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] using hcast
  calc
    Real.log ((64 : ℝ)/(rank : ℝ)) =
        Real.log (((d+n : Nat) : ℝ)/((d-n : Nat) : ℝ)) +
          (k : ℝ) * Real.log 2 := by
      rw [hx, Real.log_mul (ne_of_gt hq) (ne_of_gt hp)]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    _ ≤ (unitUpper n d : ℝ) + (k : ℝ) * (unitUpper 1 3 : ℝ) :=
      add_le_add hu htw
    _ ≤ (roundedLog k n d : ℝ) := hrounded

/-- Eight actual bit logarithms, rounded outward once after binary reduction. -/
theorem current_rounded_log_enclosures :
    Real.log ((64 : ℝ)/1) ≤ (roundedLog 5 1 3 : ℝ) ∧
    Real.log ((64 : ℝ)/2) ≤ (roundedLog 4 1 3 : ℝ) ∧
    Real.log ((64 : ℝ)/3) ≤ (roundedLog 4 1 7 : ℝ) ∧
    Real.log ((64 : ℝ)/4) ≤ (roundedLog 3 1 3 : ℝ) ∧
    Real.log ((64 : ℝ)/5) ≤ (roundedLog 3 3 13 : ℝ) ∧
    Real.log ((64 : ℝ)/6) ≤ (roundedLog 3 1 7 : ℝ) ∧
    Real.log ((64 : ℝ)/7) ≤ (roundedLog 3 1 15 : ℝ) ∧
    Real.log ((64 : ℝ)/42) ≤ (roundedLog 0 11 53 : ℝ) := by
  have hu1_3 : Real.log (((3+1 : Nat) : ℝ)/((3-1 : Nat) : ℝ)) ≤
      (unitUpper 1 3 : ℝ) := by
    convert log_two_upper using 1 <;> norm_num
  have hu1_7 : Real.log (((7+1 : Nat) : ℝ)/((7-1 : Nat) : ℝ)) ≤
      (unitUpper 1 7 : ℝ) := by
    convert log_four_thirds_upper using 1 <;> norm_num
  have hu1_15 : Real.log (((15+1 : Nat) : ℝ)/((15-1 : Nat) : ℝ)) ≤
      (unitUpper 1 15 : ℝ) := by
    convert log_eight_sevenths_upper using 1 <;> norm_num
  have hu3_13 : Real.log (((13+3 : Nat) : ℝ)/((13-3 : Nat) : ℝ)) ≤
      (unitUpper 3 13 : ℝ) := by
    convert log_eight_fifths_upper using 1 <;> norm_num
  have hu11_53 : Real.log (((53+11 : Nat) : ℝ)/((53-11 : Nat) : ℝ)) ≤
      (unitUpper 11 53 : ℝ) := by
    convert log_thirty_two_twenty_one_upper using 1 <;> norm_num
  rcases current_domains with ⟨h1, h2, h3, h4, h5, h6, h7, h8, _⟩
  exact ⟨(by simpa only [Nat.cast_one] using (rounded_from_domain 1 381024 5 1 3 h1 hu1_3)),
    rounded_from_domain 2 400416 4 1 3 h2 hu1_3,
    rounded_from_domain 3 22752 4 1 7 h3 hu1_7,
    rounded_from_domain 4 26880 3 1 3 h4 hu1_3,
    rounded_from_domain 5 29376 3 3 13 h5 hu3_13,
    rounded_from_domain 6 17376 3 1 7 h6 hu1_7,
    rounded_from_domain 7 26784 3 1 15 h7 hu1_15,
    rounded_from_domain 42 288 0 11 53 h8 hu11_53⟩

/-- Exact ordinary rational body before its source ceiling. -/
private def ordinaryUnrounded : Rat :=
  (((((((((0 : Rat) + (((1 * 381024 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 5 1 3))) + (((2 * 400416 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 4 1 3))) + (((3 * 22752 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 4 1 7))) + (((4 * 26880 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 1 3))) + (((5 * 29376 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 3 13))) + (((6 * 17376 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 1 7))) + (((7 * 26784 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 1 15))) + (((42 * 288 : Nat) : Rat) / ((64 * 28416 : Nat) : Rat) * expUpper (bCurrent * roundedLog 0 11 53)))

private def fallbackUnrounded : Rat :=
  (currentFallbackCount : Rat) / ((64*28416 : Nat) : Rat) *
    expUpper (bCurrent * roundedLog 5 1 3)

private noncomputable def ordinaryRealMoment : ℝ :=
  (0 : ℝ) +
    (((1 * 381024 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/1)))) +
    (((2 * 400416 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/2)))) +
    (((3 * 22752 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/3)))) +
    (((4 * 26880 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/4)))) +
    (((5 * 29376 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/5)))) +
    (((6 * 17376 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/6)))) +
    (((7 * 26784 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/7)))) +
    (((42 * 288 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/42))))

private noncomputable def fallbackRealMoment : ℝ :=
  (currentFallbackCount : ℝ) / ((64*28416 : Nat) : ℝ) *
    Real.exp ((bCurrent : ℝ) * Real.log ((64 : ℝ)/1))

/-- Actual bit expression, with its independently enclosed rank-one fallback. -/
noncomputable def currentRealMoment : ℝ :=
  ordinaryRealMoment + fallbackRealMoment / 10000000000000000

private theorem saving_nonnegative : (0 : ℝ) ≤ (bCurrent : ℝ) := by
  norm_num [bCurrent]

private theorem exp_from_log (x : ℝ) (q : Rat)
    (hl : x ≤ (q : ℝ))
    (he : Real.exp ((bCurrent*q : Rat) : ℝ) ≤ (expUpper (bCurrent*q) : ℝ)) :
    Real.exp ((bCurrent : ℝ)*x) ≤ (expUpper (bCurrent*q) : ℝ) := by
  have hm := mul_le_mul_of_nonneg_left hl saving_nonnegative
  refine (Real.exp_le_exp.mpr hm).trans ?_
  simpa only [Rat.cast_mul] using he

private theorem source_term_enclosures :
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/1))) ≤ (expUpper (bCurrent * roundedLog 5 1 3) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/2))) ≤ (expUpper (bCurrent * roundedLog 4 1 3) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/3))) ≤ (expUpper (bCurrent * roundedLog 4 1 7) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/4))) ≤ (expUpper (bCurrent * roundedLog 3 1 3) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/5))) ≤ (expUpper (bCurrent * roundedLog 3 3 13) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/6))) ≤ (expUpper (bCurrent * roundedLog 3 1 7) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/7))) ≤ (expUpper (bCurrent * roundedLog 3 1 15) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((64 : ℝ)/42))) ≤ (expUpper (bCurrent * roundedLog 0 11 53) : ℝ) := by
  rcases current_rounded_log_enclosures with ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩
  rcases current_domains with ⟨_, _, _, _, _, _, _, _, d1, d2, d3, d4, d5, d6, d7, d8⟩
  have e1 := expUpper_real_enclosure _ d1.1 d1.2
  have e2 := expUpper_real_enclosure _ d2.1 d2.2
  have e3 := expUpper_real_enclosure _ d3.1 d3.2
  have e4 := expUpper_real_enclosure _ d4.1 d4.2
  have e5 := expUpper_real_enclosure _ d5.1 d5.2
  have e6 := expUpper_real_enclosure _ d6.1 d6.2
  have e7 := expUpper_real_enclosure _ d7.1 d7.2
  have e8 := expUpper_real_enclosure _ d8.1 d8.2
  exact ⟨exp_from_log _ _ l1 e1,
    exp_from_log _ _ l2 e2,
    exp_from_log _ _ l3 e3,
    exp_from_log _ _ l4 e4,
    exp_from_log _ _ l5 e5,
    exp_from_log _ _ l6 e6,
    exp_from_log _ _ l7 e7,
    exp_from_log _ _ l8 e8⟩

private theorem ordinary_real_upper : ordinaryRealMoment ≤ (currentOrdinaryRounded : ℝ) := by
  rcases source_term_enclosures with ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩
  have h1 := mul_le_mul_of_nonneg_left e1
    (by positivity : (0 : ℝ) ≤ (((1 * 381024 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left e2
    (by positivity : (0 : ℝ) ≤ (((2 * 400416 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h3 := mul_le_mul_of_nonneg_left e3
    (by positivity : (0 : ℝ) ≤ (((3 * 22752 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h4 := mul_le_mul_of_nonneg_left e4
    (by positivity : (0 : ℝ) ≤ (((4 * 26880 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h5 := mul_le_mul_of_nonneg_left e5
    (by positivity : (0 : ℝ) ≤ (((5 * 29376 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h6 := mul_le_mul_of_nonneg_left e6
    (by positivity : (0 : ℝ) ≤ (((6 * 17376 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h7 := mul_le_mul_of_nonneg_left e7
    (by positivity : (0 : ℝ) ≤ (((7 * 26784 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have h8 := mul_le_mul_of_nonneg_left e8
    (by positivity : (0 : ℝ) ≤ (((42 * 288 : Nat) : ℝ) / ((64 * 28416 : Nat) : ℝ)))
  have hs : ordinaryRealMoment ≤ (ordinaryUnrounded : ℝ) := by
    unfold ordinaryRealMoment ordinaryUnrounded
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_zero]
    exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) h1) h2) h3) h4) h5) h6) h7) h8)
  have hc : (ordinaryUnrounded : ℝ) ≤ (currentOrdinaryRounded : ℝ) := by
    change (ordinaryUnrounded : ℝ) ≤ (ceilGrid ordinaryUnrounded : ℝ)
    exact_mod_cast (ceilGrid_outward ordinaryUnrounded)
  exact hs.trans hc

private theorem fallback_real_upper : fallbackRealMoment ≤ (currentFallbackRounded : ℝ) := by
  have h := mul_le_mul_of_nonneg_left source_term_enclosures.1
    (by positivity : (0 : ℝ) ≤ (currentFallbackCount : ℝ) / ((64*28416 : Nat) : ℝ))
  have hs : fallbackRealMoment ≤ (fallbackUnrounded : ℝ) := by
    simpa only [fallbackRealMoment, fallbackUnrounded, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast] using h
  have hc : (fallbackUnrounded : ℝ) ≤ (currentFallbackRounded : ℝ) := by
    change (fallbackUnrounded : ℝ) ≤ (ceilGrid fallbackUnrounded : ℝ)
    exact_mod_cast (ceilGrid_outward fallbackUnrounded)
  exact hs.trans hc

/-- The separate source ceilings give a certified upper bound on the real expression. -/
theorem currentRealMoment_le_upper : currentRealMoment ≤ (currentUpper : ℝ) := by
  unfold currentRealMoment currentUpper
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  exact add_le_add ordinary_real_upper
    (div_le_div_of_nonneg_right fallback_real_upper (by norm_num))

/-- The selected finite real moment is strictly below1 at the supplied current bit saving. -/
theorem currentRealMoment_strict : currentRealMoment < 1 := by
  refine currentRealMoment_le_upper.trans_lt ?_
  exact_mod_cast current_upper_strict

#print axioms current_rounded_log_enclosures
#print axioms currentRealMoment_le_upper
#print axioms currentRealMoment_strict
end CurrentMain.Current589BitRealEnclosure
