import CurrentComplexUpperAggregate
import SelectedMomentExpEnclosure
import SelectedRoundedLogEnclosure

/-!
Current PR535 finite complex Real moment at the pinned 7dfa22b assembly input.
The nine whole weighted exponentials follow the exact supplied profile order.
Eight rounded-log facts are reused and the new rank-eight binary identity is
proved explicitly. The generic accepted exponential bound applies at the new
bCurrent; ordinary and fallback ceilings remain separate before10^-16 scaling.

Author-checked conditional source kappa = 1584931111785787/1000000000000000000
= 0.001584931111785787. This finite inequality does not establish profile or
operator realization, PR510's bit moment, initial saving validity, bootstrap
interpretation, outer transfer or an all-size multiplier/kappa theorem.
Attribution: PR535 assemble_combined.py, PR361 base_two_moment.py, and the
accepted rational/log/exp certificate modules. Prepared with OpenAI assistance.
-/
namespace CurrentMain.CurrentComplexRealEnclosure

open CurrentComplexUpperAggregate SelectedMomentUpperAggregate SelectedMomentExpEnclosure
open SelectedMomentLogCheckpoints SelectedMomentLogUnitEnclosure
open SelectedRoundedLogEnclosure
set_option Elab.async false

theorem log_rank8_upper :
    Real.log ((73 : ℝ)/8) ≤ (roundedLog 3 9 137 : ℝ) := by
  have h2 := mul_le_mul_of_nonneg_left log_two_upper
    (by norm_num : (0 : ℝ) ≤ 3)
  have hs := add_le_add log_73_64_upper h2
  have he : Real.log ((73 : ℝ)/8) =
      Real.log ((73 : ℝ)/64) + 3*Real.log 2 := by
    rw [show (73 : ℝ)/8 = ((73 : ℝ)/64)*(2:ℝ)^3 by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num)]
    rw [Real.log_pow]
    norm_num
  have hc : ((unitUpper 9 137 + (3:Rat)*unitUpper 1 3 : Rat):ℝ) ≤
      (roundedLog 3 9 137 : ℝ) := by
    change ((unitUpper 9 137 + (3:Rat)*unitUpper 1 3 : Rat):ℝ) ≤
      (ceilGrid (unitUpper 9 137 + (3:Rat)*unitUpper 1 3):ℝ)
    exact_mod_cast (ceilGrid_outward (unitUpper 9 137 + (3:Rat)*unitUpper 1 3))
  calc
    Real.log ((73:ℝ)/8) = Real.log ((73:ℝ)/64) + 3*Real.log 2 := he
    _ ≤ ((unitUpper 9 137 + (3:Rat)*unitUpper 1 3 : Rat):ℝ) := by
      simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat] using hs
    _ ≤ (roundedLog 3 9 137 : ℝ) := hc


/-- The original rational nine-term expression, before its single ceiling. -/
private def ordinaryUnrounded : Rat :=
  ((((((((((0 : Rat) + (((1 * 158976 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 6 9 137))) + (((2 * 52864 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 5 9 137))) + (((3 * 15200 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 4 25 121))) + (((4 * 20160 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 4 9 137))) + (((5 * 4032 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 33 113))) + (((6 * 4032 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 25 121))) + (((7 * 352 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 17 129))) + (((8 * 576 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 3 9 137))) + (((48 * 1632 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bCurrent * roundedLog 0 25 121)))

private def fallbackUnrounded : Rat :=
  (currentFallbackCount : Rat) / ((73 * 7168 : Nat) : Rat) *
    expUpper (bCurrent * roundedLog 6 9 137)

/-- The actual real exponential/logarithmic moment, in the original profile order. -/
private noncomputable def ordinaryRealMoment : ℝ :=
  (0 : ℝ) +
    (((1 * 158976 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log (73 : ℝ))) +
    (((2 * 52864 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 2))) +
    (((3 * 15200 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 3))) +
    (((4 * 20160 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 4))) +
    (((5 * 4032 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 5))) +
    (((6 * 4032 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 6))) +
    (((7 * 352 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 7))) +
    (((8 * 576 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 8))) +
    (((48 * 1632 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bCurrent : ℝ) * Real.log ((73 : ℝ) / 48)))

private noncomputable def fallbackRealMoment : ℝ :=
  (currentFallbackCount : ℝ) / ((73 * 7168 : Nat) : ℝ) *
    Real.exp ((bCurrent : ℝ) * Real.log 73)

/-- The selected real expression; the rank-one fallback has the exact10^-16 factor. -/
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
    Real.exp ((bCurrent : ℝ) * (Real.log (73 : ℝ))) ≤ (expUpper (bCurrent * roundedLog 6 9 137) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/2))) ≤ (expUpper (bCurrent * roundedLog 5 9 137) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/3))) ≤ (expUpper (bCurrent * roundedLog 4 25 121) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/4))) ≤ (expUpper (bCurrent * roundedLog 4 9 137) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/5))) ≤ (expUpper (bCurrent * roundedLog 3 33 113) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/6))) ≤ (expUpper (bCurrent * roundedLog 3 25 121) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/7))) ≤ (expUpper (bCurrent * roundedLog 3 17 129) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/8))) ≤ (expUpper (bCurrent * roundedLog 3 9 137) : ℝ) ∧
    Real.exp ((bCurrent : ℝ) * (Real.log ((73 : ℝ)/48))) ≤ (expUpper (bCurrent * roundedLog 0 25 121) : ℝ) := by
  rcases selected_rounded_log_enclosures with ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩
  rcases current_domains with ⟨_, _, _, _, _, _, _, _, _, d1, d2, d3, d4, d5, d6, d7, d8, d9⟩
  have e1 := expUpper_real_enclosure _ d1.1 d1.2
  have e2 := expUpper_real_enclosure _ d2.1 d2.2
  have e3 := expUpper_real_enclosure _ d3.1 d3.2
  have e4 := expUpper_real_enclosure _ d4.1 d4.2
  have e5 := expUpper_real_enclosure _ d5.1 d5.2
  have e6 := expUpper_real_enclosure _ d6.1 d6.2
  have e7 := expUpper_real_enclosure _ d7.1 d7.2
  have e8 := expUpper_real_enclosure _ d8.1 d8.2
  have e9 := expUpper_real_enclosure _ d9.1 d9.2
  exact ⟨exp_from_log _ _ l1 e1,
    exp_from_log _ _ l2 e2,
    exp_from_log _ _ l3 e3,
    exp_from_log _ _ l4 e4,
    exp_from_log _ _ l5 e5,
    exp_from_log _ _ l6 e6,
    exp_from_log _ _ l7 e7,
    exp_from_log _ _ log_rank8_upper e8,
    exp_from_log _ _ l9 e9⟩

private theorem ordinary_real_upper : ordinaryRealMoment ≤ (currentOrdinaryRounded : ℝ) := by
  rcases source_term_enclosures with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩
  have h1 := mul_le_mul_of_nonneg_left e1
    (by positivity : (0 : ℝ) ≤ (((1 * 158976 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left e2
    (by positivity : (0 : ℝ) ≤ (((2 * 52864 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h3 := mul_le_mul_of_nonneg_left e3
    (by positivity : (0 : ℝ) ≤ (((3 * 15200 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h4 := mul_le_mul_of_nonneg_left e4
    (by positivity : (0 : ℝ) ≤ (((4 * 20160 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h5 := mul_le_mul_of_nonneg_left e5
    (by positivity : (0 : ℝ) ≤ (((5 * 4032 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h6 := mul_le_mul_of_nonneg_left e6
    (by positivity : (0 : ℝ) ≤ (((6 * 4032 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h7 := mul_le_mul_of_nonneg_left e7
    (by positivity : (0 : ℝ) ≤ (((7 * 352 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h8 := mul_le_mul_of_nonneg_left e8
    (by positivity : (0 : ℝ) ≤ (((8 * 576 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h9 := mul_le_mul_of_nonneg_left e9
    (by positivity : (0 : ℝ) ≤ (((48 * 1632 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have hs : ordinaryRealMoment ≤ (ordinaryUnrounded : ℝ) := by
    unfold ordinaryRealMoment ordinaryUnrounded
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_zero]
    exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) h1) h2) h3) h4) h5) h6) h7) h8) h9)
  have hc : (ordinaryUnrounded : ℝ) ≤ (currentOrdinaryRounded : ℝ) := by
    change (ordinaryUnrounded : ℝ) ≤ (ceilGrid ordinaryUnrounded : ℝ)
    exact_mod_cast (ceilGrid_outward ordinaryUnrounded)
  exact hs.trans hc

private theorem fallback_real_upper : fallbackRealMoment ≤ (currentFallbackRounded : ℝ) := by
  have h := mul_le_mul_of_nonneg_left source_term_enclosures.1
    (by positivity : (0 : ℝ) ≤ (currentFallbackCount : ℝ) / ((73*7168 : Nat) : ℝ))
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

/-- The selected finite real moment is strictly below1 at the supplied bCurrent. -/
theorem currentRealMoment_strict : currentRealMoment < 1 := by
  refine currentRealMoment_le_upper.trans_lt ?_
  exact_mod_cast current_upper_strict

#print axioms log_rank8_upper
#print axioms currentRealMoment_le_upper
#print axioms currentRealMoment_strict
end CurrentMain.CurrentComplexRealEnclosure
