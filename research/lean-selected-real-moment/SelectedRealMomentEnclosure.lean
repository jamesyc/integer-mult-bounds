import SelectedMomentExpEnclosure
import SelectedRoundedLogEnclosure

/-!
The selected finite real moment is bounded by the already checked rational
upper aggregate from PR531's direct-ASSEMBLY certificate. The nine source
weights and their order are preserved. Ordinary and fallback calls are
rounded independently; only then is the fallback discounted by10^-16.
This uses accepted real log/exp enclosures and exact source arithmetic.

Conditional source context: kappa = 1517760977820331/1000000000000000000
= 0.001517760977820331. The finite moment inequality is not an operator/profile
realization, initial saving supplier, perturbation theorem, all-size transfer
or complete multiplier/kappa theorem. Counts are the pinned supplied data.
Attribution: PR361's engine through PR531's assembly and the preceding exact
Lean certificate/enclosure modules. Prepared with OpenAI assistance.
-/
namespace CurrentMain.SelectedRealMomentEnclosure

open SelectedMomentUpperAggregate SelectedMomentExpEnclosure
open SelectedRoundedLogEnclosure
set_option Elab.async false

/-- The original rational nine-term expression, before its single ceiling. -/
private def ordinaryUnrounded : Rat :=
  ((((((((((0 : Rat) + (((1 * 146016 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 6 9 137))) + (((2 * 54144 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 5 9 137))) + (((3 * 13991 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 4 25 121))) + (((4 * 28224 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 4 9 137))) + (((5 * 7615 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 3 33 113))) + (((6 * 4032 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 3 25 121))) + (((7 * 1376 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 3 17 129))) + (((32 * 1 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 1 9 137))) + (((48 * 825 : Nat) : Rat) / ((73 * 7168 : Nat) : Rat) * expUpper (bMinus * roundedLog 0 25 121)))

private def fallbackUnrounded : Rat :=
  (fallbackCount : Rat) / ((73 * 7168 : Nat) : Rat) *
    expUpper (bMinus * roundedLog 6 9 137)

/-- The actual real exponential/logarithmic moment, in the original profile order. -/
private noncomputable def ordinaryRealMoment : ℝ :=
  (0 : ℝ) +
    (((1 * 146016 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log (73 : ℝ))) +
    (((2 * 54144 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 2))) +
    (((3 * 13991 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 3))) +
    (((4 * 28224 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 4))) +
    (((5 * 7615 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 5))) +
    (((6 * 4032 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 6))) +
    (((7 * 1376 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 7))) +
    (((32 * 1 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 32))) +
    (((48 * 825 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ) * Real.exp ((bMinus : ℝ) * Real.log ((73 : ℝ) / 48)))

private noncomputable def fallbackRealMoment : ℝ :=
  (fallbackCount : ℝ) / ((73 * 7168 : Nat) : ℝ) *
    Real.exp ((bMinus : ℝ) * Real.log 73)

/-- The selected real expression; the rank-one fallback has the exact10^-16 factor. -/
noncomputable def selectedRealMoment : ℝ :=
  ordinaryRealMoment + fallbackRealMoment / 10000000000000000

private theorem saving_nonnegative : (0 : ℝ) ≤ (bMinus : ℝ) := by
  norm_num [bMinus]

private theorem exp_from_log (x : ℝ) (q : Rat)
    (hl : x ≤ (q : ℝ))
    (he : Real.exp ((bMinus*q : Rat) : ℝ) ≤ (expUpper (bMinus*q) : ℝ)) :
    Real.exp ((bMinus : ℝ)*x) ≤ (expUpper (bMinus*q) : ℝ) := by
  have hm := mul_le_mul_of_nonneg_left hl saving_nonnegative
  refine (Real.exp_le_exp.mpr hm).trans ?_
  simpa only [Rat.cast_mul] using he

private theorem source_term_enclosures :
    Real.exp ((bMinus : ℝ) * (Real.log (73 : ℝ))) ≤ (expUpper (bMinus * roundedLog 6 9 137) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/2))) ≤ (expUpper (bMinus * roundedLog 5 9 137) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/3))) ≤ (expUpper (bMinus * roundedLog 4 25 121) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/4))) ≤ (expUpper (bMinus * roundedLog 4 9 137) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/5))) ≤ (expUpper (bMinus * roundedLog 3 33 113) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/6))) ≤ (expUpper (bMinus * roundedLog 3 25 121) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/7))) ≤ (expUpper (bMinus * roundedLog 3 17 129) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/32))) ≤ (expUpper (bMinus * roundedLog 1 9 137) : ℝ) ∧
    Real.exp ((bMinus : ℝ) * (Real.log ((73 : ℝ)/48))) ≤ (expUpper (bMinus * roundedLog 0 25 121) : ℝ) := by
  rcases selected_rounded_log_enclosures with ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩
  rcases selected_exp_enclosures with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩
  exact ⟨exp_from_log _ _ l1 e1,
    exp_from_log _ _ l2 e2,
    exp_from_log _ _ l3 e3,
    exp_from_log _ _ l4 e4,
    exp_from_log _ _ l5 e5,
    exp_from_log _ _ l6 e6,
    exp_from_log _ _ l7 e7,
    exp_from_log _ _ l8 e8,
    exp_from_log _ _ l9 e9⟩

private theorem ordinary_real_upper : ordinaryRealMoment ≤ (ordinaryRounded : ℝ) := by
  rcases source_term_enclosures with ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩
  have h1 := mul_le_mul_of_nonneg_left e1
    (by positivity : (0 : ℝ) ≤ (((1 * 146016 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h2 := mul_le_mul_of_nonneg_left e2
    (by positivity : (0 : ℝ) ≤ (((2 * 54144 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h3 := mul_le_mul_of_nonneg_left e3
    (by positivity : (0 : ℝ) ≤ (((3 * 13991 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h4 := mul_le_mul_of_nonneg_left e4
    (by positivity : (0 : ℝ) ≤ (((4 * 28224 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h5 := mul_le_mul_of_nonneg_left e5
    (by positivity : (0 : ℝ) ≤ (((5 * 7615 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h6 := mul_le_mul_of_nonneg_left e6
    (by positivity : (0 : ℝ) ≤ (((6 * 4032 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h7 := mul_le_mul_of_nonneg_left e7
    (by positivity : (0 : ℝ) ≤ (((7 * 1376 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h8 := mul_le_mul_of_nonneg_left e8
    (by positivity : (0 : ℝ) ≤ (((32 * 1 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have h9 := mul_le_mul_of_nonneg_left e9
    (by positivity : (0 : ℝ) ≤ (((48 * 825 : Nat) : ℝ) / ((73 * 7168 : Nat) : ℝ)))
  have hs : ordinaryRealMoment ≤ (ordinaryUnrounded : ℝ) := by
    unfold ordinaryRealMoment ordinaryUnrounded
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_zero]
    exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) h1) h2) h3) h4) h5) h6) h7) h8) h9)
  have hc : (ordinaryUnrounded : ℝ) ≤ (ordinaryRounded : ℝ) := by
    change (ordinaryUnrounded : ℝ) ≤ (ceilGrid ordinaryUnrounded : ℝ)
    exact_mod_cast (ceilGrid_outward ordinaryUnrounded)
  exact hs.trans hc

private theorem fallback_real_upper : fallbackRealMoment ≤ (fallbackRounded : ℝ) := by
  have h := mul_le_mul_of_nonneg_left source_term_enclosures.1
    (by positivity : (0 : ℝ) ≤ (fallbackCount : ℝ) / ((73*7168 : Nat) : ℝ))
  have hs : fallbackRealMoment ≤ (fallbackUnrounded : ℝ) := by
    simpa only [fallbackRealMoment, fallbackUnrounded, Rat.cast_mul,
      Rat.cast_div, Rat.cast_natCast] using h
  have hc : (fallbackUnrounded : ℝ) ≤ (fallbackRounded : ℝ) := by
    change (fallbackUnrounded : ℝ) ≤ (ceilGrid fallbackUnrounded : ℝ)
    exact_mod_cast (ceilGrid_outward fallbackUnrounded)
  exact hs.trans hc

/-- The separate source ceilings give a certified upper bound on the real expression. -/
theorem selectedRealMoment_le_upper : selectedRealMoment ≤ (selectedUpper : ℝ) := by
  unfold selectedRealMoment selectedUpper
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  exact add_le_add ordinary_real_upper
    (div_le_div_of_nonneg_right fallback_real_upper (by norm_num))

/-- The selected finite real moment is strictly below1 at the supplied bMinus. -/
theorem selectedRealMoment_strict : selectedRealMoment < 1 := by
  refine selectedRealMoment_le_upper.trans_lt ?_
  exact_mod_cast upper_aggregate_strict

#print axioms selectedRealMoment_le_upper
#print axioms selectedRealMoment_strict
end CurrentMain.SelectedRealMomentEnclosure
