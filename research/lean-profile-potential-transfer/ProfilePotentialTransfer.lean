import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
A source-independent bridge from a finite normalized exponential moment to
strict contraction of a homogeneous logarithmic potential at every positive scale.
This does not supply an algorithmic recurrence or integer-child rounding rule.
Apache-2.0; prepared with OpenAI assistance.
-/
set_option Elab.async false
namespace CurrentMain.ProfilePotentialTransfer
open scoped BigOperators

noncomputable def logPotential (b t : ℝ) : ℝ :=
  Real.exp ((1 - b) * Real.log t)

/-- Positive scaling separates the exact moment coefficient. -/
theorem logPotential_scale (b q t : ℝ) (hq : 0 < q) (ht : 0 < t) :
    logPotential b (q * t) =
      q * Real.exp (b * Real.log (1 / q)) * logPotential b t := by
  unfold logPotential
  rw [Real.log_mul hq.ne' ht.ne']
  have h : (1 - b) * (Real.log q + Real.log t) =
      Real.log q + b * Real.log (1 / q) + (1 - b) * Real.log t := by
    rw [Real.log_div one_ne_zero hq.ne', Real.log_one]
    ring
  rw [h, Real.exp_add, Real.exp_add, Real.exp_log hq]

/-- The finite weighted child potential factors through its exact moment. -/
theorem weighted_logPotential_factorization {ι : Type*} (s : Finset ι)
    (c q : ι → ℝ) (b t : ℝ) (hq : ∀ i ∈ s, 0 < q i) (ht : 0 < t) :
    (∑ i ∈ s, c i * logPotential b (q i * t)) =
      (∑ i ∈ s, c i * q i * Real.exp (b * Real.log (1 / q i))) *
        logPotential b t := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [logPotential_scale b (q i) t (hq i hi) ht]
  ring

/-- A strict normalized moment bound gives contraction at every positive scale. -/
theorem normalized_moment_strict_contraction {ι : Type*} (s : Finset ι)
    (c q : ι → ℝ) (b L t : ℝ) (hq : ∀ i ∈ s, 0 < q i)
    (hL : 0 < L) (ht : 0 < t)
    (hMoment : (∑ i ∈ s, (c i * q i / L) *
      Real.exp (b * Real.log (1 / q i))) < 1) :
    (∑ i ∈ s, c i * logPotential b (q i * t)) < L * logPotential b t := by
  have hnorm : (∑ i ∈ s, c i * q i *
      Real.exp (b * Real.log (1 / q i))) / L =
      ∑ i ∈ s, (c i * q i / L) * Real.exp (b * Real.log (1 / q i)) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcoef : (∑ i ∈ s, c i * q i * Real.exp (b * Real.log (1 / q i))) < L :=
    (div_lt_one hL).mp (by rw [hnorm]; exact hMoment)
  rw [weighted_logPotential_factorization s c q b t hq ht]
  exact mul_lt_mul_of_pos_right hcoef (Real.exp_pos _)

end CurrentMain.ProfilePotentialTransfer

#print axioms CurrentMain.ProfilePotentialTransfer.logPotential_scale
#print axioms CurrentMain.ProfilePotentialTransfer.weighted_logPotential_factorization
#print axioms CurrentMain.ProfilePotentialTransfer.normalized_moment_strict_contraction
