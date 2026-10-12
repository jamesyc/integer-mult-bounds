import CurrentBitLogCheckpoints
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
The two new PR510 Real log-unit enclosures, at4/3 and8/7, source-bound to
z=1/7 and1/15 and the accepted eighty-term rational identities. The private
remainder/cast chain below is copied verbatim from the accepted historical
five-unit module; SOURCE_BINDING records the exact segment correspondence.
Only two finite six-term tail comparisons and their two unit instantiations
are new. The final two facts substitute the accepted exact rational values.

Author-checked conditional current source context at7dfa22b:
kappa=1584931111785787/1000000000000000000=0.001584931111785787.
These four bounds do not yet prove the six binary-reduced rounded bit logs,
the current bit weighted moment, profile/operator realization or an all-size
selected-kappa theorem. Historical source proofs and endpoints are preserved.
Attribution: PR361 base_two_moment.py via PR535's pinned PR510 input, the
accepted analytic log proof chain, and Mathlib's logarithm Taylor remainder.
Prepared with OpenAI assistance; all new finite decisions use the kernel.
-/
namespace CurrentMain.CurrentBitLogRealEnclosure
open scoped BigOperators
open Finset SelectedMomentLogCheckpoints CurrentBitLogCheckpoints
set_option Elab.async false

private noncomputable def oddSum (z : ℝ) (n : Nat) : ℝ :=
  ∑ j ∈ range n, z^(2*j+1) / ((2*j+1 : Nat) : ℝ)

/-- Pair even and odd Taylor terms without expanding a 172-term expression. -/
private theorem paired_sum (z : ℝ) (m : Nat) :
    (∑ i ∈ range (2*m), z^(i+1) / ((i+1 : Nat) : ℝ)) -
      (∑ i ∈ range (2*m), (-z)^(i+1) / ((i+1 : Nat) : ℝ)) =
    2 * oddSum z m := by
  induction m with
  | zero => simp [oddSum]
  | succ m ih =>
    have ho : (-z)^(2*m+1) = -(z^(2*m+1)) := by
      simp [pow_add, pow_mul]
    have he : (-z)^(2*m+1+1) = z^(2*m+1+1) := by
      rw [show 2*m+1+1 = 2*(m+1) by omega]
      simp [pow_mul]
    rw [show 2*(m+1) = 2*m+1+1 by omega]
    simp only [Finset.sum_range_succ, oddSum] at ih ⊢
    rw [ho, he]
    simp only [neg_div]
    linarith

/-- The two signed library remainders give the required one-sided log bound. -/
private theorem log_auxiliary (z : ℝ) (hz : 0 ≤ z) (h1 : z < 1) :
    Real.log ((1+z)/(1-z)) ≤
      2 * oddSum z 86 + 2*z^173/(1-z) := by
  have hp := Real.abs_log_sub_add_sum_range_le
    (show |z| < 1 by simpa only [abs_of_nonneg hz] using h1) 172
  have hm := Real.abs_log_sub_add_sum_range_le
    (show |-z| < 1 by simpa only [abs_neg, abs_of_nonneg hz] using h1) 172
  simp only [abs_of_nonneg hz] at hp
  simp only [abs_neg, abs_of_nonneg hz, sub_neg_eq_add] at hm
  have hpair := paired_sum z 86
  have hlo := (abs_le.mp hp).1
  have hhi := (abs_le.mp hm).2
  have hplus : 1+z ≠ 0 := ne_of_gt (by linarith)
  have hminus : 1-z ≠ 0 := ne_of_gt (by linarith)
  rw [Real.log_div hplus hminus]
  simp only [Nat.cast_add, Nat.cast_one] at hpair
  change (∑ i ∈ range 172, z^(i+1) / ((i : ℝ)+1)) -
    (∑ i ∈ range 172, (-z)^(i+1) / ((i : ℝ)+1)) =
    2 * oddSum z 86 at hpair
  change -(z^173/(1-z)) ≤
    (∑ i ∈ range 172, z^(i+1)/((i : ℝ)+1)) + Real.log (1-z) at hlo
  change (∑ i ∈ range 172, (-z)^(i+1)/((i : ℝ)+1)) + Real.log (1+z) ≤
    z^173/(1-z) at hhi
  have hbound : Real.log (1+z) - Real.log (1-z) ≤
      2 * oddSum z 86 + 2 * (z^173/(1-z)) := by
    linarith only [hlo, hhi, hpair]
  simpa only [mul_div_assoc] using hbound

private theorem cast_power (n d exponent : Nat) :
    (powerFraction n d exponent : ℝ) = ((n : ℝ)/(d : ℝ))^exponent := by
  simp only [powerFraction, Rat.cast_div, Rat.cast_natCast, Nat.cast_pow, Rat.cast_pow, div_pow]

private theorem cast_term (n d j : Nat) :
    (logTerm n d j : ℝ) =
      ((n : ℝ)/(d : ℝ))^(2*j+1) / ((2*j+1 : Nat) : ℝ) := by
  simp only [logTerm, Rat.cast_div, cast_power, Rat.cast_natCast]

/-- Only eight additions are normalized at a time. -/
private theorem cast_block (n d start : Nat) (acc : Rat) :
    (logBlock n d start acc : ℝ) = (acc : ℝ) +
      ∑ j ∈ range 8, ((n : ℝ)/(d : ℝ))^(2*(start+j)+1) /
        ((2*(start+j)+1 : Nat) : ℝ) := by
  simp only [logBlock, Rat.cast_add, cast_term, Finset.sum_range_succ,
    Finset.sum_range_zero, add_zero, zero_add] <;> ring

private theorem cast_block_step (n d start : Nat) (acc : Rat)
    (hacc : (acc : ℝ) = oddSum ((n : ℝ)/(d : ℝ)) start) :
    (logBlock n d start acc : ℝ) = oddSum ((n : ℝ)/(d : ℝ)) (start+8) := by
  rw [cast_block, hacc]
  exact (Finset.sum_range_add _ start 8).symm

/-- Cast correspondence to the existing ten-block expression, not new evaluation. -/
private theorem cast_sum80 (n d : Nat) :
    (logSum80 n d : ℝ) = oddSum ((n : ℝ)/(d : ℝ)) 80 := by
  have h0 : ((0 : Rat) : ℝ) = oddSum ((n : ℝ)/(d : ℝ)) 0 := by
    simp [oddSum]
  have h8 := cast_block_step n d 0 0 h0
  have h16 := cast_block_step n d 8 _ h8
  have h24 := cast_block_step n d 16 _ h16
  have h32 := cast_block_step n d 24 _ h24
  have h40 := cast_block_step n d 32 _ h32
  have h48 := cast_block_step n d 40 _ h40
  have h56 := cast_block_step n d 48 _ h48
  have h64 := cast_block_step n d 56 _ h56
  have h72 := cast_block_step n d 64 _ h64
  have h80 := cast_block_step n d 72 _ h72
  exact h80

private def auxiliaryTail (n d : Nat) : Rat :=
  2 * (logTerm n d 80 + logTerm n d 81 + logTerm n d 82 +
    logTerm n d 83 + logTerm n d 84 + logTerm n d 85) +
  2 * powerFraction n d 173 / (1 - (n : Rat)/(d : Rat))

private def sourceTail (n d : Nat) : Rat :=
  2 * powerFraction n d 161 / (161 * (1 - powerFraction n d 2))

private theorem cast_auxiliaryTail (n d : Nat) :
    (auxiliaryTail n d : ℝ) =
    2 * (∑ j ∈ range 6, ((n : ℝ)/(d : ℝ))^(2*(80+j)+1) /
      ((2*(80+j)+1 : Nat) : ℝ)) +
    2 * ((n : ℝ)/(d : ℝ))^173 / (1 - (n : ℝ)/(d : ℝ)) := by
  simp only [auxiliaryTail, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_sub, Rat.cast_natCast, Rat.cast_ofNat, cast_power, cast_term,
    Finset.sum_range_succ, Finset.sum_range_zero, add_zero, zero_add] <;> norm_num

private theorem cast_sourceTail (n d : Nat) :
    (sourceTail n d : ℝ) = 2 * ((n : ℝ)/(d : ℝ))^161 /
      (161 * (1 - ((n : ℝ)/(d : ℝ))^2)) := by
  simp only [sourceTail, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
    Rat.cast_ofNat, Rat.cast_one, cast_power]

private theorem cast_unitUpper (n d : Nat) :
    (unitUpper n d : ℝ) = 2 * oddSum ((n : ℝ)/(d : ℝ)) 80 +
      2 * ((n : ℝ)/(d : ℝ))^161 / (161 * (1 - ((n : ℝ)/(d : ℝ))^2)) := by
  change ((2 * logSum80 n d + sourceTail n d : Rat) : ℝ) = _
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, cast_sum80, cast_sourceTail]

/-- Two new finite comparisons, each with only six extra terms and two tails. -/
private theorem tail_1_7 : auxiliaryTail 1 7 ≤ sourceTail 1 7 := by decide +kernel
private theorem tail_1_15 : auxiliaryTail 1 15 ≤ sourceTail 1 15 := by decide +kernel

private theorem unit_from_tail (n d : Nat)
    (hz : 0 ≤ (n : ℝ)/(d : ℝ)) (h1 : (n : ℝ)/(d : ℝ) < 1)
    (ht : auxiliaryTail n d ≤ sourceTail n d) :
    Real.log ((1+(n : ℝ)/(d : ℝ))/(1-(n : ℝ)/(d : ℝ))) ≤
      (unitUpper n d : ℝ) := by
  have ha := log_auxiliary ((n : ℝ)/(d : ℝ)) hz h1
  have hc : (auxiliaryTail n d : ℝ) ≤ (sourceTail n d : ℝ) := by
    exact_mod_cast ht
  rw [cast_auxiliaryTail, cast_sourceTail] at hc
  have hs : oddSum ((n : ℝ)/(d : ℝ)) 86 =
      oddSum ((n : ℝ)/(d : ℝ)) 80 +
      ∑ j ∈ range 6, ((n : ℝ)/(d : ℝ))^(2*(80+j)+1) /
        ((2*(80+j)+1 : Nat) : ℝ) := Finset.sum_range_add _ 80 6
  rw [hs] at ha
  rw [cast_unitUpper]
  linarith

theorem log_four_thirds_upper : Real.log ((4 : ℝ)/3) ≤ (unitUpper 1 7 : ℝ) := by
  have h := unit_from_tail 1 7 (by norm_num) (by norm_num) tail_1_7
  convert h using 1 <;> norm_num

theorem log_eight_sevenths_upper : Real.log ((8 : ℝ)/7) ≤ (unitUpper 1 15 : ℝ) := by
  have h := unit_from_tail 1 15 (by norm_num) (by norm_num) tail_1_15
  convert h using 1 <;> norm_num

theorem log_four_thirds_literal : Real.log ((4 : ℝ)/3) ≤
    (((1917583945038911950451071993730030841774274315834269362882085106238032288562549231345927528100573946855680240642540239858177002067882463478295710129039466239517734161195101992073515802625388705731833 : Rat) / 6665635883029599387909796641622010790319634285846494165831283086054462946808932821031431408280966790350431259284665380758118384464723864873105220602665836386842541428297082558442546501072105292321000) : ℝ) := by
  simpa only [z1_7_upper] using log_four_thirds_upper

theorem log_eight_sevenths_literal : Real.log ((8 : ℝ)/7) ≤
    (((828523316073806291025673513158892396096476411371284171679897071517804954188261522396166329963681356675253653711589601713606145760737129984363144904697509849540420602697056744255575363435988741480808940578259166345437197557177077778166068577814526527 : Rat) / 6204708119861625498162059951568108507448968378445453646688417910017147154355897728903579489541929142010159086360398347601078264480377082408174482233762145248381377702792471610391538643508611635509594799597551939562833922536810860037803649902343750000) : ℝ) := by
  simpa only [z1_15_upper] using log_eight_sevenths_upper

#print axioms log_four_thirds_upper
#print axioms log_eight_sevenths_upper
#print axioms log_four_thirds_literal
#print axioms log_eight_sevenths_literal
end CurrentMain.CurrentBitLogRealEnclosure
