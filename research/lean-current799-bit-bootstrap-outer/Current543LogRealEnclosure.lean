import Current543LogCheckpoints
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
The two new selected PR543 Real log-unit enclosures, at8/5 and32/21,
source-bound to z=3/13 and11/53 and the accepted eighty-term rational
identities. Both private generic remainder/cast segments are copied verbatim
from the accepted historical five-unit source. Only two finite six-term tail
comparisons and their concrete unit instantiations are new; the literal
conclusions use the already reviewed explicit Rat.cast_div/ofNat normalization.

Author-checked conditional current source context at5996:
kappa=16127213726553/10000000000000000=0.0016127213726553.
The selected PR543 bit branch retains its fallback surcharge, unlike native
complex. These four log bounds do not establish the eight-profile weighted
bit moment, its recurrence/model realization, or the all-size kappa theorem.
Attribution: PR361 base_two_moment.py with pinned PR543 source data, accepted
analytic log proof chain, and Mathlib's logarithm Taylor remainder.
Prepared with OpenAI assistance; all new finite decisions use the kernel.
-/
namespace CurrentMain.Current543LogRealEnclosure
open scoped BigOperators
open Finset SelectedMomentLogCheckpoints Current543LogCheckpoints
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

/-- Two finite comparisons, each with six extra terms and two rational tails. -/
private theorem tail_3_13 : auxiliaryTail 3 13 ≤ sourceTail 3 13 := by decide +kernel
private theorem tail_11_53 : auxiliaryTail 11 53 ≤ sourceTail 11 53 := by decide +kernel

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

theorem log_eight_fifths_upper : Real.log ((8 : ℝ)/5) ≤ (unitUpper 3 13 : ℝ) := by
  have h := unit_from_tail 3 13 (by norm_num) (by norm_num) tail_3_13
  convert h using 1 <;> norm_num

theorem log_thirty_two_twenty_one_upper : Real.log ((32 : ℝ)/21) ≤ (unitUpper 11 53 : ℝ) := by
  have h := unit_from_tail 11 53 (by norm_num) (by norm_num) tail_11_53
  convert h using 1 <;> norm_num

theorem log_eight_fifths_literal : Real.log ((8 : ℝ)/5) ≤
    (((6447905907869983072408678215642743434115440225347832158339701576949236962719145572050521571672370413328965948598450739770220684592289574657953003792825494396835097018008985061363611620398048144662698457612464529524279212870292642209520423 : Rat) / 13718842805996239743985078292465714201763488058191677834283408698880653122719648394595487595017716829275922611563420084522467646976808929306066785503995662168514530861352571508666405175689823925244737937539648873778488619944178949831058000) : ℝ) := by
  simpa only [z3_13_upper, Rat.cast_div, Rat.cast_ofNat] using log_eight_fifths_upper

theorem log_thirty_two_twenty_one_literal : Real.log ((32 : ℝ)/21) ≤
    (((2959532525041993318146014596272840402119157805065713166204019370795429042985037174301776228372201769272715828159299753851950852166198996300448313399304070939191411643719464563410778468620974744439489196096599450249578777656187313946570217041781546431528093709648122411878162010628264344308804225372742707640827128502896544797326011342050711 : Rat) / 7026205879970785982255069070842073989157033264134613384322249560203525571922531054158937988071858988165109410562224225654147524343294739867580924510021386765512184212693780046988772761083301179722396155255754736673341304381962573913415636998000940601782877251909182983851247812648508536032909500896682629269938457989708609377022796586568000) : ℝ) := by
  simpa only [z11_53_upper, Rat.cast_div, Rat.cast_ofNat] using log_thirty_two_twenty_one_upper

#print axioms log_eight_fifths_upper
#print axioms log_thirty_two_twenty_one_upper
#print axioms log_eight_fifths_literal
#print axioms log_thirty_two_twenty_one_literal
end CurrentMain.Current543LogRealEnclosure
