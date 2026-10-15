import Current1094Row2DyadicReference

/-!
Actual sequential composition of the accepted raw1 SCALE(-1/2) reference tape
with the accepted raw2 ADD(+1/2) reference tape. Both operate on family119;
raw2 reads family169. This module embeds the old core instructions unchanged,
then appends the actual complete ADD program. Original source reads and exact
raw Cell results follow from the already checked disjoint-block traversals.

A per-output-cell bound is independent of the number n of complex components:
if the original target/source numerators fit b bits and exponents are at most P,
the final numerator fits b+P+1 bits and its exponent is at most P+1. The explicit
alignment bound is also retained. There is no global exponent shift, and every
cell outside the written block keeps its original numerator and exponent.

The 16*n length counts abstract reference instructions only. This supplies no
bit-operation time for shifts/addition/addressing, no uniform cost C, no initial
encoding or selected width, no precision schedule, no metadata/scratch cleanup,
and no equivalence with the complete emitted word. Physical chart/address and
all non-scalar-event refinements remain separate. Finite invoice C0 is unchanged.
Attribution: selected PR1094 forward raw1/raw2, machine's accepted flat SCALE/ADD
programs and family allocation, analytic exact dyadic interpreters and carry
bound. Apache-2.0; OpenAI-assisted. Author-checked selected kappa is unchanged:
836330098538459/500000000000000000. Source candidate, initially uncompiled.
-/
set_option Elab.async false
set_option autoImplicit false
namespace CurrentMain.Current1094Rows12DyadicReference
open Current1094Row1DyadicReference DyadicCellAddition Current1094Row1FamilyBlocks
open ComponentStoreFoldRefinement Current1094Row2AddReference Current1094Row2DyadicReference

/-- The old SCALE instructions, followed by the actual complete ADD tape. -/
def rows12Program (n target source : ℕ) : List Instruction :=
  (Current1094Row1FlatReference.program n (familyBase n target)).map Instruction.core ++
    Current1094Row2AddReference.program n target source

def selectedRows12Program (n : ℕ) : List Instruction :=
  rows12Program n selectedTargetFamily selectedSourceFamily

/-- Core embedding preserves the entire encoded state, including dirty scratch. -/
theorem run_core (ops : List Current1094Row1FlatReference.Instruction) (s : EncodedState) :
    runAdd (ops.map Instruction.core) s = Current1094Row1DyadicReference.run ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih (Current1094Row1DyadicReference.step op s)

private theorem runAdd_append (xs ys : List Instruction) (s : EncodedState) :
    runAdd (xs ++ ys) s = runAdd ys (runAdd xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih (stepAdd op s)

/-- Two complete 8*n reference traversals; this is not a bit-cost formula. -/
theorem rows12_length (n target source : ℕ) :
    (rows12Program n target source).length = 16 * n := by
  simp only [rows12Program, List.length_append, List.length_map,
    Current1094Row1FlatReference.program_length, Current1094Row2AddReference.program_length]
  omega

/-- The full instruction prefix decodes to the existing real interpreter. -/
theorem rows12_prefix_decodes (n target source k : ℕ) (s : EncodedState) :
    decodeState (runAdd ((rows12Program n target source).take k) s) =
      execute ((rows12Program n target source).take k) (decodeState s) :=
  decode_runAdd _ _

/-- The ADD source is the original source Cell because SCALE touches only the
separate target block. Both exact traversals are reused without a new fold. -/
theorem rows12_cell (n target source : ℕ) (hne : source ≠ target)
    (s : EncodedState) (slot : Slot (Fin n)) :
    (runAdd (rows12Program n target source) s).memory (address n target slot) =
      addCell (minusHalfCell (s.memory (address n target slot)))
        (halfCell (s.memory (address n source slot))) := by
  rw [rows12Program, runAdd_append, run_core,
    Current1094Row2DyadicReference.program_cell n target source hne]
  have ht := Current1094Row1DyadicReference.program_cell n (familyBase n target) s slot
  have hs := Current1094Row1DyadicReference.program_outside_cell n (familyBase n target) s
    (address n source slot) (other_block_outside n target source hne slot)
  dsimp only [address] at hs ⊢
  rw [ht, hs]

/-- Every outside address, including the complete source block, retains both
raw Cell fields. No global fractional-bit change is performed. -/
theorem rows12_outside_cell (n target source : ℕ) (s : EncodedState) (a : ℕ)
    (hout : a < familyBase n target ∨ familyBase n target + 2 * n ≤ a) :
    (runAdd (rows12Program n target source) s).memory a = s.memory a := by
  rw [rows12Program, runAdd_append, run_core,
    Current1094Row2DyadicReference.program_outside_cell n target source _ a hout]
  exact Current1094Row1DyadicReference.program_outside_cell n (familyBase n target) s a hout

/-- The represented endpoint is exactly (original source-original target)/2. -/
theorem rows12_cell_value (n target source : ℕ) (hne : source ≠ target)
    (s : EncodedState) (slot : Slot (Fin n)) :
    value ((runAdd (rows12Program n target source) s).memory (address n target slot)) =
      (value (s.memory (address n source slot)) - value (s.memory (address n target slot))) / 2 := by
  rw [rows12_cell n target source hne, addCell_value]
  simp only [value, minusHalfCell, halfCell, Int.cast_neg, pow_succ,
    div_mul_eq_div_div, neg_div]
  ring

/-- Exact alignment/carry budget, prior to any uniform exponent ceiling. -/
theorem rows12_cell_budget (n target source : ℕ) (hne : source ≠ target)
    (s : EncodedState) (slot : Slot (Fin n)) (bt bs : ℕ)
    (ht : (s.memory (address n target slot)).numerator.natAbs < 2 ^ bt)
    (hs : (s.memory (address n source slot)).numerator.natAbs < 2 ^ bs) :
    let t := s.memory (address n target slot)
    let u := s.memory (address n source slot)
    let q := max (t.fractionalBits + 1) (u.fractionalBits + 1)
    ((runAdd (rows12Program n target source) s).memory (address n target slot)).fractionalBits = q ∧
    ((runAdd (rows12Program n target source) s).memory (address n target slot)).numerator.natAbs <
      2 ^ (max (bt + (q - (t.fractionalBits + 1)))
        (bs + (q - (u.fractionalBits + 1))) + 1) := by
  dsimp only
  rw [rows12_cell n target source hne]
  refine ⟨rfl, ?_⟩
  exact addCell_bit_budget _ _ bt bs
    (by simpa only [minusHalfCell, Int.natAbs_neg] using ht) hs

/-- A sharper whole-traversal output bound does not accumulate an exponent or
carry for every component: each actual target is written once by each tape. -/
theorem rows12_uniform_cell_budget (n target source : ℕ) (hne : source ≠ target)
    (s : EncodedState) (slot : Slot (Fin n)) (b P : ℕ)
    (ht : (s.memory (address n target slot)).numerator.natAbs < 2 ^ b)
    (hs : (s.memory (address n source slot)).numerator.natAbs < 2 ^ b)
    (hpt : (s.memory (address n target slot)).fractionalBits ≤ P)
    (hps : (s.memory (address n source slot)).fractionalBits ≤ P) :
    ((runAdd (rows12Program n target source) s).memory (address n target slot)).fractionalBits ≤ P + 1 ∧
    ((runAdd (rows12Program n target source) s).memory (address n target slot)).numerator.natAbs <
      2 ^ (b + P + 1) := by
  have h := rows12_cell_budget n target source hne s slot b b ht hs
  dsimp only at h
  have hq : max ((s.memory (address n target slot)).fractionalBits + 1)
      ((s.memory (address n source slot)).fractionalBits + 1) ≤ P + 1 :=
    max_le (by omega) (by omega)
  refine ⟨h.1.le.trans hq, h.2.trans_le ?_⟩
  apply pow_le_pow_right₀ (by norm_num)
  omega

/-- Bank-bound families119 and169 specialize the actual two-tape composition.
No slot is silently restricted, including the vacuous n=0 family. -/
theorem selected_rows12_cell (n : ℕ) (s : EncodedState) (slot : Slot (Fin n)) :
    (runAdd (selectedRows12Program n) s).memory (address n 119 slot) =
      addCell (minusHalfCell (s.memory (address n 119 slot)))
        (halfCell (s.memory (address n 169 slot))) := by
  have h := rows12_cell n selectedTargetFamily selectedSourceFamily selected_families_ne s slot
  simpa only [selectedRows12Program, selected_family_literals.1, selected_family_literals.2] using h

end CurrentMain.Current1094Rows12DyadicReference

#print axioms CurrentMain.Current1094Rows12DyadicReference.run_core
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_length
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_prefix_decodes
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_cell
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_outside_cell
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_cell_value
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_cell_budget
#print axioms CurrentMain.Current1094Rows12DyadicReference.rows12_uniform_cell_budget
#print axioms CurrentMain.Current1094Rows12DyadicReference.selected_rows12_cell
#check @CurrentMain.Current1094Rows12DyadicReference.rows12_uniform_cell_budget
