import Current535RecipeLabelBindings

/-!
Explicit low-four/high-five address transport for current535 child0→6/[11].
This reuses the checked historical child009 identity. The actual bit order,
forward/inverse row actions, input-coordinate phases, right offset/global
phase1 and Gaussian C0 are bound below. Apache-2.0; see NOTICE.md.
-/
set_option Elab.async false

namespace CurrentMain.Current535Child006PayloadTransport

open scoped BigOperators Matrix
open CliffordNineBitDecoder (Bit Address matrix mask qvalue)

abbrev Low := CliffordChild009Decoder.Low
abbrev High := Fin 5 → Bit
abbrev SplitAddress := Low × High

def ofBool (b : Bool) : Bit := if b then 1 else 0
def toBool (b : Bit) : Bool := decide (b = 1)

@[simp] theorem ofBool_toBool (b : Bit) : ofBool (toBool b) = b := by
  have h : ∀ z : Bit, ofBool (toBool z) = z := by decide +kernel
  exact h b

@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> rfl

@[simp] theorem ofBool_xor (a b : Bool) : ofBool (a ^^ b) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide +kernel

@[simp] theorem ofBool_not (a : Bool) : ofBool (!a) = ofBool a + 1 := by
  cases a <;> decide +kernel

def split (x : Address) : SplitAddress :=
  ((toBool (x 0), toBool (x 1), toBool (x 2), toBool (x 3)),
    fun i => x ⟨i.val + 4, by omega⟩)

def join (x : SplitAddress) : Address :=
  ![ofBool x.1.1, ofBool x.1.2.1, ofBool x.1.2.2.1, ofBool x.1.2.2.2,
    x.2 0, x.2 1, x.2 2, x.2 3, x.2 4]

theorem join_split (x : Address) : join (split x) = x := by
  funext i
  fin_cases i <;> simp [join, split]

theorem split_join (x : SplitAddress) : split (join x) = x := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  apply Prod.ext
  · simp [split, join]
  · funext i
    fin_cases i <;> simp [split, join]

def addressEquiv : Address ≃ SplitAddress where
  toFun := split
  invFun := join
  left_inv := join_split
  right_inv := split_join

/-- The low bit index remains its little-endian source index; higher bits
4–8 become High indices0–4, with no permutation or payload restriction. -/
theorem coordinate_order (x : Address) :
    (addressEquiv x).1 =
      (toBool (x 0), toBool (x 1), toBool (x 2), toBool (x 3)) ∧
    (∀ i : Fin 5, (addressEquiv x).2 i = x ⟨i.val + 4, by omega⟩) := by
  exact ⟨rfl, fun _ => rfl⟩

def leftInverseRows : List Nat := [8, 9, 10, 4, 16, 32, 64, 128, 256]
def rightInverseRows : List Nat := [5, 3, 8, 7, 16, 32, 64, 128, 256]

theorem left_rows (x : SplitAddress) :
    matrix CliffordChild009Decoder.leftRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.leftEquiv x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, CliffordChild009Decoder.leftRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.leftEquiv,
      CliffordChild009Decoder.leftMap, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem right_rows (x : SplitAddress) :
    matrix CliffordChild009Decoder.rightRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.rightEquiv x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, CliffordChild009Decoder.rightRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.rightEquiv,
      CliffordChild009Decoder.rightMap, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem left_inverse_rows (x : SplitAddress) :
    matrix leftInverseRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.leftEquiv.symm x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, leftInverseRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.leftEquiv,
      CliffordChild009Decoder.leftInverse, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem right_inverse_rows (x : SplitAddress) :
    matrix rightInverseRows *ᵥ join x =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.rightEquiv.symm x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Nat.testBit_eq_decide_div_mod_eq, rightInverseRows,
      join, CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.rightEquiv,
      CliffordChild009Decoder.rightInverse, Equiv.prodCongr_apply, Prod.map_apply, add_assoc]

theorem offset_rows (x : SplitAddress) :
    join x + mask 1 =
      join (CliffordChild009Decoder.liftAddress CliffordChild009Decoder.offsetEquiv x) := by
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  funext i
  fin_cases i <;>
    simp [join, mask, Nat.testBit_eq_decide_div_mod_eq,
      CliffordChild009Decoder.liftAddress, CliffordChild009Decoder.offsetEquiv,
      Equiv.prodCongr_apply, Prod.map_apply]

end CurrentMain.Current535Child006PayloadTransport

#print axioms CurrentMain.Current535Child006PayloadTransport.addressEquiv
#print axioms CurrentMain.Current535Child006PayloadTransport.coordinate_order
#print axioms CurrentMain.Current535Child006PayloadTransport.left_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.right_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.left_inverse_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.right_inverse_rows
#print axioms CurrentMain.Current535Child006PayloadTransport.offset_rows
