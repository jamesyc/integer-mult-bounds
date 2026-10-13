import PackedMatrixReindex

/-!
Symbolic discharge of the PR593 gate-adjoint validity predicate.
The source Gate.ok definition remains unchanged. Diagonal validity follows by
paired-list induction, XOR validity by the bounded involution, and permutation
validity by the already accepted packed/matrix correspondence. No address is
enumerated. Matrix lengths and both inverse equations remain explicit inputs.
Apache-2.0; prepared with OpenAI assistance. See NOTICE.md.
-/
set_option Elab.async false
namespace CurrentMain.PackedGateValidity
open HyperplaneEnd.Clifford
open CliffordNineBitDecoder Current535PackedCoordinates PackedMatrixReindex
open scoped Matrix

private theorem qvAux_adjoint (Q alpha : List Nat) (x i : Nat) :
    (qvAux Q alpha x i +
      qvAux Q (alpha.map fun a => (4 - a % 4) % 4) x i) % 4 = 0 := by
  induction Q generalizing alpha i with
  | nil => simp [qvAux]
  | cons q Q ih =>
    cases alpha with
    | nil => simp [qvAux]
    | cons a alpha =>
      have ht := ih alpha (i + 1)
      have ha : a % 4 < 4 := Nat.mod_lt _ (by decide)
      by_cases hx : (x >>> i) % 2 = 1
      · cases hp : par9 ((q >>> (i + 1)) &&& (x >>> (i + 1))) <;>
          simp only [List.map_cons, qvAux, hx, hp, if_true, if_false,
            Bool.false_eq_true] <;> omega
      · simpa only [List.map_cons, qvAux, hx, if_false, zero_add] using ht

/-- The same strict-upper quadratic part is its own inverse modulo four;
only the diagonal coefficients are negated, exactly as Gate.adj prescribes. -/
theorem diagonal_ok (N : Nat) (Q alpha : List Nat) :
    Gate.ok N (.dg Q alpha) = true := by
  apply List.all_eq_true.mpr
  intro x _
  have h := qvAux_adjoint Q alpha x 0
  simpa only [qv, beq_iff_eq, Nat.add_mod, Nat.mod_mod] using h

private theorem xor_twice (x b : Nat) (hx : x < 512) (hb : b < 512) :
    ((x ^^^ b) % 512 ^^^ b) % 512 = x := by
  have hxb : x ^^^ b < 512 := Nat.xor_lt_two_pow (n := 9) hx hb
  rw [Nat.mod_eq_of_lt hxb, Nat.xor_assoc, Nat.xor_self,
    Nat.xor_zero, Nat.mod_eq_of_lt hx]

/-- A bounded XOR translation satisfies the literal source inverse predicate. -/
theorem translation_ok (b : Nat) (hb : b < 512) :
    Gate.ok 512 (.xg b) = true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact beq_iff_eq.mpr (xor_twice x b (List.mem_range.mp hx) hb)

/-- Either Gaussian sign uses the same bounded XOR involution. -/
theorem gaussian_ok (q : Nat) (hq : q < 512) (s : Bool) :
    Gate.ok 512 (.cg q s) = true := by
  exact translation_ok q hq

/-- Every stored global phase has the source-specified inverse. -/
theorem phase_ok (N p : Nat) : Gate.ok N (.ph p) = true := rfl

private def packedMap (rows : List Nat) (x : Packed) : Packed :=
  fx 512 (mv rows x.val)

private theorem packedMap_inverse (rows inverseRows : List Nat)
    (hr : rows.length = 9) (hi : inverseRows.length = 9)
    (h : matrix inverseRows * matrix rows = 1) (x : Packed) :
    packedMap inverseRows (packedMap rows x) = x := by
  apply addressEquiv.injective
  change unpack (fx 512 (mv inverseRows (fx 512 (mv rows x.val)).val)) = unpack x
  rw [packed_matrix inverseRows hi, packed_matrix rows hr,
    Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- Both source inverse reads follow from the two matrix equations. The modulo
operation is retained literally, with its packed interpretation already proved. -/
theorem permutation_ok (rows inverseRows : List Nat)
    (hr : rows.length = 9) (hi : inverseRows.length = 9)
    (hf : matrix rows * matrix inverseRows = 1)
    (hb : matrix inverseRows * matrix rows = 1) :
    Gate.ok 512 (.pm rows inverseRows) = true := by
  apply List.all_eq_true.mpr
  intro x hx
  have hxb : x < 512 := List.mem_range.mp hx
  have h₁ := congrArg Fin.val (packedMap_inverse rows inverseRows hr hi hb ⟨x, hxb⟩)
  have h₂ := congrArg Fin.val (packedMap_inverse inverseRows rows hi hr hf ⟨x, hxb⟩)
  exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr h₁, beq_iff_eq.mpr h₂⟩

end CurrentMain.PackedGateValidity

#print axioms CurrentMain.PackedGateValidity.diagonal_ok
#print axioms CurrentMain.PackedGateValidity.translation_ok
#print axioms CurrentMain.PackedGateValidity.gaussian_ok
#print axioms CurrentMain.PackedGateValidity.phase_ok
#print axioms CurrentMain.PackedGateValidity.permutation_ok
