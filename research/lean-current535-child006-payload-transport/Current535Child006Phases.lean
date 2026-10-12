import Current535Child006Coordinates

/-! Exact raw phase correspondence for current535 child0→6/[11].
Apache-2.0; see NOTICE.md. Reduce each nine-coordinate source sum once,
then retain only the two or eight relevant Boolean cases. No payload is fixed. -/
set_option Elab.async false
namespace CurrentMain.Current535Child006PayloadTransport
open scoped BigOperators Matrix
open CliffordNineBitDecoder (Bit Address matrix mask qvalue)

private theorem left_qvalue_reduced (x : Address) :
    qvalue CliffordChild009Decoder.leftQ CliffordChild009Decoder.leftAlpha x =
      (2 * (x 0).val) % 4 := by
  simp [qvalue, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
    CliffordChild009Decoder.leftQ, CliffordChild009Decoder.leftAlpha]

private theorem right_qvalue_reduced (x : Address) :
    qvalue CliffordChild009Decoder.rightQ CliffordChild009Decoder.rightAlpha x =
      (3 * (x 0).val + 3 * (x 1).val + 2 * (x 3).val +
        2 * (x 0).val * (x 1).val) % 4 := by
  simp [qvalue, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
    CliffordChild009Decoder.rightQ, CliffordChild009Decoder.rightAlpha,
    Nat.add_assoc, Nat.mul_assoc]

private theorem canonical_qvalue_reduced (x : Address) :
    qvalue CliffordChild009Canonical.canonicalQ (List.replicate 9 0) x =
      (2 * ((x 0).val * (x 3).val + (x 1).val * (x 3).val)) % 4 := by
  simp [qvalue, matrix, Fin.sum_univ_succ, Nat.testBit_eq_decide_div_mod_eq,
    CliffordChild009Canonical.canonicalQ]

theorem left_phase (x : SplitAddress) :
    qvalue CliffordChild009Decoder.leftQ CliffordChild009Decoder.leftAlpha (join x) =
      CliffordChild009Decoder.leftPhase x.1 := by
  rw [left_qvalue_reduced]
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  cases a <;> simp [join, ofBool, CliffordChild009Decoder.leftPhase]

theorem right_phase (x : SplitAddress) :
    qvalue CliffordChild009Decoder.rightQ CliffordChild009Decoder.rightAlpha (join x) =
      CliffordChild009Decoder.rightPhase x.1 := by
  rw [right_qvalue_reduced]
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  cases a <;> cases b <;> cases d <;>
    simp [join, ofBool, CliffordChild009Decoder.rightPhase]

theorem canonical_phase (x : SplitAddress) :
    qvalue CliffordChild009Canonical.canonicalQ (List.replicate 9 0) (join x) =
      CliffordChild009Canonical.canonicalPhase x.1 := by
  rw [canonical_qvalue_reduced]
  rcases x with ⟨⟨a, b, c, d⟩, h⟩
  cases a <;> cases b <;> cases d <;>
    simp [join, ofBool, CliffordChild009Canonical.canonicalPhase]

end CurrentMain.Current535Child006PayloadTransport

#print axioms CurrentMain.Current535Child006PayloadTransport.left_phase
#print axioms CurrentMain.Current535Child006PayloadTransport.right_phase
#print axioms CurrentMain.Current535Child006PayloadTransport.canonical_phase
