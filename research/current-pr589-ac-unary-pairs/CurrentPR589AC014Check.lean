import CurrentPR589AC014Data
import BitXorReversal

/-! Selected PR589 bounded A/C scalar inverse certificate.
Only A[1792:1920] and C[654:782] occur here, each128 unary operands.
Exact frame1 reversal is kernel-bound without identifying different frame IDs.
All A writes go to helpers; arbitrary661 input bits are allowed. Conditional
cleanup explicitly assumes the intervening map preserves off-target coordinates.
Other A/C windows, actual two-level middle-map instances, D compensation,
Fin662 temporary lifecycle, physical frames and the full theorem stay separate.
Prepared with OpenAI assistance; supplier and generic proof attribution retained. -/
namespace CurrentMain.CurrentPR589AC014
open Data
set_option Elab.async false
abbrev RawGate := Nat × Nat × List Nat
abbrev Register := Fin 661
abbrev State := BitXor.State Register

def IsTarget (r : Register) : Prop := 111 ≤ r.val ∧ r.val < 222
instance (r : Register) : Decidable (IsTarget r) := inferInstanceAs (Decidable (111 ≤ r.val ∧ r.val < 222))

def rawFrameOne (g : RawGate) : RawGate := (1, g.2.1, g.2.2)

theorem block_shape :
    phaseA.length = 128 ∧ phaseC.length = 128 ∧
    (phaseA.map (fun g => g.2.2.length)).foldl Nat.add 0 = 128 ∧
    (phaseC.map (fun g => g.2.2.length)).foldl Nat.add 0 = 128 ∧
    (phaseA.map (fun g => g.2.2.length)).foldl Nat.max 0 = 1 := by decide +kernel

theorem raw_domains :
    (phaseA ++ phaseC).all (fun g =>
      decide (g.1 < 636 ∧ g.2.1 < 661) &&
        g.2.2.all (fun r => decide (r < 661))) = true := by decide +kernel

/-- Exact ordered cleanup relation, without identifying unequal frame IDs. -/
theorem raw_cleanup_binding : phaseC = phaseA.reverse.map rawFrameOne := by
  decide +kernel

theorem no_self_reads :
    phaseA.all (fun g => g.2.2.all (fun r => decide (r ≠ g.2.1))) = true := by
  decide +kernel

theorem no_target_reads :
    phaseA.all (fun g => g.2.2.all (fun r => decide (r < 111 ∨ 222 ≤ r))) = true := by
  decide +kernel

theorem no_target_writes :
    phaseA.all (fun g => decide (g.2.1 < 111 ∨ 222 ≤ g.2.1)) = true := by
  decide +kernel

theorem helper_only_destinations :
    phaseA.all (fun g => decide (222 ≤ g.2.1)) = true := by decide +kernel

attribute [local irreducible] phaseA phaseC

private theorem a_domains (g : RawGate) (hg : g ∈ phaseA) :
    g.1 < 636 ∧ g.2.1 < 661 ∧ ∀ r ∈ g.2.2, r < 661 := by
  have hm : g ∈ phaseA ++ phaseC := List.mem_append_left _ hg
  have h := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp raw_domains) g hm)
  have hd := of_decide_eq_true h.1
  refine ⟨hd.1, hd.2, ?_⟩
  intro r hr
  exact of_decide_eq_true ((List.all_eq_true.mp h.2) r hr)

def decodeGate (g : RawGate) (hg : g ∈ phaseA) : BitXor.Gate Register where
  frame := g.1
  dst := ⟨g.2.1, (a_domains g hg).2.1⟩
  sources := g.2.2.attach.map (fun r => ⟨r.val, (a_domains g hg).2.2 r.val r.property⟩)

def decodedA : List (BitXor.Gate Register) :=
  phaseA.attach.map (fun g => decodeGate g.val g.property)

def frameOne (g : BitXor.Gate Register) : BitXor.Gate Register :=
  { frame := 1, dst := g.dst, sources := g.sources }

def decodedC : List (BitXor.Gate Register) := decodedA.reverse.map frameOne

def encodeGate (g : BitXor.Gate Register) : RawGate :=
  (g.frame, g.dst.val, g.sources.map Fin.val)

theorem decode_roundtrip (g : RawGate) (hg : g ∈ phaseA) :
    encodeGate (decodeGate g hg) = g := by
  rcases g with ⟨f,d,rs⟩
  simp only [encodeGate, decodeGate, List.map_map, Function.comp_def]
  rw [List.attach_map_subtype_val]

theorem ordered_A_binding : decodedA.map encodeGate = phaseA := by
  unfold decodedA
  rw [List.map_map]
  simp only [Function.comp_def, decode_roundtrip]
  exact List.attach_map_subtype_val _

theorem ordered_C_binding : decodedC.map encodeGate = phaseC := by
  calc
    decodedC.map encodeGate = (decodedA.map encodeGate).reverse.map rawFrameOne := by
      simp only [decodedC, List.map_map, List.map_reverse, Function.comp_def,
        encodeGate, frameOne, rawFrameOne]
    _ = phaseA.reverse.map rawFrameOne := by rw [ordered_A_binding]
    _ = phaseC := raw_cleanup_binding.symm

theorem decoded_no_self_reads (g : BitXor.Gate Register) (hg : g ∈ decodedA) :
    g.dst ∉ g.sources := by
  obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hg
  subst g
  intro hd
  simp only [decodeGate] at hd
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hd
  have h := of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp no_self_reads) raw.val raw.property)) source.val source.property)
  exact h (congrArg Fin.val heq)

theorem decoded_no_target_reads (g : BitXor.Gate Register) (hg : g ∈ decodedA) :
    ∀ r ∈ g.sources, ¬ IsTarget r := by
  obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hg
  subst g
  intro r hr
  simp only [decodeGate] at hr
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hr
  subst r
  change ¬ (111 ≤ source.val ∧ source.val < 222)
  have h := of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp no_target_reads) raw.val raw.property)) source.val source.property)
  rcases h with hlt | hge
  · exact fun ht => (Nat.not_le_of_lt hlt) ht.1
  · exact fun ht => (Nat.not_le_of_lt ht.2) hge

theorem decoded_no_target_writes (g : BitXor.Gate Register) (hg : g ∈ decodedA) :
    ¬ IsTarget g.dst := by
  obtain ⟨raw, hraw, heq⟩ := List.mem_map.mp hg
  subst g
  change ¬ (111 ≤ raw.val.2.1 ∧ raw.val.2.1 < 222)
  have h := of_decide_eq_true ((List.all_eq_true.mp no_target_writes) raw.val raw.property)
  rcases h with hlt | hge
  · exact fun ht => (Nat.not_le_of_lt hlt) ht.1
  · exact fun ht => (Nat.not_le_of_lt ht.2) hge

theorem cleanup_runs_reverse (s : State) :
    BitXor.run decodedC s = BitXor.run decodedA.reverse s := by
  have h : decodedC.map BitXorReversal.scalarize =
      decodedA.reverse.map BitXorReversal.scalarize := by
    simp only [decodedC, List.map_map, Function.comp_def, frameOne, BitXorReversal.scalarize]
    rfl
  calc
    BitXor.run decodedC s = BitXor.run (decodedC.map BitXorReversal.scalarize) s :=
      (BitXorReversal.run_scalarize decodedC s).symm
    _ = BitXor.run (decodedA.reverse.map BitXorReversal.scalarize) s := by rw [h]
    _ = BitXor.run decodedA.reverse s := BitXorReversal.run_scalarize decodedA.reverse s

/-- The exact isolated 128+128 scalar word cancels on arbitrary 661-bit state. -/
theorem isolated_block_inverse (s : State) :
    BitXor.run decodedC (BitXor.run decodedA s) = s := by
  rw [cleanup_runs_reverse]
  exact BitXorReversal.run_reverse_cancel decodedA decoded_no_self_reads s

/-- A target-only middle update does not prevent this block's off-target cleanup. -/
theorem conditional_off_target_cleanup (middle : State → State)
    (hmiddle : ∀ s r, ¬ IsTarget r → middle s r = s r)
    (s : State) (r : Register) (hr : ¬ IsTarget r) :
    BitXor.run decodedC (middle (BitXor.run decodedA s)) r = s r := by
  rw [cleanup_runs_reverse]
  exact BitXorReversal.cleanup_off_target IsTarget decodedA decoded_no_self_reads
    decoded_no_target_reads middle hmiddle s r hr

theorem conditional_target_value (middle : State → State)
    (s : State) (r : Register) (hr : IsTarget r) :
    BitXor.run decodedC (middle (BitXor.run decodedA s)) r =
      middle (BitXor.run decodedA s) r := by
  rw [cleanup_runs_reverse]
  exact BitXorReversal.cleanup_target_value IsTarget decodedA decoded_no_target_writes
    middle s r hr

end CurrentMain.CurrentPR589AC014
#print axioms CurrentMain.CurrentPR589AC014.block_shape
#print axioms CurrentMain.CurrentPR589AC014.raw_domains
#print axioms CurrentMain.CurrentPR589AC014.raw_cleanup_binding
#print axioms CurrentMain.CurrentPR589AC014.no_self_reads
#print axioms CurrentMain.CurrentPR589AC014.no_target_reads
#print axioms CurrentMain.CurrentPR589AC014.no_target_writes
#print axioms CurrentMain.CurrentPR589AC014.helper_only_destinations
#print axioms CurrentMain.CurrentPR589AC014.decode_roundtrip
#print axioms CurrentMain.CurrentPR589AC014.ordered_A_binding
#print axioms CurrentMain.CurrentPR589AC014.ordered_C_binding
#print axioms CurrentMain.CurrentPR589AC014.decoded_no_self_reads
#print axioms CurrentMain.CurrentPR589AC014.decoded_no_target_reads
#print axioms CurrentMain.CurrentPR589AC014.decoded_no_target_writes
#print axioms CurrentMain.CurrentPR589AC014.cleanup_runs_reverse
#print axioms CurrentMain.CurrentPR589AC014.isolated_block_inverse
#print axioms CurrentMain.CurrentPR589AC014.conditional_off_target_cleanup
#print axioms CurrentMain.CurrentPR589AC014.conditional_target_value
