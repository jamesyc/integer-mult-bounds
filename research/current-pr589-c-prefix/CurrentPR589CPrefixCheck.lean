import CurrentPR589CPrefixData
import CurrentPR589PhaseBXor
import CurrentPR589ACJoin
import BitXorTwoLevelCleanup

/-! Current PR589 scalar A/B/C assembly through the exact499-gate C prefix.
B's middle writes483 source destinations and16 helper destinations; neither
source nor unconditional helper preservation is assumed during that middle.
The first102 and last111 B gates are target-only updates. Their actual contracts
supply the two-level cleanup hypotheses, with arbitrary original661 bits.
A and the C suffix reuse all17 accepted windows. Only one new finite equality
binds C[0:499] to frame1 reverse B[102:601]. D parity, Fin662 temporary lifecycle,
frame geometry, physical realization and the full multiplication theorem remain separate.
Prepared with OpenAI assistance; selected supplier and accepted generic attribution retained. -/
namespace CurrentMain.CurrentPR589CPrefix
open BitXor BitXorReversal
set_option Elab.async false
abbrev Register := Fin 661
abbrev State := BitXor.State Register
abbrev RawGate := Nat × Nat × List Nat
abbrev IsTarget := CurrentPR589PhaseBXor.IsTarget
instance (r : Register) : Decidable (IsTarget r) := inferInstanceAs (Decidable (111 ≤ r.val ∧ r.val < 222))
abbrev encodeGate := CurrentPR589PhaseBXor.encodeGate

def rawFrameOne (g : RawGate) : RawGate := (1, g.2.1, g.2.2)

/-- The sole fresh finite predicate, preserving ordered multiplicity and frame1. -/
theorem raw_cleanup_binding : Data.phaseCPrefix =
    CurrentPR589B.Data.offTargetMiddle.reverse.map rawFrameOne := by
  decide +kernel

attribute [local irreducible] Data.phaseCPrefix CurrentPR589B.Data.phaseB
  CurrentPR589B.Data.firstTargets CurrentPR589B.Data.offTargetMiddle CurrentPR589B.Data.lastTargets
  CurrentPR589PhaseBXor.decodedPhaseB CurrentPR589ACJoin.assembledA CurrentPR589ACJoin.assembledCSuffix

def firstDecoded : List (Gate Register) := CurrentPR589PhaseBXor.decodedPhaseB.take 102
def middleDecoded : List (Gate Register) := (CurrentPR589PhaseBXor.decodedPhaseB.drop 102).take 499
def lastDecoded : List (Gate Register) := (CurrentPR589PhaseBXor.decodedPhaseB.drop 102).drop 499

def frameOne (g : Gate Register) : Gate Register :=
  { frame := 1, dst := g.dst, sources := g.sources }
def decodedCPrefix : List (Gate Register) := middleDecoded.reverse.map frameOne
def assembledC : List (Gate Register) := decodedCPrefix ++ CurrentPR589ACJoin.assembledCSuffix

private theorem raw_tail : CurrentPR589B.Data.phaseB.drop 102 =
    CurrentPR589B.Data.offTargetMiddle ++ CurrentPR589B.Data.lastTargets := by
  rw [CurrentPR589B.band_order, List.append_assoc]
  exact List.drop_left' CurrentPR589B.band_lengths.1

theorem ordered_first_binding : firstDecoded.map encodeGate = CurrentPR589B.Data.firstTargets := by
  unfold firstDecoded
  rw [List.map_take, CurrentPR589PhaseBXor.ordered_word_binding,
    CurrentPR589B.band_order, List.append_assoc]
  exact List.take_left' CurrentPR589B.band_lengths.1

theorem ordered_middle_binding : middleDecoded.map encodeGate = CurrentPR589B.Data.offTargetMiddle := by
  unfold middleDecoded
  rw [List.map_take, List.map_drop, CurrentPR589PhaseBXor.ordered_word_binding, raw_tail]
  exact List.take_left' CurrentPR589B.band_lengths.2.1

theorem ordered_last_binding : lastDecoded.map encodeGate = CurrentPR589B.Data.lastTargets := by
  unfold lastDecoded
  rw [List.map_drop, List.map_drop, CurrentPR589PhaseBXor.ordered_word_binding, raw_tail]
  exact List.drop_left' CurrentPR589B.band_lengths.2.1

theorem decoded_B_split : CurrentPR589PhaseBXor.decodedPhaseB =
    firstDecoded ++ (middleDecoded ++ lastDecoded) := by
  unfold firstDecoded middleDecoded lastDecoded
  rw [List.take_append_drop, List.take_append_drop]

theorem execute_B_split (s : State) : CurrentPR589PhaseBXor.executeB s =
    run lastDecoded (run middleDecoded (run firstDecoded s)) := by
  unfold CurrentPR589PhaseBXor.executeB
  rw [decoded_B_split, run_append, run_append]

private theorem middle_subset (g : Gate Register) (hg : g ∈ middleDecoded) :
    g ∈ CurrentPR589PhaseBXor.decodedPhaseB :=
  List.mem_of_mem_drop (List.mem_of_mem_take hg)

/-- Inherited exact write counts, without redeciding the B literals. -/
theorem middle_write_counts :
    (CurrentPR589B.Data.offTargetMiddle.filter (fun g => decide (g.2.1 < 111))).length = 483 ∧
    (CurrentPR589B.Data.offTargetMiddle.filter (fun g => decide (222 ≤ g.2.1))).length = 16 :=
  CurrentPR589B.middle_write_counts

theorem middle_no_self_reads (g : Gate Register) (hg : g ∈ middleDecoded) :
    g.dst ∉ g.sources := by
  have he : encodeGate g ∈ CurrentPR589B.Data.phaseB := by
    rw [← CurrentPR589PhaseBXor.ordered_word_binding]
    exact List.mem_map.mpr ⟨g, middle_subset g hg, rfl⟩
  intro hs
  have hd : g.dst.val ∈ g.sources.map Fin.val := List.mem_map.mpr ⟨g.dst, hs, rfl⟩
  have h := of_decide_eq_true ((List.all_eq_true.mp
    ((List.all_eq_true.mp CurrentPR589B.no_self_reads) (encodeGate g) he)) g.dst.val hd)
  exact h rfl

theorem middle_no_target_reads (g : Gate Register) (hg : g ∈ middleDecoded) :
    ∀ r ∈ g.sources, ¬ IsTarget r :=
  (CurrentPR589PhaseBXor.decoded_gate_properties g (middle_subset g hg)).2

theorem middle_no_target_writes (g : Gate Register) (hg : g ∈ middleDecoded) :
    ¬ IsTarget g.dst := by
  have he : encodeGate g ∈ CurrentPR589B.Data.offTargetMiddle := by
    rw [← ordered_middle_binding]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have h := (of_decide_eq_true ((List.all_eq_true.mp CurrentPR589B.middle_off_target_band)
    (encodeGate g) he)).1
  change ¬ (111 ≤ g.dst.val ∧ g.dst.val < 222)
  rcases h with hlt | hge
  · exact fun ht => (Nat.not_le_of_lt hlt) ht.1
  · exact fun ht => (Nat.not_le_of_lt ht.2) hge

private theorem first_targets (g : Gate Register) (hg : g ∈ firstDecoded) : IsTarget g.dst := by
  have he : encodeGate g ∈ CurrentPR589B.Data.firstTargets := by
    rw [← ordered_first_binding]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp
    ((List.all_eq_true.mp CurrentPR589B.first_target_band) (encodeGate g) he)).1
  exact ⟨h.1, h.2.1⟩

private theorem last_targets (g : Gate Register) (hg : g ∈ lastDecoded) : IsTarget g.dst := by
  have he : encodeGate g ∈ CurrentPR589B.Data.lastTargets := by
    rw [← ordered_last_binding]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have h := of_decide_eq_true (Bool.and_eq_true_iff.mp
    ((List.all_eq_true.mp CurrentPR589B.last_target_band) (encodeGate g) he)).1
  exact ⟨h.1, h.2.1⟩

theorem first_preserves_off_target (s : State) (r : Register) (hr : ¬ IsTarget r) :
    run firstDecoded s r = s r :=
  run_off_target IsTarget firstDecoded first_targets s r hr

theorem last_preserves_off_target (s : State) (r : Register) (hr : ¬ IsTarget r) :
    run lastDecoded s r = s r :=
  run_off_target IsTarget lastDecoded last_targets s r hr

theorem ordered_C_prefix_binding : decodedCPrefix.map encodeGate = Data.phaseCPrefix := by
  calc
    decodedCPrefix.map encodeGate = (middleDecoded.map encodeGate).reverse.map rawFrameOne := by
      simp only [decodedCPrefix, List.map_map, List.map_reverse, Function.comp_def,
        encodeGate, CurrentPR589PhaseBXor.encodeGate, frameOne, rawFrameOne]
    _ = CurrentPR589B.Data.offTargetMiddle.reverse.map rawFrameOne := by rw [ordered_middle_binding]
    _ = Data.phaseCPrefix := raw_cleanup_binding.symm

theorem prefix_runs_reverse (s : State) : run decodedCPrefix s = run middleDecoded.reverse s := by
  have h : decodedCPrefix.map scalarize = middleDecoded.reverse.map scalarize := by
    simp only [decodedCPrefix, List.map_map, Function.comp_def, frameOne, scalarize]
    rfl
  exact BitXorChunkComposition.run_of_reverse_binding middleDecoded decodedCPrefix h s

/-- Exact whole C syntax, assembled from independently source-bound contiguous pieces. -/
theorem ordered_C_binding : assembledC.map encodeGate =
    Data.phaseCPrefix ++ CurrentPR589ACJoin.rawCSuffix := by
  unfold assembledC
  rw [List.map_append, ordered_C_prefix_binding]
  exact congrArg (fun xs => Data.phaseCPrefix ++ xs) CurrentPR589ACJoin.ordered_C_suffix_binding

/-- Actual first/last B target-only maps discharge both generic cleanup hypotheses. -/
theorem selected_off_target_cleanup (s : State) (r : Register) (hr : ¬ IsTarget r) :
    run assembledC (CurrentPR589PhaseBXor.executeB (run CurrentPR589ACJoin.assembledA s)) r = s r := by
  unfold assembledC
  rw [run_append, CurrentPR589ACJoin.cleanup_runs_reverse, prefix_runs_reverse, execute_B_split]
  exact BitXorTwoLevelCleanup.two_level_cleanup_off_target IsTarget
    CurrentPR589ACJoin.assembledA middleDecoded
    CurrentPR589ACJoin.decoded_no_self_reads middle_no_self_reads
    CurrentPR589ACJoin.decoded_no_target_reads middle_no_target_reads
    (run firstDecoded) (run lastDecoded) first_preserves_off_target last_preserves_off_target s r hr

/-- Cleanup retains the target value produced by actual A then B; D is still separate. -/
theorem selected_target_value (s : State) (r : Register) (hr : IsTarget r) :
    run assembledC (CurrentPR589PhaseBXor.executeB (run CurrentPR589ACJoin.assembledA s)) r =
      CurrentPR589PhaseBXor.executeB (run CurrentPR589ACJoin.assembledA s) r := by
  unfold assembledC
  rw [run_append, CurrentPR589ACJoin.cleanup_runs_reverse, prefix_runs_reverse]
  exact BitXorTwoLevelCleanup.two_level_target_value IsTarget
    CurrentPR589ACJoin.assembledA middleDecoded
    CurrentPR589ACJoin.decoded_no_target_writes middle_no_target_writes _ r hr

end CurrentMain.CurrentPR589CPrefix
#print axioms CurrentMain.CurrentPR589CPrefix.raw_cleanup_binding
#print axioms CurrentMain.CurrentPR589CPrefix.ordered_first_binding
#print axioms CurrentMain.CurrentPR589CPrefix.ordered_middle_binding
#print axioms CurrentMain.CurrentPR589CPrefix.ordered_last_binding
#print axioms CurrentMain.CurrentPR589CPrefix.decoded_B_split
#print axioms CurrentMain.CurrentPR589CPrefix.execute_B_split
#print axioms CurrentMain.CurrentPR589CPrefix.middle_write_counts
#print axioms CurrentMain.CurrentPR589CPrefix.middle_no_self_reads
#print axioms CurrentMain.CurrentPR589CPrefix.middle_no_target_reads
#print axioms CurrentMain.CurrentPR589CPrefix.middle_no_target_writes
#print axioms CurrentMain.CurrentPR589CPrefix.first_preserves_off_target
#print axioms CurrentMain.CurrentPR589CPrefix.last_preserves_off_target
#print axioms CurrentMain.CurrentPR589CPrefix.ordered_C_prefix_binding
#print axioms CurrentMain.CurrentPR589CPrefix.prefix_runs_reverse
#print axioms CurrentMain.CurrentPR589CPrefix.ordered_C_binding
#print axioms CurrentMain.CurrentPR589CPrefix.selected_off_target_cleanup
#print axioms CurrentMain.CurrentPR589CPrefix.selected_target_value
