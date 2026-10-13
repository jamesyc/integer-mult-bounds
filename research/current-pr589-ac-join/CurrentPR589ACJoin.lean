import CurrentPR589AC128Check
import CurrentPR589AC001Check
import CurrentPR589AC002Check
import CurrentPR589AC003Check
import CurrentPR589AC004Check
import CurrentPR589AC005Check
import CurrentPR589AC006Check
import CurrentPR589AC007Check
import CurrentPR589AC008Check
import CurrentPR589AC009Check
import CurrentPR589AC010Check
import CurrentPR589AC011Check
import CurrentPR589AC012Check
import CurrentPR589AC013Check
import CurrentPR589AC014Check
import CurrentPR589AC015Check
import CurrentPR589AC016Check

/-! Symbolic current PR589 A/C-suffix composition.
All17 exact windows cover A[0:2075] and only C[499:2574]. This source imports
accepted window predicates instead of replaying literals. The 499-gate C prefix,
actual B middle-map conditions, D parity, Fin662 COPY lifecycle and physical
frame/provider realization remain separate. In particular B writes source
registers and helpers465/466/468, so B does not satisfy the target-only premise.
Arbitrary original661 bits are allowed. No whole multiplication claim.
Prepared with OpenAI assistance; PR589 supplier and accepted BitXor attribution retained.
-/
namespace CurrentMain.CurrentPR589ACJoin
open BitXor BitXorReversal
set_option Elab.async false
abbrev Register := Fin 661
abbrev State := BitXor.State Register
abbrev RawGate := Nat × Nat × List Nat
abbrev IsTarget := CurrentPR589AC128.IsTarget
instance (r : Register) : Decidable (IsTarget r) := inferInstanceAs (Decidable (111 ≤ r.val ∧ r.val < 222))
abbrev encodeGate := CurrentPR589AC128.encodeGate

attribute [local irreducible] CurrentPR589AC128.decodedA CurrentPR589AC128.decodedC CurrentPR589AC128.Data.phaseA CurrentPR589AC128.Data.phaseC CurrentPR589AC001.decodedA CurrentPR589AC001.decodedC CurrentPR589AC001.Data.phaseA CurrentPR589AC001.Data.phaseC CurrentPR589AC002.decodedA CurrentPR589AC002.decodedC CurrentPR589AC002.Data.phaseA CurrentPR589AC002.Data.phaseC CurrentPR589AC003.decodedA CurrentPR589AC003.decodedC CurrentPR589AC003.Data.phaseA CurrentPR589AC003.Data.phaseC CurrentPR589AC004.decodedA CurrentPR589AC004.decodedC CurrentPR589AC004.Data.phaseA CurrentPR589AC004.Data.phaseC CurrentPR589AC005.decodedA CurrentPR589AC005.decodedC CurrentPR589AC005.Data.phaseA CurrentPR589AC005.Data.phaseC CurrentPR589AC006.decodedA CurrentPR589AC006.decodedC CurrentPR589AC006.Data.phaseA CurrentPR589AC006.Data.phaseC CurrentPR589AC007.decodedA CurrentPR589AC007.decodedC CurrentPR589AC007.Data.phaseA CurrentPR589AC007.Data.phaseC CurrentPR589AC008.decodedA CurrentPR589AC008.decodedC CurrentPR589AC008.Data.phaseA CurrentPR589AC008.Data.phaseC CurrentPR589AC009.decodedA CurrentPR589AC009.decodedC CurrentPR589AC009.Data.phaseA CurrentPR589AC009.Data.phaseC CurrentPR589AC010.decodedA CurrentPR589AC010.decodedC CurrentPR589AC010.Data.phaseA CurrentPR589AC010.Data.phaseC CurrentPR589AC011.decodedA CurrentPR589AC011.decodedC CurrentPR589AC011.Data.phaseA CurrentPR589AC011.Data.phaseC CurrentPR589AC012.decodedA CurrentPR589AC012.decodedC CurrentPR589AC012.Data.phaseA CurrentPR589AC012.Data.phaseC CurrentPR589AC013.decodedA CurrentPR589AC013.decodedC CurrentPR589AC013.Data.phaseA CurrentPR589AC013.Data.phaseC CurrentPR589AC014.decodedA CurrentPR589AC014.decodedC CurrentPR589AC014.Data.phaseA CurrentPR589AC014.Data.phaseC CurrentPR589AC015.decodedA CurrentPR589AC015.decodedC CurrentPR589AC015.Data.phaseA CurrentPR589AC015.Data.phaseC CurrentPR589AC016.decodedA CurrentPR589AC016.decodedC CurrentPR589AC016.Data.phaseA CurrentPR589AC016.Data.phaseC

def assembledA : List (Gate Register) := ((((CurrentPR589AC128.decodedA ++ CurrentPR589AC001.decodedA) ++ (CurrentPR589AC002.decodedA ++ CurrentPR589AC003.decodedA)) ++ ((CurrentPR589AC004.decodedA ++ CurrentPR589AC005.decodedA) ++ (CurrentPR589AC006.decodedA ++ CurrentPR589AC007.decodedA))) ++ (((CurrentPR589AC008.decodedA ++ CurrentPR589AC009.decodedA) ++ (CurrentPR589AC010.decodedA ++ CurrentPR589AC011.decodedA)) ++ ((CurrentPR589AC012.decodedA ++ CurrentPR589AC013.decodedA) ++ (CurrentPR589AC014.decodedA ++ (CurrentPR589AC015.decodedA ++ CurrentPR589AC016.decodedA)))))
def assembledCSuffix : List (Gate Register) := ((((CurrentPR589AC016.decodedC ++ CurrentPR589AC015.decodedC) ++ (CurrentPR589AC014.decodedC ++ CurrentPR589AC013.decodedC)) ++ ((CurrentPR589AC012.decodedC ++ CurrentPR589AC011.decodedC) ++ (CurrentPR589AC010.decodedC ++ CurrentPR589AC009.decodedC))) ++ (((CurrentPR589AC008.decodedC ++ CurrentPR589AC007.decodedC) ++ (CurrentPR589AC006.decodedC ++ CurrentPR589AC005.decodedC)) ++ ((CurrentPR589AC004.decodedC ++ CurrentPR589AC003.decodedC) ++ (CurrentPR589AC002.decodedC ++ (CurrentPR589AC001.decodedC ++ CurrentPR589AC128.decodedC)))))
def rawA : List RawGate := ((((CurrentPR589AC128.Data.phaseA ++ CurrentPR589AC001.Data.phaseA) ++ (CurrentPR589AC002.Data.phaseA ++ CurrentPR589AC003.Data.phaseA)) ++ ((CurrentPR589AC004.Data.phaseA ++ CurrentPR589AC005.Data.phaseA) ++ (CurrentPR589AC006.Data.phaseA ++ CurrentPR589AC007.Data.phaseA))) ++ (((CurrentPR589AC008.Data.phaseA ++ CurrentPR589AC009.Data.phaseA) ++ (CurrentPR589AC010.Data.phaseA ++ CurrentPR589AC011.Data.phaseA)) ++ ((CurrentPR589AC012.Data.phaseA ++ CurrentPR589AC013.Data.phaseA) ++ (CurrentPR589AC014.Data.phaseA ++ (CurrentPR589AC015.Data.phaseA ++ CurrentPR589AC016.Data.phaseA)))))
def rawCSuffix : List RawGate := ((((CurrentPR589AC016.Data.phaseC ++ CurrentPR589AC015.Data.phaseC) ++ (CurrentPR589AC014.Data.phaseC ++ CurrentPR589AC013.Data.phaseC)) ++ ((CurrentPR589AC012.Data.phaseC ++ CurrentPR589AC011.Data.phaseC) ++ (CurrentPR589AC010.Data.phaseC ++ CurrentPR589AC009.Data.phaseC))) ++ (((CurrentPR589AC008.Data.phaseC ++ CurrentPR589AC007.Data.phaseC) ++ (CurrentPR589AC006.Data.phaseC ++ CurrentPR589AC005.Data.phaseC)) ++ ((CurrentPR589AC004.Data.phaseC ++ CurrentPR589AC003.Data.phaseC) ++ (CurrentPR589AC002.Data.phaseC ++ (CurrentPR589AC001.Data.phaseC ++ CurrentPR589AC128.Data.phaseC)))))

private theorem property_append (P : Gate Register → Prop)
    (a b : List (Gate Register))
    (ha : ∀ g ∈ a, P g) (hb : ∀ g ∈ b, P g) :
    ∀ g ∈ a ++ b, P g := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ha g h
  · exact hb g h

/-- Ordered binding to the exact concatenation of source-bound A windows. -/
theorem ordered_A_binding : assembledA.map encodeGate = rawA := by
  unfold assembledA rawA
  simp only [List.map_append]
  change (((((CurrentPR589AC128.decodedA.map CurrentPR589AC128.encodeGate) ++ (CurrentPR589AC001.decodedA.map CurrentPR589AC001.encodeGate)) ++ ((CurrentPR589AC002.decodedA.map CurrentPR589AC002.encodeGate) ++ (CurrentPR589AC003.decodedA.map CurrentPR589AC003.encodeGate))) ++ (((CurrentPR589AC004.decodedA.map CurrentPR589AC004.encodeGate) ++ (CurrentPR589AC005.decodedA.map CurrentPR589AC005.encodeGate)) ++ ((CurrentPR589AC006.decodedA.map CurrentPR589AC006.encodeGate) ++ (CurrentPR589AC007.decodedA.map CurrentPR589AC007.encodeGate)))) ++ ((((CurrentPR589AC008.decodedA.map CurrentPR589AC008.encodeGate) ++ (CurrentPR589AC009.decodedA.map CurrentPR589AC009.encodeGate)) ++ ((CurrentPR589AC010.decodedA.map CurrentPR589AC010.encodeGate) ++ (CurrentPR589AC011.decodedA.map CurrentPR589AC011.encodeGate))) ++ (((CurrentPR589AC012.decodedA.map CurrentPR589AC012.encodeGate) ++ (CurrentPR589AC013.decodedA.map CurrentPR589AC013.encodeGate)) ++ ((CurrentPR589AC014.decodedA.map CurrentPR589AC014.encodeGate) ++ ((CurrentPR589AC015.decodedA.map CurrentPR589AC015.encodeGate) ++ (CurrentPR589AC016.decodedA.map CurrentPR589AC016.encodeGate)))))) = ((((CurrentPR589AC128.Data.phaseA ++ CurrentPR589AC001.Data.phaseA) ++ (CurrentPR589AC002.Data.phaseA ++ CurrentPR589AC003.Data.phaseA)) ++ ((CurrentPR589AC004.Data.phaseA ++ CurrentPR589AC005.Data.phaseA) ++ (CurrentPR589AC006.Data.phaseA ++ CurrentPR589AC007.Data.phaseA))) ++ (((CurrentPR589AC008.Data.phaseA ++ CurrentPR589AC009.Data.phaseA) ++ (CurrentPR589AC010.Data.phaseA ++ CurrentPR589AC011.Data.phaseA)) ++ ((CurrentPR589AC012.Data.phaseA ++ CurrentPR589AC013.Data.phaseA) ++ (CurrentPR589AC014.Data.phaseA ++ (CurrentPR589AC015.Data.phaseA ++ CurrentPR589AC016.Data.phaseA)))))
  rw [CurrentPR589AC128.ordered_A_binding, CurrentPR589AC001.ordered_A_binding, CurrentPR589AC002.ordered_A_binding, CurrentPR589AC003.ordered_A_binding, CurrentPR589AC004.ordered_A_binding, CurrentPR589AC005.ordered_A_binding, CurrentPR589AC006.ordered_A_binding, CurrentPR589AC007.ordered_A_binding, CurrentPR589AC008.ordered_A_binding, CurrentPR589AC009.ordered_A_binding, CurrentPR589AC010.ordered_A_binding, CurrentPR589AC011.ordered_A_binding, CurrentPR589AC012.ordered_A_binding, CurrentPR589AC013.ordered_A_binding, CurrentPR589AC014.ordered_A_binding, CurrentPR589AC015.ordered_A_binding, CurrentPR589AC016.ordered_A_binding]

/-- Ordered binding to C[499:2574], with reverse chunk order preserved. -/
theorem ordered_C_suffix_binding : assembledCSuffix.map encodeGate = rawCSuffix := by
  unfold assembledCSuffix rawCSuffix
  simp only [List.map_append]
  change (((((CurrentPR589AC016.decodedC.map CurrentPR589AC016.encodeGate) ++ (CurrentPR589AC015.decodedC.map CurrentPR589AC015.encodeGate)) ++ ((CurrentPR589AC014.decodedC.map CurrentPR589AC014.encodeGate) ++ (CurrentPR589AC013.decodedC.map CurrentPR589AC013.encodeGate))) ++ (((CurrentPR589AC012.decodedC.map CurrentPR589AC012.encodeGate) ++ (CurrentPR589AC011.decodedC.map CurrentPR589AC011.encodeGate)) ++ ((CurrentPR589AC010.decodedC.map CurrentPR589AC010.encodeGate) ++ (CurrentPR589AC009.decodedC.map CurrentPR589AC009.encodeGate)))) ++ ((((CurrentPR589AC008.decodedC.map CurrentPR589AC008.encodeGate) ++ (CurrentPR589AC007.decodedC.map CurrentPR589AC007.encodeGate)) ++ ((CurrentPR589AC006.decodedC.map CurrentPR589AC006.encodeGate) ++ (CurrentPR589AC005.decodedC.map CurrentPR589AC005.encodeGate))) ++ (((CurrentPR589AC004.decodedC.map CurrentPR589AC004.encodeGate) ++ (CurrentPR589AC003.decodedC.map CurrentPR589AC003.encodeGate)) ++ ((CurrentPR589AC002.decodedC.map CurrentPR589AC002.encodeGate) ++ ((CurrentPR589AC001.decodedC.map CurrentPR589AC001.encodeGate) ++ (CurrentPR589AC128.decodedC.map CurrentPR589AC128.encodeGate)))))) = ((((CurrentPR589AC016.Data.phaseC ++ CurrentPR589AC015.Data.phaseC) ++ (CurrentPR589AC014.Data.phaseC ++ CurrentPR589AC013.Data.phaseC)) ++ ((CurrentPR589AC012.Data.phaseC ++ CurrentPR589AC011.Data.phaseC) ++ (CurrentPR589AC010.Data.phaseC ++ CurrentPR589AC009.Data.phaseC))) ++ (((CurrentPR589AC008.Data.phaseC ++ CurrentPR589AC007.Data.phaseC) ++ (CurrentPR589AC006.Data.phaseC ++ CurrentPR589AC005.Data.phaseC)) ++ ((CurrentPR589AC004.Data.phaseC ++ CurrentPR589AC003.Data.phaseC) ++ (CurrentPR589AC002.Data.phaseC ++ (CurrentPR589AC001.Data.phaseC ++ CurrentPR589AC128.Data.phaseC)))))
  rw [CurrentPR589AC016.ordered_C_binding, CurrentPR589AC015.ordered_C_binding, CurrentPR589AC014.ordered_C_binding, CurrentPR589AC013.ordered_C_binding, CurrentPR589AC012.ordered_C_binding, CurrentPR589AC011.ordered_C_binding, CurrentPR589AC010.ordered_C_binding, CurrentPR589AC009.ordered_C_binding, CurrentPR589AC008.ordered_C_binding, CurrentPR589AC007.ordered_C_binding, CurrentPR589AC006.ordered_C_binding, CurrentPR589AC005.ordered_C_binding, CurrentPR589AC004.ordered_C_binding, CurrentPR589AC003.ordered_C_binding, CurrentPR589AC002.ordered_C_binding, CurrentPR589AC001.ordered_C_binding, CurrentPR589AC128.ordered_C_binding]

theorem decoded_no_self_reads : ∀ g ∈ assembledA, g.dst ∉ g.sources := by
  exact (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC128.decoded_no_self_reads CurrentPR589AC001.decoded_no_self_reads) (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC002.decoded_no_self_reads CurrentPR589AC003.decoded_no_self_reads)) (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC004.decoded_no_self_reads CurrentPR589AC005.decoded_no_self_reads) (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC006.decoded_no_self_reads CurrentPR589AC007.decoded_no_self_reads))) (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC008.decoded_no_self_reads CurrentPR589AC009.decoded_no_self_reads) (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC010.decoded_no_self_reads CurrentPR589AC011.decoded_no_self_reads)) (property_append (fun g => g.dst ∉ g.sources) _ _ (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC012.decoded_no_self_reads CurrentPR589AC013.decoded_no_self_reads) (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC014.decoded_no_self_reads (property_append (fun g => g.dst ∉ g.sources) _ _ CurrentPR589AC015.decoded_no_self_reads CurrentPR589AC016.decoded_no_self_reads)))))

theorem decoded_no_target_reads : ∀ g ∈ assembledA, ∀ r ∈ g.sources, ¬ IsTarget r := by
  exact (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC128.decoded_no_target_reads CurrentPR589AC001.decoded_no_target_reads) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC002.decoded_no_target_reads CurrentPR589AC003.decoded_no_target_reads)) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC004.decoded_no_target_reads CurrentPR589AC005.decoded_no_target_reads) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC006.decoded_no_target_reads CurrentPR589AC007.decoded_no_target_reads))) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC008.decoded_no_target_reads CurrentPR589AC009.decoded_no_target_reads) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC010.decoded_no_target_reads CurrentPR589AC011.decoded_no_target_reads)) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC012.decoded_no_target_reads CurrentPR589AC013.decoded_no_target_reads) (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC014.decoded_no_target_reads (property_append (fun g => ∀ r ∈ g.sources, ¬ IsTarget r) _ _ CurrentPR589AC015.decoded_no_target_reads CurrentPR589AC016.decoded_no_target_reads)))))

theorem decoded_no_target_writes : ∀ g ∈ assembledA, ¬ IsTarget g.dst := by
  exact (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC128.decoded_no_target_writes CurrentPR589AC001.decoded_no_target_writes) (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC002.decoded_no_target_writes CurrentPR589AC003.decoded_no_target_writes)) (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC004.decoded_no_target_writes CurrentPR589AC005.decoded_no_target_writes) (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC006.decoded_no_target_writes CurrentPR589AC007.decoded_no_target_writes))) (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC008.decoded_no_target_writes CurrentPR589AC009.decoded_no_target_writes) (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC010.decoded_no_target_writes CurrentPR589AC011.decoded_no_target_writes)) (property_append (fun g => ¬ IsTarget g.dst) _ _ (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC012.decoded_no_target_writes CurrentPR589AC013.decoded_no_target_writes) (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC014.decoded_no_target_writes (property_append (fun g => ¬ IsTarget g.dst) _ _ CurrentPR589AC015.decoded_no_target_writes CurrentPR589AC016.decoded_no_target_writes)))))

/-- Only seventeen opaque child executions and append/reverse laws are rewritten. -/
theorem cleanup_runs_reverse (s : State) :
    run assembledCSuffix s = run assembledA.reverse s := by
  unfold assembledCSuffix assembledA
  simp only [List.reverse_append, run_append,
    CurrentPR589AC128.cleanup_runs_reverse,
    CurrentPR589AC001.cleanup_runs_reverse,
    CurrentPR589AC002.cleanup_runs_reverse,
    CurrentPR589AC003.cleanup_runs_reverse,
    CurrentPR589AC004.cleanup_runs_reverse,
    CurrentPR589AC005.cleanup_runs_reverse,
    CurrentPR589AC006.cleanup_runs_reverse,
    CurrentPR589AC007.cleanup_runs_reverse,
    CurrentPR589AC008.cleanup_runs_reverse,
    CurrentPR589AC009.cleanup_runs_reverse,
    CurrentPR589AC010.cleanup_runs_reverse,
    CurrentPR589AC011.cleanup_runs_reverse,
    CurrentPR589AC012.cleanup_runs_reverse,
    CurrentPR589AC013.cleanup_runs_reverse,
    CurrentPR589AC014.cleanup_runs_reverse,
    CurrentPR589AC015.cleanup_runs_reverse,
    CurrentPR589AC016.cleanup_runs_reverse]

/-- Exact A followed by its bound cleanup suffix cancels on arbitrary661 bits. -/
theorem isolated_A_inverse (s : State) :
    run assembledCSuffix (run assembledA s) = s := by
  rw [cleanup_runs_reverse]
  exact run_reverse_cancel assembledA decoded_no_self_reads s

/-- This conditional statement does not instantiate the middle map with B. -/
theorem conditional_off_target_cleanup (middle : State → State)
    (hmiddle : ∀ s r, ¬ IsTarget r → middle s r = s r)
    (s : State) (r : Register) (hr : ¬ IsTarget r) :
    run assembledCSuffix (middle (run assembledA s)) r = s r := by
  rw [cleanup_runs_reverse]
  exact cleanup_off_target IsTarget assembledA decoded_no_self_reads
    decoded_no_target_reads middle hmiddle s r hr

theorem conditional_target_value (middle : State → State)
    (s : State) (r : Register) (hr : IsTarget r) :
    run assembledCSuffix (middle (run assembledA s)) r =
      middle (run assembledA s) r := by
  rw [cleanup_runs_reverse]
  exact cleanup_target_value IsTarget assembledA decoded_no_target_writes middle s r hr

end CurrentMain.CurrentPR589ACJoin
#print axioms CurrentMain.CurrentPR589ACJoin.ordered_A_binding
#print axioms CurrentMain.CurrentPR589ACJoin.ordered_C_suffix_binding
#print axioms CurrentMain.CurrentPR589ACJoin.decoded_no_self_reads
#print axioms CurrentMain.CurrentPR589ACJoin.decoded_no_target_reads
#print axioms CurrentMain.CurrentPR589ACJoin.decoded_no_target_writes
#print axioms CurrentMain.CurrentPR589ACJoin.cleanup_runs_reverse
#print axioms CurrentMain.CurrentPR589ACJoin.isolated_A_inverse
#print axioms CurrentMain.CurrentPR589ACJoin.conditional_off_target_cleanup
#print axioms CurrentMain.CurrentPR589ACJoin.conditional_target_value
