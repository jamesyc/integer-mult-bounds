import BitXorChunkComposition

/-! Two nested off-target words separated by arbitrary target-only maps.
This reuses accepted agreement, reversal and scalarized-binding facts, without
new XOR induction. No actual A/C literals, scatter lifecycle, D compensation,
physical realization or selected full-word theorem is asserted.
Prepared with OpenAI assistance; prior BitXor attribution retained. -/
namespace CurrentMain.BitXorTwoLevelCleanup
open BitXor BitXorReversal BitXorChunkComposition
set_option Elab.async false
variable {Reg : Type} [DecidableEq Reg]
variable (target : Reg → Prop) [DecidablePred target]

/-- Each middle map changes only targets; source/helper values may be arbitrary. -/
theorem two_level_cleanup_off_target (a z : List (Gate Reg))
    (hselfA : ∀ g ∈ a, g.dst ∉ g.sources)
    (hselfZ : ∀ g ∈ z, g.dst ∉ g.sources)
    (hreadsA : ∀ g ∈ a, ∀ r ∈ g.sources, ¬ target r)
    (hreadsZ : ∀ g ∈ z, ∀ r ∈ g.sources, ¬ target r)
    (M0 M1 : State Reg → State Reg)
    (hM0 : ∀ s r, ¬ target r → M0 s r = s r)
    (hM1 : ∀ s r, ¬ target r → M1 s r = s r)
    (s : State Reg) (r : Reg) (hr : ¬ target r) :
    run a.reverse (run z.reverse (M1 (run z (M0 (run a s))))) r = s r := by
  have hZ : ∀ q, ¬ target q →
      run z.reverse (M1 (run z (M0 (run a s)))) q = M0 (run a s) q := by
    intro q hq
    exact cleanup_off_target target z hselfZ hreadsZ M1 hM1 (M0 (run a s)) q hq
  have hreverseA : ∀ g ∈ a.reverse, ∀ q ∈ g.sources, ¬ target q := by
    intro g hg
    exact hreadsA g (List.mem_reverse.mp hg)
  calc
    run a.reverse (run z.reverse (M1 (run z (M0 (run a s))))) r =
        run a.reverse (M0 (run a s)) r :=
      run_agree_off_target target a.reverse hreverseA _ _ hZ r hr
    _ = s r := cleanup_off_target target a hselfA hreadsA M0 hM0 s r hr

/-- Off-target cleanup leaves the complete intervening target contribution intact. -/
theorem two_level_target_value (a z : List (Gate Reg))
    (hdstA : ∀ g ∈ a, ¬ target g.dst)
    (hdstZ : ∀ g ∈ z, ¬ target g.dst)
    (s : State Reg) (r : Reg) (hr : target r) :
    run a.reverse (run z.reverse s) r = s r := by
  calc
    run a.reverse (run z.reverse s) r = run z.reverse s r :=
      run_off_target (fun q => ¬ target q) a.reverse
        (fun g hg => hdstA g (List.mem_reverse.mp hg))
        (run z.reverse s) r (fun hn => hn hr)
    _ = s r := run_off_target (fun q => ¬ target q) z.reverse
      (fun g hg => hdstZ g (List.mem_reverse.mp hg)) s r (fun hn => hn hr)

/-- Actual cleanup chunks may change frame metadata, but need exact scalar bindings. -/
theorem bound_two_level_cleanup (a z ca cz : List (Gate Reg))
    (ha : ca.map scalarize = a.reverse.map scalarize)
    (hz : cz.map scalarize = z.reverse.map scalarize)
    (hselfA : ∀ g ∈ a, g.dst ∉ g.sources)
    (hselfZ : ∀ g ∈ z, g.dst ∉ g.sources)
    (hreadsA : ∀ g ∈ a, ∀ r ∈ g.sources, ¬ target r)
    (hreadsZ : ∀ g ∈ z, ∀ r ∈ g.sources, ¬ target r)
    (M0 M1 : State Reg → State Reg)
    (hM0 : ∀ s r, ¬ target r → M0 s r = s r)
    (hM1 : ∀ s r, ¬ target r → M1 s r = s r)
    (s : State Reg) (r : Reg) (hr : ¬ target r) :
    run (cz ++ ca) (M1 (run z (M0 (run a s)))) r = s r := by
  rw [run_append, run_of_reverse_binding a ca ha, run_of_reverse_binding z cz hz]
  exact two_level_cleanup_off_target target a z hselfA hselfZ hreadsA hreadsZ
    M0 M1 hM0 hM1 s r hr

theorem bound_two_level_target_value (a z ca cz : List (Gate Reg))
    (ha : ca.map scalarize = a.reverse.map scalarize)
    (hz : cz.map scalarize = z.reverse.map scalarize)
    (hdstA : ∀ g ∈ a, ¬ target g.dst)
    (hdstZ : ∀ g ∈ z, ¬ target g.dst)
    (s : State Reg) (r : Reg) (hr : target r) :
    run (cz ++ ca) s r = s r := by
  rw [run_append, run_of_reverse_binding a ca ha, run_of_reverse_binding z cz hz]
  exact two_level_target_value target a z hdstA hdstZ s r hr

end CurrentMain.BitXorTwoLevelCleanup
#print axioms CurrentMain.BitXorTwoLevelCleanup.two_level_cleanup_off_target
#print axioms CurrentMain.BitXorTwoLevelCleanup.two_level_target_value
#print axioms CurrentMain.BitXorTwoLevelCleanup.bound_two_level_cleanup
#print axioms CurrentMain.BitXorTwoLevelCleanup.bound_two_level_target_value
