import BitXorReversal

/-!
Symbolic two-chunk composition for the accepted ordered Boolean XOR interpreter.
The cleanup chunks run in reverse chunk order. Their frame-erased words are
bound to the gate-wise reversals, without reversing any gate's operand list.
Only existing run/reversal/conditional-cleanup theorems are reused here.
No selected literal word, cumulative finite coverage, D compensation, physical
frame interpretation or multiplier theorem is supplied by these generic facts.
Prepared with OpenAI assistance; Lean core and prior BitXor attribution retained.
-/
namespace CurrentMain.BitXorChunkComposition
open BitXor BitXorReversal
set_option Elab.async false
variable {Reg : Type} [DecidableEq Reg]

private theorem property_append (P : Gate Reg → Prop)
    (a b : List (Gate Reg))
    (ha : ∀ g ∈ a, P g) (hb : ∀ g ∈ b, P g) :
    ∀ g ∈ a ++ b, P g := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact ha g h
  · exact hb g h

/-- Combine exact child reversal bindings in the required reverse chunk order. -/
theorem scalarized_reverse_append (a b ca cb : List (Gate Reg))
    (ha : ca.map scalarize = a.reverse.map scalarize)
    (hb : cb.map scalarize = b.reverse.map scalarize) :
    (cb ++ ca).map scalarize = (a ++ b).reverse.map scalarize := by
  simp only [List.map_append, List.reverse_append, ha, hb]

/-- A bound cleanup word has exactly the accepted reverse-word scalar action. -/
theorem run_of_reverse_binding (a c : List (Gate Reg))
    (h : c.map scalarize = a.reverse.map scalarize) (s : State Reg) :
    run c s = run a.reverse s := by
  calc
    run c s = run (c.map scalarize) s := (run_scalarize c s).symm
    _ = run (a.reverse.map scalarize) s := congrArg (fun gs => run gs s) h
    _ = run a.reverse s := run_scalarize a.reverse s

/-- Two exact child bindings and their no-self-read facts give an arbitrary-state
inverse. The gate or operand literals are not evaluated by this proof. -/
theorem append_inverse (a b ca cb : List (Gate Reg))
    (ha : ca.map scalarize = a.reverse.map scalarize)
    (hb : cb.map scalarize = b.reverse.map scalarize)
    (hselfA : ∀ g ∈ a, g.dst ∉ g.sources)
    (hselfB : ∀ g ∈ b, g.dst ∉ g.sources) (s : State Reg) :
    run (cb ++ ca) (run (a ++ b) s) = s := by
  calc
    run (cb ++ ca) (run (a ++ b) s) =
        run (a ++ b).reverse (run (a ++ b) s) :=
      run_of_reverse_binding (a ++ b) (cb ++ ca)
        (scalarized_reverse_append a b ca cb ha hb) _
    _ = s := run_reverse_cancel (a ++ b)
      (property_append (fun g => g.dst ∉ g.sources) a b hselfA hselfB) s

variable (target : Reg → Prop) [DecidablePred target]

/-- Off-target restoration still requires that the middle map change only targets.
No clean-input premise or vanishing target contribution is inserted. -/
theorem append_cleanup_off_target (a b ca cb : List (Gate Reg))
    (ha : ca.map scalarize = a.reverse.map scalarize)
    (hb : cb.map scalarize = b.reverse.map scalarize)
    (hselfA : ∀ g ∈ a, g.dst ∉ g.sources)
    (hselfB : ∀ g ∈ b, g.dst ∉ g.sources)
    (hreadsA : ∀ g ∈ a, ∀ r ∈ g.sources, ¬ target r)
    (hreadsB : ∀ g ∈ b, ∀ r ∈ g.sources, ¬ target r)
    (middle : State Reg → State Reg)
    (hmiddle : ∀ s r, ¬ target r → middle s r = s r)
    (s : State Reg) (r : Reg) (hr : ¬ target r) :
    run (cb ++ ca) (middle (run (a ++ b) s)) r = s r := by
  calc
    run (cb ++ ca) (middle (run (a ++ b) s)) r =
        run (a ++ b).reverse (middle (run (a ++ b) s)) r :=
      congrFun (run_of_reverse_binding (a ++ b) (cb ++ ca)
        (scalarized_reverse_append a b ca cb ha hb) _) r
    _ = s r := cleanup_off_target target (a ++ b)
      (property_append (fun g => g.dst ∉ g.sources) a b hselfA hselfB)
      (property_append (fun g => ∀ q ∈ g.sources, ¬ target q) a b hreadsA hreadsB)
      middle hmiddle s r hr

/-- With target destinations excluded, cleanup preserves the middle target value;
this does not identify that value with a desired shear or zero. -/
theorem append_cleanup_target_value (a b ca cb : List (Gate Reg))
    (ha : ca.map scalarize = a.reverse.map scalarize)
    (hb : cb.map scalarize = b.reverse.map scalarize)
    (hdstA : ∀ g ∈ a, ¬ target g.dst)
    (hdstB : ∀ g ∈ b, ¬ target g.dst)
    (middle : State Reg → State Reg) (s : State Reg)
    (r : Reg) (hr : target r) :
    run (cb ++ ca) (middle (run (a ++ b) s)) r =
      middle (run (a ++ b) s) r := by
  calc
    run (cb ++ ca) (middle (run (a ++ b) s)) r =
        run (a ++ b).reverse (middle (run (a ++ b) s)) r :=
      congrFun (run_of_reverse_binding (a ++ b) (cb ++ ca)
        (scalarized_reverse_append a b ca cb ha hb) _) r
    _ = middle (run (a ++ b) s) r := cleanup_target_value target (a ++ b)
      (property_append (fun g => ¬ target g.dst) a b hdstA hdstB) middle s r hr

end CurrentMain.BitXorChunkComposition
#print axioms CurrentMain.BitXorChunkComposition.scalarized_reverse_append
#print axioms CurrentMain.BitXorChunkComposition.run_of_reverse_binding
#print axioms CurrentMain.BitXorChunkComposition.append_inverse
#print axioms CurrentMain.BitXorChunkComposition.append_cleanup_off_target
#print axioms CurrentMain.BitXorChunkComposition.append_cleanup_target_value
