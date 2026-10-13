import Current799EntryConnection

/-!
Independent per-register entry updates, with one source-bound PR799 application.
The generic fold permits arbitrary operators on every register and arbitrary
payloads; a no-duplicate schedule applies each selected operator exactly once.
The selected source emits the entry register order 0,...,727. The eight centre
registers are outside that schedule. No full-state replay is performed.

The sixteen selected operator equations remain explicit hypotheses, as does
any equality between this formal fold and the actual Python/physical executor.
The source emitter's check_local ignores adapters and is not evidence for their
semantics. Concrete residual R(4,1) interpretation, incoming prew/hstart labels,
and both scalar destination traces remain separate supplier obligations.

Attribution: source order from the PR799 selected retained HPE emitter; generic
function-update/list APIs from Lean/Mathlib; accepted Current799EntryConnection.
Prepared with OpenAI assistance. Apache-2.0.
-/
set_option Elab.async false
namespace CurrentMain.IndependentEntryFold

variable {I M : Type*} [DecidableEq I]

/-- Chronological one-register updates; each operator reads its own current value. -/
def runUpdates (act : I → M → M) : List I → (I → M) → (I → M)
  | [], h => h
  | j :: js, h => runUpdates act js (Function.update h j (act j (h j)))

theorem runUpdates_eq_foldl (act : I → M → M) (js : List I) (h : I → M) :
    runUpdates act js h =
      js.foldl (fun s j => Function.update s j (act j (s j))) h := by
  induction js generalizing h with
  | nil => rfl
  | cons j js ih => simp only [runUpdates, List.foldl_cons, ih]

/-- Operators elsewhere cannot affect this coordinate, even if those operators
are nonlinear or the other coordinates are repeated. -/
theorem runUpdates_of_not_mem (act : I → M → M) (js : List I)
    (i : I) (hi : i ∉ js) (h : I → M) :
    runUpdates act js h i = h i := by
  induction js generalizing h with
  | nil => rfl
  | cons j js ih =>
      have hs : i ≠ j ∧ i ∉ js := by
        simpa only [List.mem_cons, not_or] using hi
      rw [runUpdates, ih hs.2, Function.update_of_ne hs.1]

/-- Membership and no duplicates suffice; operators on other coordinates are
unrestricted. There is no permutation or commutativity premise on the operators. -/
theorem runUpdates_of_mem (act : I → M → M) (js : List I)
    (hnd : js.Nodup) (i : I) (hi : i ∈ js) (h : I → M) :
    runUpdates act js h i = act i (h i) := by
  induction js generalizing h with
  | nil => simp only [List.not_mem_nil] at hi
  | cons j js ih =>
      have hn : j ∉ js ∧ js.Nodup := List.nodup_cons.mp hnd
      by_cases hij : i = j
      · subst i
        rw [runUpdates, runUpdates_of_not_mem act js j hn.1,
          Function.update_self]
      · have him : i ∈ js := (List.mem_cons.mp hi).resolve_left hij
        rw [runUpdates, ih hn.2 him, Function.update_of_ne hij]

end CurrentMain.IndependentEntryFold

namespace CurrentMain.Current799EntryFold
open IndependentEntryFold Current799ScalarSupport Current799EntryConnection

/-- Exact base-register embedding; the eight centre coordinates are untouched. -/
def entryIndex (i : Fin 728) : Fin 736 := ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

/-- The literal emitter enumerates every base register once in increasing order. -/
def entryRegisters : List (Fin 736) := List.ofFn entryIndex

theorem entryRegisters_nodup : entryRegisters.Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

theorem entryRegisters_values : entryRegisters.map Fin.val = List.range 728 := by
  rw [entryRegisters, List.map_ofFn]
  change (List.ofFn (fun i : Fin 728 => i.val)) = List.range 728
  rw [List.ofFn_eq_map, List.map_coe_finRange]

theorem mem_entryRegisters (i : Fin 736) (hi : i.val < 728) : i ∈ entryRegisters := by
  apply List.mem_ofFn.mpr
  exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

private theorem selected_base (i : Fin 736) (hi : i ∈ selectedSupport) : i.val < 728 := by
  simp only [selectedSupport, ScalarWriteSupport.Historical596.first33Support,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i <;> decide

/-- All728 actions are parametric. Only sixteen equations are needed to connect
the selected formal entry fold to the accepted first-climb value interface. -/
theorem selected_entry_action {M : Type*}
    (act : Fin 736 → M → M) (Rinv : M → M)
    (hselected : ∀ i ∈ selectedSupport, ∀ v, act i v = entryValue Rinv i v) :
    HasSelectedEntryAction (runUpdates act entryRegisters) Rinv := by
  intro h i hi
  rw [runUpdates_of_mem act entryRegisters entryRegisters_nodup i
    (mem_entryRegisters i (selected_base i hi))]
  exact hselected i hi (h i)

/-- A separately supplied executor equality may be used without assuming its
implementation, or deriving it from the source's scalar-only check_local. -/
theorem selected_executor_action {M : Type*}
    (actualEntry : (Fin 736 → M) → (Fin 736 → M))
    (act : Fin 736 → M → M) (Rinv : M → M)
    (hexec : actualEntry = runUpdates act entryRegisters)
    (hselected : ∀ i ∈ selectedSupport, ∀ v, act i v = entryValue Rinv i v) :
    HasSelectedEntryAction actualEntry Rinv := by
  rw [hexec]
  exact selected_entry_action act Rinv hselected

end CurrentMain.Current799EntryFold

#print axioms CurrentMain.IndependentEntryFold.runUpdates_eq_foldl
#print axioms CurrentMain.IndependentEntryFold.runUpdates_of_not_mem
#print axioms CurrentMain.IndependentEntryFold.runUpdates_of_mem
#print axioms CurrentMain.Current799EntryFold.entryRegisters_nodup
#print axioms CurrentMain.Current799EntryFold.entryRegisters_values
#print axioms CurrentMain.Current799EntryFold.selected_entry_action
#print axioms CurrentMain.Current799EntryFold.selected_executor_action
#check @CurrentMain.Current799EntryFold.selected_entry_action
#check @CurrentMain.Current799EntryFold.selected_executor_action
