import FixedGridReference

/-!
The first three actual scalar rows of the selected forward word:
SCALE(119,-1/2), ADD(119,169,+1/2), ADD(169,119,-1).
The two accepted complete traversals are followed by the actual four-instruction
subtract traversal. No new instruction, runtime scalar oracle or initial encoding
is introduced. Both memory fields and the visible accumulator are interpreted.

The 24*n count is reference instruction length, not bit time. The fixed-Q result
uses the accepted rows1-2 exponent bound and proves that the third row adds no
halving. Initial finite-footprint bounds and Q=P+1 remain explicit. The selected
pair is a signed output permutation of H0, not literally H0 in the same ports.
The physical component wrapper, host cleanup and complete selected layer remain
separate. The supplied chronological reserve proof in PR2390/2327 is credited;
this finite prefix does not reprove or instantiate its all-size induction.
James Chang, OpenAI-assisted, Apache-2.0. Author-checked contextual kappa:
836330098538459/500000000000000000.
-/
set_option Elab.async false
set_option autoImplicit false
namespace CurrentMain.SelectedFirstButterflyReference
open Current1094Row1DyadicReference DyadicCellAddition Current1094Row1FamilyBlocks
open ComponentStoreFoldRefinement IndependentEntryFold
open Current1094Row2AddReference Current1094Row2DyadicReference
open Current1094Rows12DyadicReference Current1094Rows12PrefixBitBudget

/-- This is the literal emitted coefficient -1, with no new instruction. -/
def row3Code (target source : Nat) : List Instruction :=
  [.core (.read source), .core .negate, .addMemory target, .core (.write target)]

def row3Emit {I : Type*} (target source : I → Nat) : List I → List Instruction
  | [] => []
  | i :: rest => row3Code (target i) (source i) ++ row3Emit target source rest

def row3Run {I : Type*} (target source : I → Nat) : List I → EncodedState → EncodedState
  | [], s => s
  | i :: rest, s => row3Run target source rest (runAdd (row3Code (target i) (source i)) s)

private theorem run_append (xs ys : List Instruction) (s : EncodedState) :
    runAdd (xs ++ ys) s = runAdd ys (runAdd xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih (stepAdd op s)

/-- The new traversal writes the difference and leaves it in actual scratch. -/
theorem row3_state (target source : Nat) (s : EncodedState) :
    runAdd (row3Code target source) s =
      ⟨Function.update s.memory target (addCell (s.memory target) (negCell (s.memory source))),
        addCell (s.memory target) (negCell (s.memory source))⟩ := rfl

theorem row3_run_emit {I : Type*} (target source : I → Nat)
    (order : List I) (s : EncodedState) :
    runAdd (row3Emit target source order) s = row3Run target source order s := by
  induction order generalizing s with
  | nil => rfl
  | cons i rest ih =>
      simpa only [row3Emit, run_append, row3Run] using
        ih (runAdd (row3Code (target i) (source i)) s)

private theorem row3_length {I : Type*} (target source : I → Nat) (order : List I) :
    (row3Emit target source order).length = 4 * order.length := by
  induction order with
  | nil => rfl
  | cons i rest ih =>
      simp only [row3Emit, List.length_append, row3Code, List.length_cons, List.length_nil, ih]
      omega

private theorem row3_projection {I : Type*} [DecidableEq I]
    (target source : I → Nat) (hinj : Function.Injective target)
    (hsep : ∀ i j, source i ≠ target j) (values : I → Cell)
    (order : List I) (s : EncodedState) (hread : ∀ i, s.memory (source i) = values i) :
    (fun i => (row3Run target source order s).memory (target i)) =
      runUpdates (fun i c => addCell c (negCell (values i))) order
        (fun i => s.memory (target i)) := by
  induction order generalizing s with
  | nil => rfl
  | cons j rest ih =>
      have hnext : ∀ i,
          (runAdd (row3Code (target j) (source j)) s).memory (source i) = values i := by
        intro i
        rw [row3_state]
        dsimp only
        rw [Function.update_of_ne (hsep i j)]
        exact hread i
      have hupdate :
          (fun i => (runAdd (row3Code (target j) (source j)) s).memory (target i)) =
          Function.update (fun i => s.memory (target i)) j
            (addCell (s.memory (target j)) (negCell (values j))) := by
        simp only [row3_state]
        rw [hread j]
        exact Function.update_comp_eq_of_injective' s.memory hinj j _
      calc
        (fun i => (row3Run target source (j :: rest) s).memory (target i)) =
            runUpdates (fun i c => addCell c (negCell (values i))) rest
              (fun i => (runAdd (row3Code (target j) (source j)) s).memory (target i)) :=
          ih (runAdd (row3Code (target j) (source j)) s) hnext
        _ = runUpdates (fun i c => addCell c (negCell (values i))) rest
              (Function.update (fun i => s.memory (target i)) j
                (addCell (s.memory (target j)) (negCell (values j)))) := by rw [hupdate]
        _ = _ := rfl

private theorem row3_outside {I : Type*} (target source : I → Nat)
    (order : List I) (s : EncodedState) (a : Nat) (ha : a ∉ order.map target) :
    (row3Run target source order s).memory a = s.memory a := by
  induction order generalizing s with
  | nil => rfl
  | cons i rest ih =>
      have h : a ≠ target i ∧ a ∉ rest.map target := by
        simpa only [List.map_cons, List.mem_cons, not_or] using ha
      rw [row3Run, ih _ h.2, row3_state]
      dsimp only
      rw [Function.update_of_ne h.1]

/-- The third row writes family169 while reading the completed family119. -/
def row3Program (n target source : Nat) : List Instruction :=
  row3Emit (address n source) (address n target)
    (Current1094Row1FlatReference.componentOrder n)

def program (n target source : Nat) : List Instruction :=
  rows12Program n target source ++ row3Program n target source

def selectedProgram (n : Nat) : List Instruction := program n 119 169

theorem program_length (n target source : Nat) :
    (program n target source).length = 24 * n := by
  simp only [program, List.length_append, rows12_length, row3Program,
    row3_length, Current1094Row1FlatReference.componentOrder_length]
  omega

private theorem third_cell (n target source : Nat) (hne : source ≠ target)
    (s : EncodedState) (slot : Slot (Fin n)) :
    (runAdd (row3Program n target source) s).memory (address n source slot) =
      addCell (s.memory (address n source slot)) (negCell (s.memory (address n target slot))) := by
  rw [row3Program, row3_run_emit]
  have h := row3_projection (address n source) (address n target)
    (Current1094Row1FlatReference.flatAddress_injective n (familyBase n source))
    (address_separation n source target (Ne.symm hne))
    (fun i => s.memory (address n target i))
    (Current1094Row1FlatReference.componentOrder n) s (fun _ => rfl)
  exact (congrFun h slot).trans
    (runUpdates_of_mem _ _ (Current1094Row1FlatReference.componentOrder_nodup n)
      slot (Current1094Row1FlatReference.componentOrder_complete n slot) _)

private theorem third_outside (n target source : Nat) (s : EncodedState) (a : Nat)
    (hout : a < familyBase n source ∨ familyBase n source + 2*n ≤ a) :
    (runAdd (row3Program n target source) s).memory a = s.memory a := by
  rw [row3Program, row3_run_emit]
  apply row3_outside
  intro ha
  rcases List.mem_map.mp ha with ⟨slot, _, heq⟩
  have hb := Current1094Row1FlatReference.flatAddress_bounds n (familyBase n source) slot
  change Current1094Row1FlatReference.flatAddress (familyBase n source) slot = a at heq
  omega

def firstResult (t u : Cell) : Cell := addCell (minusHalfCell t) (halfCell u)
def secondResult (t u : Cell) : Cell := addCell u (negCell (firstResult t u))

/-- Both literal raw representations follow from the three original traversals. -/
theorem endpoint_cells (n target source : Nat) (hne : source ≠ target)
    (s : EncodedState) (slot : Slot (Fin n)) :
    (runAdd (program n target source) s).memory (address n target slot) =
      firstResult (s.memory (address n target slot)) (s.memory (address n source slot)) ∧
    (runAdd (program n target source) s).memory (address n source slot) =
      secondResult (s.memory (address n target slot)) (s.memory (address n source slot)) := by
  rw [program, run_append]
  constructor
  · rw [third_outside n target source (runAdd (rows12Program n target source) s)
      (address n target slot) (other_block_outside n source target (Ne.symm hne) slot),
      rows12_cell n target source hne]
    rfl
  · rw [third_cell n target source hne, rows12_cell n target source hne,
      rows12_outside_cell n target source s (address n source slot)
        (other_block_outside n target source hne slot)]
    rfl

theorem outside_cell (n target source : Nat) (s : EncodedState) (a : Nat)
    (ht : a < familyBase n target ∨ familyBase n target + 2*n ≤ a)
    (hs : a < familyBase n source ∨ familyBase n source + 2*n ≤ a) :
    (runAdd (program n target source) s).memory a = s.memory a := by
  rw [program, run_append, third_outside n target source _ a hs,
    rows12_outside_cell n target source s a ht]

theorem first_value (t u : Cell) : value (firstResult t u) = (value u - value t) / 2 := by
  rw [firstResult, addCell_value]
  simp only [value, minusHalfCell, halfCell, Int.cast_neg, pow_succ, div_mul_eq_div_div, neg_div]
  ring

theorem second_value (t u : Cell) : value (secondResult t u) = (value u + value t) / 2 := by
  rw [secondResult, addCell_value]
  have hn : value (negCell (firstResult t u)) = -value (firstResult t u) := by
    simp only [value, negCell, Int.cast_neg, neg_div]
  rw [hn, first_value]
  ring

/-- H0 needs the fixed signed output permutation J(a,b)=(-b,a). -/
theorem signed_H0_orientation (t u : Cell) :
    (value (firstResult t u), value (secondResult t u)) =
      (-((value t - value u) / 2), (value t + value u) / 2) := by
  rw [first_value, second_value]
  congr 1 <;> ring

/-- Every reference cut includes the exact accumulator, with no cleanup fiction. -/
theorem prefix_decodes (n target source k : Nat) (s : EncodedState) :
    decodeState (runAdd ((program n target source).take k) s) =
      execute ((program n target source).take k) (decodeState s) := decode_runAdd _ _

/-- Only exponent support is needed to lift the complete word to one fixed grid. -/
def ExponentBound (S : List Nat) (Q : Nat) (s : EncodedState) : Prop :=
  (∀ a ∈ S, (s.memory a).fractionalBits ≤ Q) ∧ s.accumulator.fractionalBits ≤ Q

private theorem subtract_prefix (S : List Nat) (Q target source : Nat) (s : EncodedState)
    (h : ExponentBound S Q s) (ht : target ∈ S) (hs : source ∈ S) :
    ∀ k, ExponentBound S Q (runAdd ((row3Code target source).take k) s) := by
  intro k
  have hr := h.1 source hs
  have hadd : (addCell (s.memory target) (negCell (s.memory source))).fractionalBits ≤ Q :=
    max_le (h.1 target ht) hr
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ 4≤k := by omega
  rcases cases with rfl | rfl | rfl | rfl | hk
  · exact h
  · exact ⟨h.1,hr⟩
  · exact ⟨h.1,hr⟩
  · exact ⟨h.1,hadd⟩
  · rw [List.take_of_length_le (show (row3Code target source).length ≤ k from hk), row3_state]
    refine ⟨?_,hadd⟩
    intro a ha
    dsimp only
    by_cases he : a=target
    · subst a; simpa only [Function.update_self] using hadd
    · rw [Function.update_of_ne he];exact h.1 a ha

private theorem prefix_append (S : List Nat) (Q : Nat) (xs ys : List Instruction)
    (s : EncodedState)
    (hx : ∀ k, ExponentBound S Q (runAdd (xs.take k) s))
    (hy : ∀ k, ExponentBound S Q (runAdd (ys.take k) (runAdd xs s))) :
    ∀ k, ExponentBound S Q (runAdd ((xs++ys).take k) s) := by
  intro k
  by_cases hk : k ≤ xs.length
  · rw [List.take_append_of_le_length hk];exact hx k
  · rw [List.take_append_eq_append_take, List.take_of_length_le (by omega), run_append]
    exact hy (k-xs.length)

private theorem row3_prefix {I : Type*} (S : List Nat) (Q : Nat)
    (target source : I → Nat) (order : List I) (s : EncodedState)
    (ht : ∀ i ∈ order, target i ∈ S) (hs : ∀ i ∈ order, source i ∈ S)
    (h : ExponentBound S Q s) :
    ∀ k, ExponentBound S Q (runAdd ((row3Emit target source order).take k) s) := by
  induction order generalizing s with
  | nil => intro k;simpa only [row3Emit,List.take_nil,runAdd] using h
  | cons i rest ih =>
      have hp := subtract_prefix S Q (target i) (source i) s h (ht i (by simp)) (hs i (by simp))
      have hf : ExponentBound S Q (runAdd (row3Code (target i) (source i)) s) := by
        simpa only [List.take_length] using hp (row3Code (target i) (source i)).length
      exact prefix_append S Q _ _ s hp
        (ih (runAdd (row3Code (target i) (source i)) s)
          (fun j hj => ht j (by simp [hj])) (fun j hj => hs j (by simp [hj])) hf)

/-- The third selected row never increases the accepted Q=P+1 ceiling. -/
theorem all_prefix_exponents (n target source b P : Nat) (hne : source ≠ target)
    (s : EncodedState) (h : StateBudget (footprint n target source) b P s) :
    ∀ k, ExponentBound (footprint n target source) (P+1)
      (runAdd ((program n target source).take k) s) := by
  have hx : ∀ k, ExponentBound (footprint n target source) (P+1)
      (runAdd ((rows12Program n target source).take k) s) := by
    intro k
    have hb := rows12_all_prefixes n target source b P hne s h k
    exact ⟨fun a ha => (hb.1 a ha).2,hb.2.2⟩
  have hf : ExponentBound (footprint n target source) (P+1)
      (runAdd (rows12Program n target source) s) := by
    simpa only [List.take_length] using hx (rows12Program n target source).length
  have ht : ∀ i : Slot (Fin n), address n target i ∈ footprint n target source := by
    intro i;apply List.mem_append_left
    exact List.mem_map.mpr ⟨i,Current1094Row1FlatReference.componentOrder_complete n i,rfl⟩
  have hs : ∀ i : Slot (Fin n), address n source i ∈ footprint n target source := by
    intro i;apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,Current1094Row1FlatReference.componentOrder_complete n i,rfl⟩
  exact prefix_append _ _ _ _ s hx (row3_prefix _ _ (address n source) (address n target)
    (Current1094Row1FlatReference.componentOrder n) _ (fun i _ => hs i) (fun i _ => ht i) hf)

/-- Same actual reference prefixes, now interpreted using only integer ADD/HALVE. -/
theorem fixed_grid_prefix (n target source b P k : Nat) (hne : source ≠ target)
    (s : EncodedState) (h : StateBudget (footprint n target source) b P s) :
    FixedGridReference.run ((program n target source).take k) (FixedGridReference.encode (P+1) s) =
      FixedGridReference.encode (P+1) (runAdd ((program n target source).take k) s) := by
  apply FixedGridReference.run_encode
  intro j
  simpa only [List.take_take] using
    (all_prefix_exponents n target source b P hne s h (min j k)).2

/-- Both active fields and the visible scratch decode at every interrupted cut. -/
theorem fixed_grid_prefix_values (n target source b P k : Nat) (hne : source ≠ target)
    (s : EncodedState) (h : StateBudget (footprint n target source) b P s) :
    (∀ a ∈ footprint n target source,
      ((FixedGridReference.run ((program n target source).take k)
        (FixedGridReference.encode (P+1) s)).memory a : Real) / (2 : Real)^(P+1) =
        value ((runAdd ((program n target source).take k) s).memory a)) ∧
    ((FixedGridReference.run ((program n target source).take k)
      (FixedGridReference.encode (P+1) s)).accumulator : Real) / (2 : Real)^(P+1) =
      value ((runAdd ((program n target source).take k) s).accumulator) := by
  rw [fixed_grid_prefix n target source b P k hne s h]
  have hb := all_prefix_exponents n target source b P hne s h k
  exact ⟨fun a ha => aligned_value (P+1) _ (hb.1 a ha), aligned_value (P+1) _ hb.2⟩

/-- The selected literal family pair has the two required butterfly outputs. -/
theorem selected_endpoint_values (n : Nat) (s : EncodedState) (slot : Slot (Fin n)) :
    value ((runAdd (selectedProgram n) s).memory (address n 119 slot)) =
      (value (s.memory (address n 169 slot)) - value (s.memory (address n 119 slot))) / 2 ∧
    value ((runAdd (selectedProgram n) s).memory (address n 169 slot)) =
      (value (s.memory (address n 169 slot)) + value (s.memory (address n 119 slot))) / 2 := by
  have he := endpoint_cells n 119 169 (by decide) s slot
  change value ((runAdd (program n 119 169) s).memory _) = _ ∧
    value ((runAdd (program n 119 169) s).memory _) = _
  rw [he.1,he.2,first_value,second_value]
  exact ⟨rfl,rfl⟩

end CurrentMain.SelectedFirstButterflyReference
#print axioms CurrentMain.SelectedFirstButterflyReference.row3_state
#print axioms CurrentMain.SelectedFirstButterflyReference.program_length
#print axioms CurrentMain.SelectedFirstButterflyReference.endpoint_cells
#print axioms CurrentMain.SelectedFirstButterflyReference.outside_cell
#print axioms CurrentMain.SelectedFirstButterflyReference.signed_H0_orientation
#print axioms CurrentMain.SelectedFirstButterflyReference.prefix_decodes
#print axioms CurrentMain.SelectedFirstButterflyReference.all_prefix_exponents
#print axioms CurrentMain.SelectedFirstButterflyReference.fixed_grid_prefix_values
#print axioms CurrentMain.SelectedFirstButterflyReference.selected_endpoint_values
#check @CurrentMain.SelectedFirstButterflyReference.fixed_grid_prefix_values
#check @CurrentMain.SelectedFirstButterflyReference.selected_endpoint_values
