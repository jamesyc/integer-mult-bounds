import Current1094Rows12DyadicReference

/-!
An intermediate-instruction budget for the actual two reference traversals.
Each unvisited SCALE target retains its original budget. Each unvisited ADD
target retains its once-scaled Cell, including a positive exponent; source
cells remain unchanged. No-repeat traversal and block disjointness therefore
avoid charging one exponent/carry increase for unrelated components.

Only the two active address blocks and the initial dirty accumulator are bounded.
Every prefix, including the empty prefix, retains numerator magnitude below
2^(b+P+1) and exponent at most P+1 on that finite footprint and scratch. This is
exact integer/exponent execution, not a primitive bit-cost or rounding theorem.
No initial encoding, width, global precision, selected whole-word/physical
refinement, metadata cleanup or uniform cost C is supplied. Finite invoice C0
remains separate. Reuses machine flat SCALE/ADD traversals and analytic Cell
and two-tape implementations. Apache-2.0; OpenAI-assisted. Author-checked selected
kappa836330098538459/500000000000000000 remains unchanged. Uncompiled candidate.
-/
set_option Elab.async false
set_option autoImplicit false
namespace CurrentMain.Current1094Rows12PrefixBitBudget
open Current1094Row1DyadicReference DyadicCellAddition Current1094Row1FamilyBlocks
open ComponentStoreFoldRefinement Current1094Row2AddReference Current1094Row2DyadicReference
open Current1094Rows12DyadicReference

/-- Sign/exponent/address metadata are not included in the numerator budget. -/
def CellBudget (b P : ℕ) (c : Cell) : Prop :=
  c.numerator.natAbs < 2 ^ b ∧ c.fractionalBits ≤ P

def StateBudget (S : List ℕ) (b P : ℕ) (s : EncodedState) : Prop :=
  (∀ a ∈ S, CellBudget b P (s.memory a)) ∧ CellBudget b P s.accumulator

private theorem cell_mono {b P B Q : ℕ} {c : Cell}
    (h : CellBudget b P c) (hb : b ≤ B) (hp : P ≤ Q) : CellBudget B Q c := by
  exact ⟨h.1.trans_le (pow_le_pow_right₀ (by norm_num) hb), h.2.trans hp⟩

private theorem half_budget {b P : ℕ} {c : Cell} (h : CellBudget b P c) :
    CellBudget b (P+1) (halfCell c) := ⟨h.1, Nat.add_le_add_right h.2 1⟩

private theorem negative_budget {b P : ℕ} {c : Cell} (h : CellBudget b P c) :
    CellBudget b P (negCell c) := by
  simpa only [CellBudget, negCell, Int.natAbs_neg] using h

private theorem minus_half_budget {b P : ℕ} {c : Cell} (h : CellBudget b P c) :
    CellBudget b (P+1) (minusHalfCell c) := by
  exact negative_budget (half_budget h)

private theorem update_budget (S : List ℕ) (b P a : ℕ) (s : EncodedState) (c : Cell)
    (h : StateBudget S b P s) (hc : CellBudget b P c) :
    StateBudget S b P ⟨Function.update s.memory a c,c⟩ := by
  refine ⟨?_, hc⟩
  intro x hx
  dsimp only
  by_cases he : x = a
  · subst x; simpa only [Function.update_self] using hc
  · rw [Function.update_of_ne he]; exact h.1 x hx

/-- An ADD target already halved by SCALE has exponent at least one. This
removes the spurious extra alignment bit from the uniform prefix budget. -/
private theorem add_after_scale_budget (b P : ℕ) (target source : Cell)
    (ht : CellBudget b (P+1) target) (htpos : 1 ≤ target.fractionalBits)
    (hs : CellBudget b P source) :
    CellBudget (b+P+1) (P+1) (addCell target (halfCell source)) := by
  have hq : commonExponent target (halfCell source) ≤ P+1 :=
    max_le ht.2 (Nat.add_le_add_right hs.2 1)
  refine ⟨?_, hq⟩
  have hb := addCell_bit_budget target (halfCell source) b b ht.1 hs.1
  apply hb.trans_le
  apply pow_le_pow_right₀ (by norm_num)
  have hsource : 1 ≤ (halfCell source).fractionalBits := by simp [halfCell]
  omega

private theorem run_append (xs ys : List Instruction) (s : EncodedState) :
    runAdd (xs++ys) s = runAdd ys (runAdd xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op ops ih => exact ih (stepAdd op s)

private theorem prefix_append (S : List ℕ) (b P : ℕ) (xs ys : List Instruction)
    (s : EncodedState)
    (hx : ∀ k, StateBudget S b P (runAdd (xs.take k) s))
    (hy : ∀ k, StateBudget S b P (runAdd (ys.take k) (runAdd xs s))) :
    ∀ k, StateBudget S b P (runAdd ((xs++ys).take k) s) := by
  intro k
  by_cases hk : k ≤ xs.length
  · rw [List.take_append_of_le_length hk]; exact hx k
  · rw [List.take_append_eq_append_take, List.take_of_length_le (by omega), run_append]
    exact hy (k-xs.length)

def scaleCode (a : ℕ) : List Instruction :=
  (Current1094Row1FlatReference.componentCode a).map Instruction.core

private theorem scale_component_state (a : ℕ) (s : EncodedState) :
    runAdd (scaleCode a) s =
      ⟨Function.update s.memory a (minusHalfCell (s.memory a)),minusHalfCell (s.memory a)⟩ := rfl

/-- All four actual SCALE instruction cuts, including dirty input scratch. -/
theorem scale_component_prefix (S : List ℕ) (b P a : ℕ) (s : EncodedState)
    (h : StateBudget S (b+P+1) (P+1) s) (ha : CellBudget b P (s.memory a)) :
    ∀ k, StateBudget S (b+P+1) (P+1) (runAdd ((scaleCode a).take k) s) := by
  intro k
  have hr := cell_mono ha (show b ≤ b+P+1 by omega) (show P ≤ P+1 by omega)
  have hh := cell_mono (half_budget ha) (show b ≤ b+P+1 by omega) (le_refl (P+1))
  have hn := cell_mono (minus_half_budget ha) (show b ≤ b+P+1 by omega) (le_refl (P+1))
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ 4≤k := by omega
  rcases cases with rfl | rfl | rfl | rfl | hk
  · exact h
  · exact ⟨h.1,hr⟩
  · exact ⟨h.1,hh⟩
  · exact ⟨h.1,hn⟩
  · rw [List.take_of_length_le (show (scaleCode a).length ≤ k from hk), scale_component_state]
    exact update_budget S _ _ a s _ h hn

/-- All four actual ADD instruction cuts. The target exponent positivity is
inherited from the preceding SCALE, and source halving is performed here. -/
theorem add_component_prefix (S : List ℕ) (b P target source : ℕ) (s : EncodedState)
    (h : StateBudget S (b+P+1) (P+1) s)
    (ht : CellBudget b (P+1) (s.memory target))
    (htpos : 1 ≤ (s.memory target).fractionalBits)
    (hs : CellBudget b P (s.memory source)) :
    ∀ k, StateBudget S (b+P+1) (P+1) (runAdd ((componentCode target source).take k) s) := by
  intro k
  have hr := cell_mono hs (show b ≤ b+P+1 by omega) (show P ≤ P+1 by omega)
  have hh := cell_mono (half_budget hs) (show b ≤ b+P+1 by omega) (le_refl (P+1))
  have hadd := add_after_scale_budget b P (s.memory target) (s.memory source) ht htpos hs
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ 4≤k := by omega
  rcases cases with rfl | rfl | rfl | rfl | hk
  · exact h
  · exact ⟨h.1,hr⟩
  · exact ⟨h.1,hh⟩
  · exact ⟨h.1,hadd⟩
  · rw [List.take_of_length_le (show (componentCode target source).length ≤ k from hk), component_state]
    exact update_budget S _ _ target s _ h hadd

private def scaleEmit : List ℕ → List Instruction
  | [] => []
  | a::rest => scaleCode a ++ scaleEmit rest

private theorem scaleEmit_core (as : List ℕ) :
    scaleEmit as = (Current1094Row1FlatReference.emit as).map Instruction.core := by
  induction as with
  | nil => rfl
  | cons a rest ih => simp only [scaleEmit, Current1094Row1FlatReference.emit, List.map_append, scaleCode, ih]

/-- No-repeat SCALE traversal keeps every not-yet-read target within its
original budget, rather than increasing the exponent budget for all cells. -/
private theorem scale_prefix (S as : List ℕ) (b P : ℕ) (hn : as.Nodup)
    (s : EncodedState) (h : StateBudget S (b+P+1) (P+1) s)
    (hr : ∀ a∈as, CellBudget b P (s.memory a)) :
    ∀ k, StateBudget S (b+P+1) (P+1) (runAdd ((scaleEmit as).take k) s) := by
  induction as generalizing s with
  | nil => intro k; simpa only [scaleEmit,List.take_nil,runAdd] using h
  | cons a rest ih =>
      have hd := List.nodup_cons.mp hn
      have ha := hr a (by simp)
      have hpart := scale_component_prefix S b P a s h ha
      have hfull : StateBudget S (b+P+1) (P+1) (runAdd (scaleCode a) s) := by
        simpa only [List.take_length] using hpart (scaleCode a).length
      have hrest : ∀ x∈rest, CellBudget b P ((runAdd (scaleCode a) s).memory x) := by
        intro x hx
        have hxa : x≠a := by intro he; subst x; exact hd.1 hx
        rw [scale_component_state]
        dsimp only
        rw [Function.update_of_ne hxa]
        exact hr x (by simp [hx])
      exact prefix_append S _ _ (scaleCode a) (scaleEmit rest) s hpart
        (ih hd.2 (runAdd (scaleCode a) s) hfull hrest)

/-- ADD's untouched remaining targets retain their once-scaled bound; all
source reads retain their original bound because the two blocks are disjoint. -/
private theorem add_prefix {I : Type*} (S : List ℕ) (b P : ℕ)
    (target source : I→ℕ) (hinj : Function.Injective target)
    (hsep : ∀ i j, source i ≠ target j)
    (order : List I) (hn : order.Nodup) (s : EncodedState)
    (h : StateBudget S (b+P+1) (P+1) s)
    (ht : ∀ i∈order, CellBudget b (P+1) (s.memory (target i)) ∧
      1 ≤ (s.memory (target i)).fractionalBits)
    (hs : ∀ i, CellBudget b P (s.memory (source i))) :
    ∀ k, StateBudget S (b+P+1) (P+1) (runAdd ((emit target source order).take k) s) := by
  induction order generalizing s with
  | nil => intro k; simpa only [emit,List.take_nil,runAdd] using h
  | cons i rest ih =>
      have hd := List.nodup_cons.mp hn
      have hi := ht i (by simp)
      have hpart := add_component_prefix S b P (target i) (source i) s h hi.1 hi.2 (hs i)
      have hfull : StateBudget S (b+P+1) (P+1) (runAdd (componentCode (target i) (source i)) s) := by
        simpa only [List.take_length] using hpart (componentCode (target i) (source i)).length
      have ht' : ∀ j∈rest,
          CellBudget b (P+1) ((runAdd (componentCode (target i) (source i)) s).memory (target j)) ∧
          1 ≤ ((runAdd (componentCode (target i) (source i)) s).memory (target j)).fractionalBits := by
        intro j hj
        have hji : target j ≠ target i := by intro he; have hEq := hinj he; subst j; exact hd.1 hj
        rw [component_state]
        dsimp only
        rw [Function.update_of_ne hji]
        exact ht j (by simp [hj])
      have hs' : ∀ j, CellBudget b P ((runAdd (componentCode (target i) (source i)) s).memory (source j)) := by
        intro j
        rw [component_state]
        dsimp only
        rw [Function.update_of_ne (hsep j i)]
        exact hs j
      exact prefix_append S _ _ (componentCode (target i) (source i)) (emit target source rest) s
        hpart (ih hd.2 (runAdd (componentCode (target i) (source i)) s) hfull ht' hs')

/-- Exactly the two finite active blocks; all other initial Cells are unrestricted. -/
def footprint (n target source : ℕ) : List ℕ :=
  (Current1094Row1FlatReference.componentOrder n).map (address n target) ++
    (Current1094Row1FlatReference.componentOrder n).map (address n source)

/-- Every partial instruction prefix of the actual full SCALE-then-ADD tapes
has the sharp n-independent active-cell and dirty-scratch budget. -/
theorem rows12_all_prefixes (n target source b P : ℕ) (hne : source≠target)
    (s : EncodedState) (h : StateBudget (footprint n target source) b P s) :
    ∀ k, StateBudget (footprint n target source) (b+P+1) (P+1)
      (runAdd ((rows12Program n target source).take k) s) := by
  let S := footprint n target source
  let order := Current1094Row1FlatReference.componentOrder n
  let xs := (Current1094Row1FlatReference.program n (familyBase n target)).map Instruction.core
  have target_mem : ∀ i : Slot (Fin n), address n target i ∈ S := by
    intro i
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨i,Current1094Row1FlatReference.componentOrder_complete n i,rfl⟩
  have source_mem : ∀ i : Slot (Fin n), address n source i ∈ S := by
    intro i
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨i,Current1094Row1FlatReference.componentOrder_complete n i,rfl⟩
  have hglobal : StateBudget S (b+P+1) (P+1) s :=
    ⟨fun a ha => cell_mono (h.1 a ha) (by omega) (by omega),cell_mono h.2 (by omega) (by omega)⟩
  have hxEq : xs = scaleEmit (order.map (address n target)) := by
    rw [scaleEmit_core]
    rfl
  have hscale : ∀ k, StateBudget S (b+P+1) (P+1) (runAdd (xs.take k) s) := by
    rw [hxEq]
    apply scale_prefix S _ b P
      (List.Nodup.map (Current1094Row1FlatReference.flatAddress_injective n (familyBase n target))
        (Current1094Row1FlatReference.componentOrder_nodup n)) s hglobal
    intro a ha
    exact h.1 a (List.mem_append_left _ ha)
  have hscaled : StateBudget S (b+P+1) (P+1) (runAdd xs s) := by
    simpa only [List.take_length] using hscale xs.length
  have ht : ∀ i∈order, CellBudget b (P+1) ((runAdd xs s).memory (address n target i)) ∧
      1 ≤ ((runAdd xs s).memory (address n target i)).fractionalBits := by
    intro i hi
    rw [show runAdd xs s = Current1094Row1DyadicReference.run
      (Current1094Row1FlatReference.program n (familyBase n target)) s from run_core _ _]
    dsimp only [address]
    rw [Current1094Row1DyadicReference.program_cell]
    exact ⟨minus_half_budget (h.1 _ (target_mem i)),by simp [minusHalfCell]⟩
  have hs : ∀ i, CellBudget b P ((runAdd xs s).memory (address n source i)) := by
    intro i
    rw [show runAdd xs s = Current1094Row1DyadicReference.run
      (Current1094Row1FlatReference.program n (familyBase n target)) s from run_core _ _]
    dsimp only [address]
    rw [Current1094Row1DyadicReference.program_outside_cell n (familyBase n target) s _
      (other_block_outside n target source hne i)]
    exact h.1 _ (source_mem i)
  have hadd := add_prefix S b P (address n target) (address n source)
    (Current1094Row1FlatReference.flatAddress_injective n (familyBase n target))
    (address_separation n target source hne) order
    (Current1094Row1FlatReference.componentOrder_nodup n) (runAdd xs s) hscaled ht hs
  exact prefix_append S _ _ xs (Current1094Row2AddReference.program n target source) s hscale hadd

/-- Concrete bank-bound119/169 instance; no initial encoding is inferred. -/
theorem selected_all_prefixes (n b P : ℕ) (s : EncodedState)
    (h : StateBudget (footprint n selectedTargetFamily selectedSourceFamily) b P s) :
    ∀ k, StateBudget (footprint n selectedTargetFamily selectedSourceFamily) (b+P+1) (P+1)
      (runAdd ((selectedRows12Program n).take k) s) :=
  rows12_all_prefixes n selectedTargetFamily selectedSourceFamily b P selected_families_ne s h

end CurrentMain.Current1094Rows12PrefixBitBudget
#print axioms CurrentMain.Current1094Rows12PrefixBitBudget.scale_component_prefix
#print axioms CurrentMain.Current1094Rows12PrefixBitBudget.add_component_prefix
#print axioms CurrentMain.Current1094Rows12PrefixBitBudget.rows12_all_prefixes
#print axioms CurrentMain.Current1094Rows12PrefixBitBudget.selected_all_prefixes
#check @CurrentMain.Current1094Rows12PrefixBitBudget.rows12_all_prefixes
