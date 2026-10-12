import CurrentR420BoundaryData
import Init.Data.List.Sort.Impl

/-! Exact first three declarations from the preserved R420 domain Check.
This bounded index diagnostic places each original axiom probe immediately
behind its declaration. It does not localize the earlier allocation failure
until an actual diagnostic result is observed. Remaining groups and the
original-name composition wrapper stay planned and unactivated.
Prepared with OpenAI assistance; supplier and core attribution retained. -/
namespace CurrentMain.CurrentR420Boundary
open Data
set_option Elab.async false

theorem selected_shape :
    h = 8 ∧ v = 120 ∧ R = 420 ∧ registers = 660 ∧
    format = "bitE8/1+mut" ∧ form = "<x,y>/2" ∧ coords = "ham" := by decide +kernel
#print axioms CurrentMain.CurrentR420Boundary.selected_shape

theorem line_shape :
    lines.length = 120 ∧ lines.all (fun row => row.length == 8) = true :=
  SelectedBitCarrierBoundary.line_shape
#print axioms CurrentMain.CurrentR420Boundary.line_shape

theorem frame_index_permutation :
    (frameOrder.map Fin.val).mergeSort (fun a b => decide (a ≤ b)) = List.range 672 := by
  rw [List.MergeSort.Internal.mergeSort_eq_mergeSortTR]
  decide +kernel
#print axioms CurrentMain.CurrentR420Boundary.frame_index_permutation

end CurrentMain.CurrentR420Boundary
