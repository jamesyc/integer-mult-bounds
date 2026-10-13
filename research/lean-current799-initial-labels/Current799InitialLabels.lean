import Current799EntryConnection
import Current799First33CoverageData

/-!
Exact selected projection of the declared PR799 initial labels. The imported
bank array is unchanged and source-bound to f567 canonical.start. Each of the
sixteen support indices is below728 and uses its actual array value, not the
centre/default branch. No first33 row predicate or scalar execution is replayed.
This supplies only declared-label values, not actual prefix label execution,
operator equations, an executor implementation, incoming charts or hstart.
Prepared with OpenAI assistance. Apache-2.0. See SOURCE_BINDING.json.
-/
set_option Elab.async false
namespace CurrentMain.Current799InitialLabels
open Current799ScalarSupport Current799EntryConnection

/-- The eight plain selected registers have label0; the eight residual selected
registers have label4. This is a projection of the existing declared initializer. -/
theorem selected_initial_labels (i : Fin 736) (hi : i ∈ selectedSupport) :
    Current799First33CoverageData.labels0 i =
      if i.val ∈ residualRegisters then (4 : Fin 1005) else 0 := by
  simp only [selectedSupport, ScalarWriteSupport.Historical596.first33Support,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst i <;> decide +kernel

end CurrentMain.Current799InitialLabels
#print axioms CurrentMain.Current799InitialLabels.selected_initial_labels
#check @CurrentMain.Current799InitialLabels.selected_initial_labels
