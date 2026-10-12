/- Scoped selected-source label/canonical-recipe coverage; no operator or omitted-adapter claim. -/
import F19CoverageBoundary192

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.SparseValues
open CurrentMain.F19SelectedCoverage

private theorem supported_moves (support : List Register) (e : LabelEvent) (r : Register)
    (hs : Boundary192.supportedB support e = true) (hm : e.moves r) : r ∈ support := by
  cases e <;> simp_all [Boundary192.supportedB, LemmaG.Event.moves]

/-- The retained untouched-register API permits an arbitrary value at each changed label.
There is no cleanliness, scalar-state, or physical chart hypothesis. -/
theorem sparse_checkpoint (rows : List Row) (labels values : Register → FrameLabel)
    (support : List Register)
    (hs : (rows.map Row.event).all (Boundary192.supportedB support) = true)
    (hv : support.all (fun r =>
      LemmaG.Stream.labRun (rows.map Row.event) labels r == values r) = true) :
    LemmaG.Stream.labRun (rows.map Row.event) labels =
      (fun r => if r ∈ support then values r else labels r) := by
  funext r
  by_cases hr : r ∈ support
  · have hval := (List.all_eq_true.mp hv) r hr
    have heq : LemmaG.Stream.labRun (rows.map Row.event) labels r = values r := by
      simpa using hval
    simpa [hr] using heq
  · have hu := LemmaG.Stream.labRun_untouched (rows.map Row.event) labels r (by
        intro e he hm
        exact hr (supported_moves support e r ((List.all_eq_true.mp hs) e he) hm))
    simpa [hr] using hu

#print axioms sparse_checkpoint
end CurrentMain.F19SelectedCoverage.SparseValues
