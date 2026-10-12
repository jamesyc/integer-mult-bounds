/- Bounded selected f19 canonical-frame coverage experiment. No operator or full-stream claim. -/
import F19CoverageStatement

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.CheckDecomposition
open CurrentMain.F19SelectedCoverage

def labelRowsB : List Row → (Register → FrameLabel) → Bool
  | [], _ => true
  | row :: rows, labels =>
      admissibleB row.event labels &&
        (scalarAnnotationB row labels && labelRowsB rows (row.event.lab labels))

def childRowsB (p : SelectedData) : List Row → Bool
  | [] => true
  | row :: rows => childReferenceB p row && childRowsB p rows

theorem checkRows_factor (p : SelectedData) (rows : List Row)
    (labels : Register → FrameLabel) :
    checkRows p rows labels = (labelRowsB rows labels && childRowsB p rows) := by
  induction rows generalizing labels with
  | nil => rfl
  | cons row rows ih =>
      simp only [checkRows, labelRowsB, childRowsB, ih,
        Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

#print axioms checkRows_factor
end CurrentMain.F19SelectedCoverage.CheckDecomposition
