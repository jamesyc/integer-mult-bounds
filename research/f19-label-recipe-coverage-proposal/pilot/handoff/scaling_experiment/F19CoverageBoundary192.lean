/- Bounded selected f19 canonical-frame coverage experiment. No operator or full-stream claim. -/
import F19CoverageBatchData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.F19SelectedCoverage.Boundary192
open CurrentMain.F19SelectedCoverage

def supportedB (support : List Register) (e : LabelEvent) : Bool :=
  match e with
  | .relabel r .. => support.contains r
  | .copy r .. => support.contains r
  | .clear r .. => support.contains r
  | .add .. => true
  | .scale .. => true

private theorem supportedB_moves (support : List Register) (e : LabelEvent) (r : Register)
    (hs : supportedB support e = true) (hm : e.moves r) : r ∈ support := by
  cases e <;> simp_all [supportedB, LemmaG.Event.moves]

/-- A sparse label-state equality only; no assumption on payload values. -/
theorem sparse_checkpoint (rows : List Row) (labels : Register → FrameLabel)
    (support : List Register)
    (hs : (rows.map Row.event).all (supportedB support) = true)
    (hv : support.all (fun r =>
      LemmaG.Stream.labRun (rows.map Row.event) labels r == (2 : FrameLabel)) = true) :
    LemmaG.Stream.labRun (rows.map Row.event) labels =
      (fun r => if r ∈ support then 2 else labels r) := by
  funext r
  by_cases hr : r ∈ support
  · have hval := (List.all_eq_true.mp hv) r hr
    have heq : LemmaG.Stream.labRun (rows.map Row.event) labels r = (2 : FrameLabel) := by
      simpa using hval
    simpa [hr] using heq
  · have hu := LemmaG.Stream.labRun_untouched (rows.map Row.event) labels r (by
        intro e he hm
        exact hr (supportedB_moves support e r ((List.all_eq_true.mp hs) e he) hm))
    simpa [hr] using hu

theorem forward_support :
    (NextData.forward.map Row.event).all (supportedB BatchData.new192) = true := by
  decide +kernel

theorem forward_touched :
    BatchData.new192.all (fun r =>
      LemmaG.Stream.labRun (NextData.forward.map Row.event)
        NextData.checkpointLabels r == (2 : FrameLabel)) = true := by
  decide +kernel

theorem forward_checkpoint192 :
    LemmaG.Stream.labRun (NextData.forward.map Row.event) NextData.checkpointLabels =
      BatchData.labels192 :=
  sparse_checkpoint NextData.forward NextData.checkpointLabels BatchData.new192
    forward_support forward_touched

theorem forward_composed_checkpoint192 :
    LemmaG.Stream.labRun ((PilotData.forward ++ NextData.forward).map Row.event)
      (initialLabels PilotData.data) = BatchData.labels192 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, PilotBoundary.forward_checkpoint]
  exact forward_checkpoint192

theorem backward_support :
    (NextData.backward.map Row.event).all (supportedB BatchData.new192) = true := by
  decide +kernel

theorem backward_touched :
    BatchData.new192.all (fun r =>
      LemmaG.Stream.labRun (NextData.backward.map Row.event)
        NextData.checkpointLabels r == (2 : FrameLabel)) = true := by
  decide +kernel

theorem backward_checkpoint192 :
    LemmaG.Stream.labRun (NextData.backward.map Row.event) NextData.checkpointLabels =
      BatchData.labels192 :=
  sparse_checkpoint NextData.backward NextData.checkpointLabels BatchData.new192
    backward_support backward_touched

theorem backward_composed_checkpoint192 :
    LemmaG.Stream.labRun ((PilotData.backward ++ NextData.backward).map Row.event)
      (initialLabels PilotData.data) = BatchData.labels192 := by
  rw [List.map_append, LemmaG.Stream.labRun_append, PilotBoundary.backward_checkpoint]
  exact backward_checkpoint192


#print axioms sparse_checkpoint
#print axioms forward_support
#print axioms forward_touched
#print axioms forward_checkpoint192
#print axioms forward_composed_checkpoint192
#print axioms backward_support
#print axioms backward_touched
#print axioms backward_checkpoint192
#print axioms backward_composed_checkpoint192
end CurrentMain.F19SelectedCoverage.Boundary192
