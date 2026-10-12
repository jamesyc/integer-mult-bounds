/- Exact label-state boundary for the accepted pilot. Reuses PR509 labRun_untouched.
There is no payload, operator, next-slice admissibility, or full-stream claim. -/
import F19CoveragePilotCheck
import F19CoverageNextData

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace CurrentMain.F19SelectedCoverage.PilotBoundary
open CurrentMain.F19SelectedCoverage

def supportedB (e : LabelEvent) : Bool :=
  match e with
  | .relabel r .. => NextData.movedRegisters.contains r
  | .copy r .. => NextData.movedRegisters.contains r
  | .clear r .. => NextData.movedRegisters.contains r
  | .add .. => true
  | .scale .. => true

private theorem supportedB_moves (e : LabelEvent) (r : Register)
    (hs : supportedB e = true) (hm : e.moves r) :
    r ∈ NextData.movedRegisters := by
  cases e <;> simp_all [supportedB, LemmaG.Event.moves]

theorem forward_support :
    (PilotData.forward.map Row.event).all supportedB = true := by decide +kernel
theorem backward_support :
    (PilotData.backward.map Row.event).all supportedB = true := by decide +kernel

theorem forward_touched :
    NextData.movedRegisters.all (fun r =>
      LemmaG.Stream.labRun (PilotData.forward.map Row.event)
        (initialLabels PilotData.data) r == (2 : FrameLabel)) = true := by decide +kernel
theorem backward_touched :
    NextData.movedRegisters.all (fun r =>
      LemmaG.Stream.labRun (PilotData.backward.map Row.event)
        (initialLabels PilotData.data) r == (2 : FrameLabel)) = true := by decide +kernel

private theorem checkpoint_of_support (rows : List Row)
    (hs : (rows.map Row.event).all supportedB = true)
    (hv : NextData.movedRegisters.all (fun r =>
      LemmaG.Stream.labRun (rows.map Row.event)
        (initialLabels PilotData.data) r == (2 : FrameLabel)) = true) :
    LemmaG.Stream.labRun (rows.map Row.event) (initialLabels PilotData.data) =
      NextData.checkpointLabels := by
  funext r
  by_cases hr : r ∈ NextData.movedRegisters
  · have hval := (List.all_eq_true.mp hv) r hr
    have heq : LemmaG.Stream.labRun (rows.map Row.event)
        (initialLabels PilotData.data) r = (2 : FrameLabel) := by simpa using hval
    simpa [NextData.checkpointLabels, hr] using heq
  · have hu := LemmaG.Stream.labRun_untouched (rows.map Row.event)
        (initialLabels PilotData.data) r (by
          intro e he hm
          exact hr (supportedB_moves e r ((List.all_eq_true.mp hs) e he) hm))
    simpa [NextData.checkpointLabels, hr] using hu

theorem forward_checkpoint :
    LemmaG.Stream.labRun (PilotData.forward.map Row.event)
      (initialLabels PilotData.data) = NextData.checkpointLabels :=
  checkpoint_of_support PilotData.forward forward_support forward_touched

theorem backward_checkpoint :
    LemmaG.Stream.labRun (PilotData.backward.map Row.event)
      (initialLabels PilotData.data) = NextData.checkpointLabels :=
  checkpoint_of_support PilotData.backward backward_support backward_touched

#print axioms forward_support
#print axioms backward_support
#print axioms forward_touched
#print axioms backward_touched
#print axioms forward_checkpoint
#print axioms backward_checkpoint
end CurrentMain.F19SelectedCoverage.PilotBoundary
