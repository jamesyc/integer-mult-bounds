/-
Source preparation only: rational interpretation of retained f19 scalar rows.
Not compiled or accepted. No whole-word or physical-work endpoint is claimed.

Reuses F19SelectedCoverage's exact signed numerator/denominator syntax and
PR509 Lemma G Event semantics (DreamingOfClouds, Claude Opus 5.5 assistance).
The selected emitter/auditor retain PR425/PR433/PR514 and icekylinx/OpenAI
attribution. Prepared with OpenAI assistance. Apache-2.0.
-/
import F19CoverageStatement
import Mathlib.Algebra.Field.Rat

namespace CurrentMain.F19ScalarEventInterpretation

open F19SelectedCoverage

abbrev ScalarEvent := LemmaG.Event Register FrameLabel ℚ

/-- Python Fraction's signed numerator and signed denominator are both retained.
A zero denominator is rejected before rational division's totalized value is used. -/
def decodeCoefficient (q : CoefficientCode) : Option ℚ :=
  if q.2 = 0 then none else some ((q.1 : ℚ) / (q.2 : ℚ))

/-- Only the existing retained canonical-frame event projection is interpreted.
This does not add the boundary adapters omitted by that projection. -/
def decodeEvent : LabelEvent → Option ScalarEvent
  | .relabel r a b => some (.relabel r a b)
  | .add t s q => (decodeCoefficient q).map (fun c => .add t s c)
  | .scale t q => (decodeCoefficient q).map (fun c => .scale t c)
  | .copy t s f => some (.copy t s f)
  | .clear t f => some (.clear t f)

/-- The list decoder preserves order and rejects any bad scalar denominator. -/
def decodeRows (rows : List Row) : Option (List ScalarEvent) :=
  rows.mapM (fun row => decodeEvent row.event)

section ScalarSemantics
variable {M : Type*} [AddCommMonoid M] [Module ℚ M]

/-- Direct source-level scalar update on all 736 registers. Relabel rows leave
the scalar shadow unchanged; COPY overwrites and CLEAR writes zero. -/
def rawScalarStep (e : LabelEvent) (h : Register → M) : Option (Register → M) :=
  match e with
  | .relabel .. => some h
  | .add t s q => (decodeCoefficient q).map
      (fun c => Function.update h t (h t + c • h s))
  | .scale t q => (decodeCoefficient q).map
      (fun c => Function.update h t (c • h t))
  | .copy t s _ => some (Function.update h t (h s))
  | .clear t _ => some (Function.update h t 0)

/-- The interpreted scalar event has exactly the source macro update. This is
one-event decoding soundness, not another stream conjugation proof. -/
theorem decoded_step (e : LabelEvent) (decoded : ScalarEvent)
    (hdecode : decodeEvent e = some decoded) (h : Register → M) :
    rawScalarStep e h = some (decoded.scal h) := by
  cases e with
  | relabel r a b =>
      simp_all [decodeEvent, rawScalarStep, LemmaG.Event.scal, LemmaG.Event.phys]
  | add t s q =>
      by_cases hd : q.2 = 0 <;>
        simp_all [decodeEvent, decodeCoefficient, hd, rawScalarStep,
          LemmaG.Event.scal, LemmaG.Event.phys]
  | scale t q =>
      by_cases hd : q.2 = 0 <;>
        simp_all [decodeEvent, decodeCoefficient, hd, rawScalarStep,
          LemmaG.Event.scal, LemmaG.Event.phys]
  | copy t s f =>
      simp_all [decodeEvent, rawScalarStep, LemmaG.Event.scal, LemmaG.Event.phys]
  | clear t f =>
      simp_all [decodeEvent, rawScalarStep, LemmaG.Event.scal, LemmaG.Event.phys]

/-- The auditor's centre copy does not require a clean input centre. -/
theorem copy_overwrites (t s : Register) (f : FrameLabel) (h : Register → M) :
    rawScalarStep (.copy t s f) h = some (Function.update h t (h s)) := rfl

/-- The explicit centre CLEAR affects its chosen register, not an implicit
coefficient-work register absent from the serialized local program. -/
theorem clear_writes_zero (t : Register) (f : FrameLabel) (h : Register → M) :
    rawScalarStep (.clear t f) h = some (Function.update h t 0) := rfl
end ScalarSemantics

/-- Coefficient interpretation leaves the exact label update unchanged. -/
theorem decoded_labels (e : LabelEvent) (decoded : ScalarEvent)
    (hdecode : decodeEvent e = some decoded) (labels : Register → FrameLabel) :
    decoded.lab labels = e.lab labels := by
  cases e with
  | relabel r a b => simp_all [decodeEvent, LemmaG.Event.lab]
  | add t s q =>
      by_cases hd : q.2 = 0 <;>
        simp_all [decodeEvent, decodeCoefficient, hd, LemmaG.Event.lab]
  | scale t q =>
      by_cases hd : q.2 = 0 <;>
        simp_all [decodeEvent, decodeCoefficient, hd, LemmaG.Event.lab]
  | copy t s f => simp_all [decodeEvent, LemmaG.Event.lab]
  | clear t f => simp_all [decodeEvent, LemmaG.Event.lab]

/-- Actual backward SCALE syntax includes this negative denominator. -/
theorem signed_denominator_example : decodeCoefficient (2, -1) = some (-2) := by
  decide +kernel

theorem zero_denominator_rejected (n : Int) : decodeCoefficient (n, 0) = none := by
  simp [decodeCoefficient]

end CurrentMain.F19ScalarEventInterpretation

#print axioms CurrentMain.F19ScalarEventInterpretation.decoded_step
#print axioms CurrentMain.F19ScalarEventInterpretation.copy_overwrites
#print axioms CurrentMain.F19ScalarEventInterpretation.clear_writes_zero
#print axioms CurrentMain.F19ScalarEventInterpretation.decoded_labels
#print axioms CurrentMain.F19ScalarEventInterpretation.signed_denominator_example
#print axioms CurrentMain.F19ScalarEventInterpretation.zero_denominator_rejected
