/-
Source-only proposal for the exact f19 selected canonical-frame macro projection.
No selected data, proof, compilation result, or physical endpoint is claimed here.
Reuses Lemma G by DreamingOfClouds (Claude-assisted), PR509, unchanged.
The upstream direct-delivery emitter/auditor attribution stays in SOURCE_PINS.json.
Apache-2.0. Prepared with OpenAI assistance.
-/
import PR509Stream

namespace CurrentMain.F19SelectedCoverage

abbrev Register := Fin 736 -- L0..727, then C0..7
abbrev FrameLabel := Fin 983
/-- Exact signed numerator/denominator syntax; no scalar interpretation here. -/
abbrev CoefficientCode := Int × Int
abbrev LabelEvent := LemmaG.Event Register FrameLabel CoefficientCode

/-- Only the key/rank projection of a retained directed child record. -/
structure ChildKey where
  oldFrame : FrameLabel
  newFrame : FrameLabel
  rank : Nat

/-- Each retained row carries its original zero-based LOCAL-PROGRAMS index. -/
structure Row where
  sourceIndex : Nat
  event : LabelEvent
  scalarFrame : Option FrameLabel
  childRef : Option (Nat × Nat) -- original child ordinal and emitted rank

structure SelectedData where
  frameDimensions : Array Nat
  initialOriginalLabels : Array FrameLabel
  children : Array ChildKey
  forward : List Row
  backward : List Row

/-- These are canonical-frame labels, not boundary adapter/operator charts. -/
def initialLabels (p : SelectedData) (r : Register) : FrameLabel :=
  if r.val < 728 then (p.initialOriginalLabels[r.val]?).getD 0 else 0

/-- The exact finite equality test underlying PR509 Event.Admissible. -/
def admissibleB (e : LabelEvent) (labels : Register → FrameLabel) : Bool :=
  match e with
  | .relabel r a _ => labels r == a
  | .add t s _ => labels t == labels s
  | .copy _ r f => labels r == f
  | .scale .. => true
  | .clear .. => true

/-- Keep the literal scalar row's declared frame and coefficient syntax. -/
def scalarAnnotationB (row : Row) (labels : Register → FrameLabel) : Bool :=
  match row.event with
  | .relabel .. => row.scalarFrame.isNone
  | .add t s q =>
      row.scalarFrame == some (labels t) && labels t == labels s && q.2 != 0
  | .scale t q => row.scalarFrame == some (labels t) && q.2 != 0
  | .copy _ _ f => row.scalarFrame == some f
  | .clear _ f => row.scalarFrame == some f

/-- Directed lookup is by retained array ordinal, never a sorted/reversed key. -/
def childReferenceB (p : SelectedData) (row : Row) : Bool :=
  match row.event, row.childRef with
  | .relabel _ a b, some (ordinal, emittedRank) =>
      match p.children[ordinal]? with
      | none => false
      | some child =>
          let da := p.frameDimensions[a.val]!
          let db := p.frameDimensions[b.val]!
          let difference := if da ≤ db then db - da else da - db
          child.oldFrame == a && child.newFrame == b &&
            child.rank == emittedRank && emittedRank == difference &&
            decide (0 < emittedRank ∧ emittedRank ≤ 9)
  | .relabel .., none => false
  | _, none => true
  | _, some _ => false

/-- Labels evolve exactly by the accepted PR509 Event.lab operation. -/
def checkRows (p : SelectedData) : List Row → (Register → FrameLabel) → Bool
  | [], _ => true
  | row :: rows, labels =>
      admissibleB row.event labels && (scalarAnnotationB row labels &&
        (childReferenceB p row && checkRows p rows (row.event.lab labels)))

/-- No retained event may be duplicated, reordered, or given an out-of-range index. -/
def sourceIndicesB (next : Nat) : List Row → Bool
  | [] => true
  | row :: rows =>
      decide (next ≤ row.sourceIndex ∧ row.sourceIndex < 22937) &&
        sourceIndicesB (row.sourceIndex + 1) rows

/-- The concrete proposed finite goal. Exact data emission is a separate held step. -/
def checkSelected (p : SelectedData) : Bool :=
  p.frameDimensions.size == 983 && p.initialOriginalLabels.size == 728 &&
    p.children.size == 2922 && p.forward.length == 21320 &&
    p.backward.length == 21320 &&
    sourceIndicesB 0 p.forward && sourceIndicesB 0 p.backward &&
    checkRows p p.forward (initialLabels p) &&
    checkRows p p.backward (initialLabels p)

def SelectedCertificate (p : SelectedData) : Prop := checkSelected p = true

/-- Intended consequence after a separately reviewed Boolean soundness bridge.
This is a proposition definition, not a proved theorem or a physical-word claim. -/
def ProjectedWellLabelled (p : SelectedData) : Prop :=
  LemmaG.Stream.WellLabelled (p.forward.map Row.event) (initialLabels p) ∧
  LemmaG.Stream.WellLabelled (p.backward.map Row.event) (initialLabels p)

/-- The pilot covers exactly raw source rows 10851 through 10978, inclusive. -/
def pilotShapeB (p : SelectedData) : Bool :=
  p.frameDimensions.size == 983 && p.initialOriginalLabels.size == 728 &&
    p.children.size == 2922 &&
    p.forward.map Row.sourceIndex == List.range' 10851 128 &&
    p.backward.map Row.sourceIndex == List.range' 10851 128

def checkPilot (p : SelectedData) : Bool :=
  pilotShapeB p && (checkRows p p.forward (initialLabels p) &&
    checkRows p p.backward (initialLabels p))

/-- Only Boolean equality soundness; no physical or scalar realization induction. -/
theorem admissibleB_sound (e : LabelEvent) (labels : Register → FrameLabel)
    (h : admissibleB e labels = true) : e.Admissible labels := by
  cases e <;> simp_all [admissibleB, LemmaG.Event.Admissible]

/-- Reuse the upstream structural label predicate on the exact supplied rows. -/
theorem checkRows_wellLabelled (p : SelectedData) (rows : List Row)
    (labels : Register → FrameLabel) (h : checkRows p rows labels = true) :
    LemmaG.Stream.WellLabelled (rows.map Row.event) labels := by
  induction rows generalizing labels with
  | nil => trivial
  | cons row rows ih =>
      change (admissibleB row.event labels && (scalarAnnotationB row labels &&
        (childReferenceB p row && checkRows p rows (row.event.lab labels)))) = true at h
      have ha := (Bool.and_eq_true_iff.mp h).1
      have ht := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp h).2).2).2
      change row.event.Admissible labels ∧
        LemmaG.Stream.WellLabelled (rows.map Row.event) (row.event.lab labels)
      exact ⟨admissibleB_sound row.event labels ha, ih _ ht⟩

theorem checkPilot_wellLabelled (p : SelectedData) (h : checkPilot p = true) :
    ProjectedWellLabelled p := by
  have ht := (Bool.and_eq_true_iff.mp h).2
  exact ⟨checkRows_wellLabelled p p.forward (initialLabels p) (Bool.and_eq_true_iff.mp ht).1,
    checkRows_wellLabelled p p.backward (initialLabels p) (Bool.and_eq_true_iff.mp ht).2⟩

end CurrentMain.F19SelectedCoverage

#print axioms CurrentMain.F19SelectedCoverage.admissibleB_sound
#print axioms CurrentMain.F19SelectedCoverage.checkRows_wellLabelled
#print axioms CurrentMain.F19SelectedCoverage.checkPilot_wellLabelled
