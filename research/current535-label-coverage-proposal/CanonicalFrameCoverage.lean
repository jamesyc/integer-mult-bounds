/- Parameterized canonical-frame coverage helper for the selected h=9 source.
The Boolean tests and proofs are generalized from the accepted f19 coverage modules.
PR509 Stream/WellLabelled: DreamingOfClouds (Claude-assisted), pinned unchanged.
No whole-stream, omitted-adapter, scalar endpoint or operator realization claim.
Apache-2.0. Prepared with OpenAI assistance. -/
import PR509Stream

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
namespace CurrentMain.CanonicalFrameCoverage

abbrev Register := Fin 736 -- L0..727, then C0..7
abbrev FrameLabel (frameCount : Nat) := Fin frameCount
/-- Exact signed numerator/denominator syntax; no scalar interpretation here. -/
abbrev CoefficientCode := Int × Int
abbrev LabelEvent (frameCount : Nat) := LemmaG.Event Register (FrameLabel frameCount) CoefficientCode

/-- Only the key/rank projection of a retained directed child record. -/
structure ChildKey (frameCount : Nat) where
  oldFrame : (FrameLabel frameCount)
  newFrame : (FrameLabel frameCount)
  rank : Nat

/-- Each retained row carries its original zero-based LOCAL-PROGRAMS index. -/
structure Row (frameCount : Nat) where
  sourceIndex : Nat
  event : (LabelEvent frameCount)
  scalarFrame : Option (FrameLabel frameCount)
  childRef : Option (Nat × Nat) -- original child ordinal and emitted rank

structure SelectedData (frameCount : Nat) where
  frameDimensions : Array Nat
  initialOriginalLabels : Array (FrameLabel frameCount)
  children : Array (ChildKey frameCount)
  forward : List (Row frameCount)
  backward : List (Row frameCount)

variable {frameCount : Nat}

/-- Canonical labels only. The default label is supplied explicitly; no hidden finite-cardinality assumption. -/
def initialLabels (zero : FrameLabel frameCount) (p : (SelectedData frameCount)) (r : Register) : (FrameLabel frameCount) :=
  if r.val < 728 then (p.initialOriginalLabels[r.val]?).getD zero else zero

/-- The exact finite equality test underlying PR509 Event.Admissible. -/
def admissibleB (e : (LabelEvent frameCount)) (labels : Register → (FrameLabel frameCount)) : Bool :=
  match e with
  | .relabel r a _ => labels r == a
  | .add t s _ => labels t == labels s
  | .copy _ r f => labels r == f
  | .scale .. => true
  | .clear .. => true

/-- Keep the literal scalar row's declared frame and coefficient syntax. -/
def scalarAnnotationB (row : (Row frameCount)) (labels : Register → (FrameLabel frameCount)) : Bool :=
  match row.event with
  | .relabel .. => row.scalarFrame.isNone
  | .add t s q =>
      row.scalarFrame == some (labels t) && labels t == labels s && q.2 != 0
  | .scale t q => row.scalarFrame == some (labels t) && q.2 != 0
  | .copy _ _ f => row.scalarFrame == some f
  | .clear _ f => row.scalarFrame == some f

/-- Directed lookup is by retained array ordinal, never a sorted/reversed key. -/
def childReferenceB (p : (SelectedData frameCount)) (row : (Row frameCount)) : Bool :=
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
def checkRows (p : (SelectedData frameCount)) : List (Row frameCount) → (Register → (FrameLabel frameCount)) → Bool
  | [], _ => true
  | row :: rows, labels =>
      admissibleB row.event labels && (scalarAnnotationB row labels &&
        (childReferenceB p row && checkRows p rows (row.event.lab labels)))

/-- Only Boolean equality soundness; no physical or scalar realization induction. -/
theorem admissibleB_sound (e : (LabelEvent frameCount)) (labels : Register → (FrameLabel frameCount))
    (h : admissibleB e labels = true) : e.Admissible labels := by
  cases e <;> simp_all [admissibleB, LemmaG.Event.Admissible]

/-- Reuse the upstream structural label predicate on the exact supplied rows. -/
theorem checkRows_wellLabelled (p : (SelectedData frameCount)) (rows : List (Row frameCount))
    (labels : Register → (FrameLabel frameCount)) (h : checkRows p rows labels = true) :
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

def labelRowsB : List (Row frameCount) → (Register → (FrameLabel frameCount)) → Bool
  | [], _ => true
  | row :: rows, labels =>
      admissibleB row.event labels &&
        (scalarAnnotationB row labels && labelRowsB rows (row.event.lab labels))

def childRowsB (p : (SelectedData frameCount)) : List (Row frameCount) → Bool
  | [] => true
  | row :: rows => childReferenceB p row && childRowsB p rows

theorem checkRows_factor (p : (SelectedData frameCount)) (rows : List (Row frameCount))
    (labels : Register → (FrameLabel frameCount)) :
    checkRows p rows labels = (labelRowsB rows labels && childRowsB p rows) := by
  induction rows generalizing labels with
  | nil => rfl
  | cons row rows ih =>
      simp only [checkRows, labelRowsB, childRowsB, ih,
        Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

def supportedB (support : List Register) (e : (LabelEvent frameCount)) : Bool :=
  match e with
  | .relabel r .. => support.contains r
  | .copy r .. => support.contains r
  | .clear r .. => support.contains r
  | .add .. => true
  | .scale .. => true

private theorem supported_moves (support : List Register) (e : (LabelEvent frameCount)) (r : Register)
    (hs : supportedB support e = true) (hm : e.moves r) : r ∈ support := by
  cases e <;> simp_all [supportedB, LemmaG.Event.moves]

/-- The retained untouched-register API permits an arbitrary value at each changed label.
There is no cleanliness, scalar-state, or physical chart hypothesis. -/
theorem sparse_checkpoint (rows : List (Row frameCount)) (labels values : Register → (FrameLabel frameCount))
    (support : List Register)
    (hs : (rows.map Row.event).all (supportedB support) = true)
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

#print axioms admissibleB_sound
#print axioms checkRows_wellLabelled
#print axioms checkRows_factor
#print axioms sparse_checkpoint
end CurrentMain.CanonicalFrameCoverage
