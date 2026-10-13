/- Exact current PR799 next16 rows, zero-based raw9274..9289, both orientations.
Only canonical labels/catalog coverage; current record3 operator and actual entrance execution remain separate.
Author-checked conditional source context: kappa=1661634653669567/1000000000000000000.
Attribution: selected PR799 source and accepted PR509/checker interfaces. -/
import Current799First33CoverageCheck

set_option Elab.async false
namespace CurrentMain.Current799Next16Data
open CurrentMain.CanonicalFrameCoverage
def children : Array (ChildKey 1005) := #[
  ⟨0, 2, 1⟩,
  ⟨0, 3, 1⟩,
  ⟨0, 4, 1⟩,
  ⟨0, 5, 1⟩
]

def forwardC : List (Row 1005) := [
  ⟨9274, .relabel 474 0 5, none, some (3, 1)⟩,
  ⟨9275, .add 474 488 ((-1), (1)), some 5, none⟩,
  ⟨9276, .relabel 475 0 5, none, some (3, 1)⟩,
  ⟨9277, .add 475 489 ((-1), (1)), some 5, none⟩,
  ⟨9278, .relabel 480 0 5, none, some (3, 1)⟩,
  ⟨9279, .add 480 536 ((1), (2)), some 5, none⟩,
  ⟨9280, .relabel 481 0 5, none, some (3, 1)⟩,
  ⟨9281, .add 481 537 ((1), (2)), some 5, none⟩,
  ⟨9282, .relabel 490 0 5, none, some (3, 1)⟩,
  ⟨9283, .add 490 538 ((-1), (1)), some 5, none⟩,
  ⟨9284, .relabel 491 0 5, none, some (3, 1)⟩,
  ⟨9285, .add 491 539 ((-1), (1)), some 5, none⟩,
  ⟨9286, .relabel 526 0 5, none, some (3, 1)⟩,
  ⟨9287, .add 526 574 ((-1), (1)), some 5, none⟩,
  ⟨9288, .relabel 527 0 5, none, some (3, 1)⟩,
  ⟨9289, .add 527 575 ((-1), (1)), some 5, none⟩
]

def backwardC : List (Row 1005) := [
  ⟨9274, .relabel 474 0 5, none, some (3, 1)⟩,
  ⟨9275, .add 488 474 ((1), (1)), some 5, none⟩,
  ⟨9276, .relabel 475 0 5, none, some (3, 1)⟩,
  ⟨9277, .add 489 475 ((1), (1)), some 5, none⟩,
  ⟨9278, .relabel 480 0 5, none, some (3, 1)⟩,
  ⟨9279, .add 536 480 ((-1), (2)), some 5, none⟩,
  ⟨9280, .relabel 481 0 5, none, some (3, 1)⟩,
  ⟨9281, .add 537 481 ((-1), (2)), some 5, none⟩,
  ⟨9282, .relabel 490 0 5, none, some (3, 1)⟩,
  ⟨9283, .add 538 490 ((1), (1)), some 5, none⟩,
  ⟨9284, .relabel 491 0 5, none, some (3, 1)⟩,
  ⟨9285, .add 539 491 ((1), (1)), some 5, none⟩,
  ⟨9286, .relabel 526 0 5, none, some (3, 1)⟩,
  ⟨9287, .add 574 526 ((1), (1)), some 5, none⟩,
  ⟨9288, .relabel 527 0 5, none, some (3, 1)⟩,
  ⟨9289, .add 575 527 ((1), (1)), some 5, none⟩
]

def data : SelectedData 1005 :=
  ⟨Current799First33CoverageData.frameDimensions,
    Current799First33CoverageData.initialOriginalLabels, children, forwardC, backwardC⟩
def support49 : List Register := [474, 475, 480, 481, 490, 491, 526, 527]
def labels49 (r : Register) : FrameLabel 1005 :=
  if r ∈ support49 then 5 else Current799First33CoverageData.labels33 r
end CurrentMain.Current799Next16Data
