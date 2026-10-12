/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageStaticGapCheckB
namespace CurrentMain.F19SelectedCoverage.Child6Data
open CurrentMain.F19SelectedCoverage

def new719 : List Register := [488, 489, 498, 486, 487, 500, 536, 537, 546, 534, 535, 548]
def labels719 (r : Register) : FrameLabel :=
  if r ∈ new719 then 8 else StaticGapData.labels695 r

def new743 : List Register := [586, 588, 656, 657]
def labels743 (r : Register) : FrameLabel :=
  if r ∈ new743 then 8 else labels719 r

def forwardS : List Row := [
  ⟨11546, .relabel 488 0 8, none, some (6, 1)⟩,
  ⟨11547, .add 488 499 ((-1), (1)), some 8, none⟩,
  ⟨11548, .relabel 489 0 8, none, some (6, 1)⟩,
  ⟨11549, .add 489 499 ((-1), (1)), some 8, none⟩,
  ⟨11550, .relabel 498 0 8, none, some (6, 1)⟩,
  ⟨11551, .add 498 499 ((1), (1)), some 8, none⟩,
  ⟨11552, .relabel 486 0 8, none, some (6, 1)⟩,
  ⟨11553, .add 486 501 ((-1), (1)), some 8, none⟩,
  ⟨11554, .relabel 487 0 8, none, some (6, 1)⟩,
  ⟨11555, .add 487 501 ((-1), (1)), some 8, none⟩,
  ⟨11556, .relabel 500 0 8, none, some (6, 1)⟩,
  ⟨11557, .add 500 501 ((1), (1)), some 8, none⟩,
  ⟨11558, .relabel 536 0 8, none, some (6, 1)⟩,
  ⟨11559, .add 536 547 ((-1), (1)), some 8, none⟩,
  ⟨11560, .relabel 537 0 8, none, some (6, 1)⟩,
  ⟨11561, .add 537 547 ((-1), (1)), some 8, none⟩,
  ⟨11562, .relabel 546 0 8, none, some (6, 1)⟩,
  ⟨11563, .add 546 547 ((1), (1)), some 8, none⟩,
  ⟨11564, .relabel 534 0 8, none, some (6, 1)⟩,
  ⟨11565, .add 534 549 ((-1), (1)), some 8, none⟩,
  ⟨11566, .relabel 535 0 8, none, some (6, 1)⟩,
  ⟨11567, .add 535 549 ((-1), (1)), some 8, none⟩,
  ⟨11568, .relabel 548 0 8, none, some (6, 1)⟩,
  ⟨11569, .add 548 549 ((1), (1)), some 8, none⟩
]

def backwardS : List Row := [
  ⟨11546, .relabel 488 0 8, none, some (6, 1)⟩,
  ⟨11547, .add 499 488 ((1), (1)), some 8, none⟩,
  ⟨11548, .relabel 489 0 8, none, some (6, 1)⟩,
  ⟨11549, .add 499 489 ((1), (1)), some 8, none⟩,
  ⟨11550, .relabel 498 0 8, none, some (6, 1)⟩,
  ⟨11551, .add 499 498 ((-1), (1)), some 8, none⟩,
  ⟨11552, .relabel 486 0 8, none, some (6, 1)⟩,
  ⟨11553, .add 501 486 ((1), (1)), some 8, none⟩,
  ⟨11554, .relabel 487 0 8, none, some (6, 1)⟩,
  ⟨11555, .add 501 487 ((1), (1)), some 8, none⟩,
  ⟨11556, .relabel 500 0 8, none, some (6, 1)⟩,
  ⟨11557, .add 501 500 ((-1), (1)), some 8, none⟩,
  ⟨11558, .relabel 536 0 8, none, some (6, 1)⟩,
  ⟨11559, .add 547 536 ((1), (1)), some 8, none⟩,
  ⟨11560, .relabel 537 0 8, none, some (6, 1)⟩,
  ⟨11561, .add 547 537 ((1), (1)), some 8, none⟩,
  ⟨11562, .relabel 546 0 8, none, some (6, 1)⟩,
  ⟨11563, .add 547 546 ((-1), (1)), some 8, none⟩,
  ⟨11564, .relabel 534 0 8, none, some (6, 1)⟩,
  ⟨11565, .add 549 534 ((1), (1)), some 8, none⟩,
  ⟨11566, .relabel 535 0 8, none, some (6, 1)⟩,
  ⟨11567, .add 549 535 ((1), (1)), some 8, none⟩,
  ⟨11568, .relabel 548 0 8, none, some (6, 1)⟩,
  ⟨11569, .add 549 548 ((-1), (1)), some 8, none⟩
]

def forwardT : List Row := [
  ⟨11570, .add 534 587 ((-2), (1)), some 8, none⟩,
  ⟨11571, .add 535 587 ((2), (1)), some 8, none⟩,
  ⟨11572, .relabel 586 0 8, none, some (6, 1)⟩,
  ⟨11573, .add 586 587 ((-1), (1)), some 8, none⟩,
  ⟨11574, .add 536 589 ((2), (1)), some 8, none⟩,
  ⟨11575, .add 537 589 ((2), (1)), some 8, none⟩,
  ⟨11576, .add 546 589 ((-4), (1)), some 8, none⟩,
  ⟨11577, .relabel 588 0 8, none, some (6, 1)⟩,
  ⟨11578, .add 588 589 ((-1), (1)), some 8, none⟩,
  ⟨11579, .add 534 598 ((-2), (1)), some 8, none⟩,
  ⟨11580, .add 548 598 ((2), (1)), some 8, none⟩,
  ⟨11581, .add 586 598 ((-1), (1)), some 8, none⟩,
  ⟨11582, .add 535 599 ((2), (1)), some 8, none⟩,
  ⟨11583, .add 548 599 ((-2), (1)), some 8, none⟩,
  ⟨11584, .add 586 599 ((-1), (1)), some 8, none⟩,
  ⟨11585, .add 536 600 ((2), (1)), some 8, none⟩,
  ⟨11586, .add 546 600 ((-2), (1)), some 8, none⟩,
  ⟨11587, .add 588 600 ((-1), (1)), some 8, none⟩,
  ⟨11588, .add 537 601 ((2), (1)), some 8, none⟩,
  ⟨11589, .add 546 601 ((-2), (1)), some 8, none⟩,
  ⟨11590, .add 588 601 ((-1), (1)), some 8, none⟩,
  ⟨11591, .relabel 656 0 8, none, some (6, 1)⟩,
  ⟨11592, .add 656 659 ((-1), (1)), some 8, none⟩,
  ⟨11593, .relabel 657 0 8, none, some (6, 1)⟩
]

def backwardT : List Row := [
  ⟨11570, .add 587 534 ((2), (1)), some 8, none⟩,
  ⟨11571, .add 587 535 ((-2), (1)), some 8, none⟩,
  ⟨11572, .relabel 586 0 8, none, some (6, 1)⟩,
  ⟨11573, .add 587 586 ((1), (1)), some 8, none⟩,
  ⟨11574, .add 589 536 ((-2), (1)), some 8, none⟩,
  ⟨11575, .add 589 537 ((-2), (1)), some 8, none⟩,
  ⟨11576, .add 589 546 ((4), (1)), some 8, none⟩,
  ⟨11577, .relabel 588 0 8, none, some (6, 1)⟩,
  ⟨11578, .add 589 588 ((1), (1)), some 8, none⟩,
  ⟨11579, .add 598 534 ((2), (1)), some 8, none⟩,
  ⟨11580, .add 598 548 ((-2), (1)), some 8, none⟩,
  ⟨11581, .add 598 586 ((1), (1)), some 8, none⟩,
  ⟨11582, .add 599 535 ((-2), (1)), some 8, none⟩,
  ⟨11583, .add 599 548 ((2), (1)), some 8, none⟩,
  ⟨11584, .add 599 586 ((1), (1)), some 8, none⟩,
  ⟨11585, .add 600 536 ((-2), (1)), some 8, none⟩,
  ⟨11586, .add 600 546 ((2), (1)), some 8, none⟩,
  ⟨11587, .add 600 588 ((1), (1)), some 8, none⟩,
  ⟨11588, .add 601 537 ((-2), (1)), some 8, none⟩,
  ⟨11589, .add 601 546 ((2), (1)), some 8, none⟩,
  ⟨11590, .add 601 588 ((1), (1)), some 8, none⟩,
  ⟨11591, .relabel 656 0 8, none, some (6, 1)⟩,
  ⟨11592, .add 659 656 ((1), (1)), some 8, none⟩,
  ⟨11593, .relabel 657 0 8, none, some (6, 1)⟩
]

end CurrentMain.F19SelectedCoverage.Child6Data
