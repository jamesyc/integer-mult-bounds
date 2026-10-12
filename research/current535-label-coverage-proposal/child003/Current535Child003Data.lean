/- Exact current535 source rows10736..10780 in both orientations.
Fresh source literals, ending before current child2 begins at10781.
No operator, full-stream or omitted-adapter conclusion. -/
import Current535CoverageCheck

set_option Elab.async false
namespace CurrentMain.Current535Child003Data
open CurrentMain.CanonicalFrameCoverage
def forwardC : List (Row 997) := [
  ⟨10736, .relabel 488 0 3, none, some (1, 1)⟩,
  ⟨10737, .add 488 499 ((-1), (1)), some 3, none⟩,
  ⟨10738, .relabel 489 0 3, none, some (1, 1)⟩,
  ⟨10739, .add 489 499 ((-1), (1)), some 3, none⟩,
  ⟨10740, .relabel 498 0 3, none, some (1, 1)⟩,
  ⟨10741, .add 498 499 ((1), (1)), some 3, none⟩,
  ⟨10742, .relabel 486 0 3, none, some (1, 1)⟩,
  ⟨10743, .add 486 501 ((-1), (1)), some 3, none⟩,
  ⟨10744, .relabel 487 0 3, none, some (1, 1)⟩,
  ⟨10745, .add 487 501 ((-1), (1)), some 3, none⟩,
  ⟨10746, .relabel 500 0 3, none, some (1, 1)⟩,
  ⟨10747, .add 500 501 ((1), (1)), some 3, none⟩,
  ⟨10748, .relabel 536 0 3, none, some (1, 1)⟩,
  ⟨10749, .add 536 547 ((-1), (1)), some 3, none⟩,
  ⟨10750, .relabel 537 0 3, none, some (1, 1)⟩,
  ⟨10751, .add 537 547 ((-1), (1)), some 3, none⟩,
  ⟨10752, .relabel 546 0 3, none, some (1, 1)⟩,
  ⟨10753, .add 546 547 ((1), (1)), some 3, none⟩,
  ⟨10754, .relabel 534 0 3, none, some (1, 1)⟩,
  ⟨10755, .add 534 549 ((-1), (1)), some 3, none⟩,
  ⟨10756, .relabel 535 0 3, none, some (1, 1)⟩,
  ⟨10757, .add 535 549 ((-1), (1)), some 3, none⟩,
  ⟨10758, .relabel 548 0 3, none, some (1, 1)⟩,
  ⟨10759, .add 548 549 ((1), (1)), some 3, none⟩
]

def forwardD : List (Row 997) := [
  ⟨10760, .add 534 587 ((-2), (1)), some 3, none⟩,
  ⟨10761, .add 535 587 ((2), (1)), some 3, none⟩,
  ⟨10762, .relabel 586 0 3, none, some (1, 1)⟩,
  ⟨10763, .add 586 587 ((-1), (1)), some 3, none⟩,
  ⟨10764, .add 536 589 ((2), (1)), some 3, none⟩,
  ⟨10765, .add 537 589 ((2), (1)), some 3, none⟩,
  ⟨10766, .add 546 589 ((-4), (1)), some 3, none⟩,
  ⟨10767, .relabel 588 0 3, none, some (1, 1)⟩,
  ⟨10768, .add 588 589 ((-1), (1)), some 3, none⟩,
  ⟨10769, .add 534 598 ((-2), (1)), some 3, none⟩,
  ⟨10770, .add 548 598 ((2), (1)), some 3, none⟩,
  ⟨10771, .add 586 598 ((-1), (1)), some 3, none⟩,
  ⟨10772, .add 535 599 ((2), (1)), some 3, none⟩,
  ⟨10773, .add 548 599 ((-2), (1)), some 3, none⟩,
  ⟨10774, .add 586 599 ((-1), (1)), some 3, none⟩,
  ⟨10775, .add 536 600 ((2), (1)), some 3, none⟩,
  ⟨10776, .add 546 600 ((-2), (1)), some 3, none⟩,
  ⟨10777, .add 588 600 ((-1), (1)), some 3, none⟩,
  ⟨10778, .add 537 601 ((2), (1)), some 3, none⟩,
  ⟨10779, .add 546 601 ((-2), (1)), some 3, none⟩,
  ⟨10780, .add 588 601 ((-1), (1)), some 3, none⟩
]

def backwardC : List (Row 997) := [
  ⟨10736, .relabel 488 0 3, none, some (1, 1)⟩,
  ⟨10737, .add 499 488 ((1), (1)), some 3, none⟩,
  ⟨10738, .relabel 489 0 3, none, some (1, 1)⟩,
  ⟨10739, .add 499 489 ((1), (1)), some 3, none⟩,
  ⟨10740, .relabel 498 0 3, none, some (1, 1)⟩,
  ⟨10741, .add 499 498 ((-1), (1)), some 3, none⟩,
  ⟨10742, .relabel 486 0 3, none, some (1, 1)⟩,
  ⟨10743, .add 501 486 ((1), (1)), some 3, none⟩,
  ⟨10744, .relabel 487 0 3, none, some (1, 1)⟩,
  ⟨10745, .add 501 487 ((1), (1)), some 3, none⟩,
  ⟨10746, .relabel 500 0 3, none, some (1, 1)⟩,
  ⟨10747, .add 501 500 ((-1), (1)), some 3, none⟩,
  ⟨10748, .relabel 536 0 3, none, some (1, 1)⟩,
  ⟨10749, .add 547 536 ((1), (1)), some 3, none⟩,
  ⟨10750, .relabel 537 0 3, none, some (1, 1)⟩,
  ⟨10751, .add 547 537 ((1), (1)), some 3, none⟩,
  ⟨10752, .relabel 546 0 3, none, some (1, 1)⟩,
  ⟨10753, .add 547 546 ((-1), (1)), some 3, none⟩,
  ⟨10754, .relabel 534 0 3, none, some (1, 1)⟩,
  ⟨10755, .add 549 534 ((1), (1)), some 3, none⟩,
  ⟨10756, .relabel 535 0 3, none, some (1, 1)⟩,
  ⟨10757, .add 549 535 ((1), (1)), some 3, none⟩,
  ⟨10758, .relabel 548 0 3, none, some (1, 1)⟩,
  ⟨10759, .add 549 548 ((-1), (1)), some 3, none⟩
]

def backwardD : List (Row 997) := [
  ⟨10760, .add 587 534 ((2), (1)), some 3, none⟩,
  ⟨10761, .add 587 535 ((-2), (1)), some 3, none⟩,
  ⟨10762, .relabel 586 0 3, none, some (1, 1)⟩,
  ⟨10763, .add 587 586 ((1), (1)), some 3, none⟩,
  ⟨10764, .add 589 536 ((-2), (1)), some 3, none⟩,
  ⟨10765, .add 589 537 ((-2), (1)), some 3, none⟩,
  ⟨10766, .add 589 546 ((4), (1)), some 3, none⟩,
  ⟨10767, .relabel 588 0 3, none, some (1, 1)⟩,
  ⟨10768, .add 589 588 ((1), (1)), some 3, none⟩,
  ⟨10769, .add 598 534 ((2), (1)), some 3, none⟩,
  ⟨10770, .add 598 548 ((-2), (1)), some 3, none⟩,
  ⟨10771, .add 598 586 ((1), (1)), some 3, none⟩,
  ⟨10772, .add 599 535 ((-2), (1)), some 3, none⟩,
  ⟨10773, .add 599 548 ((2), (1)), some 3, none⟩,
  ⟨10774, .add 599 586 ((1), (1)), some 3, none⟩,
  ⟨10775, .add 600 536 ((-2), (1)), some 3, none⟩,
  ⟨10776, .add 600 546 ((2), (1)), some 3, none⟩,
  ⟨10777, .add 600 588 ((1), (1)), some 3, none⟩,
  ⟨10778, .add 601 537 ((-2), (1)), some 3, none⟩,
  ⟨10779, .add 601 546 ((2), (1)), some 3, none⟩,
  ⟨10780, .add 601 588 ((1), (1)), some 3, none⟩
]

def support69 : List Register := [488, 489, 498, 486, 487, 500, 536, 537, 546, 534, 535, 548]
def labels69 (r : Register) : FrameLabel 997 :=
  if r ∈ support69 then 3 else Current535CoverageData.labels45 r
def support90 : List Register := [586, 588]
def labels90 (r : Register) : FrameLabel 997 :=
  if r ∈ support90 then 3 else labels69 r
end CurrentMain.Current535Child003Data
