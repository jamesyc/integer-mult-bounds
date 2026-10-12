/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild5TailCheck
namespace CurrentMain.F19SelectedCoverage.Child5BodyData
open CurrentMain.F19SelectedCoverage

def new481 : List Register := [566, 567]
def labels481 (r : Register) : FrameLabel :=
  if r ∈ new481 then 7 else Child5TailData.labels457 r

def new501 : List Register := []
def labels501 (r : Register) : FrameLabel :=
  if r ∈ new501 then 7 else labels481 r

def forwardI : List Row := [
  ⟨11308, .add 511 674 ((1), (1)), some 7, none⟩,
  ⟨11309, .add 513 674 ((-1), (1)), some 7, none⟩,
  ⟨11310, .add 518 674 ((-1), (1)), some 7, none⟩,
  ⟨11311, .add 522 674 ((1), (1)), some 7, none⟩,
  ⟨11312, .add 524 674 ((-1), (1)), some 7, none⟩,
  ⟨11313, .relabel 566 0 7, none, some (5, 1)⟩,
  ⟨11314, .add 566 674 ((1), (2)), some 7, none⟩,
  ⟨11315, .relabel 567 0 7, none, some (5, 1)⟩,
  ⟨11316, .add 567 674 ((1), (2)), some 7, none⟩,
  ⟨11317, .add 578 674 ((1), (2)), some 7, none⟩,
  ⟨11318, .add 579 674 ((-1), (2)), some 7, none⟩,
  ⟨11319, .add 640 674 ((-1), (1)), some 7, none⟩,
  ⟨11320, .add 641 674 ((-1), (1)), some 7, none⟩,
  ⟨11321, .add 642 674 ((2), (1)), some 7, none⟩,
  ⟨11322, .add 648 674 ((-1), (1)), some 7, none⟩,
  ⟨11323, .add 649 674 ((1), (1)), some 7, none⟩,
  ⟨11324, .add 672 674 ((-1), (1)), some 7, none⟩,
  ⟨11325, .add 511 675 ((-1), (1)), some 7, none⟩,
  ⟨11326, .add 513 675 ((-1), (1)), some 7, none⟩,
  ⟨11327, .add 519 675 ((1), (1)), some 7, none⟩,
  ⟨11328, .add 522 675 ((1), (1)), some 7, none⟩,
  ⟨11329, .add 524 675 ((1), (1)), some 7, none⟩,
  ⟨11330, .add 559 675 ((2), (1)), some 7, none⟩,
  ⟨11331, .add 566 675 ((-1), (2)), some 7, none⟩
]

def backwardI : List Row := [
  ⟨11308, .add 674 511 ((-1), (1)), some 7, none⟩,
  ⟨11309, .add 674 513 ((1), (1)), some 7, none⟩,
  ⟨11310, .add 674 518 ((1), (1)), some 7, none⟩,
  ⟨11311, .add 674 522 ((-1), (1)), some 7, none⟩,
  ⟨11312, .add 674 524 ((1), (1)), some 7, none⟩,
  ⟨11313, .relabel 566 0 7, none, some (5, 1)⟩,
  ⟨11314, .add 674 566 ((-1), (2)), some 7, none⟩,
  ⟨11315, .relabel 567 0 7, none, some (5, 1)⟩,
  ⟨11316, .add 674 567 ((-1), (2)), some 7, none⟩,
  ⟨11317, .add 674 578 ((-1), (2)), some 7, none⟩,
  ⟨11318, .add 674 579 ((1), (2)), some 7, none⟩,
  ⟨11319, .add 674 640 ((1), (1)), some 7, none⟩,
  ⟨11320, .add 674 641 ((1), (1)), some 7, none⟩,
  ⟨11321, .add 674 642 ((-2), (1)), some 7, none⟩,
  ⟨11322, .add 674 648 ((1), (1)), some 7, none⟩,
  ⟨11323, .add 674 649 ((-1), (1)), some 7, none⟩,
  ⟨11324, .add 674 672 ((1), (1)), some 7, none⟩,
  ⟨11325, .add 675 511 ((1), (1)), some 7, none⟩,
  ⟨11326, .add 675 513 ((1), (1)), some 7, none⟩,
  ⟨11327, .add 675 519 ((-1), (1)), some 7, none⟩,
  ⟨11328, .add 675 522 ((-1), (1)), some 7, none⟩,
  ⟨11329, .add 675 524 ((-1), (1)), some 7, none⟩,
  ⟨11330, .add 675 559 ((-2), (1)), some 7, none⟩,
  ⟨11331, .add 675 566 ((1), (2)), some 7, none⟩
]

def forwardJ : List Row := [
  ⟨11332, .add 567 675 ((-1), (2)), some 7, none⟩,
  ⟨11333, .add 572 675 ((-2), (1)), some 7, none⟩,
  ⟨11334, .add 578 675 ((1), (2)), some 7, none⟩,
  ⟨11335, .add 579 675 ((-1), (2)), some 7, none⟩,
  ⟨11336, .add 640 675 ((1), (1)), some 7, none⟩,
  ⟨11337, .add 641 675 ((1), (1)), some 7, none⟩,
  ⟨11338, .add 642 675 ((-2), (1)), some 7, none⟩,
  ⟨11339, .add 648 675 ((-1), (1)), some 7, none⟩,
  ⟨11340, .add 649 675 ((1), (1)), some 7, none⟩,
  ⟨11341, .add 672 675 ((-1), (1)), some 7, none⟩,
  ⟨11342, .add 513 677 ((-2), (1)), some 7, none⟩,
  ⟨11343, .add 518 677 ((-1), (1)), some 7, none⟩,
  ⟨11344, .add 519 677 ((1), (1)), some 7, none⟩,
  ⟨11345, .add 522 677 ((2), (1)), some 7, none⟩,
  ⟨11346, .add 559 677 ((2), (1)), some 7, none⟩,
  ⟨11347, .add 572 677 ((-2), (1)), some 7, none⟩,
  ⟨11348, .add 578 677 ((1), (1)), some 7, none⟩,
  ⟨11349, .add 579 677 ((-1), (1)), some 7, none⟩,
  ⟨11350, .add 648 677 ((-2), (1)), some 7, none⟩,
  ⟨11351, .add 649 677 ((2), (1)), some 7, none⟩
]

def backwardJ : List Row := [
  ⟨11332, .add 675 567 ((1), (2)), some 7, none⟩,
  ⟨11333, .add 675 572 ((2), (1)), some 7, none⟩,
  ⟨11334, .add 675 578 ((-1), (2)), some 7, none⟩,
  ⟨11335, .add 675 579 ((1), (2)), some 7, none⟩,
  ⟨11336, .add 675 640 ((-1), (1)), some 7, none⟩,
  ⟨11337, .add 675 641 ((-1), (1)), some 7, none⟩,
  ⟨11338, .add 675 642 ((2), (1)), some 7, none⟩,
  ⟨11339, .add 675 648 ((1), (1)), some 7, none⟩,
  ⟨11340, .add 675 649 ((-1), (1)), some 7, none⟩,
  ⟨11341, .add 675 672 ((1), (1)), some 7, none⟩,
  ⟨11342, .add 677 513 ((2), (1)), some 7, none⟩,
  ⟨11343, .add 677 518 ((1), (1)), some 7, none⟩,
  ⟨11344, .add 677 519 ((-1), (1)), some 7, none⟩,
  ⟨11345, .add 677 522 ((-2), (1)), some 7, none⟩,
  ⟨11346, .add 677 559 ((-2), (1)), some 7, none⟩,
  ⟨11347, .add 677 572 ((2), (1)), some 7, none⟩,
  ⟨11348, .add 677 578 ((-1), (1)), some 7, none⟩,
  ⟨11349, .add 677 579 ((1), (1)), some 7, none⟩,
  ⟨11350, .add 677 648 ((2), (1)), some 7, none⟩,
  ⟨11351, .add 677 649 ((-2), (1)), some 7, none⟩
]

end CurrentMain.F19SelectedCoverage.Child5BodyData
