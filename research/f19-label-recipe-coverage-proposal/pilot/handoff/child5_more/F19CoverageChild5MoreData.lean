/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild5BodyCheck
namespace CurrentMain.F19SelectedCoverage.Child5MoreData
open CurrentMain.F19SelectedCoverage

def new525 : List Register := [676]
def labels525 (r : Register) : FrameLabel :=
  if r ∈ new525 then 7 else Child5BodyData.labels501 r

def new549 : List Register := [454, 455, 530, 531]
def labels549 (r : Register) : FrameLabel :=
  if r ∈ new549 then 7 else labels525 r

def forwardK : List Row := [
  ⟨11352, .relabel 676 0 7, none, some (5, 1)⟩,
  ⟨11353, .add 676 677 ((-1), (1)), some 7, none⟩,
  ⟨11354, .add 511 678 ((1), (1)), some 7, none⟩,
  ⟨11355, .add 513 678 ((-1), (1)), some 7, none⟩,
  ⟨11356, .add 518 678 ((-1), (1)), some 7, none⟩,
  ⟨11357, .add 522 678 ((1), (1)), some 7, none⟩,
  ⟨11358, .add 524 678 ((-1), (1)), some 7, none⟩,
  ⟨11359, .add 566 678 ((1), (2)), some 7, none⟩,
  ⟨11360, .add 567 678 ((1), (2)), some 7, none⟩,
  ⟨11361, .add 578 678 ((1), (2)), some 7, none⟩,
  ⟨11362, .add 579 678 ((-1), (2)), some 7, none⟩,
  ⟨11363, .add 640 678 ((-1), (1)), some 7, none⟩,
  ⟨11364, .add 641 678 ((-1), (1)), some 7, none⟩,
  ⟨11365, .add 642 678 ((2), (1)), some 7, none⟩,
  ⟨11366, .add 648 678 ((-1), (1)), some 7, none⟩,
  ⟨11367, .add 649 678 ((1), (1)), some 7, none⟩,
  ⟨11368, .add 676 678 ((-1), (1)), some 7, none⟩,
  ⟨11369, .add 511 679 ((-1), (1)), some 7, none⟩,
  ⟨11370, .add 513 679 ((-1), (1)), some 7, none⟩,
  ⟨11371, .add 519 679 ((1), (1)), some 7, none⟩,
  ⟨11372, .add 522 679 ((1), (1)), some 7, none⟩,
  ⟨11373, .add 524 679 ((1), (1)), some 7, none⟩,
  ⟨11374, .add 559 679 ((2), (1)), some 7, none⟩,
  ⟨11375, .add 566 679 ((-1), (2)), some 7, none⟩
]

def backwardK : List Row := [
  ⟨11352, .relabel 676 0 7, none, some (5, 1)⟩,
  ⟨11353, .add 677 676 ((1), (1)), some 7, none⟩,
  ⟨11354, .add 678 511 ((-1), (1)), some 7, none⟩,
  ⟨11355, .add 678 513 ((1), (1)), some 7, none⟩,
  ⟨11356, .add 678 518 ((1), (1)), some 7, none⟩,
  ⟨11357, .add 678 522 ((-1), (1)), some 7, none⟩,
  ⟨11358, .add 678 524 ((1), (1)), some 7, none⟩,
  ⟨11359, .add 678 566 ((-1), (2)), some 7, none⟩,
  ⟨11360, .add 678 567 ((-1), (2)), some 7, none⟩,
  ⟨11361, .add 678 578 ((-1), (2)), some 7, none⟩,
  ⟨11362, .add 678 579 ((1), (2)), some 7, none⟩,
  ⟨11363, .add 678 640 ((1), (1)), some 7, none⟩,
  ⟨11364, .add 678 641 ((1), (1)), some 7, none⟩,
  ⟨11365, .add 678 642 ((-2), (1)), some 7, none⟩,
  ⟨11366, .add 678 648 ((1), (1)), some 7, none⟩,
  ⟨11367, .add 678 649 ((-1), (1)), some 7, none⟩,
  ⟨11368, .add 678 676 ((1), (1)), some 7, none⟩,
  ⟨11369, .add 679 511 ((1), (1)), some 7, none⟩,
  ⟨11370, .add 679 513 ((1), (1)), some 7, none⟩,
  ⟨11371, .add 679 519 ((-1), (1)), some 7, none⟩,
  ⟨11372, .add 679 522 ((-1), (1)), some 7, none⟩,
  ⟨11373, .add 679 524 ((-1), (1)), some 7, none⟩,
  ⟨11374, .add 679 559 ((-2), (1)), some 7, none⟩,
  ⟨11375, .add 679 566 ((1), (2)), some 7, none⟩
]

def forwardL : List Row := [
  ⟨11376, .add 567 679 ((-1), (2)), some 7, none⟩,
  ⟨11377, .add 572 679 ((-2), (1)), some 7, none⟩,
  ⟨11378, .add 578 679 ((1), (2)), some 7, none⟩,
  ⟨11379, .add 579 679 ((-1), (2)), some 7, none⟩,
  ⟨11380, .add 640 679 ((1), (1)), some 7, none⟩,
  ⟨11381, .add 641 679 ((1), (1)), some 7, none⟩,
  ⟨11382, .add 642 679 ((-2), (1)), some 7, none⟩,
  ⟨11383, .add 648 679 ((-1), (1)), some 7, none⟩,
  ⟨11384, .add 649 679 ((1), (1)), some 7, none⟩,
  ⟨11385, .add 676 679 ((-1), (1)), some 7, none⟩,
  ⟨11386, .relabel 454 0 7, none, some (5, 1)⟩,
  ⟨11387, .add 454 680 ((1), (2)), some 7, none⟩,
  ⟨11388, .relabel 455 0 7, none, some (5, 1)⟩,
  ⟨11389, .add 455 680 ((-1), (2)), some 7, none⟩,
  ⟨11390, .add 511 680 ((1), (1)), some 7, none⟩,
  ⟨11391, .add 513 680 ((-1), (1)), some 7, none⟩,
  ⟨11392, .add 518 680 ((-1), (2)), some 7, none⟩,
  ⟨11393, .add 519 680 ((1), (2)), some 7, none⟩,
  ⟨11394, .add 522 680 ((1), (1)), some 7, none⟩,
  ⟨11395, .add 524 680 ((-1), (1)), some 7, none⟩,
  ⟨11396, .relabel 530 0 7, none, some (5, 1)⟩,
  ⟨11397, .add 530 680 ((1), (2)), some 7, none⟩,
  ⟨11398, .relabel 531 0 7, none, some (5, 1)⟩,
  ⟨11399, .add 531 680 ((-1), (2)), some 7, none⟩
]

def backwardL : List Row := [
  ⟨11376, .add 679 567 ((1), (2)), some 7, none⟩,
  ⟨11377, .add 679 572 ((2), (1)), some 7, none⟩,
  ⟨11378, .add 679 578 ((-1), (2)), some 7, none⟩,
  ⟨11379, .add 679 579 ((1), (2)), some 7, none⟩,
  ⟨11380, .add 679 640 ((-1), (1)), some 7, none⟩,
  ⟨11381, .add 679 641 ((-1), (1)), some 7, none⟩,
  ⟨11382, .add 679 642 ((2), (1)), some 7, none⟩,
  ⟨11383, .add 679 648 ((1), (1)), some 7, none⟩,
  ⟨11384, .add 679 649 ((-1), (1)), some 7, none⟩,
  ⟨11385, .add 679 676 ((1), (1)), some 7, none⟩,
  ⟨11386, .relabel 454 0 7, none, some (5, 1)⟩,
  ⟨11387, .add 680 454 ((-1), (2)), some 7, none⟩,
  ⟨11388, .relabel 455 0 7, none, some (5, 1)⟩,
  ⟨11389, .add 680 455 ((1), (2)), some 7, none⟩,
  ⟨11390, .add 680 511 ((-1), (1)), some 7, none⟩,
  ⟨11391, .add 680 513 ((1), (1)), some 7, none⟩,
  ⟨11392, .add 680 518 ((1), (2)), some 7, none⟩,
  ⟨11393, .add 680 519 ((-1), (2)), some 7, none⟩,
  ⟨11394, .add 680 522 ((-1), (1)), some 7, none⟩,
  ⟨11395, .add 680 524 ((1), (1)), some 7, none⟩,
  ⟨11396, .relabel 530 0 7, none, some (5, 1)⟩,
  ⟨11397, .add 680 530 ((-1), (2)), some 7, none⟩,
  ⟨11398, .relabel 531 0 7, none, some (5, 1)⟩,
  ⟨11399, .add 680 531 ((1), (2)), some 7, none⟩
]

end CurrentMain.F19SelectedCoverage.Child5MoreData
