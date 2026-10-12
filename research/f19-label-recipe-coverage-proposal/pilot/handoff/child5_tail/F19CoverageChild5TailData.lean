/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild5Check
namespace CurrentMain.F19SelectedCoverage.Child5TailData
open CurrentMain.F19SelectedCoverage

def new433 : List Register := [640, 641, 642, 644, 648, 649, 650]
def labels433 (r : Register) : FrameLabel :=
  if r ∈ new433 then 7 else Child5Data.labels409 r

def new457 : List Register := [652, 518, 519, 578, 579, 672]
def labels457 (r : Register) : FrameLabel :=
  if r ∈ new457 then 7 else labels433 r

def forwardG : List Row := [
  ⟨11260, .relabel 640 0 7, none, some (5, 1)⟩,
  ⟨11261, .add 640 643 ((-1), (1)), some 7, none⟩,
  ⟨11262, .relabel 641 0 7, none, some (5, 1)⟩,
  ⟨11263, .add 641 643 ((-1), (1)), some 7, none⟩,
  ⟨11264, .relabel 642 0 7, none, some (5, 1)⟩,
  ⟨11265, .add 642 643 ((1), (1)), some 7, none⟩,
  ⟨11266, .add 640 645 ((-2), (1)), some 7, none⟩,
  ⟨11267, .add 641 645 ((2), (1)), some 7, none⟩,
  ⟨11268, .relabel 644 0 7, none, some (5, 1)⟩,
  ⟨11269, .add 644 645 ((-1), (1)), some 7, none⟩,
  ⟨11270, .add 640 646 ((-2), (1)), some 7, none⟩,
  ⟨11271, .add 642 646 ((2), (1)), some 7, none⟩,
  ⟨11272, .add 644 646 ((-1), (1)), some 7, none⟩,
  ⟨11273, .add 641 647 ((2), (1)), some 7, none⟩,
  ⟨11274, .add 642 647 ((-2), (1)), some 7, none⟩,
  ⟨11275, .add 644 647 ((-1), (1)), some 7, none⟩,
  ⟨11276, .relabel 648 0 7, none, some (5, 1)⟩,
  ⟨11277, .add 648 651 ((-1), (1)), some 7, none⟩,
  ⟨11278, .relabel 649 0 7, none, some (5, 1)⟩,
  ⟨11279, .add 649 651 ((-1), (1)), some 7, none⟩,
  ⟨11280, .relabel 650 0 7, none, some (5, 1)⟩,
  ⟨11281, .add 650 651 ((1), (1)), some 7, none⟩,
  ⟨11282, .add 648 653 ((-2), (1)), some 7, none⟩,
  ⟨11283, .add 649 653 ((2), (1)), some 7, none⟩
]

def backwardG : List Row := [
  ⟨11260, .relabel 640 0 7, none, some (5, 1)⟩,
  ⟨11261, .add 643 640 ((1), (1)), some 7, none⟩,
  ⟨11262, .relabel 641 0 7, none, some (5, 1)⟩,
  ⟨11263, .add 643 641 ((1), (1)), some 7, none⟩,
  ⟨11264, .relabel 642 0 7, none, some (5, 1)⟩,
  ⟨11265, .add 643 642 ((-1), (1)), some 7, none⟩,
  ⟨11266, .add 645 640 ((2), (1)), some 7, none⟩,
  ⟨11267, .add 645 641 ((-2), (1)), some 7, none⟩,
  ⟨11268, .relabel 644 0 7, none, some (5, 1)⟩,
  ⟨11269, .add 645 644 ((1), (1)), some 7, none⟩,
  ⟨11270, .add 646 640 ((2), (1)), some 7, none⟩,
  ⟨11271, .add 646 642 ((-2), (1)), some 7, none⟩,
  ⟨11272, .add 646 644 ((1), (1)), some 7, none⟩,
  ⟨11273, .add 647 641 ((-2), (1)), some 7, none⟩,
  ⟨11274, .add 647 642 ((2), (1)), some 7, none⟩,
  ⟨11275, .add 647 644 ((1), (1)), some 7, none⟩,
  ⟨11276, .relabel 648 0 7, none, some (5, 1)⟩,
  ⟨11277, .add 651 648 ((1), (1)), some 7, none⟩,
  ⟨11278, .relabel 649 0 7, none, some (5, 1)⟩,
  ⟨11279, .add 651 649 ((1), (1)), some 7, none⟩,
  ⟨11280, .relabel 650 0 7, none, some (5, 1)⟩,
  ⟨11281, .add 651 650 ((-1), (1)), some 7, none⟩,
  ⟨11282, .add 653 648 ((2), (1)), some 7, none⟩,
  ⟨11283, .add 653 649 ((-2), (1)), some 7, none⟩
]

def forwardH : List Row := [
  ⟨11284, .relabel 652 0 7, none, some (5, 1)⟩,
  ⟨11285, .add 652 653 ((-1), (1)), some 7, none⟩,
  ⟨11286, .add 648 654 ((-2), (1)), some 7, none⟩,
  ⟨11287, .add 650 654 ((2), (1)), some 7, none⟩,
  ⟨11288, .add 652 654 ((-1), (1)), some 7, none⟩,
  ⟨11289, .add 649 655 ((2), (1)), some 7, none⟩,
  ⟨11290, .add 650 655 ((-2), (1)), some 7, none⟩,
  ⟨11291, .add 652 655 ((-1), (1)), some 7, none⟩,
  ⟨11292, .add 513 673 ((-2), (1)), some 7, none⟩,
  ⟨11293, .relabel 518 0 7, none, some (5, 1)⟩,
  ⟨11294, .add 518 673 ((-1), (1)), some 7, none⟩,
  ⟨11295, .relabel 519 0 7, none, some (5, 1)⟩,
  ⟨11296, .add 519 673 ((1), (1)), some 7, none⟩,
  ⟨11297, .add 522 673 ((2), (1)), some 7, none⟩,
  ⟨11298, .add 559 673 ((2), (1)), some 7, none⟩,
  ⟨11299, .add 572 673 ((-2), (1)), some 7, none⟩,
  ⟨11300, .relabel 578 0 7, none, some (5, 1)⟩,
  ⟨11301, .add 578 673 ((1), (1)), some 7, none⟩,
  ⟨11302, .relabel 579 0 7, none, some (5, 1)⟩,
  ⟨11303, .add 579 673 ((-1), (1)), some 7, none⟩,
  ⟨11304, .add 648 673 ((-2), (1)), some 7, none⟩,
  ⟨11305, .add 649 673 ((2), (1)), some 7, none⟩,
  ⟨11306, .relabel 672 0 7, none, some (5, 1)⟩,
  ⟨11307, .add 672 673 ((-1), (1)), some 7, none⟩
]

def backwardH : List Row := [
  ⟨11284, .relabel 652 0 7, none, some (5, 1)⟩,
  ⟨11285, .add 653 652 ((1), (1)), some 7, none⟩,
  ⟨11286, .add 654 648 ((2), (1)), some 7, none⟩,
  ⟨11287, .add 654 650 ((-2), (1)), some 7, none⟩,
  ⟨11288, .add 654 652 ((1), (1)), some 7, none⟩,
  ⟨11289, .add 655 649 ((-2), (1)), some 7, none⟩,
  ⟨11290, .add 655 650 ((2), (1)), some 7, none⟩,
  ⟨11291, .add 655 652 ((1), (1)), some 7, none⟩,
  ⟨11292, .add 673 513 ((2), (1)), some 7, none⟩,
  ⟨11293, .relabel 518 0 7, none, some (5, 1)⟩,
  ⟨11294, .add 673 518 ((1), (1)), some 7, none⟩,
  ⟨11295, .relabel 519 0 7, none, some (5, 1)⟩,
  ⟨11296, .add 673 519 ((-1), (1)), some 7, none⟩,
  ⟨11297, .add 673 522 ((-2), (1)), some 7, none⟩,
  ⟨11298, .add 673 559 ((-2), (1)), some 7, none⟩,
  ⟨11299, .add 673 572 ((2), (1)), some 7, none⟩,
  ⟨11300, .relabel 578 0 7, none, some (5, 1)⟩,
  ⟨11301, .add 673 578 ((-1), (1)), some 7, none⟩,
  ⟨11302, .relabel 579 0 7, none, some (5, 1)⟩,
  ⟨11303, .add 673 579 ((1), (1)), some 7, none⟩,
  ⟨11304, .add 673 648 ((2), (1)), some 7, none⟩,
  ⟨11305, .add 673 649 ((-2), (1)), some 7, none⟩,
  ⟨11306, .relabel 672 0 7, none, some (5, 1)⟩,
  ⟨11307, .add 673 672 ((1), (1)), some 7, none⟩
]

end CurrentMain.F19SelectedCoverage.Child5TailData
