/- Exact selected static-label rows; checkpoint validity is proved separately.
Raw signed coefficients and original indices/order are retained. All rows are ADD;
child lookup is vacuous in this packet. No scalar/operator endpoint is asserted. -/
import F19CoverageChild5MoreCheck
namespace CurrentMain.F19SelectedCoverage.StaticGapData
open CurrentMain.F19SelectedCoverage

def new573 : List Register := []
def labels573 (r : Register) : FrameLabel :=
  if r ∈ new573 then 7 else Child5MoreData.labels549 r

def new597 : List Register := []
def labels597 (r : Register) : FrameLabel :=
  if r ∈ new597 then 7 else labels573 r

def new621 : List Register := []
def labels621 (r : Register) : FrameLabel :=
  if r ∈ new621 then 7 else labels597 r

def new645 : List Register := []
def labels645 (r : Register) : FrameLabel :=
  if r ∈ new645 then 7 else labels621 r

def new669 : List Register := []
def labels669 (r : Register) : FrameLabel :=
  if r ∈ new669 then 7 else labels645 r

def new695 : List Register := []
def labels695 (r : Register) : FrameLabel :=
  if r ∈ new695 then 7 else labels669 r

def forwardM : List Row := [
  ⟨11400, .add 561 680 ((-1), (1)), some 7, none⟩,
  ⟨11401, .add 566 680 ((-1), (2)), some 7, none⟩,
  ⟨11402, .add 567 680 ((1), (2)), some 7, none⟩,
  ⟨11403, .add 570 680 ((2), (1)), some 7, none⟩,
  ⟨11404, .add 572 680 ((-1), (1)), some 7, none⟩,
  ⟨11405, .add 578 680 ((1), (2)), some 7, none⟩,
  ⟨11406, .add 579 680 ((-1), (2)), some 7, none⟩,
  ⟨11407, .add 582 680 ((-1), (1)), some 7, none⟩,
  ⟨11408, .add 584 680 ((-1), (1)), some 7, none⟩,
  ⟨11409, .add 640 680 ((1), (1)), some 7, none⟩,
  ⟨11410, .add 641 680 ((-1), (1)), some 7, none⟩,
  ⟨11411, .add 648 680 ((-1), (1)), some 7, none⟩,
  ⟨11412, .add 649 680 ((1), (1)), some 7, none⟩,
  ⟨11413, .add 672 680 ((-1), (1)), some 7, none⟩,
  ⟨11414, .add 454 681 ((1), (2)), some 7, none⟩,
  ⟨11415, .add 455 681 ((-1), (2)), some 7, none⟩,
  ⟨11416, .add 511 681 ((-1), (1)), some 7, none⟩,
  ⟨11417, .add 513 681 ((-1), (1)), some 7, none⟩,
  ⟨11418, .add 518 681 ((-1), (2)), some 7, none⟩,
  ⟨11419, .add 519 681 ((1), (2)), some 7, none⟩,
  ⟨11420, .add 522 681 ((1), (1)), some 7, none⟩,
  ⟨11421, .add 524 681 ((1), (1)), some 7, none⟩,
  ⟨11422, .add 530 681 ((-1), (2)), some 7, none⟩,
  ⟨11423, .add 531 681 ((1), (2)), some 7, none⟩
]

def backwardM : List Row := [
  ⟨11400, .add 680 561 ((1), (1)), some 7, none⟩,
  ⟨11401, .add 680 566 ((1), (2)), some 7, none⟩,
  ⟨11402, .add 680 567 ((-1), (2)), some 7, none⟩,
  ⟨11403, .add 680 570 ((-2), (1)), some 7, none⟩,
  ⟨11404, .add 680 572 ((1), (1)), some 7, none⟩,
  ⟨11405, .add 680 578 ((-1), (2)), some 7, none⟩,
  ⟨11406, .add 680 579 ((1), (2)), some 7, none⟩,
  ⟨11407, .add 680 582 ((1), (1)), some 7, none⟩,
  ⟨11408, .add 680 584 ((1), (1)), some 7, none⟩,
  ⟨11409, .add 680 640 ((-1), (1)), some 7, none⟩,
  ⟨11410, .add 680 641 ((1), (1)), some 7, none⟩,
  ⟨11411, .add 680 648 ((1), (1)), some 7, none⟩,
  ⟨11412, .add 680 649 ((-1), (1)), some 7, none⟩,
  ⟨11413, .add 680 672 ((1), (1)), some 7, none⟩,
  ⟨11414, .add 681 454 ((-1), (2)), some 7, none⟩,
  ⟨11415, .add 681 455 ((1), (2)), some 7, none⟩,
  ⟨11416, .add 681 511 ((1), (1)), some 7, none⟩,
  ⟨11417, .add 681 513 ((1), (1)), some 7, none⟩,
  ⟨11418, .add 681 518 ((1), (2)), some 7, none⟩,
  ⟨11419, .add 681 519 ((-1), (2)), some 7, none⟩,
  ⟨11420, .add 681 522 ((-1), (1)), some 7, none⟩,
  ⟨11421, .add 681 524 ((-1), (1)), some 7, none⟩,
  ⟨11422, .add 681 530 ((1), (2)), some 7, none⟩,
  ⟨11423, .add 681 531 ((-1), (2)), some 7, none⟩
]

def forwardN : List Row := [
  ⟨11424, .add 561 681 ((1), (1)), some 7, none⟩,
  ⟨11425, .add 566 681 ((1), (2)), some 7, none⟩,
  ⟨11426, .add 567 681 ((-1), (2)), some 7, none⟩,
  ⟨11427, .add 572 681 ((-1), (1)), some 7, none⟩,
  ⟨11428, .add 578 681 ((1), (2)), some 7, none⟩,
  ⟨11429, .add 579 681 ((-1), (2)), some 7, none⟩,
  ⟨11430, .add 582 681 ((-1), (1)), some 7, none⟩,
  ⟨11431, .add 584 681 ((-1), (1)), some 7, none⟩,
  ⟨11432, .add 640 681 ((-1), (1)), some 7, none⟩,
  ⟨11433, .add 641 681 ((1), (1)), some 7, none⟩,
  ⟨11434, .add 648 681 ((-1), (1)), some 7, none⟩,
  ⟨11435, .add 649 681 ((1), (1)), some 7, none⟩,
  ⟨11436, .add 672 681 ((-1), (1)), some 7, none⟩,
  ⟨11437, .add 454 682 ((1), (2)), some 7, none⟩,
  ⟨11438, .add 455 682 ((-1), (2)), some 7, none⟩,
  ⟨11439, .add 518 682 ((-1), (2)), some 7, none⟩,
  ⟨11440, .add 519 682 ((1), (2)), some 7, none⟩,
  ⟨11441, .add 530 682 ((-1), (2)), some 7, none⟩,
  ⟨11442, .add 531 682 ((-1), (2)), some 7, none⟩,
  ⟨11443, .add 561 682 ((-1), (1)), some 7, none⟩,
  ⟨11444, .add 570 682 ((2), (1)), some 7, none⟩,
  ⟨11445, .add 572 682 ((-1), (1)), some 7, none⟩,
  ⟨11446, .add 578 682 ((1), (1)), some 7, none⟩,
  ⟨11447, .add 582 682 ((-1), (1)), some 7, none⟩
]

def backwardN : List Row := [
  ⟨11424, .add 681 561 ((-1), (1)), some 7, none⟩,
  ⟨11425, .add 681 566 ((-1), (2)), some 7, none⟩,
  ⟨11426, .add 681 567 ((1), (2)), some 7, none⟩,
  ⟨11427, .add 681 572 ((1), (1)), some 7, none⟩,
  ⟨11428, .add 681 578 ((-1), (2)), some 7, none⟩,
  ⟨11429, .add 681 579 ((1), (2)), some 7, none⟩,
  ⟨11430, .add 681 582 ((1), (1)), some 7, none⟩,
  ⟨11431, .add 681 584 ((1), (1)), some 7, none⟩,
  ⟨11432, .add 681 640 ((1), (1)), some 7, none⟩,
  ⟨11433, .add 681 641 ((-1), (1)), some 7, none⟩,
  ⟨11434, .add 681 648 ((1), (1)), some 7, none⟩,
  ⟨11435, .add 681 649 ((-1), (1)), some 7, none⟩,
  ⟨11436, .add 681 672 ((1), (1)), some 7, none⟩,
  ⟨11437, .add 682 454 ((-1), (2)), some 7, none⟩,
  ⟨11438, .add 682 455 ((1), (2)), some 7, none⟩,
  ⟨11439, .add 682 518 ((1), (2)), some 7, none⟩,
  ⟨11440, .add 682 519 ((-1), (2)), some 7, none⟩,
  ⟨11441, .add 682 530 ((1), (2)), some 7, none⟩,
  ⟨11442, .add 682 531 ((1), (2)), some 7, none⟩,
  ⟨11443, .add 682 561 ((1), (1)), some 7, none⟩,
  ⟨11444, .add 682 570 ((-2), (1)), some 7, none⟩,
  ⟨11445, .add 682 572 ((1), (1)), some 7, none⟩,
  ⟨11446, .add 682 578 ((-1), (1)), some 7, none⟩,
  ⟨11447, .add 682 582 ((1), (1)), some 7, none⟩
]

def forwardO : List Row := [
  ⟨11448, .add 584 682 ((-1), (1)), some 7, none⟩,
  ⟨11449, .add 648 682 ((-2), (1)), some 7, none⟩,
  ⟨11450, .add 650 682 ((2), (1)), some 7, none⟩,
  ⟨11451, .add 672 682 ((-1), (1)), some 7, none⟩,
  ⟨11452, .add 454 683 ((1), (2)), some 7, none⟩,
  ⟨11453, .add 455 683 ((-1), (2)), some 7, none⟩,
  ⟨11454, .add 513 683 ((-2), (1)), some 7, none⟩,
  ⟨11455, .add 518 683 ((-1), (2)), some 7, none⟩,
  ⟨11456, .add 519 683 ((1), (2)), some 7, none⟩,
  ⟨11457, .add 522 683 ((2), (1)), some 7, none⟩,
  ⟨11458, .add 530 683 ((1), (2)), some 7, none⟩,
  ⟨11459, .add 531 683 ((1), (2)), some 7, none⟩,
  ⟨11460, .add 561 683 ((1), (1)), some 7, none⟩,
  ⟨11461, .add 572 683 ((-1), (1)), some 7, none⟩,
  ⟨11462, .add 579 683 ((-1), (1)), some 7, none⟩,
  ⟨11463, .add 582 683 ((-1), (1)), some 7, none⟩,
  ⟨11464, .add 584 683 ((-1), (1)), some 7, none⟩,
  ⟨11465, .add 649 683 ((2), (1)), some 7, none⟩,
  ⟨11466, .add 650 683 ((-2), (1)), some 7, none⟩,
  ⟨11467, .add 672 683 ((-1), (1)), some 7, none⟩,
  ⟨11468, .add 454 684 ((-1), (2)), some 7, none⟩,
  ⟨11469, .add 455 684 ((-1), (2)), some 7, none⟩,
  ⟨11470, .add 511 684 ((1), (1)), some 7, none⟩,
  ⟨11471, .add 513 684 ((-1), (1)), some 7, none⟩
]

def backwardO : List Row := [
  ⟨11448, .add 682 584 ((1), (1)), some 7, none⟩,
  ⟨11449, .add 682 648 ((2), (1)), some 7, none⟩,
  ⟨11450, .add 682 650 ((-2), (1)), some 7, none⟩,
  ⟨11451, .add 682 672 ((1), (1)), some 7, none⟩,
  ⟨11452, .add 683 454 ((-1), (2)), some 7, none⟩,
  ⟨11453, .add 683 455 ((1), (2)), some 7, none⟩,
  ⟨11454, .add 683 513 ((2), (1)), some 7, none⟩,
  ⟨11455, .add 683 518 ((1), (2)), some 7, none⟩,
  ⟨11456, .add 683 519 ((-1), (2)), some 7, none⟩,
  ⟨11457, .add 683 522 ((-2), (1)), some 7, none⟩,
  ⟨11458, .add 683 530 ((-1), (2)), some 7, none⟩,
  ⟨11459, .add 683 531 ((-1), (2)), some 7, none⟩,
  ⟨11460, .add 683 561 ((-1), (1)), some 7, none⟩,
  ⟨11461, .add 683 572 ((1), (1)), some 7, none⟩,
  ⟨11462, .add 683 579 ((1), (1)), some 7, none⟩,
  ⟨11463, .add 683 582 ((1), (1)), some 7, none⟩,
  ⟨11464, .add 683 584 ((1), (1)), some 7, none⟩,
  ⟨11465, .add 683 649 ((-2), (1)), some 7, none⟩,
  ⟨11466, .add 683 650 ((2), (1)), some 7, none⟩,
  ⟨11467, .add 683 672 ((1), (1)), some 7, none⟩,
  ⟨11468, .add 684 454 ((1), (2)), some 7, none⟩,
  ⟨11469, .add 684 455 ((1), (2)), some 7, none⟩,
  ⟨11470, .add 684 511 ((-1), (1)), some 7, none⟩,
  ⟨11471, .add 684 513 ((1), (1)), some 7, none⟩
]

def forwardP : List Row := [
  ⟨11472, .add 518 684 ((-1), (2)), some 7, none⟩,
  ⟨11473, .add 519 684 ((1), (2)), some 7, none⟩,
  ⟨11474, .add 522 684 ((1), (1)), some 7, none⟩,
  ⟨11475, .add 524 684 ((-1), (1)), some 7, none⟩,
  ⟨11476, .add 530 684 ((1), (2)), some 7, none⟩,
  ⟨11477, .add 531 684 ((-1), (2)), some 7, none⟩,
  ⟨11478, .add 561 684 ((-1), (1)), some 7, none⟩,
  ⟨11479, .add 566 684 ((-1), (2)), some 7, none⟩,
  ⟨11480, .add 567 684 ((1), (2)), some 7, none⟩,
  ⟨11481, .add 572 684 ((-1), (1)), some 7, none⟩,
  ⟨11482, .add 578 684 ((1), (2)), some 7, none⟩,
  ⟨11483, .add 579 684 ((-1), (2)), some 7, none⟩,
  ⟨11484, .add 582 684 ((-1), (1)), some 7, none⟩,
  ⟨11485, .add 584 684 ((1), (1)), some 7, none⟩,
  ⟨11486, .add 640 684 ((1), (1)), some 7, none⟩,
  ⟨11487, .add 641 684 ((-1), (1)), some 7, none⟩,
  ⟨11488, .add 648 684 ((-1), (1)), some 7, none⟩,
  ⟨11489, .add 649 684 ((1), (1)), some 7, none⟩,
  ⟨11490, .add 676 684 ((-1), (1)), some 7, none⟩,
  ⟨11491, .add 454 685 ((-1), (2)), some 7, none⟩,
  ⟨11492, .add 455 685 ((-1), (2)), some 7, none⟩,
  ⟨11493, .add 511 685 ((-1), (1)), some 7, none⟩,
  ⟨11494, .add 513 685 ((-1), (1)), some 7, none⟩,
  ⟨11495, .add 518 685 ((-1), (2)), some 7, none⟩
]

def backwardP : List Row := [
  ⟨11472, .add 684 518 ((1), (2)), some 7, none⟩,
  ⟨11473, .add 684 519 ((-1), (2)), some 7, none⟩,
  ⟨11474, .add 684 522 ((-1), (1)), some 7, none⟩,
  ⟨11475, .add 684 524 ((1), (1)), some 7, none⟩,
  ⟨11476, .add 684 530 ((-1), (2)), some 7, none⟩,
  ⟨11477, .add 684 531 ((1), (2)), some 7, none⟩,
  ⟨11478, .add 684 561 ((1), (1)), some 7, none⟩,
  ⟨11479, .add 684 566 ((1), (2)), some 7, none⟩,
  ⟨11480, .add 684 567 ((-1), (2)), some 7, none⟩,
  ⟨11481, .add 684 572 ((1), (1)), some 7, none⟩,
  ⟨11482, .add 684 578 ((-1), (2)), some 7, none⟩,
  ⟨11483, .add 684 579 ((1), (2)), some 7, none⟩,
  ⟨11484, .add 684 582 ((1), (1)), some 7, none⟩,
  ⟨11485, .add 684 584 ((-1), (1)), some 7, none⟩,
  ⟨11486, .add 684 640 ((-1), (1)), some 7, none⟩,
  ⟨11487, .add 684 641 ((1), (1)), some 7, none⟩,
  ⟨11488, .add 684 648 ((1), (1)), some 7, none⟩,
  ⟨11489, .add 684 649 ((-1), (1)), some 7, none⟩,
  ⟨11490, .add 684 676 ((1), (1)), some 7, none⟩,
  ⟨11491, .add 685 454 ((1), (2)), some 7, none⟩,
  ⟨11492, .add 685 455 ((1), (2)), some 7, none⟩,
  ⟨11493, .add 685 511 ((1), (1)), some 7, none⟩,
  ⟨11494, .add 685 513 ((1), (1)), some 7, none⟩,
  ⟨11495, .add 685 518 ((1), (2)), some 7, none⟩
]

def forwardQ : List Row := [
  ⟨11496, .add 519 685 ((1), (2)), some 7, none⟩,
  ⟨11497, .add 522 685 ((1), (1)), some 7, none⟩,
  ⟨11498, .add 524 685 ((1), (1)), some 7, none⟩,
  ⟨11499, .add 530 685 ((-1), (2)), some 7, none⟩,
  ⟨11500, .add 531 685 ((1), (2)), some 7, none⟩,
  ⟨11501, .add 561 685 ((1), (1)), some 7, none⟩,
  ⟨11502, .add 566 685 ((1), (2)), some 7, none⟩,
  ⟨11503, .add 567 685 ((-1), (2)), some 7, none⟩,
  ⟨11504, .add 570 685 ((-2), (1)), some 7, none⟩,
  ⟨11505, .add 572 685 ((-1), (1)), some 7, none⟩,
  ⟨11506, .add 578 685 ((1), (2)), some 7, none⟩,
  ⟨11507, .add 579 685 ((-1), (2)), some 7, none⟩,
  ⟨11508, .add 582 685 ((-1), (1)), some 7, none⟩,
  ⟨11509, .add 584 685 ((1), (1)), some 7, none⟩,
  ⟨11510, .add 640 685 ((-1), (1)), some 7, none⟩,
  ⟨11511, .add 641 685 ((1), (1)), some 7, none⟩,
  ⟨11512, .add 648 685 ((-1), (1)), some 7, none⟩,
  ⟨11513, .add 649 685 ((1), (1)), some 7, none⟩,
  ⟨11514, .add 676 685 ((-1), (1)), some 7, none⟩,
  ⟨11515, .add 454 686 ((-1), (2)), some 7, none⟩,
  ⟨11516, .add 455 686 ((-1), (2)), some 7, none⟩,
  ⟨11517, .add 518 686 ((-1), (2)), some 7, none⟩,
  ⟨11518, .add 519 686 ((1), (2)), some 7, none⟩,
  ⟨11519, .add 530 686 ((-1), (2)), some 7, none⟩
]

def backwardQ : List Row := [
  ⟨11496, .add 685 519 ((-1), (2)), some 7, none⟩,
  ⟨11497, .add 685 522 ((-1), (1)), some 7, none⟩,
  ⟨11498, .add 685 524 ((-1), (1)), some 7, none⟩,
  ⟨11499, .add 685 530 ((1), (2)), some 7, none⟩,
  ⟨11500, .add 685 531 ((-1), (2)), some 7, none⟩,
  ⟨11501, .add 685 561 ((-1), (1)), some 7, none⟩,
  ⟨11502, .add 685 566 ((-1), (2)), some 7, none⟩,
  ⟨11503, .add 685 567 ((1), (2)), some 7, none⟩,
  ⟨11504, .add 685 570 ((2), (1)), some 7, none⟩,
  ⟨11505, .add 685 572 ((1), (1)), some 7, none⟩,
  ⟨11506, .add 685 578 ((-1), (2)), some 7, none⟩,
  ⟨11507, .add 685 579 ((1), (2)), some 7, none⟩,
  ⟨11508, .add 685 582 ((1), (1)), some 7, none⟩,
  ⟨11509, .add 685 584 ((-1), (1)), some 7, none⟩,
  ⟨11510, .add 685 640 ((1), (1)), some 7, none⟩,
  ⟨11511, .add 685 641 ((-1), (1)), some 7, none⟩,
  ⟨11512, .add 685 648 ((1), (1)), some 7, none⟩,
  ⟨11513, .add 685 649 ((-1), (1)), some 7, none⟩,
  ⟨11514, .add 685 676 ((1), (1)), some 7, none⟩,
  ⟨11515, .add 686 454 ((1), (2)), some 7, none⟩,
  ⟨11516, .add 686 455 ((1), (2)), some 7, none⟩,
  ⟨11517, .add 686 518 ((1), (2)), some 7, none⟩,
  ⟨11518, .add 686 519 ((-1), (2)), some 7, none⟩,
  ⟨11519, .add 686 530 ((1), (2)), some 7, none⟩
]

def forwardR : List Row := [
  ⟨11520, .add 531 686 ((-1), (2)), some 7, none⟩,
  ⟨11521, .add 561 686 ((-1), (1)), some 7, none⟩,
  ⟨11522, .add 572 686 ((-1), (1)), some 7, none⟩,
  ⟨11523, .add 578 686 ((1), (1)), some 7, none⟩,
  ⟨11524, .add 582 686 ((-1), (1)), some 7, none⟩,
  ⟨11525, .add 584 686 ((1), (1)), some 7, none⟩,
  ⟨11526, .add 648 686 ((-2), (1)), some 7, none⟩,
  ⟨11527, .add 650 686 ((2), (1)), some 7, none⟩,
  ⟨11528, .add 676 686 ((-1), (1)), some 7, none⟩,
  ⟨11529, .add 454 687 ((-1), (2)), some 7, none⟩,
  ⟨11530, .add 455 687 ((-1), (2)), some 7, none⟩,
  ⟨11531, .add 513 687 ((-2), (1)), some 7, none⟩,
  ⟨11532, .add 518 687 ((-1), (2)), some 7, none⟩,
  ⟨11533, .add 519 687 ((1), (2)), some 7, none⟩,
  ⟨11534, .add 522 687 ((2), (1)), some 7, none⟩,
  ⟨11535, .add 530 687 ((1), (2)), some 7, none⟩,
  ⟨11536, .add 531 687 ((1), (2)), some 7, none⟩,
  ⟨11537, .add 561 687 ((1), (1)), some 7, none⟩,
  ⟨11538, .add 570 687 ((-2), (1)), some 7, none⟩,
  ⟨11539, .add 572 687 ((-1), (1)), some 7, none⟩,
  ⟨11540, .add 579 687 ((-1), (1)), some 7, none⟩,
  ⟨11541, .add 582 687 ((-1), (1)), some 7, none⟩,
  ⟨11542, .add 584 687 ((1), (1)), some 7, none⟩,
  ⟨11543, .add 649 687 ((2), (1)), some 7, none⟩,
  ⟨11544, .add 650 687 ((-2), (1)), some 7, none⟩,
  ⟨11545, .add 676 687 ((-1), (1)), some 7, none⟩
]

def backwardR : List Row := [
  ⟨11520, .add 686 531 ((1), (2)), some 7, none⟩,
  ⟨11521, .add 686 561 ((1), (1)), some 7, none⟩,
  ⟨11522, .add 686 572 ((1), (1)), some 7, none⟩,
  ⟨11523, .add 686 578 ((-1), (1)), some 7, none⟩,
  ⟨11524, .add 686 582 ((1), (1)), some 7, none⟩,
  ⟨11525, .add 686 584 ((-1), (1)), some 7, none⟩,
  ⟨11526, .add 686 648 ((2), (1)), some 7, none⟩,
  ⟨11527, .add 686 650 ((-2), (1)), some 7, none⟩,
  ⟨11528, .add 686 676 ((1), (1)), some 7, none⟩,
  ⟨11529, .add 687 454 ((1), (2)), some 7, none⟩,
  ⟨11530, .add 687 455 ((1), (2)), some 7, none⟩,
  ⟨11531, .add 687 513 ((2), (1)), some 7, none⟩,
  ⟨11532, .add 687 518 ((1), (2)), some 7, none⟩,
  ⟨11533, .add 687 519 ((-1), (2)), some 7, none⟩,
  ⟨11534, .add 687 522 ((-2), (1)), some 7, none⟩,
  ⟨11535, .add 687 530 ((-1), (2)), some 7, none⟩,
  ⟨11536, .add 687 531 ((-1), (2)), some 7, none⟩,
  ⟨11537, .add 687 561 ((-1), (1)), some 7, none⟩,
  ⟨11538, .add 687 570 ((2), (1)), some 7, none⟩,
  ⟨11539, .add 687 572 ((1), (1)), some 7, none⟩,
  ⟨11540, .add 687 579 ((1), (1)), some 7, none⟩,
  ⟨11541, .add 687 582 ((1), (1)), some 7, none⟩,
  ⟨11542, .add 687 584 ((-1), (1)), some 7, none⟩,
  ⟨11543, .add 687 649 ((-2), (1)), some 7, none⟩,
  ⟨11544, .add 687 650 ((2), (1)), some 7, none⟩,
  ⟨11545, .add 687 676 ((1), (1)), some 7, none⟩
]

end CurrentMain.F19SelectedCoverage.StaticGapData
