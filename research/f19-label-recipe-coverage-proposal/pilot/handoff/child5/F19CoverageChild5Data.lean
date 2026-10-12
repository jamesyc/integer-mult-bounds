/- Exact selected source rows; checkpoint validity is proved separately.
Raw signed coefficient syntax, order, source indices and child ordinals are retained. -/
import F19CoverageChild34Check
namespace CurrentMain.F19SelectedCoverage.Child5Data
open CurrentMain.F19SelectedCoverage

def new388 : List Register := [512, 513, 522, 510, 511, 524, 560, 561, 570, 558, 559, 572]
def labels388 (r : Register) : FrameLabel :=
  if r ∈ new388 then 7 else Child34Data.labels364 r

def new409 : List Register := [582, 584]
def labels409 (r : Register) : FrameLabel :=
  if r ∈ new409 then 7 else labels388 r

def forwardE : List Row := [
  ⟨11215, .relabel 512 0 7, none, some (5, 1)⟩,
  ⟨11216, .add 512 523 ((-1), (1)), some 7, none⟩,
  ⟨11217, .relabel 513 0 7, none, some (5, 1)⟩,
  ⟨11218, .add 513 523 ((-1), (1)), some 7, none⟩,
  ⟨11219, .relabel 522 0 7, none, some (5, 1)⟩,
  ⟨11220, .add 522 523 ((1), (1)), some 7, none⟩,
  ⟨11221, .relabel 510 0 7, none, some (5, 1)⟩,
  ⟨11222, .add 510 525 ((-1), (1)), some 7, none⟩,
  ⟨11223, .relabel 511 0 7, none, some (5, 1)⟩,
  ⟨11224, .add 511 525 ((-1), (1)), some 7, none⟩,
  ⟨11225, .relabel 524 0 7, none, some (5, 1)⟩,
  ⟨11226, .add 524 525 ((1), (1)), some 7, none⟩,
  ⟨11227, .relabel 560 0 7, none, some (5, 1)⟩,
  ⟨11228, .add 560 571 ((-1), (1)), some 7, none⟩,
  ⟨11229, .relabel 561 0 7, none, some (5, 1)⟩,
  ⟨11230, .add 561 571 ((-1), (1)), some 7, none⟩,
  ⟨11231, .relabel 570 0 7, none, some (5, 1)⟩,
  ⟨11232, .add 570 571 ((1), (1)), some 7, none⟩,
  ⟨11233, .relabel 558 0 7, none, some (5, 1)⟩,
  ⟨11234, .add 558 573 ((-1), (1)), some 7, none⟩,
  ⟨11235, .relabel 559 0 7, none, some (5, 1)⟩,
  ⟨11236, .add 559 573 ((-1), (1)), some 7, none⟩,
  ⟨11237, .relabel 572 0 7, none, some (5, 1)⟩,
  ⟨11238, .add 572 573 ((1), (1)), some 7, none⟩
]

def backwardE : List Row := [
  ⟨11215, .relabel 512 0 7, none, some (5, 1)⟩,
  ⟨11216, .add 523 512 ((1), (1)), some 7, none⟩,
  ⟨11217, .relabel 513 0 7, none, some (5, 1)⟩,
  ⟨11218, .add 523 513 ((1), (1)), some 7, none⟩,
  ⟨11219, .relabel 522 0 7, none, some (5, 1)⟩,
  ⟨11220, .add 523 522 ((-1), (1)), some 7, none⟩,
  ⟨11221, .relabel 510 0 7, none, some (5, 1)⟩,
  ⟨11222, .add 525 510 ((1), (1)), some 7, none⟩,
  ⟨11223, .relabel 511 0 7, none, some (5, 1)⟩,
  ⟨11224, .add 525 511 ((1), (1)), some 7, none⟩,
  ⟨11225, .relabel 524 0 7, none, some (5, 1)⟩,
  ⟨11226, .add 525 524 ((-1), (1)), some 7, none⟩,
  ⟨11227, .relabel 560 0 7, none, some (5, 1)⟩,
  ⟨11228, .add 571 560 ((1), (1)), some 7, none⟩,
  ⟨11229, .relabel 561 0 7, none, some (5, 1)⟩,
  ⟨11230, .add 571 561 ((1), (1)), some 7, none⟩,
  ⟨11231, .relabel 570 0 7, none, some (5, 1)⟩,
  ⟨11232, .add 571 570 ((-1), (1)), some 7, none⟩,
  ⟨11233, .relabel 558 0 7, none, some (5, 1)⟩,
  ⟨11234, .add 573 558 ((1), (1)), some 7, none⟩,
  ⟨11235, .relabel 559 0 7, none, some (5, 1)⟩,
  ⟨11236, .add 573 559 ((1), (1)), some 7, none⟩,
  ⟨11237, .relabel 572 0 7, none, some (5, 1)⟩,
  ⟨11238, .add 573 572 ((-1), (1)), some 7, none⟩
]

def forwardF : List Row := [
  ⟨11239, .add 558 583 ((1), (1)), some 7, none⟩,
  ⟨11240, .add 559 583 ((-1), (1)), some 7, none⟩,
  ⟨11241, .relabel 582 0 7, none, some (5, 1)⟩,
  ⟨11242, .add 582 583 ((-1), (1)), some 7, none⟩,
  ⟨11243, .add 560 585 ((-1), (1)), some 7, none⟩,
  ⟨11244, .add 561 585 ((-1), (1)), some 7, none⟩,
  ⟨11245, .add 570 585 ((2), (1)), some 7, none⟩,
  ⟨11246, .relabel 584 0 7, none, some (5, 1)⟩,
  ⟨11247, .add 584 585 ((-1), (1)), some 7, none⟩,
  ⟨11248, .add 560 594 ((-1), (1)), some 7, none⟩,
  ⟨11249, .add 570 594 ((1), (1)), some 7, none⟩,
  ⟨11250, .add 584 594 ((-1), (1)), some 7, none⟩,
  ⟨11251, .add 561 595 ((-1), (1)), some 7, none⟩,
  ⟨11252, .add 570 595 ((1), (1)), some 7, none⟩,
  ⟨11253, .add 584 595 ((-1), (1)), some 7, none⟩,
  ⟨11254, .add 558 596 ((1), (1)), some 7, none⟩,
  ⟨11255, .add 572 596 ((-1), (1)), some 7, none⟩,
  ⟨11256, .add 582 596 ((-1), (1)), some 7, none⟩,
  ⟨11257, .add 559 597 ((-1), (1)), some 7, none⟩,
  ⟨11258, .add 572 597 ((1), (1)), some 7, none⟩,
  ⟨11259, .add 582 597 ((-1), (1)), some 7, none⟩
]

def backwardF : List Row := [
  ⟨11239, .add 583 558 ((-1), (1)), some 7, none⟩,
  ⟨11240, .add 583 559 ((1), (1)), some 7, none⟩,
  ⟨11241, .relabel 582 0 7, none, some (5, 1)⟩,
  ⟨11242, .add 583 582 ((1), (1)), some 7, none⟩,
  ⟨11243, .add 585 560 ((1), (1)), some 7, none⟩,
  ⟨11244, .add 585 561 ((1), (1)), some 7, none⟩,
  ⟨11245, .add 585 570 ((-2), (1)), some 7, none⟩,
  ⟨11246, .relabel 584 0 7, none, some (5, 1)⟩,
  ⟨11247, .add 585 584 ((1), (1)), some 7, none⟩,
  ⟨11248, .add 594 560 ((1), (1)), some 7, none⟩,
  ⟨11249, .add 594 570 ((-1), (1)), some 7, none⟩,
  ⟨11250, .add 594 584 ((1), (1)), some 7, none⟩,
  ⟨11251, .add 595 561 ((1), (1)), some 7, none⟩,
  ⟨11252, .add 595 570 ((-1), (1)), some 7, none⟩,
  ⟨11253, .add 595 584 ((1), (1)), some 7, none⟩,
  ⟨11254, .add 596 558 ((-1), (1)), some 7, none⟩,
  ⟨11255, .add 596 572 ((1), (1)), some 7, none⟩,
  ⟨11256, .add 596 582 ((1), (1)), some 7, none⟩,
  ⟨11257, .add 597 559 ((1), (1)), some 7, none⟩,
  ⟨11258, .add 597 572 ((-1), (1)), some 7, none⟩,
  ⟨11259, .add 597 582 ((1), (1)), some 7, none⟩
]

end CurrentMain.F19SelectedCoverage.Child5Data
