/- Exact current PR799 next48 rows, zero-based raw9290..9337, both orientations.
Only label/catalog coverage; three operator suppliers and actual entrance remain separate.
Author-checked conditional source context: kappa=1661634653669567/1000000000000000000.
Attribution: selected PR799 source and accepted PR509/checker interfaces. -/
import Current799Next16Check

set_option Elab.async false
namespace CurrentMain.Current799Next48Data
open CurrentMain.CanonicalFrameCoverage
def children : Array (ChildKey 1005) := #[
  ⟨0, 2, 1⟩,
  ⟨0, 3, 1⟩,
  ⟨0, 4, 1⟩,
  ⟨0, 5, 1⟩,
  ⟨0, 6, 1⟩,
  ⟨0, 7, 1⟩,
  ⟨0, 8, 1⟩
]

def forwardD : List (Row 1005) := [
  ⟨9290, .relabel 478 0 6, none, some (4, 1)⟩,
  ⟨9291, .add 478 548 ((1), (2)), some 6, none⟩,
  ⟨9292, .relabel 479 0 6, none, some (4, 1)⟩,
  ⟨9293, .add 479 549 ((1), (2)), some 6, none⟩,
  ⟨9294, .relabel 492 0 7, none, some (5, 1)⟩,
  ⟨9295, .add 492 552 ((-1), (1)), some 7, none⟩,
  ⟨9296, .relabel 493 0 7, none, some (5, 1)⟩,
  ⟨9297, .add 493 553 ((-1), (1)), some 7, none⟩,
  ⟨9298, .relabel 528 0 8, none, some (6, 1)⟩,
  ⟨9299, .add 528 564 ((-1), (1)), some 8, none⟩,
  ⟨9300, .relabel 529 0 8, none, some (6, 1)⟩,
  ⟨9301, .add 529 565 ((-1), (1)), some 8, none⟩,
  ⟨9302, .relabel 476 0 6, none, some (4, 1)⟩,
  ⟨9303, .add 476 500 ((-1), (1)), some 6, none⟩,
  ⟨9304, .relabel 477 0 6, none, some (4, 1)⟩,
  ⟨9305, .add 477 501 ((-1), (1)), some 6, none⟩,
  ⟨9306, .relabel 502 0 6, none, some (4, 1)⟩,
  ⟨9307, .add 502 550 ((-1), (1)), some 6, none⟩,
  ⟨9308, .relabel 503 0 6, none, some (4, 1)⟩,
  ⟨9309, .add 503 551 ((-1), (1)), some 6, none⟩,
  ⟨9310, .relabel 514 0 6, none, some (4, 1)⟩,
  ⟨9311, .add 514 562 ((-1), (1)), some 6, none⟩,
  ⟨9312, .relabel 515 0 6, none, some (4, 1)⟩,
  ⟨9313, .add 515 563 ((-1), (1)), some 6, none⟩
]

def forwardE : List (Row 1005) := [
  ⟨9314, .relabel 504 0 8, none, some (6, 1)⟩,
  ⟨9315, .add 504 540 ((-1), (1)), some 8, none⟩,
  ⟨9316, .relabel 505 0 8, none, some (6, 1)⟩,
  ⟨9317, .add 505 541 ((-1), (1)), some 8, none⟩,
  ⟨9318, .relabel 516 0 7, none, some (5, 1)⟩,
  ⟨9319, .add 516 576 ((-1), (1)), some 7, none⟩,
  ⟨9320, .relabel 517 0 7, none, some (5, 1)⟩,
  ⟨9321, .add 517 577 ((-1), (1)), some 7, none⟩,
  ⟨9322, .relabel 462 0 7, none, some (5, 1)⟩,
  ⟨9323, .add 462 486 ((-1), (1)), some 7, none⟩,
  ⟨9324, .relabel 463 0 7, none, some (5, 1)⟩,
  ⟨9325, .add 463 487 ((-1), (1)), some 7, none⟩,
  ⟨9326, .relabel 468 0 7, none, some (5, 1)⟩,
  ⟨9327, .add 468 546 ((1), (2)), some 7, none⟩,
  ⟨9328, .relabel 469 0 7, none, some (5, 1)⟩,
  ⟨9329, .add 469 547 ((1), (2)), some 7, none⟩,
  ⟨9330, .relabel 466 0 8, none, some (6, 1)⟩,
  ⟨9331, .add 466 534 ((1), (2)), some 8, none⟩,
  ⟨9332, .relabel 467 0 8, none, some (6, 1)⟩,
  ⟨9333, .add 467 535 ((1), (2)), some 8, none⟩,
  ⟨9334, .relabel 464 0 8, none, some (6, 1)⟩,
  ⟨9335, .add 464 498 ((-1), (1)), some 8, none⟩,
  ⟨9336, .relabel 465 0 8, none, some (6, 1)⟩,
  ⟨9337, .add 465 499 ((-1), (1)), some 8, none⟩
]

def backwardD : List (Row 1005) := [
  ⟨9290, .relabel 478 0 6, none, some (4, 1)⟩,
  ⟨9291, .add 548 478 ((-1), (2)), some 6, none⟩,
  ⟨9292, .relabel 479 0 6, none, some (4, 1)⟩,
  ⟨9293, .add 549 479 ((-1), (2)), some 6, none⟩,
  ⟨9294, .relabel 492 0 7, none, some (5, 1)⟩,
  ⟨9295, .add 552 492 ((1), (1)), some 7, none⟩,
  ⟨9296, .relabel 493 0 7, none, some (5, 1)⟩,
  ⟨9297, .add 553 493 ((1), (1)), some 7, none⟩,
  ⟨9298, .relabel 528 0 8, none, some (6, 1)⟩,
  ⟨9299, .add 564 528 ((1), (1)), some 8, none⟩,
  ⟨9300, .relabel 529 0 8, none, some (6, 1)⟩,
  ⟨9301, .add 565 529 ((1), (1)), some 8, none⟩,
  ⟨9302, .relabel 476 0 6, none, some (4, 1)⟩,
  ⟨9303, .add 500 476 ((1), (1)), some 6, none⟩,
  ⟨9304, .relabel 477 0 6, none, some (4, 1)⟩,
  ⟨9305, .add 501 477 ((1), (1)), some 6, none⟩,
  ⟨9306, .relabel 502 0 6, none, some (4, 1)⟩,
  ⟨9307, .add 550 502 ((1), (1)), some 6, none⟩,
  ⟨9308, .relabel 503 0 6, none, some (4, 1)⟩,
  ⟨9309, .add 551 503 ((1), (1)), some 6, none⟩,
  ⟨9310, .relabel 514 0 6, none, some (4, 1)⟩,
  ⟨9311, .add 562 514 ((1), (1)), some 6, none⟩,
  ⟨9312, .relabel 515 0 6, none, some (4, 1)⟩,
  ⟨9313, .add 563 515 ((1), (1)), some 6, none⟩
]

def backwardE : List (Row 1005) := [
  ⟨9314, .relabel 504 0 8, none, some (6, 1)⟩,
  ⟨9315, .add 540 504 ((1), (1)), some 8, none⟩,
  ⟨9316, .relabel 505 0 8, none, some (6, 1)⟩,
  ⟨9317, .add 541 505 ((1), (1)), some 8, none⟩,
  ⟨9318, .relabel 516 0 7, none, some (5, 1)⟩,
  ⟨9319, .add 576 516 ((1), (1)), some 7, none⟩,
  ⟨9320, .relabel 517 0 7, none, some (5, 1)⟩,
  ⟨9321, .add 577 517 ((1), (1)), some 7, none⟩,
  ⟨9322, .relabel 462 0 7, none, some (5, 1)⟩,
  ⟨9323, .add 486 462 ((1), (1)), some 7, none⟩,
  ⟨9324, .relabel 463 0 7, none, some (5, 1)⟩,
  ⟨9325, .add 487 463 ((1), (1)), some 7, none⟩,
  ⟨9326, .relabel 468 0 7, none, some (5, 1)⟩,
  ⟨9327, .add 546 468 ((-1), (2)), some 7, none⟩,
  ⟨9328, .relabel 469 0 7, none, some (5, 1)⟩,
  ⟨9329, .add 547 469 ((-1), (2)), some 7, none⟩,
  ⟨9330, .relabel 466 0 8, none, some (6, 1)⟩,
  ⟨9331, .add 534 466 ((-1), (2)), some 8, none⟩,
  ⟨9332, .relabel 467 0 8, none, some (6, 1)⟩,
  ⟨9333, .add 535 467 ((-1), (2)), some 8, none⟩,
  ⟨9334, .relabel 464 0 8, none, some (6, 1)⟩,
  ⟨9335, .add 498 464 ((1), (1)), some 8, none⟩,
  ⟨9336, .relabel 465 0 8, none, some (6, 1)⟩,
  ⟨9337, .add 499 465 ((1), (1)), some 8, none⟩
]

def data : SelectedData 1005 :=
  ⟨Current799First33CoverageData.frameDimensions,
    Current799First33CoverageData.initialOriginalLabels, children, forwardD ++ forwardE, backwardD ++ backwardE⟩
def support73 : List Register := [478, 479, 492, 493, 528, 529, 476, 477, 502, 503, 514, 515]
def target73 (r : Register) : FrameLabel 1005 :=
  if r ∈ ([478, 479, 476, 477, 502, 503, 514, 515] : List Register) then 6 else if r ∈ ([492, 493] : List Register) then 7 else 8
def labels73 (r : Register) : FrameLabel 1005 :=
  if r ∈ support73 then target73 r else Current799Next16Data.labels49 r
def support97 : List Register := [504, 505, 516, 517, 462, 463, 468, 469, 466, 467, 464, 465]
def target97 (r : Register) : FrameLabel 1005 :=
  if r ∈ ([516, 517, 462, 463, 468, 469] : List Register) then 7 else 8
def labels97 (r : Register) : FrameLabel 1005 :=
  if r ∈ support97 then target97 r else labels73 r
end CurrentMain.Current799Next48Data
