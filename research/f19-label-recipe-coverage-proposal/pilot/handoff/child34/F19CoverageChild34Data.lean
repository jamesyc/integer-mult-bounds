/- Exact source data only; sparse label functions require the separately proved full handoffs.
Raw signed coefficients, direction, order, source indices and child ordinals are unchanged. -/
import F19CoverageChunkBSplit
namespace CurrentMain.F19SelectedCoverage.Child34Data
open CurrentMain.F19SelectedCoverage

def to3 : List Register := [504, 505, 528, 529]
def to4 : List Register := [492, 493, 516, 517]
def new320 : List Register := to3 ++ to4
def values320 (r : Register) : FrameLabel := if r ∈ to3 then 3 else 4
def labels320 (r : Register) : FrameLabel :=
  if r ∈ new320 then values320 r else BatchData.labels256 r

def new344 : List Register := [502, 503, 514, 515]
def labels344 (r : Register) : FrameLabel :=
  if r ∈ new344 then 5 else labels320 r

def new364 : List Register := [490, 491, 526, 527]
def labels364 (r : Register) : FrameLabel :=
  if r ∈ new364 then 6 else labels344 r

def forwardC : List Row := [
  ⟨11171, .add 492 565 ((1), (2)), some 4, none⟩,
  ⟨11172, .add 493 565 ((-1), (2)), some 4, none⟩,
  ⟨11173, .add 516 565 ((-1), (2)), some 4, none⟩,
  ⟨11174, .add 517 565 ((-1), (2)), some 4, none⟩,
  ⟨11175, .relabel 502 0 5, none, some (3, 1)⟩,
  ⟨11176, .add 502 538 ((-1), (2)), some 5, none⟩,
  ⟨11177, .relabel 503 0 5, none, some (3, 1)⟩,
  ⟨11178, .add 503 538 ((-1), (2)), some 5, none⟩,
  ⟨11179, .relabel 514 0 5, none, some (3, 1)⟩,
  ⟨11180, .add 514 538 ((-1), (2)), some 5, none⟩,
  ⟨11181, .relabel 515 0 5, none, some (3, 1)⟩,
  ⟨11182, .add 515 538 ((1), (2)), some 5, none⟩,
  ⟨11183, .add 502 539 ((-1), (2)), some 5, none⟩,
  ⟨11184, .add 503 539 ((-1), (2)), some 5, none⟩,
  ⟨11185, .add 514 539 ((1), (2)), some 5, none⟩,
  ⟨11186, .add 515 539 ((-1), (2)), some 5, none⟩,
  ⟨11187, .add 502 574 ((-1), (2)), some 5, none⟩,
  ⟨11188, .add 503 574 ((1), (2)), some 5, none⟩,
  ⟨11189, .add 514 574 ((-1), (2)), some 5, none⟩,
  ⟨11190, .add 515 574 ((-1), (2)), some 5, none⟩,
  ⟨11191, .add 502 575 ((1), (2)), some 5, none⟩,
  ⟨11192, .add 503 575 ((-1), (2)), some 5, none⟩,
  ⟨11193, .add 514 575 ((-1), (2)), some 5, none⟩,
  ⟨11194, .add 515 575 ((-1), (2)), some 5, none⟩
]

def backwardC : List Row := [
  ⟨11171, .add 565 492 ((-1), (2)), some 4, none⟩,
  ⟨11172, .add 565 493 ((1), (2)), some 4, none⟩,
  ⟨11173, .add 565 516 ((1), (2)), some 4, none⟩,
  ⟨11174, .add 565 517 ((1), (2)), some 4, none⟩,
  ⟨11175, .relabel 502 0 5, none, some (3, 1)⟩,
  ⟨11176, .add 538 502 ((1), (2)), some 5, none⟩,
  ⟨11177, .relabel 503 0 5, none, some (3, 1)⟩,
  ⟨11178, .add 538 503 ((1), (2)), some 5, none⟩,
  ⟨11179, .relabel 514 0 5, none, some (3, 1)⟩,
  ⟨11180, .add 538 514 ((1), (2)), some 5, none⟩,
  ⟨11181, .relabel 515 0 5, none, some (3, 1)⟩,
  ⟨11182, .add 538 515 ((-1), (2)), some 5, none⟩,
  ⟨11183, .add 539 502 ((1), (2)), some 5, none⟩,
  ⟨11184, .add 539 503 ((1), (2)), some 5, none⟩,
  ⟨11185, .add 539 514 ((-1), (2)), some 5, none⟩,
  ⟨11186, .add 539 515 ((1), (2)), some 5, none⟩,
  ⟨11187, .add 574 502 ((1), (2)), some 5, none⟩,
  ⟨11188, .add 574 503 ((-1), (2)), some 5, none⟩,
  ⟨11189, .add 574 514 ((1), (2)), some 5, none⟩,
  ⟨11190, .add 574 515 ((1), (2)), some 5, none⟩,
  ⟨11191, .add 575 502 ((-1), (2)), some 5, none⟩,
  ⟨11192, .add 575 503 ((1), (2)), some 5, none⟩,
  ⟨11193, .add 575 514 ((1), (2)), some 5, none⟩,
  ⟨11194, .add 575 515 ((1), (2)), some 5, none⟩
]

def forwardD : List Row := [
  ⟨11195, .relabel 490 0 6, none, some (4, 1)⟩,
  ⟨11196, .add 490 550 ((-1), (2)), some 6, none⟩,
  ⟨11197, .relabel 491 0 6, none, some (4, 1)⟩,
  ⟨11198, .add 491 550 ((-1), (2)), some 6, none⟩,
  ⟨11199, .relabel 526 0 6, none, some (4, 1)⟩,
  ⟨11200, .add 526 550 ((-1), (2)), some 6, none⟩,
  ⟨11201, .relabel 527 0 6, none, some (4, 1)⟩,
  ⟨11202, .add 527 550 ((1), (2)), some 6, none⟩,
  ⟨11203, .add 490 551 ((-1), (2)), some 6, none⟩,
  ⟨11204, .add 491 551 ((-1), (2)), some 6, none⟩,
  ⟨11205, .add 526 551 ((1), (2)), some 6, none⟩,
  ⟨11206, .add 527 551 ((-1), (2)), some 6, none⟩,
  ⟨11207, .add 490 562 ((-1), (2)), some 6, none⟩,
  ⟨11208, .add 491 562 ((1), (2)), some 6, none⟩,
  ⟨11209, .add 526 562 ((-1), (2)), some 6, none⟩,
  ⟨11210, .add 527 562 ((-1), (2)), some 6, none⟩,
  ⟨11211, .add 490 563 ((1), (2)), some 6, none⟩,
  ⟨11212, .add 491 563 ((-1), (2)), some 6, none⟩,
  ⟨11213, .add 526 563 ((-1), (2)), some 6, none⟩,
  ⟨11214, .add 527 563 ((-1), (2)), some 6, none⟩
]

def backwardD : List Row := [
  ⟨11195, .relabel 490 0 6, none, some (4, 1)⟩,
  ⟨11196, .add 550 490 ((1), (2)), some 6, none⟩,
  ⟨11197, .relabel 491 0 6, none, some (4, 1)⟩,
  ⟨11198, .add 550 491 ((1), (2)), some 6, none⟩,
  ⟨11199, .relabel 526 0 6, none, some (4, 1)⟩,
  ⟨11200, .add 550 526 ((1), (2)), some 6, none⟩,
  ⟨11201, .relabel 527 0 6, none, some (4, 1)⟩,
  ⟨11202, .add 550 527 ((-1), (2)), some 6, none⟩,
  ⟨11203, .add 551 490 ((1), (2)), some 6, none⟩,
  ⟨11204, .add 551 491 ((1), (2)), some 6, none⟩,
  ⟨11205, .add 551 526 ((-1), (2)), some 6, none⟩,
  ⟨11206, .add 551 527 ((1), (2)), some 6, none⟩,
  ⟨11207, .add 562 490 ((1), (2)), some 6, none⟩,
  ⟨11208, .add 562 491 ((-1), (2)), some 6, none⟩,
  ⟨11209, .add 562 526 ((1), (2)), some 6, none⟩,
  ⟨11210, .add 562 527 ((1), (2)), some 6, none⟩,
  ⟨11211, .add 563 490 ((-1), (2)), some 6, none⟩,
  ⟨11212, .add 563 491 ((1), (2)), some 6, none⟩,
  ⟨11213, .add 563 526 ((1), (2)), some 6, none⟩,
  ⟨11214, .add 563 527 ((1), (2)), some 6, none⟩
]

end CurrentMain.F19SelectedCoverage.Child34Data
