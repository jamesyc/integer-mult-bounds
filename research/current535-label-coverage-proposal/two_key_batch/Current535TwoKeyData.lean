/- Exact current535 two-key source-literal batch raw10781..10870, both orientations.
Keys ordinal2/0→4 and ordinal3/0→5 retain all ordered operands and signed coefficients.
No operator, whole-stream or omitted-adapter conclusion. -/
import Current535Child003Check

set_option Elab.async false
namespace CurrentMain.Current535TwoKeyData
open CurrentMain.CanonicalFrameCoverage
def forwardE : List (Row 997) := [
  ⟨10781, .relabel 464 0 4, none, some (2, 1)⟩,
  ⟨10782, .add 464 475 ((-1), (1)), some 4, none⟩,
  ⟨10783, .relabel 465 0 4, none, some (2, 1)⟩,
  ⟨10784, .add 465 475 ((-1), (1)), some 4, none⟩,
  ⟨10785, .relabel 474 0 4, none, some (2, 1)⟩,
  ⟨10786, .add 474 475 ((1), (1)), some 4, none⟩,
  ⟨10787, .relabel 462 0 4, none, some (2, 1)⟩,
  ⟨10788, .add 462 477 ((-1), (1)), some 4, none⟩,
  ⟨10789, .relabel 463 0 4, none, some (2, 1)⟩,
  ⟨10790, .add 463 477 ((-1), (1)), some 4, none⟩,
  ⟨10791, .relabel 476 0 4, none, some (2, 1)⟩,
  ⟨10792, .add 476 477 ((1), (1)), some 4, none⟩,
  ⟨10793, .relabel 538 0 4, none, some (2, 1)⟩,
  ⟨10794, .add 538 551 ((-1), (1)), some 4, none⟩,
  ⟨10795, .relabel 539 0 4, none, some (2, 1)⟩,
  ⟨10796, .add 539 551 ((-1), (1)), some 4, none⟩,
  ⟨10797, .relabel 550 0 4, none, some (2, 1)⟩,
  ⟨10798, .add 550 551 ((1), (1)), some 4, none⟩,
  ⟨10799, .relabel 540 0 4, none, some (2, 1)⟩,
  ⟨10800, .add 540 553 ((-1), (1)), some 4, none⟩,
  ⟨10801, .relabel 541 0 4, none, some (2, 1)⟩,
  ⟨10802, .add 541 553 ((-1), (1)), some 4, none⟩,
  ⟨10803, .relabel 552 0 4, none, some (2, 1)⟩,
  ⟨10804, .add 552 553 ((1), (1)), some 4, none⟩
]

def forwardF : List (Row 997) := [
  ⟨10805, .add 538 563 ((1), (1)), some 4, none⟩,
  ⟨10806, .add 539 563 ((-1), (1)), some 4, none⟩,
  ⟨10807, .relabel 562 0 4, none, some (2, 1)⟩,
  ⟨10808, .add 562 563 ((-1), (1)), some 4, none⟩,
  ⟨10809, .add 540 565 ((-1), (1)), some 4, none⟩,
  ⟨10810, .add 541 565 ((-1), (1)), some 4, none⟩,
  ⟨10811, .add 552 565 ((2), (1)), some 4, none⟩,
  ⟨10812, .relabel 564 0 4, none, some (2, 1)⟩,
  ⟨10813, .add 564 565 ((-1), (1)), some 4, none⟩,
  ⟨10814, .add 538 574 ((1), (1)), some 4, none⟩,
  ⟨10815, .add 550 574 ((-1), (1)), some 4, none⟩,
  ⟨10816, .add 562 574 ((-1), (1)), some 4, none⟩,
  ⟨10817, .add 539 575 ((-1), (1)), some 4, none⟩,
  ⟨10818, .add 550 575 ((1), (1)), some 4, none⟩,
  ⟨10819, .add 562 575 ((-1), (1)), some 4, none⟩,
  ⟨10820, .add 540 576 ((-1), (1)), some 4, none⟩,
  ⟨10821, .add 552 576 ((1), (1)), some 4, none⟩,
  ⟨10822, .add 564 576 ((-1), (1)), some 4, none⟩,
  ⟨10823, .add 541 577 ((-1), (1)), some 4, none⟩,
  ⟨10824, .add 552 577 ((1), (1)), some 4, none⟩,
  ⟨10825, .add 564 577 ((-1), (1)), some 4, none⟩
]

def forwardG : List (Row 997) := [
  ⟨10826, .relabel 466 0 5, none, some (3, 1)⟩,
  ⟨10827, .add 466 479 ((-1), (1)), some 5, none⟩,
  ⟨10828, .relabel 467 0 5, none, some (3, 1)⟩,
  ⟨10829, .add 467 479 ((-1), (1)), some 5, none⟩,
  ⟨10830, .relabel 478 0 5, none, some (3, 1)⟩,
  ⟨10831, .add 478 479 ((1), (1)), some 5, none⟩,
  ⟨10832, .relabel 468 0 5, none, some (3, 1)⟩,
  ⟨10833, .add 468 481 ((-1), (1)), some 5, none⟩,
  ⟨10834, .relabel 469 0 5, none, some (3, 1)⟩,
  ⟨10835, .add 469 481 ((-1), (1)), some 5, none⟩,
  ⟨10836, .relabel 480 0 5, none, some (3, 1)⟩,
  ⟨10837, .add 480 481 ((1), (1)), some 5, none⟩,
  ⟨10838, .relabel 490 0 5, none, some (3, 1)⟩,
  ⟨10839, .add 490 503 ((-1), (1)), some 5, none⟩,
  ⟨10840, .relabel 491 0 5, none, some (3, 1)⟩,
  ⟨10841, .add 491 503 ((-1), (1)), some 5, none⟩,
  ⟨10842, .relabel 502 0 5, none, some (3, 1)⟩,
  ⟨10843, .add 502 503 ((1), (1)), some 5, none⟩,
  ⟨10844, .relabel 492 0 5, none, some (3, 1)⟩,
  ⟨10845, .add 492 505 ((-1), (1)), some 5, none⟩,
  ⟨10846, .relabel 493 0 5, none, some (3, 1)⟩,
  ⟨10847, .add 493 505 ((-1), (1)), some 5, none⟩,
  ⟨10848, .relabel 504 0 5, none, some (3, 1)⟩,
  ⟨10849, .add 504 505 ((1), (1)), some 5, none⟩
]

def forwardH : List (Row 997) := [
  ⟨10850, .add 490 515 ((1), (1)), some 5, none⟩,
  ⟨10851, .add 491 515 ((-1), (1)), some 5, none⟩,
  ⟨10852, .relabel 514 0 5, none, some (3, 1)⟩,
  ⟨10853, .add 514 515 ((-1), (1)), some 5, none⟩,
  ⟨10854, .add 492 517 ((-1), (1)), some 5, none⟩,
  ⟨10855, .add 493 517 ((-1), (1)), some 5, none⟩,
  ⟨10856, .add 504 517 ((2), (1)), some 5, none⟩,
  ⟨10857, .relabel 516 0 5, none, some (3, 1)⟩,
  ⟨10858, .add 516 517 ((-1), (1)), some 5, none⟩,
  ⟨10859, .add 490 526 ((1), (1)), some 5, none⟩,
  ⟨10860, .add 502 526 ((-1), (1)), some 5, none⟩,
  ⟨10861, .add 514 526 ((-1), (1)), some 5, none⟩,
  ⟨10862, .add 491 527 ((-1), (1)), some 5, none⟩,
  ⟨10863, .add 502 527 ((1), (1)), some 5, none⟩,
  ⟨10864, .add 514 527 ((-1), (1)), some 5, none⟩,
  ⟨10865, .add 492 528 ((-1), (1)), some 5, none⟩,
  ⟨10866, .add 504 528 ((1), (1)), some 5, none⟩,
  ⟨10867, .add 516 528 ((-1), (1)), some 5, none⟩,
  ⟨10868, .add 493 529 ((-1), (1)), some 5, none⟩,
  ⟨10869, .add 504 529 ((1), (1)), some 5, none⟩,
  ⟨10870, .add 516 529 ((-1), (1)), some 5, none⟩
]

def backwardE : List (Row 997) := [
  ⟨10781, .relabel 464 0 4, none, some (2, 1)⟩,
  ⟨10782, .add 475 464 ((1), (1)), some 4, none⟩,
  ⟨10783, .relabel 465 0 4, none, some (2, 1)⟩,
  ⟨10784, .add 475 465 ((1), (1)), some 4, none⟩,
  ⟨10785, .relabel 474 0 4, none, some (2, 1)⟩,
  ⟨10786, .add 475 474 ((-1), (1)), some 4, none⟩,
  ⟨10787, .relabel 462 0 4, none, some (2, 1)⟩,
  ⟨10788, .add 477 462 ((1), (1)), some 4, none⟩,
  ⟨10789, .relabel 463 0 4, none, some (2, 1)⟩,
  ⟨10790, .add 477 463 ((1), (1)), some 4, none⟩,
  ⟨10791, .relabel 476 0 4, none, some (2, 1)⟩,
  ⟨10792, .add 477 476 ((-1), (1)), some 4, none⟩,
  ⟨10793, .relabel 538 0 4, none, some (2, 1)⟩,
  ⟨10794, .add 551 538 ((1), (1)), some 4, none⟩,
  ⟨10795, .relabel 539 0 4, none, some (2, 1)⟩,
  ⟨10796, .add 551 539 ((1), (1)), some 4, none⟩,
  ⟨10797, .relabel 550 0 4, none, some (2, 1)⟩,
  ⟨10798, .add 551 550 ((-1), (1)), some 4, none⟩,
  ⟨10799, .relabel 540 0 4, none, some (2, 1)⟩,
  ⟨10800, .add 553 540 ((1), (1)), some 4, none⟩,
  ⟨10801, .relabel 541 0 4, none, some (2, 1)⟩,
  ⟨10802, .add 553 541 ((1), (1)), some 4, none⟩,
  ⟨10803, .relabel 552 0 4, none, some (2, 1)⟩,
  ⟨10804, .add 553 552 ((-1), (1)), some 4, none⟩
]

def backwardF : List (Row 997) := [
  ⟨10805, .add 563 538 ((-1), (1)), some 4, none⟩,
  ⟨10806, .add 563 539 ((1), (1)), some 4, none⟩,
  ⟨10807, .relabel 562 0 4, none, some (2, 1)⟩,
  ⟨10808, .add 563 562 ((1), (1)), some 4, none⟩,
  ⟨10809, .add 565 540 ((1), (1)), some 4, none⟩,
  ⟨10810, .add 565 541 ((1), (1)), some 4, none⟩,
  ⟨10811, .add 565 552 ((-2), (1)), some 4, none⟩,
  ⟨10812, .relabel 564 0 4, none, some (2, 1)⟩,
  ⟨10813, .add 565 564 ((1), (1)), some 4, none⟩,
  ⟨10814, .add 574 538 ((-1), (1)), some 4, none⟩,
  ⟨10815, .add 574 550 ((1), (1)), some 4, none⟩,
  ⟨10816, .add 574 562 ((1), (1)), some 4, none⟩,
  ⟨10817, .add 575 539 ((1), (1)), some 4, none⟩,
  ⟨10818, .add 575 550 ((-1), (1)), some 4, none⟩,
  ⟨10819, .add 575 562 ((1), (1)), some 4, none⟩,
  ⟨10820, .add 576 540 ((1), (1)), some 4, none⟩,
  ⟨10821, .add 576 552 ((-1), (1)), some 4, none⟩,
  ⟨10822, .add 576 564 ((1), (1)), some 4, none⟩,
  ⟨10823, .add 577 541 ((1), (1)), some 4, none⟩,
  ⟨10824, .add 577 552 ((-1), (1)), some 4, none⟩,
  ⟨10825, .add 577 564 ((1), (1)), some 4, none⟩
]

def backwardG : List (Row 997) := [
  ⟨10826, .relabel 466 0 5, none, some (3, 1)⟩,
  ⟨10827, .add 479 466 ((1), (1)), some 5, none⟩,
  ⟨10828, .relabel 467 0 5, none, some (3, 1)⟩,
  ⟨10829, .add 479 467 ((1), (1)), some 5, none⟩,
  ⟨10830, .relabel 478 0 5, none, some (3, 1)⟩,
  ⟨10831, .add 479 478 ((-1), (1)), some 5, none⟩,
  ⟨10832, .relabel 468 0 5, none, some (3, 1)⟩,
  ⟨10833, .add 481 468 ((1), (1)), some 5, none⟩,
  ⟨10834, .relabel 469 0 5, none, some (3, 1)⟩,
  ⟨10835, .add 481 469 ((1), (1)), some 5, none⟩,
  ⟨10836, .relabel 480 0 5, none, some (3, 1)⟩,
  ⟨10837, .add 481 480 ((-1), (1)), some 5, none⟩,
  ⟨10838, .relabel 490 0 5, none, some (3, 1)⟩,
  ⟨10839, .add 503 490 ((1), (1)), some 5, none⟩,
  ⟨10840, .relabel 491 0 5, none, some (3, 1)⟩,
  ⟨10841, .add 503 491 ((1), (1)), some 5, none⟩,
  ⟨10842, .relabel 502 0 5, none, some (3, 1)⟩,
  ⟨10843, .add 503 502 ((-1), (1)), some 5, none⟩,
  ⟨10844, .relabel 492 0 5, none, some (3, 1)⟩,
  ⟨10845, .add 505 492 ((1), (1)), some 5, none⟩,
  ⟨10846, .relabel 493 0 5, none, some (3, 1)⟩,
  ⟨10847, .add 505 493 ((1), (1)), some 5, none⟩,
  ⟨10848, .relabel 504 0 5, none, some (3, 1)⟩,
  ⟨10849, .add 505 504 ((-1), (1)), some 5, none⟩
]

def backwardH : List (Row 997) := [
  ⟨10850, .add 515 490 ((-1), (1)), some 5, none⟩,
  ⟨10851, .add 515 491 ((1), (1)), some 5, none⟩,
  ⟨10852, .relabel 514 0 5, none, some (3, 1)⟩,
  ⟨10853, .add 515 514 ((1), (1)), some 5, none⟩,
  ⟨10854, .add 517 492 ((1), (1)), some 5, none⟩,
  ⟨10855, .add 517 493 ((1), (1)), some 5, none⟩,
  ⟨10856, .add 517 504 ((-2), (1)), some 5, none⟩,
  ⟨10857, .relabel 516 0 5, none, some (3, 1)⟩,
  ⟨10858, .add 517 516 ((1), (1)), some 5, none⟩,
  ⟨10859, .add 526 490 ((-1), (1)), some 5, none⟩,
  ⟨10860, .add 526 502 ((1), (1)), some 5, none⟩,
  ⟨10861, .add 526 514 ((1), (1)), some 5, none⟩,
  ⟨10862, .add 527 491 ((1), (1)), some 5, none⟩,
  ⟨10863, .add 527 502 ((-1), (1)), some 5, none⟩,
  ⟨10864, .add 527 514 ((1), (1)), some 5, none⟩,
  ⟨10865, .add 528 492 ((1), (1)), some 5, none⟩,
  ⟨10866, .add 528 504 ((-1), (1)), some 5, none⟩,
  ⟨10867, .add 528 516 ((1), (1)), some 5, none⟩,
  ⟨10868, .add 529 493 ((1), (1)), some 5, none⟩,
  ⟨10869, .add 529 504 ((-1), (1)), some 5, none⟩,
  ⟨10870, .add 529 516 ((1), (1)), some 5, none⟩
]

def support114 : List Register := [464, 465, 474, 462, 463, 476, 538, 539, 550, 540, 541, 552]
def labels114 (r : Register) : FrameLabel 997 :=
  if r ∈ support114 then 4 else Current535Child003Data.labels90 r
def support135 : List Register := [562, 564]
def labels135 (r : Register) : FrameLabel 997 :=
  if r ∈ support135 then 4 else labels114 r
def support159 : List Register := [466, 467, 478, 468, 469, 480, 490, 491, 502, 492, 493, 504]
def labels159 (r : Register) : FrameLabel 997 :=
  if r ∈ support159 then 5 else labels135 r
def support180 : List Register := [514, 516]
def labels180 (r : Register) : FrameLabel 997 :=
  if r ∈ support180 then 5 else labels159 r
end CurrentMain.Current535TwoKeyData
