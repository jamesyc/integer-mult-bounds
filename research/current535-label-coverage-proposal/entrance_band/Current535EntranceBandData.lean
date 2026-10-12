/- Exact current535 entrance band raw10871..10902, both orientations.
Eight ordered rank1 keys0→6…13; stop before the nonzero-old-frame joins.
No operator, omitted-adapter or full physical execution conclusion. -/
import Current535TwoKeyCheck

set_option Elab.async false
namespace CurrentMain.Current535EntranceBandData
open CurrentMain.CanonicalFrameCoverage
def forwardI : List (Row 997) := [
  ⟨10871, .relabel 224 0 6, none, some (4, 1)⟩,
  ⟨10872, .add 224 0 ((1), (1)), some 6, none⟩,
  ⟨10873, .relabel 225 0 6, none, some (4, 1)⟩,
  ⟨10874, .add 225 0 ((1), (1)), some 6, none⟩,
  ⟨10875, .relabel 226 0 7, none, some (5, 1)⟩,
  ⟨10876, .add 226 76 ((1), (1)), some 7, none⟩,
  ⟨10877, .relabel 227 0 7, none, some (5, 1)⟩,
  ⟨10878, .add 227 76 ((1), (1)), some 7, none⟩,
  ⟨10879, .relabel 228 0 8, none, some (6, 1)⟩,
  ⟨10880, .add 228 87 ((1), (1)), some 8, none⟩,
  ⟨10881, .relabel 229 0 8, none, some (6, 1)⟩,
  ⟨10882, .add 229 87 ((1), (1)), some 8, none⟩,
  ⟨10883, .relabel 230 0 9, none, some (7, 1)⟩,
  ⟨10884, .add 230 27 ((1), (1)), some 9, none⟩,
  ⟨10885, .relabel 231 0 9, none, some (7, 1)⟩,
  ⟨10886, .add 231 27 ((1), (1)), some 9, none⟩,
  ⟨10887, .relabel 232 0 10, none, some (8, 1)⟩,
  ⟨10888, .add 232 92 ((1), (1)), some 10, none⟩,
  ⟨10889, .relabel 233 0 10, none, some (8, 1)⟩,
  ⟨10890, .add 233 92 ((1), (1)), some 10, none⟩,
  ⟨10891, .relabel 234 0 11, none, some (9, 1)⟩,
  ⟨10892, .add 234 57 ((1), (1)), some 11, none⟩,
  ⟨10893, .relabel 235 0 11, none, some (9, 1)⟩,
  ⟨10894, .add 235 57 ((1), (1)), some 11, none⟩
]

def forwardJ : List (Row 997) := [
  ⟨10895, .relabel 236 0 12, none, some (10, 1)⟩,
  ⟨10896, .add 236 7 ((1), (1)), some 12, none⟩,
  ⟨10897, .relabel 237 0 12, none, some (10, 1)⟩,
  ⟨10898, .add 237 7 ((1), (1)), some 12, none⟩,
  ⟨10899, .relabel 238 0 13, none, some (11, 1)⟩,
  ⟨10900, .add 238 81 ((1), (1)), some 13, none⟩,
  ⟨10901, .relabel 239 0 13, none, some (11, 1)⟩,
  ⟨10902, .add 239 81 ((1), (1)), some 13, none⟩
]

def backwardI : List (Row 997) := [
  ⟨10871, .relabel 224 0 6, none, some (4, 1)⟩,
  ⟨10872, .add 0 224 ((-1), (1)), some 6, none⟩,
  ⟨10873, .relabel 225 0 6, none, some (4, 1)⟩,
  ⟨10874, .add 0 225 ((-1), (1)), some 6, none⟩,
  ⟨10875, .relabel 226 0 7, none, some (5, 1)⟩,
  ⟨10876, .add 76 226 ((-1), (1)), some 7, none⟩,
  ⟨10877, .relabel 227 0 7, none, some (5, 1)⟩,
  ⟨10878, .add 76 227 ((-1), (1)), some 7, none⟩,
  ⟨10879, .relabel 228 0 8, none, some (6, 1)⟩,
  ⟨10880, .add 87 228 ((-1), (1)), some 8, none⟩,
  ⟨10881, .relabel 229 0 8, none, some (6, 1)⟩,
  ⟨10882, .add 87 229 ((-1), (1)), some 8, none⟩,
  ⟨10883, .relabel 230 0 9, none, some (7, 1)⟩,
  ⟨10884, .add 27 230 ((-1), (1)), some 9, none⟩,
  ⟨10885, .relabel 231 0 9, none, some (7, 1)⟩,
  ⟨10886, .add 27 231 ((-1), (1)), some 9, none⟩,
  ⟨10887, .relabel 232 0 10, none, some (8, 1)⟩,
  ⟨10888, .add 92 232 ((-1), (1)), some 10, none⟩,
  ⟨10889, .relabel 233 0 10, none, some (8, 1)⟩,
  ⟨10890, .add 92 233 ((-1), (1)), some 10, none⟩,
  ⟨10891, .relabel 234 0 11, none, some (9, 1)⟩,
  ⟨10892, .add 57 234 ((-1), (1)), some 11, none⟩,
  ⟨10893, .relabel 235 0 11, none, some (9, 1)⟩,
  ⟨10894, .add 57 235 ((-1), (1)), some 11, none⟩
]

def backwardJ : List (Row 997) := [
  ⟨10895, .relabel 236 0 12, none, some (10, 1)⟩,
  ⟨10896, .add 7 236 ((-1), (1)), some 12, none⟩,
  ⟨10897, .relabel 237 0 12, none, some (10, 1)⟩,
  ⟨10898, .add 7 237 ((-1), (1)), some 12, none⟩,
  ⟨10899, .relabel 238 0 13, none, some (11, 1)⟩,
  ⟨10900, .add 81 238 ((-1), (1)), some 13, none⟩,
  ⟨10901, .relabel 239 0 13, none, some (11, 1)⟩,
  ⟨10902, .add 81 239 ((-1), (1)), some 13, none⟩
]

def support204 : List Register := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235]
def values204 (r : Register) : FrameLabel 997 :=
  match r.val with
  | 224 => 6
  | 225 => 6
  | 226 => 7
  | 227 => 7
  | 228 => 8
  | 229 => 8
  | 230 => 9
  | 231 => 9
  | 232 => 10
  | 233 => 10
  | 234 => 11
  | 235 => 11
  | _ => 0
def labels204 (r : Register) : FrameLabel 997 :=
  if r ∈ support204 then values204 r else Current535TwoKeyData.labels180 r
def support212 : List Register := [236, 237, 238, 239]
def values212 (r : Register) : FrameLabel 997 :=
  match r.val with
  | 236 => 12
  | 237 => 12
  | 238 => 13
  | 239 => 13
  | _ => 0
def labels212 (r : Register) : FrameLabel 997 :=
  if r ∈ support212 then values212 r else labels204 r
end CurrentMain.Current535EntranceBandData
