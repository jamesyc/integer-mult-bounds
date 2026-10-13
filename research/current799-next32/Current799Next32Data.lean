/- Exact current PR799 next32 rows, zero-based raw9338..9369, both orientations.
Only label/catalog coverage; eight operator suppliers and actual entrance remain separate.
Author-checked conditional source context: kappa=1661634653669567/1000000000000000000.
Attribution: selected PR799 source and accepted PR509/checker interfaces. -/
import Current799Next48Check

set_option Elab.async false
namespace CurrentMain.Current799Next32Data
open CurrentMain.CanonicalFrameCoverage
def children : Array (ChildKey 1005) := #[
  ⟨0, 2, 1⟩,
  ⟨0, 3, 1⟩,
  ⟨0, 4, 1⟩,
  ⟨0, 5, 1⟩,
  ⟨0, 6, 1⟩,
  ⟨0, 7, 1⟩,
  ⟨0, 8, 1⟩,
  ⟨0, 9, 1⟩,
  ⟨0, 10, 1⟩,
  ⟨0, 11, 1⟩,
  ⟨0, 12, 1⟩,
  ⟨0, 13, 1⟩,
  ⟨0, 14, 1⟩,
  ⟨0, 15, 1⟩,
  ⟨0, 16, 1⟩
]

def forwardF : List (Row 1005) := [
  ⟨9338, .relabel 224 0 9, none, some (7, 1)⟩,
  ⟨9339, .add 224 0 ((1), (1)), some 9, none⟩,
  ⟨9340, .relabel 225 0 9, none, some (7, 1)⟩,
  ⟨9341, .add 225 0 ((1), (1)), some 9, none⟩,
  ⟨9342, .relabel 226 0 10, none, some (8, 1)⟩,
  ⟨9343, .add 226 76 ((1), (1)), some 10, none⟩,
  ⟨9344, .relabel 227 0 10, none, some (8, 1)⟩,
  ⟨9345, .add 227 76 ((1), (1)), some 10, none⟩,
  ⟨9346, .relabel 228 0 11, none, some (9, 1)⟩,
  ⟨9347, .add 228 87 ((1), (1)), some 11, none⟩,
  ⟨9348, .relabel 229 0 11, none, some (9, 1)⟩,
  ⟨9349, .add 229 87 ((1), (1)), some 11, none⟩,
  ⟨9350, .relabel 230 0 12, none, some (10, 1)⟩,
  ⟨9351, .add 230 27 ((1), (1)), some 12, none⟩,
  ⟨9352, .relabel 231 0 12, none, some (10, 1)⟩,
  ⟨9353, .add 231 27 ((1), (1)), some 12, none⟩,
  ⟨9354, .relabel 232 0 13, none, some (11, 1)⟩,
  ⟨9355, .add 232 92 ((1), (1)), some 13, none⟩,
  ⟨9356, .relabel 233 0 13, none, some (11, 1)⟩,
  ⟨9357, .add 233 92 ((1), (1)), some 13, none⟩,
  ⟨9358, .relabel 234 0 14, none, some (12, 1)⟩,
  ⟨9359, .add 234 57 ((1), (1)), some 14, none⟩,
  ⟨9360, .relabel 235 0 14, none, some (12, 1)⟩,
  ⟨9361, .add 235 57 ((1), (1)), some 14, none⟩
]

def forwardG : List (Row 1005) := [
  ⟨9362, .relabel 236 0 15, none, some (13, 1)⟩,
  ⟨9363, .add 236 7 ((1), (1)), some 15, none⟩,
  ⟨9364, .relabel 237 0 15, none, some (13, 1)⟩,
  ⟨9365, .add 237 7 ((1), (1)), some 15, none⟩,
  ⟨9366, .relabel 238 0 16, none, some (14, 1)⟩,
  ⟨9367, .add 238 81 ((1), (1)), some 16, none⟩,
  ⟨9368, .relabel 239 0 16, none, some (14, 1)⟩,
  ⟨9369, .add 239 81 ((1), (1)), some 16, none⟩
]

def backwardF : List (Row 1005) := [
  ⟨9338, .relabel 224 0 9, none, some (7, 1)⟩,
  ⟨9339, .add 0 224 ((-1), (1)), some 9, none⟩,
  ⟨9340, .relabel 225 0 9, none, some (7, 1)⟩,
  ⟨9341, .add 0 225 ((-1), (1)), some 9, none⟩,
  ⟨9342, .relabel 226 0 10, none, some (8, 1)⟩,
  ⟨9343, .add 76 226 ((-1), (1)), some 10, none⟩,
  ⟨9344, .relabel 227 0 10, none, some (8, 1)⟩,
  ⟨9345, .add 76 227 ((-1), (1)), some 10, none⟩,
  ⟨9346, .relabel 228 0 11, none, some (9, 1)⟩,
  ⟨9347, .add 87 228 ((-1), (1)), some 11, none⟩,
  ⟨9348, .relabel 229 0 11, none, some (9, 1)⟩,
  ⟨9349, .add 87 229 ((-1), (1)), some 11, none⟩,
  ⟨9350, .relabel 230 0 12, none, some (10, 1)⟩,
  ⟨9351, .add 27 230 ((-1), (1)), some 12, none⟩,
  ⟨9352, .relabel 231 0 12, none, some (10, 1)⟩,
  ⟨9353, .add 27 231 ((-1), (1)), some 12, none⟩,
  ⟨9354, .relabel 232 0 13, none, some (11, 1)⟩,
  ⟨9355, .add 92 232 ((-1), (1)), some 13, none⟩,
  ⟨9356, .relabel 233 0 13, none, some (11, 1)⟩,
  ⟨9357, .add 92 233 ((-1), (1)), some 13, none⟩,
  ⟨9358, .relabel 234 0 14, none, some (12, 1)⟩,
  ⟨9359, .add 57 234 ((-1), (1)), some 14, none⟩,
  ⟨9360, .relabel 235 0 14, none, some (12, 1)⟩,
  ⟨9361, .add 57 235 ((-1), (1)), some 14, none⟩
]

def backwardG : List (Row 1005) := [
  ⟨9362, .relabel 236 0 15, none, some (13, 1)⟩,
  ⟨9363, .add 7 236 ((-1), (1)), some 15, none⟩,
  ⟨9364, .relabel 237 0 15, none, some (13, 1)⟩,
  ⟨9365, .add 7 237 ((-1), (1)), some 15, none⟩,
  ⟨9366, .relabel 238 0 16, none, some (14, 1)⟩,
  ⟨9367, .add 81 238 ((-1), (1)), some 16, none⟩,
  ⟨9368, .relabel 239 0 16, none, some (14, 1)⟩,
  ⟨9369, .add 81 239 ((-1), (1)), some 16, none⟩
]

def data : SelectedData 1005 :=
  ⟨Current799First33CoverageData.frameDimensions,
    Current799First33CoverageData.initialOriginalLabels, children, forwardF ++ forwardG, backwardF ++ backwardG⟩
def support121 : List Register := [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235]
def target121 (r : Register) : FrameLabel 1005 :=
  if r ∈ ([224, 225] : List Register) then 9 else if r ∈ ([226, 227] : List Register) then 10 else if r ∈ ([228, 229] : List Register) then 11 else if r ∈ ([230, 231] : List Register) then 12 else if r ∈ ([232, 233] : List Register) then 13 else 14
def labels121 (r : Register) : FrameLabel 1005 :=
  if r ∈ support121 then target121 r else Current799Next48Data.labels97 r
def support129 : List Register := [236, 237, 238, 239]
def target129 (r : Register) : FrameLabel 1005 :=
  if r ∈ ([236, 237] : List Register) then 15 else 16
def labels129 (r : Register) : FrameLabel 1005 :=
  if r ∈ support129 then target129 r else labels121 r
end CurrentMain.Current799Next32Data
