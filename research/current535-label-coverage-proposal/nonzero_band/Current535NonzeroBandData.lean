/- Exact pinned7dfa current535 nonzero-old-frame band raw10903..10950, both orientations.
Twenty-four ordered rank1 children253…276; old6…13 to new14…25.
No operator, omitted-adapter or full physical execution conclusion. -/
import Current535EntranceBandCheck

set_option Elab.async false
namespace CurrentMain.Current535NonzeroBandData
open CurrentMain.CanonicalFrameCoverage
def forwardK : List (Row 997) := [
  ⟨10903, .relabel 0 6 14, none, some (253, 1)⟩,
  ⟨10904, .relabel 27 9 14, none, some (262, 1)⟩,
  ⟨10905, .add 0 27 ((1), (1)), some 14, none⟩,
  ⟨10906, .add 27 0 ((-1), (2)), some 14, none⟩,
  ⟨10907, .relabel 224 6 15, none, some (254, 1)⟩,
  ⟨10908, .relabel 57 11 15, none, some (268, 1)⟩,
  ⟨10909, .add 224 57 ((1), (1)), some 15, none⟩,
  ⟨10910, .add 57 224 ((-1), (2)), some 15, none⟩,
  ⟨10911, .relabel 225 6 16, none, some (255, 1)⟩,
  ⟨10912, .relabel 7 12 16, none, some (271, 1)⟩,
  ⟨10913, .add 225 7 ((1), (1)), some 16, none⟩,
  ⟨10914, .add 7 225 ((-1), (2)), some 16, none⟩,
  ⟨10915, .relabel 76 7 17, none, some (256, 1)⟩,
  ⟨10916, .relabel 87 8 17, none, some (259, 1)⟩,
  ⟨10917, .add 76 87 ((1), (1)), some 17, none⟩,
  ⟨10918, .add 87 76 ((-1), (2)), some 17, none⟩,
  ⟨10919, .relabel 226 7 18, none, some (257, 1)⟩,
  ⟨10920, .relabel 92 10 18, none, some (265, 1)⟩,
  ⟨10921, .add 226 92 ((1), (1)), some 18, none⟩,
  ⟨10922, .add 92 226 ((-1), (2)), some 18, none⟩,
  ⟨10923, .relabel 227 7 19, none, some (258, 1)⟩,
  ⟨10924, .relabel 81 13 19, none, some (274, 1)⟩,
  ⟨10925, .add 227 81 ((1), (1)), some 19, none⟩,
  ⟨10926, .add 81 227 ((-1), (2)), some 19, none⟩
]

def forwardL : List (Row 997) := [
  ⟨10927, .relabel 228 8 20, none, some (260, 1)⟩,
  ⟨10928, .relabel 232 10 20, none, some (266, 1)⟩,
  ⟨10929, .add 228 232 ((1), (1)), some 20, none⟩,
  ⟨10930, .add 232 228 ((-1), (2)), some 20, none⟩,
  ⟨10931, .relabel 229 8 21, none, some (261, 1)⟩,
  ⟨10932, .relabel 238 13 21, none, some (275, 1)⟩,
  ⟨10933, .add 229 238 ((1), (1)), some 21, none⟩,
  ⟨10934, .add 238 229 ((-1), (2)), some 21, none⟩,
  ⟨10935, .relabel 230 9 22, none, some (263, 1)⟩,
  ⟨10936, .relabel 234 11 22, none, some (269, 1)⟩,
  ⟨10937, .add 230 234 ((1), (1)), some 22, none⟩,
  ⟨10938, .add 234 230 ((-1), (2)), some 22, none⟩,
  ⟨10939, .relabel 231 9 23, none, some (264, 1)⟩,
  ⟨10940, .relabel 236 12 23, none, some (272, 1)⟩,
  ⟨10941, .add 231 236 ((1), (1)), some 23, none⟩,
  ⟨10942, .add 236 231 ((-1), (2)), some 23, none⟩,
  ⟨10943, .relabel 233 10 24, none, some (267, 1)⟩,
  ⟨10944, .relabel 239 13 24, none, some (276, 1)⟩,
  ⟨10945, .add 233 239 ((1), (1)), some 24, none⟩,
  ⟨10946, .add 239 233 ((-1), (2)), some 24, none⟩,
  ⟨10947, .relabel 235 11 25, none, some (270, 1)⟩,
  ⟨10948, .relabel 237 12 25, none, some (273, 1)⟩,
  ⟨10949, .add 235 237 ((1), (1)), some 25, none⟩,
  ⟨10950, .add 237 235 ((-1), (2)), some 25, none⟩
]

def backwardK : List (Row 997) := [
  ⟨10903, .relabel 0 6 14, none, some (253, 1)⟩,
  ⟨10904, .relabel 27 9 14, none, some (262, 1)⟩,
  ⟨10905, .add 27 0 ((-1), (1)), some 14, none⟩,
  ⟨10906, .add 0 27 ((1), (2)), some 14, none⟩,
  ⟨10907, .relabel 224 6 15, none, some (254, 1)⟩,
  ⟨10908, .relabel 57 11 15, none, some (268, 1)⟩,
  ⟨10909, .add 57 224 ((-1), (1)), some 15, none⟩,
  ⟨10910, .add 224 57 ((1), (2)), some 15, none⟩,
  ⟨10911, .relabel 225 6 16, none, some (255, 1)⟩,
  ⟨10912, .relabel 7 12 16, none, some (271, 1)⟩,
  ⟨10913, .add 7 225 ((-1), (1)), some 16, none⟩,
  ⟨10914, .add 225 7 ((1), (2)), some 16, none⟩,
  ⟨10915, .relabel 76 7 17, none, some (256, 1)⟩,
  ⟨10916, .relabel 87 8 17, none, some (259, 1)⟩,
  ⟨10917, .add 87 76 ((-1), (1)), some 17, none⟩,
  ⟨10918, .add 76 87 ((1), (2)), some 17, none⟩,
  ⟨10919, .relabel 226 7 18, none, some (257, 1)⟩,
  ⟨10920, .relabel 92 10 18, none, some (265, 1)⟩,
  ⟨10921, .add 92 226 ((-1), (1)), some 18, none⟩,
  ⟨10922, .add 226 92 ((1), (2)), some 18, none⟩,
  ⟨10923, .relabel 227 7 19, none, some (258, 1)⟩,
  ⟨10924, .relabel 81 13 19, none, some (274, 1)⟩,
  ⟨10925, .add 81 227 ((-1), (1)), some 19, none⟩,
  ⟨10926, .add 227 81 ((1), (2)), some 19, none⟩
]

def backwardL : List (Row 997) := [
  ⟨10927, .relabel 228 8 20, none, some (260, 1)⟩,
  ⟨10928, .relabel 232 10 20, none, some (266, 1)⟩,
  ⟨10929, .add 232 228 ((-1), (1)), some 20, none⟩,
  ⟨10930, .add 228 232 ((1), (2)), some 20, none⟩,
  ⟨10931, .relabel 229 8 21, none, some (261, 1)⟩,
  ⟨10932, .relabel 238 13 21, none, some (275, 1)⟩,
  ⟨10933, .add 238 229 ((-1), (1)), some 21, none⟩,
  ⟨10934, .add 229 238 ((1), (2)), some 21, none⟩,
  ⟨10935, .relabel 230 9 22, none, some (263, 1)⟩,
  ⟨10936, .relabel 234 11 22, none, some (269, 1)⟩,
  ⟨10937, .add 234 230 ((-1), (1)), some 22, none⟩,
  ⟨10938, .add 230 234 ((1), (2)), some 22, none⟩,
  ⟨10939, .relabel 231 9 23, none, some (264, 1)⟩,
  ⟨10940, .relabel 236 12 23, none, some (272, 1)⟩,
  ⟨10941, .add 236 231 ((-1), (1)), some 23, none⟩,
  ⟨10942, .add 231 236 ((1), (2)), some 23, none⟩,
  ⟨10943, .relabel 233 10 24, none, some (267, 1)⟩,
  ⟨10944, .relabel 239 13 24, none, some (276, 1)⟩,
  ⟨10945, .add 239 233 ((-1), (1)), some 24, none⟩,
  ⟨10946, .add 233 239 ((1), (2)), some 24, none⟩,
  ⟨10947, .relabel 235 11 25, none, some (270, 1)⟩,
  ⟨10948, .relabel 237 12 25, none, some (273, 1)⟩,
  ⟨10949, .add 237 235 ((-1), (1)), some 25, none⟩,
  ⟨10950, .add 235 237 ((1), (2)), some 25, none⟩
]

def support236 : List Register := [0, 27, 224, 57, 225, 7, 76, 87, 226, 92, 227, 81]
def values236 (r : Register) : FrameLabel 997 :=
  match r.val with
  | 0 => 14
  | 27 => 14
  | 224 => 15
  | 57 => 15
  | 225 => 16
  | 7 => 16
  | 76 => 17
  | 87 => 17
  | 226 => 18
  | 92 => 18
  | 227 => 19
  | 81 => 19
  | _ => 0
def labels236 (r : Register) : FrameLabel 997 :=
  if r ∈ support236 then values236 r else Current535EntranceBandData.labels212 r
def support260 : List Register := [228, 232, 229, 238, 230, 234, 231, 236, 233, 239, 235, 237]
def values260 (r : Register) : FrameLabel 997 :=
  match r.val with
  | 228 => 20
  | 232 => 20
  | 229 => 21
  | 238 => 21
  | 230 => 22
  | 234 => 22
  | 231 => 23
  | 236 => 23
  | 233 => 24
  | 239 => 24
  | 235 => 25
  | 237 => 25
  | _ => 0
def labels260 (r : Register) : FrameLabel 997 :=
  if r ∈ support260 then values260 r else labels236 r
end CurrentMain.Current535NonzeroBandData
