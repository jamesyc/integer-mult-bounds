import PR593ExactHelpers

/-!
Source-only resource redesign of the preserved current799 record3 allocation failure.
Exact source data and conventions are unchanged; see the original frozen source
binding and the redesign proposal. Apache-2.0; prepared with OpenAI assistance.
PR593 helpers and generic soundness retain their original attribution.
-/
set_option Elab.async false

namespace CurrentMain.Current799Record3Packed
open HyperplaneEnd.Clifford HyperplaneEnd.Exact

def oldDescriptor : List Nat := []
def newDescriptor : List Nat := [75]

def leftMono : Mono :=
  ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0], [3, 5, 8, 17, 32, 64, 1, 128, 256], 0, 0⟩

def rightMono : Mono :=
  ⟨[75, 75, 0, 75, 0, 0, 11, 0, 0], [1, 1, 0, 1, 0, 0, 2, 0, 0], [11, 65, 66, 4, 72, 16, 32, 128, 256], 0, 0⟩

def fOld : List Gate := []

def fNew : List Gate := [
  .dg [64, 64, 0, 64, 0, 0, 75, 0, 0] [0, 0, 0, 0, 0, 0, 3, 0, 0],
  .pm [64, 65, 66, 4, 72, 16, 32, 128, 256] [3, 5, 8, 17, 32, 64, 1, 128, 256],
  .cg 1 true,
  .pm [3, 5, 8, 17, 32, 64, 1, 128, 256] [64, 65, 66, 4, 72, 16, 32, 128, 256],
  .dg [64, 64, 0, 64, 0, 0, 75, 0, 0] [0, 0, 0, 0, 0, 0, 1, 0, 0]
]

def wL : List Gate := [
  .dg [1, 0, 0, 0, 0, 0, 0, 0, 0] [3, 0, 0, 0, 0, 0, 0, 0, 0],
  .pm [3, 5, 8, 17, 32, 64, 1, 128, 256] [64, 65, 66, 4, 72, 16, 32, 128, 256],
  .xg 0,
  .ph 0
]

def wR : List Gate := [
  .dg [75, 75, 0, 75, 0, 0, 11, 0, 0] [1, 1, 0, 1, 0, 0, 2, 0, 0],
  .pm [11, 65, 66, 4, 72, 16, 32, 128, 256] [21, 19, 8, 7, 32, 64, 23, 128, 256],
  .xg 0,
  .ph 0
]

def lhs : List Gate := adjC fOld ++ fNew
def rhs : List Gate := wR ++ [.cg 1 true] ++ wL

/-- Evaluate the source helper once into frozen literals, before any address check. -/
theorem literal_binding :
    canon 9 oldDescriptor = fOld ∧ canon 9 newDescriptor = fNew ∧
    leftMono.gates = wL ∧ rightMono.gates = wR := by
  decide +kernel

end CurrentMain.Current799Record3Packed

#print axioms CurrentMain.Current799Record3Packed.literal_binding
