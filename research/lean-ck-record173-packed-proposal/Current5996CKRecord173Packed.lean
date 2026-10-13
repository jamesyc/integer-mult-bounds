import PR593ExactHelpers

/-!
Historical selected5996 CK child173: frame3=[42] to frame4=[75,42], rank1.
Frozen literal certificate proposal only; no current7ee selection is inferred.
Source paths, exact fields and lineage are recorded in SOURCE_BINDING.json.
Apache-2.0; prepared with OpenAI assistance. PR593 helpers/check theorem retain
Jeremy Kothe / Claude Opus5.5 (Anthropic) attribution. See NOTICE.md.
-/
set_option Elab.async false

namespace CurrentMain.Current5996CKRecord173Packed
open HyperplaneEnd.Clifford HyperplaneEnd.Exact

def oldDescriptor : List Nat := [42]
def newDescriptor : List Nat := [75, 42]

def leftMono : Mono :=
  ⟨[1, 0, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0, 0], [3, 5, 8, 17, 32, 64, 1, 128, 256], 0, 0⟩

def rightMono : Mono :=
  ⟨[75, 75, 0, 75, 0, 0, 11, 0, 0], [1, 1, 0, 1, 0, 0, 2, 0, 0], [11, 65, 66, 4, 72, 16, 32, 128, 256], 0, 0⟩

def fOld : List Gate := [
  .dg [0, 32, 0, 32, 0, 10, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0, 0],
  .pm [32, 1, 34, 4, 40, 16, 64, 128, 256] [2, 5, 8, 17, 32, 1, 64, 128, 256],
  .cg 1 true,
  .pm [2, 5, 8, 17, 32, 1, 64, 128, 256] [32, 1, 34, 4, 40, 16, 64, 128, 256],
  .dg [0, 32, 0, 32, 0, 10, 0, 0, 0] [0, 0, 0, 0, 0, 0, 0, 0, 0]
]

def fNew : List Gate := [
  .dg [64, 96, 0, 96, 0, 10, 75, 0, 0] [0, 0, 0, 0, 0, 0, 3, 0, 0],
  .pm [64, 32, 65, 98, 4, 104, 16, 128, 256] [5, 11, 16, 35, 64, 2, 1, 128, 256],
  .cg 1 true,
  .cg 2 true,
  .pm [5, 11, 16, 35, 64, 2, 1, 128, 256] [64, 32, 65, 98, 4, 104, 16, 128, 256],
  .dg [64, 96, 0, 96, 0, 10, 75, 0, 0] [0, 0, 0, 0, 0, 0, 1, 0, 0]
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

/-- The original gate predicate certifies both inverse reads and every adjoint. -/
theorem gate_validity :
    cOk 512 fOld = true ∧ cOk 512 fNew = true ∧
    cOk 512 wL = true ∧ cOk 512 wR = true := by
  decide +kernel

/-- Canonical circuit first: three Gaussian gates versus one in the child recipe. -/
theorem exact_packed_check : check lhs rhs = true := by
  decide +kernel

/-- Full complex payload equality follows from the accepted packed-check theorem. -/
theorem packed_child (v : Fin 512 → ℂ) :
    cL 512 rhs v =
      (cE fNew gate_validity.2.1) ((cE fOld gate_validity.1).symm v) := by
  have h := LinearMap.congr_fun (cL_eq_of_check lhs rhs exact_packed_check) v
  simpa only [lhs, cL_append_apply, cE_apply, cE_symm_apply] using h.symm

end CurrentMain.Current5996CKRecord173Packed

#print axioms CurrentMain.Current5996CKRecord173Packed.literal_binding
#print axioms CurrentMain.Current5996CKRecord173Packed.gate_validity
#print axioms CurrentMain.Current5996CKRecord173Packed.exact_packed_check
#print axioms CurrentMain.Current5996CKRecord173Packed.packed_child
