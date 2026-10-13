import PR593ExactHelpers

/-!
Exact selected PR799 child3: frame0=[] to frame5=[75], rank1.
Frozen literal certificate proposal; all-payload equality awaits a kernel check.
Source paths, exact fields and lineage are recorded in SOURCE_BINDING.json.
Apache-2.0; prepared with OpenAI assistance. PR593 helpers/check theorem retain
Jeremy Kothe / Claude Opus5.5 (Anthropic) attribution. See NOTICE.md.
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

/-- The original gate predicate certifies both inverse reads and every adjoint. -/
theorem gate_validity :
    cOk 512 fOld = true ∧ cOk 512 fNew = true ∧
    cOk 512 wL = true ∧ cOk 512 wR = true := by
  decide +kernel

/-- Canonical circuit first: one Gaussian gate in each circuit, exact radix16 and scale1. -/
theorem exact_packed_check : check lhs rhs = true := by
  decide +kernel

/-- Full complex payload equality follows from the accepted packed-check theorem. -/
theorem packed_child (v : Fin 512 → ℂ) :
    cL 512 rhs v =
      (cE fNew gate_validity.2.1) ((cE fOld gate_validity.1).symm v) := by
  have h := LinearMap.congr_fun (cL_eq_of_check lhs rhs exact_packed_check) v
  simpa only [lhs, cL_append_apply, cE_apply, cE_symm_apply] using h.symm

end CurrentMain.Current799Record3Packed

#print axioms CurrentMain.Current799Record3Packed.literal_binding
#print axioms CurrentMain.Current799Record3Packed.gate_validity
#print axioms CurrentMain.Current799Record3Packed.exact_packed_check
#print axioms CurrentMain.Current799Record3Packed.packed_child
