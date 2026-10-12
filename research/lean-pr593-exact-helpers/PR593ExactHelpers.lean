import PR593Clifford

/-!
Exact pure helper slice from PR593, HyperplaneEnd/Exact.lean, lines 29–96,
head fdb6dcc6d7bc29764c5b6b4d32b7fa050acf74a4. See SOURCE_SLICE.json.
Apache-2.0. Original source by Jeremy Kothe, prepared with Claude Opus 5.5
(Anthropic) in omp. Slice packaging prepared with OpenAI assistance.

Only the source definitions are reused here. No selected certificate, validity,
Python-loop correspondence, physical execution or endpoint theorem is asserted.
The original fuel-64 fallback behavior and all phase conventions are unchanged.
-/

namespace HyperplaneEnd.Exact
open HyperplaneEnd.Clifford

/-- `transpose(rows, n)`, column `i`. -/
def colBits (i : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, w => (if (r >>> i) % 2 = 1 then w else 0) + colBits i rs (2 * w)

def transpose (rows : List ℕ) (n : ℕ) : List ℕ := (List.range n).map fun i => colBits i rows 1

/-- `x.bit_length() - 1` for `0 < x < 2 ^ 64`. -/
def lead : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => if x < 2 then 0 else lead f (x / 2) + 1

/-- One step of `rank`: insert `x` into the pivot table (leading bit ↦ row). -/
def insPiv : ℕ → List (ℕ × ℕ) → ℕ → List (ℕ × ℕ)
  | 0, p, _ => p
  | f + 1, p, x =>
    if x = 0 then p else
    match p.lookup (lead 64 x) with
    | none => (lead 64 x, x) :: p
    | some r => insPiv f p (x ^^^ r)

def rank (rows : List ℕ) : ℕ := (rows.foldl (insPiv 64) []).length

def basisExtend (cols : List ℕ) (n : ℕ) : List ℕ :=
  (cols ++ (List.range n).map (2 ^ ·)).foldl
    (fun out x => if rank (out ++ [x]) > out.length then out ++ [x] else out) []

/-- `inv(rows, n)`: Gauss–Jordan over `F₂` (the result is certified by `Gate.ok`). -/
def invRows (n : ℕ) (rows : List ℕ) : List ℕ :=
  let a0 := (List.range n).map fun i => rows.getD i 0 ||| (2 ^ (n + i))
  let a := (List.range n).foldl (fun a j =>
    match (List.range n).find? (fun i => decide (j ≤ i) && (a.getD i 0 >>> j) % 2 == 1) with
    | none => a
    | some k =>
      let a := (a.set j (a.getD k 0)).set k (a.getD j 0)
      let pj := a.getD j 0
      (List.range n).map fun i =>
        let ai := a.getD i 0
        if i ≠ j ∧ (ai >>> j) % 2 = 1 then ai ^^^ pj else ai) a0
  a.map (· >>> n)

/-- `fourier(n, range(r))`. -/
def fourierC (r : ℕ) : List Gate := (List.range r).map fun i => .cg (2 ^ i) true

/-- `canonical_frame(n, U)`: `K⁻¹ · fourier(r) · K` with `K = perm(G) then diag(Q)`. -/
def canon (n : ℕ) (U : List ℕ) : List Gate :=
  let r := U.length
  if r = 0 then [] else if r = n then fourierC n else
  let G := transpose (basisExtend U n) n
  let Gi := invRows n G
  let gt := transpose Gi n
  let Q := (List.range n).map fun i =>
    2 ^ i ^^^ ((List.range n).map fun j => if par9 (gt.getD i 0 &&& gt.getD j 0) then 2 ^ j else 0).sum
  let α := (List.range n).map fun i => (Q.getD i 0 >>> i) % 2
  let K := [Gate.pm G Gi, Gate.dg Q α]
  adjC K ++ fourierC r ++ K

/-- A serialized wrapper monomial: `quadratic_rows`, `linear_Z4`, `matrix_rows`, `offset`, `phase`. -/
structure Mono where
  Q : List ℕ
  α : List ℕ
  G : List ℕ
  b : ℕ
  p : ℕ
  deriving DecidableEq

/-- `monomial_op(rec)`: `diag(Q, α)`, then `perm(G)`, then `X(offset)`, then the phase. -/
def Mono.gates (r : Mono) : List Gate := [.dg r.Q r.α, .pm r.G (invRows 9 r.G), .xg r.b, .ph r.p]

end HyperplaneEnd.Exact

#print axioms HyperplaneEnd.Exact.invRows
#print axioms HyperplaneEnd.Exact.fourierC
#print axioms HyperplaneEnd.Exact.canon
#print axioms HyperplaneEnd.Exact.Mono.gates

#check (HyperplaneEnd.Exact.canon : Nat → List Nat → List HyperplaneEnd.Clifford.Gate)
#check (HyperplaneEnd.Exact.invRows : Nat → List Nat → List Nat)
#check (HyperplaneEnd.Exact.Mono.gates : HyperplaneEnd.Exact.Mono → List HyperplaneEnd.Clifford.Gate)
