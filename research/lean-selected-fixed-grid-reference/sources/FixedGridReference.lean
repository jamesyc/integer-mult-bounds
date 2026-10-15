import Current1094Rows12PrefixBitBudget

/-!
One fixed-denominator integer interpreter for the already accepted reference
instruction type. Initial scaling is the explicit mathematical encoding
z * 2^(Q-p). This is not a paid encoding or physical bit-machine theorem.

The post-step raw exponent bound supplies exact parity before integer HALVE.
Consequently every prefix is represented at the same denominator, without
runtime exponent alignment or rounding. The selected two-row instance reuses
the accepted n-independent bound Q=P+1, including visible dirty scratch.

Outside the finite bounded footprint, the encoding is only a mathematical
integer projection; no real decoding claim is made for out-of-grid cells.
The raw Cell interpreter, its noncanonical pairs and all physical invoices
remain unchanged. PR2284 supplies generic recursive reserve arithmetic; this
module proves the distinct instruction refinement, not another depth bound.
No word overflow, initial layout, tape cost, selected whole-stage schedule or
uniform C is supplied. James Chang, OpenAI-assisted, Apache-2.0.
Author-checked contextual kappa = 836330098538459/500000000000000000.
-/
set_option Elab.async false
set_option autoImplicit false
namespace CurrentMain.FixedGridReference
open Current1094Row1DyadicReference DyadicCellAddition Current1094Row2DyadicReference
open Current1094Rows12DyadicReference Current1094Rows12PrefixBitBudget
open Current1094Row2AddReference (selectedTargetFamily selectedSourceFamily)
abbrev Instruction := Current1094Row2AddReference.Instruction

structure State where
  memory : Nat → Int
  accumulator : Int

def encode (Q : Nat) (s : EncodedState) : State :=
  ⟨fun a => alignedNumerator Q (s.memory a), alignedNumerator Q s.accumulator⟩

/-- Executable unbounded integer semantics; no exponent field is read. -/
def step : Instruction → State → State
  | .core (.read a), s => ⟨s.memory, s.memory a⟩
  | .core (.write a), s => ⟨Function.update s.memory a s.accumulator, s.accumulator⟩
  | .core .negate, s => ⟨s.memory, -s.accumulator⟩
  | .core .halve, s => ⟨s.memory, s.accumulator / 2⟩
  | .addMemory a, s => ⟨s.memory, s.memory a + s.accumulator⟩

def run : List Instruction → State → State
  | [], s => s
  | op :: ops, s => run ops (step op s)

/-- The successor exponent bound means the current integer has a low zero bit. -/
theorem half_factor (Q : Nat) (c : Cell) (h : c.fractionalBits + 1 ≤ Q) :
    alignedNumerator Q c = alignedNumerator Q (halfCell c) * 2 := by
  have e : Q-c.fractionalBits = (Q-(c.fractionalBits+1))+1 := by omega
  change c.numerator * (2 : Int)^(Q-c.fractionalBits) =
    (c.numerator * (2 : Int)^(Q-(c.fractionalBits+1))) * 2
  rw [e, pow_succ, mul_assoc]

theorem half_even (Q : Nat) (c : Cell) (h : c.fractionalBits + 1 ≤ Q) :
    (2 : Int) ∣ alignedNumerator Q c := by
  exact ⟨alignedNumerator Q (halfCell c), by rw [half_factor Q c h, mul_comm]⟩

theorem half_exact (Q : Nat) (c : Cell) (h : c.fractionalBits + 1 ≤ Q) :
    alignedNumerator Q c / 2 = alignedNumerator Q (halfCell c) := by
  rw [half_factor Q c h]
  exact Int.mul_ediv_cancel _ (by decide)

/-- Aligned addition becomes literal integer addition at the fixed grid. -/
theorem add_exact (Q : Nat) (a b : Cell)
    (ha : a.fractionalBits ≤ Q) (hb : b.fractionalBits ≤ Q) :
    alignedNumerator Q (addCell a b) = alignedNumerator Q a + alignedNumerator Q b := by
  let q := commonExponent a b
  have hq : q ≤ Q := max_le ha hb
  have hqa : a.fractionalBits ≤ q := le_max_left _ _
  have hqb : b.fractionalBits ≤ q := le_max_right _ _
  have ea : (q-a.fractionalBits)+(Q-q)=Q-a.fractionalBits := by omega
  have eb : (q-b.fractionalBits)+(Q-q)=Q-b.fractionalBits := by omega
  change (a.numerator * (2 : Int)^(q-a.fractionalBits) +
    b.numerator * (2 : Int)^(q-b.fractionalBits)) * (2 : Int)^(Q-q) =
    a.numerator * (2 : Int)^(Q-a.fractionalBits) + b.numerator * (2 : Int)^(Q-b.fractionalBits)
  rw [add_mul, mul_assoc, mul_assoc, ← pow_add, ← pow_add, ea, eb]

/-- A local post-step bound is enough for all five integer instructions. -/
theorem step_encode (Q : Nat) (op : Instruction) (s : EncodedState)
    (h : (stepAdd op s).accumulator.fractionalBits ≤ Q) :
    step op (encode Q s) = encode Q (stepAdd op s) := by
  cases op with
  | core op => cases op with
    | read a => rfl
    | write a =>
        change (⟨Function.update (fun j => alignedNumerator Q (s.memory j)) a
          (alignedNumerator Q s.accumulator), alignedNumerator Q s.accumulator⟩ : State) =
          ⟨fun j => alignedNumerator Q (Function.update s.memory a s.accumulator j),
            alignedNumerator Q s.accumulator⟩
        apply congrArg (fun m : Nat → Int => (⟨m, alignedNumerator Q s.accumulator⟩ : State))
        exact (Function.comp_update (alignedNumerator Q) s.memory a s.accumulator).symm
    | negate => simp only [step, encode, stepAdd, Current1094Row1DyadicReference.step,
        alignedNumerator, negCell, neg_mul]
    | halve =>
        change s.accumulator.fractionalBits+1 ≤ Q at h
        change (⟨fun a => alignedNumerator Q (s.memory a), alignedNumerator Q s.accumulator / 2⟩ : State) =
          ⟨fun a => alignedNumerator Q (s.memory a), alignedNumerator Q (halfCell s.accumulator)⟩
        rw [half_exact Q s.accumulator h]
  | addMemory a =>
      change max (s.memory a).fractionalBits s.accumulator.fractionalBits ≤ Q at h
      change (⟨fun j => alignedNumerator Q (s.memory j),
        alignedNumerator Q (s.memory a) + alignedNumerator Q s.accumulator⟩ : State) =
        ⟨fun j => alignedNumerator Q (s.memory j), alignedNumerator Q (addCell (s.memory a) s.accumulator)⟩
      rw [add_exact Q _ _ ((le_max_left _ _).trans h) ((le_max_right _ _).trans h)]

/-- Generic finite-prefix refinement, supplied by existing raw exponent bounds. -/
theorem run_encode (Q : Nat) (ops : List Instruction) (s : EncodedState)
    (h : ∀ k, (runAdd (ops.take k) s).accumulator.fractionalBits ≤ Q) :
    run ops (encode Q s) = encode Q (runAdd ops s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      have hs : (stepAdd op s).accumulator.fractionalBits ≤ Q := by
        simpa only [List.take_succ_cons, List.take_zero, runAdd] using h 1
      rw [run, runAdd, step_encode Q op s hs]
      apply ih
      intro k
      simpa only [List.take_succ_cons, runAdd] using h (k+1)

/-- The initial projection decodes exactly on the explicitly bounded domain. -/
theorem encode_value (Q : Nat) (c : Cell) (h : c.fractionalBits ≤ Q) :
    (alignedNumerator Q c : Real) / (2 : Real)^Q = value c := aligned_value Q c h

/-- Existing selected no-repeat/disjoint traversal precision fixes Q=P+1. -/
theorem selected_prefix (n b P : Nat) (s : EncodedState)
    (h : StateBudget (footprint n selectedTargetFamily selectedSourceFamily) b P s) (k : Nat) :
    run ((selectedRows12Program n).take k) (encode (P+1) s) =
      encode (P+1) (runAdd ((selectedRows12Program n).take k) s) := by
  apply run_encode
  intro j
  simpa only [List.take_take] using
    (selected_all_prefixes n b P s h (min j k)).2.2

/-- Both active memory and visible scratch have the unchanged exact value. -/
theorem selected_prefix_values (n b P : Nat) (s : EncodedState)
    (h : StateBudget (footprint n selectedTargetFamily selectedSourceFamily) b P s) (k : Nat) :
    (∀ a ∈ footprint n selectedTargetFamily selectedSourceFamily,
      ((run ((selectedRows12Program n).take k) (encode (P+1) s)).memory a : Real) /
        (2 : Real)^(P+1) = value ((runAdd ((selectedRows12Program n).take k) s).memory a)) ∧
    ((run ((selectedRows12Program n).take k) (encode (P+1) s)).accumulator : Real) /
      (2 : Real)^(P+1) = value (runAdd ((selectedRows12Program n).take k) s).accumulator := by
  rw [selected_prefix n b P s h k]
  have hb := selected_all_prefixes n b P s h k
  exact ⟨fun a ha => aligned_value (P+1) _ (hb.1 a ha).2,
    aligned_value (P+1) _ hb.2.2⟩

end CurrentMain.FixedGridReference
#print axioms CurrentMain.FixedGridReference.half_factor
#print axioms CurrentMain.FixedGridReference.half_even
#print axioms CurrentMain.FixedGridReference.half_exact
#print axioms CurrentMain.FixedGridReference.add_exact
#print axioms CurrentMain.FixedGridReference.step_encode
#print axioms CurrentMain.FixedGridReference.run_encode
#print axioms CurrentMain.FixedGridReference.selected_prefix
#print axioms CurrentMain.FixedGridReference.selected_prefix_values
#check @CurrentMain.FixedGridReference.step_encode
#check @CurrentMain.FixedGridReference.selected_prefix_values
