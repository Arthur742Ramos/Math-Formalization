/- AI-assisted formalization under the repository Apache-2.0 license.
Source-only draft. Supplied-cover execution on original rational Fin n labels.
The computed index table, Gaussian vector/graph-flow pair, and final original
weight/matrix tables are bound as data. No cost or sort-sharing theorem. -/
module
public import ExecutableCoverWitness
public import RationalGaussianPaperFlow
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCoverCore {n k m : ℕ} (table : CoverIndexTable n k m)
    (A : Fin n → Fin n → ℚ) : Fin k → Fin k → ℚ :=
  fun a b => A (coverTableDecode table (.inl a)) (coverTableDecode table (.inl b))

def rationalCoverCross {n k m : ℕ} (table : CoverIndexTable n k m)
    (A : Fin n → Fin n → ℚ) : Fin m → Fin k → ℚ :=
  fun i a => A (coverTableDecode table (.inr i)) (coverTableDecode table (.inl a))

def rationalCoverResidual {n k m : ℕ} (table : CoverIndexTable n k m)
    (A : Fin n → Fin n → ℚ) : Fin m → Fin m → ℚ :=
  fun i j => A (coverTableDecode table (.inr i)) (coverTableDecode table (.inr j))

def rationalCoverAnchors {n k m : ℕ} (table : CoverIndexTable n k m)
    (x : Fin n → ℚ) : Fin k → ℚ := fun a => x (coverTableDecode table (.inl a))

def rationalCoverWeights {n k m : ℕ} (table : CoverIndexTable n k m)
    (x : Fin n → ℚ) : Fin m → ℚ := fun i => x (coverTableDecode table (.inr i))

def rationalCoverExtras {n k m d : ℕ} (table : CoverIndexTable n k m)
    (E : Fin d → Fin n → ℚ) : Fin d → Fin m → ℚ :=
  fun g i => E g (coverTableDecode table (.inr i))

def rationalCoverBlock {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (D : Fin m → Fin k → ℚ) (B : Fin m → Fin m → ℚ) :
    (Fin k ⊕ Fin m) → (Fin k ⊕ Fin m) → ℚ
  | .inl a, .inl b => K a b
  | .inl a, .inr j => -D j a
  | .inr i, .inl a => D i a
  | .inr i, .inr j => B i j

def rationalCoverAssemble {n k m : ℕ} (table : CoverIndexTable n k m)
    (A : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (pair : Gaussian.QVec m × RationalFlowTable m) : Gaussian.QVec n × Gaussian.QTable n n :=
  let p := rationalCoverAnchors table x
  let K := rationalCoverCore table A
  let D := rationalCoverCross table A
  let B := rationalFlowTableEntry pair.2
  let code := coverTableEncode table
  (List.Vector.ofFn (fun v => Sum.elim p pair.1.get (code v)),
    Gaussian.tableOfFn (fun u v => rationalCoverBlock K D B (code u) (code v)))

def rationalCoveredGaussianGeneral {n d : ℕ} (C : Finset (Fin n))
    (A : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (M ρ η : ℚ) : Gaussian.QVec n × Gaussian.QTable n n :=
  let table := coverIndexTable C
  let D := rationalCoverCross table A
  let p := rationalCoverAnchors table x
  let q := rationalCoverWeights table x
  let E' := rationalCoverExtras table E
  let r := ∑ i, q i
  let pair := rationalGaussianPaperGeneralFlow D E' p q M r ρ η
  rationalCoverAssemble table A x pair

/-- One actual exact program covers positive and zero residual mass. The
existing exact-zero theorem proves the H-1 branch sound at zero mass. -/
def rationalCoveredGaussianExact {n d : ℕ} (C : Finset (Fin n))
    (A : Fin n → Fin n → ℚ) (E : Fin d → Fin n → ℚ) (x : Fin n → ℚ)
    (M η : ℚ) : Gaussian.QVec n × Gaussian.QTable n n :=
  let table := coverIndexTable C
  let D := rationalCoverCross table A
  let p := rationalCoverAnchors table x
  let q := rationalCoverWeights table x
  let E' := rationalCoverExtras table E
  let r := ∑ i, q i
  let pair := rationalGaussianPaperExactFlow D E' p q M r η
  rationalCoverAssemble table A x pair

theorem rational_cover_block_real {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (D : Fin m → Fin k → ℚ) (B : Fin m → Fin m → ℚ)
    (a b : Fin k ⊕ Fin m) :
    (rationalCoverBlock K D B a b : ℝ)=blockMatrix
      (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ)) (fun i j => (B i j : ℝ)) a b := by
  cases a <;> cases b <;> simp only [rationalCoverBlock, blockMatrix, Rat.cast_neg]

theorem rational_cover_assemble_weights {n k m : ℕ} (table : CoverIndexTable n k m)
    (A : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (pair : Gaussian.QVec m × RationalFlowTable m) (v : Fin n) :
    (rationalCoverAssemble table A x pair).1.get v=
      Sum.elim (rationalCoverAnchors table x) pair.1.get (coverTableEncode table v) := by
  simp only [rationalCoverAssemble, List.Vector.get_ofFn]

theorem rational_cover_assemble_matrix {n k m : ℕ} (table : CoverIndexTable n k m)
    (A : Fin n → Fin n → ℚ) (x : Fin n → ℚ)
    (pair : Gaussian.QVec m × RationalFlowTable m) (u v : Fin n) :
    Gaussian.entry (rationalCoverAssemble table A x pair).2 u v=
      rationalCoverBlock (rationalCoverCore table A) (rationalCoverCross table A)
        (rationalFlowTableEntry pair.2) (coverTableEncode table u) (coverTableEncode table v) := by
  simp only [rationalCoverAssemble, Gaussian.entry_tableOfFn]

end SparseCompletion
