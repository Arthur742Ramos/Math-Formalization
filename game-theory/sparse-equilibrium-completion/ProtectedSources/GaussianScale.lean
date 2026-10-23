/- AI-assisted Gaussian global-height continuation; Apache-2.0.
Exact check status is recorded in source-bound receipts outside this source.
The original uncompiled v1 draft is preserved in source-global-height-v1.
Frozen Gaussian kernel APIs are unchanged. No bit-cost or general LP claim.
-/
module
public import ProtectedSources.IntegerMinorHeight
@[expose] public section
open scoped BigOperators
namespace SparseCompletion.Gaussian

def scaleTable {r n : ℕ} (c : ℚ) (A : QTable r n) : QTable r n :=
  tableOfFn (fun i j => c * entry A i j)

@[simp] theorem entry_scaleTable {r n : ℕ} (c : ℚ) (A : QTable r n) :
    entry (scaleTable c A) = fun i j => c * entry A i j := by
  funext i j
  simp [scaleTable]

theorem firstNonzero_scale (r : ℕ) (c : ℚ) (hc : c ≠ 0)
    (a : Fin r → ℚ) :
    firstNonzero r (fun i => c * a i) = firstNonzero r a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    by_cases ha : a 0 = 0
    · simp [firstNonzero, ha, ih]
    · have hca : c * a 0 ≠ 0 := mul_ne_zero hc ha
      simp [firstNonzero, ha, hca]

/-- The cancellation law also covers a zero denominator; rational division is
total. Thus scalar invariance does not need to assume a whole stage has rank. -/
theorem residual_scale {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ)
    (p : Fin r) (c : ℚ) (hc : c ≠ 0) :
    residual (fun i j => c * A i j) p = fun i j => c * residual A p i j := by
  funext i j
  simp only [residual, mul_div_mul_left _ _ hc]
  ring

theorem lift_scale {r n : ℕ} (A : Fin r → Fin (n+1) → ℚ)
    (p : Fin r) (w : Fin n → ℚ) (c : ℚ) (hc : c ≠ 0) :
    lift (fun i j => c * A i j) p w = lift A p w := by
  simp only [lift, mul_div_mul_left _ _ hc]

theorem residual_scaleTable {r n : ℕ} (A : QTable r (n+1))
    (p : Fin r) (c : ℚ) (hc : c ≠ 0) :
    tableOfFn (residual (entry (scaleTable c A)) p) =
      scaleTable c (tableOfFn (residual (entry A) p)) := by
  apply List.Vector.ext
  intro i
  apply List.Vector.ext
  intro j
  change entry (tableOfFn (residual (entry (scaleTable c A)) p)) i j =
    entry (scaleTable c (tableOfFn (residual (entry A) p))) i j
  simp only [entry_tableOfFn, entry_scaleTable]
  rw [residual_scale _ _ c hc]

/-- Equality of actual returned Option/vector data, not merely equality of
their homogeneous solution sets. No minor/rank witness is accepted as input. -/
theorem kernel_scaleTable (r n : ℕ) (A : QTable r n)
    (c : ℚ) (hc : c ≠ 0) :
    kernel r n (scaleTable c A) = kernel r n A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : firstNonzero r (fun i => entry (scaleTable c A) i 0) =
        firstNonzero r (fun i => entry A i 0) := by
      simpa only [entry_scaleTable] using
        firstNonzero_scale r c hc (fun i => entry A i 0)
    cases he : firstNonzero r (fun i => entry A i 0) with
    | none => simp only [kernel, hp, he]
    | some p =>
      simp only [kernel, hp, he]
      rw [residual_scaleTable A p c hc, ih]
      congr 1
      funext w
      rw [entry_scaleTable, lift_scale _ p w.get c hc]

def integerNumeratorTable {r n : ℕ} (A : QTable r n) : QTable r n :=
  tableOfFn (fun i j => (Matrix.num (entry A) i j : ℚ))

theorem integerNumeratorTable_eq_scale {r n : ℕ} (A : QTable r n) :
    integerNumeratorTable A = scaleTable (Matrix.den (entry A) : ℚ) A := by
  apply List.Vector.ext
  intro i
  apply List.Vector.ext
  intro j
  simp only [integerNumeratorTable, scaleTable, tableOfFn, List.Vector.get_ofFn]
  have hD : (Matrix.den (entry A) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Matrix.den_ne_zero (entry A))
  have h := (div_eq_iff hD).mp (Matrix.num_div_den (entry A) i j)
  simpa only [mul_comm] using h

/-- Clearing denominators changes neither success/failure nor any normalized
coefficient returned by the existing deterministic Gaussian kernel. This is
the missing execution bridge beyond equality of homogeneous predicates. -/
theorem kernel_integerNumeratorTable (r n : ℕ) (A : QTable r n) :
    kernel r n (integerNumeratorTable A) = kernel r n A := by
  rw [integerNumeratorTable_eq_scale]
  exact kernel_scaleTable r n A _ (Nat.cast_ne_zero.mpr (Matrix.den_ne_zero (entry A)))

end SparseCompletion.Gaussian
