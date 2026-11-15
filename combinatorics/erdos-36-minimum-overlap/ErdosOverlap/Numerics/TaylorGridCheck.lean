module

public import ErdosOverlap.Numerics.TaylorUniform

/-! Bounded, row-oriented checking of all coefficients of a Taylor polynomial. -/

namespace ErdosOverlap.Numerics

@[expose] public section

def coefficientListCheck (factors : ℕ → List ℤ) (row : List (ℤ × ℤ)) (j : ℕ) :
    ℕ → List ℤ → Bool
  | _, [] => true
  | k, p :: ps => coefficientCheck (factors k) row j k p &&
      coefficientListCheck factors row j (k+1) ps

theorem coefficientListCheck_sound {factors : ℕ → List ℤ} {row : List (ℤ × ℤ)}
    {j start : ℕ} {ps : List ℤ}
    (h : coefficientListCheck factors row j start ps = true) {k : ℕ}
    (hk : k < ps.length) :
    coefficientCheck (factors (start+k)) row j (start+k) (ps.getD k 0) = true := by
  induction ps generalizing start k with
  | nil => simp at hk
  | cons p ps ih =>
    simp only [coefficientListCheck, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have hh := ih h.2 (k := k) (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def completeCoefficientRowCheck (factors : ℕ → List ℤ) (row : List (ℤ × ℤ))
    (j : ℕ) (ps : List ℤ) : Bool :=
  decide (ps.length = 20) && coefficientListCheck factors row j 0 ps

theorem completeCoefficientRowCheck_sound {terms : List CosineTerm}
    {factors : ℕ → List ℤ} {row : List (ℤ × ℤ)} {j : ℕ} {ps : List ℤ}
    (hf : ∀ k < 20, FactorRowCorrect terms k (factors k))
    (hr : RowTrigCorrect terms row j)
    (hc : completeCoefficientRowCheck factors row j ps = true)
    (hrem : taylorRemainderCheck terms = true) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum terms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ)*u) -
      polynomialValue (quantizedCoefficients ps) u| ≤ (1/1000000000000 : ℝ) := by
  simp only [completeCoefficientRowCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  apply cosineSum_quantizedTaylor_error_of_checks hc.1 hf hr _ hrem hu
  intro k hk
  simpa using coefficientListCheck_sound hc.2 (k := k) (by simpa [hc.1] using hk)

end
end ErdosOverlap.Numerics
