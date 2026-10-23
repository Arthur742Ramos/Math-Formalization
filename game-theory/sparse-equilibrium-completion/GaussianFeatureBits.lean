/- AI-assisted original-input and transient-value continuation; Apache-2.0.
Exact compilation/audit status is recorded in source-bound receipts.
The uncompiled original draft remains in source-input-bits-v1.
These are value/encoding bounds, not primitive or total running-time claims.
-/
module
public import GaussianOutputBits
public import RationalGaussianFeature
@[expose] public section
namespace SparseCompletion

theorem gaussian_feature_original_entry_bounds {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (B : ℕ)
    (hnum : ∀ a i, (A a i).num.natAbs ≤ 2^B)
    (hden : ∀ a i, (A a i).den ≤ 2^B) :
    ∀ row i, (gaussianFeatureRows A q row i).num.natAbs ≤ 2^B ∧
      (gaussianFeatureRows A q row i).den ≤ 2^B := by
  intro row
  refine Fin.addCases ?_ ?_ row
  · intro a i
    simpa only [gaussianFeatureRows, Fin.addCases_left] using And.intro (hnum a i) (hden a i)
  · intro row
    refine Fin.cases ?_ ?_ row
    · intro i
      simpa only [gaussianFeatureRows, Fin.addCases_right, Fin.cons_zero,
        Rat.num_one, Int.natAbs_one, Rat.den_one] using
        And.intro (Nat.one_le_two_pow (n := B)) (Nat.one_le_two_pow (n := B))
    · intro j i
      by_cases hq : 0 < q j
      · simp [gaussianFeatureRows, hq, Nat.one_le_two_pow]
      · by_cases hij : i = j <;> simp [gaussianFeatureRows, hq, hij, Nat.one_le_two_pow]

/-- A uniform original-feature bound for every ACTUAL computed direction.
In particular it is independent of the current weight encoding during all
support-deletion iterations. This is a value bound, not a runtime sharing claim. -/
theorem rational_gaussian_feature_direction_bits {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (B : ℕ)
    (hnum : ∀ a i, (A a i).num.natAbs ≤ 2^B)
    (hden : ∀ a i, (A a i).den ≤ 2^B)
    (q w : Fin m → ℚ) (hkernel : rationalGaussianFeatureKernel A q = some w) :
    ∀ i, Nat.size (w i).num.natAbs ≤ Gaussian.kernelOutputBitBound (d+(m+1)) m B ∧
      Nat.size (w i).den ≤ Gaussian.kernelOutputBitBound (d+(m+1)) m B := by
  cases hk : Gaussian.kernel (d+(m+1)) m
      (Gaussian.tableOfFn (gaussianFeatureRows A q)) with
  | none => simp [rationalGaussianFeatureKernel, hk] at hkernel
  | some v =>
    have hv : v.get = w := by simpa [rationalGaussianFeatureKernel, hk] using hkernel
    have he := gaussian_feature_original_entry_bounds A q B hnum hden
    have hb := Gaussian.kernel_output_bits_from_original_input
      (Gaussian.tableOfFn (gaussianFeatureRows A q)) B
      (fun a i => by simpa only [Gaussian.entry_tableOfFn] using (he a i).1)
      (fun a i => by simpa only [Gaussian.entry_tableOfFn] using (he a i).2) v hk
    simpa only [hv] using hb

end SparseCompletion
