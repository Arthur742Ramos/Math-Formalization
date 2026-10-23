/- AI-assisted original-input and transient-value continuation; Apache-2.0.
Exact compilation/audit status is recorded in source-bound receipts.
The uncompiled original draft remains in source-input-bits-v1.
These are value/encoding bounds, not primitive or total running-time claims.
-/
module
public import ProtectedSources.GaussianInputEncoding
public import Mathlib.Data.Nat.Size
@[expose] public section
namespace SparseCompletion.Gaussian

theorem nat_size_le_of_le_two_pow (a E : ℕ) (h : a ≤ 2^E) : Nat.size a ≤ E+1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size h

/-- A deliberately coarse polynomial exponent avoids pretending factorial
magnitude is polynomial. Its binary length is bounded by k²+E*k+1. -/
theorem factorial_times_pow_two_le (k E : ℕ) :
    max 1 (k.factorial * (2^E)^k) ≤ 2^(k*k+E*k) := by
  apply max_le
  · exact Nat.one_le_two_pow
  · calc
      k.factorial * (2^E)^k ≤ k^k * (2^E)^k :=
        Nat.mul_le_mul_right _ (Nat.factorial_le_pow k)
      _ ≤ (2^k)^k * (2^E)^k :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_of_lt k.lt_two_pow_self) k)
      _ = 2^(k*k+E*k) := by rw [← pow_mul, ← pow_mul, pow_add]

def kernelOutputBitBound (r n B : ℕ) : ℕ :=
  r*r + clearedInputExponent r n B*r + 1

/-- Actual computed coefficients, bounded directly from original rational
input entry numerators and denominators. The cleared numerator matrix is no
longer a caller-supplied height hypothesis. -/
theorem kernel_output_bits_from_original_input {r n : ℕ}
    (A : QTable r n) (B : ℕ)
    (hnum : ∀ i j, (entry A i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (entry A i j).den ≤ 2^B)
    (w : QVec n) (hkernel : kernel r n A = some w) :
    ∀ j, Nat.size (w.get j).num.natAbs ≤ kernelOutputBitBound r n B ∧
      Nat.size (w.get j).den ≤ kernelOutputBitBound r n B := by
  obtain ⟨k, hkr, _hkn, hk⟩ := kernel_rational_output_height A
    (2^(clearedInputExponent r n B))
    (matrix_num_bound_from_input_bits (entry A) B hnum hden) w hkernel
  intro j
  have hpow := factorial_times_pow_two_le k (clearedInputExponent r n B)
  have hn := nat_size_le_of_le_two_pow _ _ ((hk j).1.trans hpow)
  have hd := nat_size_le_of_le_two_pow _ _ ((hk j).2.trans hpow)
  have hk2 : k*k ≤ r*r := Nat.mul_le_mul hkr hkr
  have hkE : clearedInputExponent r n B*k ≤ clearedInputExponent r n B*r :=
    Nat.mul_le_mul_left _ hkr
  constructor <;> dsimp [kernelOutputBitBound] <;> omega

end SparseCompletion.Gaussian
