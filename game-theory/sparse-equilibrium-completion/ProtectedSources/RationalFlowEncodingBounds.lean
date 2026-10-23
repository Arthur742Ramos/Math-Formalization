/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Bounds for the actual canonical numerator/denominator
of a bounded skew rational flow, conditional on its separately earned common
denominator invariant. This is value encoding size, not primitive bit time,
normalization cost, solver termination or an overall polynomial algorithm. -/
module
public import ProtectedSources.RationalNumeratorGrowth
@[expose] public section
namespace SparseCompletion

theorem rational_skew_flow_magnitude {n : ℕ} (C F : Fin n → Fin n → ℚ)
    (hskew : ∀ u v, F u v = -F v u) (hcap : ∀ u v, F u v ≤ C u v)
    (K : ℚ) (hC : ∀ u v, C u v ≤ K) (u v : Fin n) : |F u v| ≤ K := by
  apply abs_le.mpr
  constructor
  · have hr := (hcap v u).trans (hC v u)
    have hs := hskew u v
    linarith
  · exact (hcap u v).trans (hC u v)

theorem rational_numerator_bound_from_magnitude_denominator (q : ℚ) (N D : ℕ)
    (hm : |q| ≤ (N : ℚ)) (hd : q.den ≤ D) : q.num.natAbs ≤ N*D := by
  have hc : (q.den : ℚ) ≤ (D : ℚ) := by exact_mod_cast hd
  have hn : (q.num.natAbs : ℚ) ≤ (N : ℚ)*(D : ℚ) := by
    rw [rational_num_abs_identity]
    exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans
      (mul_le_mul_of_nonneg_left hc (by positivity))
  exact_mod_cast hn

theorem rational_numerator_binary_bound_from_height (q : ℚ) (B E : ℕ)
    (hm : |q| ≤ (Nat.pow 2 B : ℚ)) (hd : q.den ≤ Nat.pow 2 E) :
    q.num.natAbs ≤ Nat.pow 2 (B+E) := by
  have h := rational_numerator_bound_from_magnitude_denominator q (Nat.pow 2 B) (Nat.pow 2 E) hm hd
  exact h.trans_eq (Nat.pow_add 2 B E).symm

theorem natural_log2_bits_bound_of_binary_bound (x E : ℕ)
    (hx : x ≤ Nat.pow 2 E) : Nat.log2 x+1 ≤ E+1 := by
  by_cases hz : x=0
  · simp only [hz,Nat.log2_zero,zero_add]
    omega
  · have hp : Nat.pow 2 E < Nat.pow 2 (E+1) := Nat.pow_lt_pow_succ Nat.one_lt_two
    have hl := (Nat.log2_lt hz).mpr (hx.trans_lt hp)
    omega

/-- One sign bit plus the binary lengths of the canonical numerator magnitude
and positive denominator. This explicitly defines a value encoding budget;
it is not a claim about Lean heap layout, external arithmetic or instruction cost. -/
def rationalCanonicalEncodingBits (q : ℚ) : ℕ :=
  (Nat.log2 q.num.natAbs+1)+(Nat.log2 q.den+1)+1

theorem rational_canonical_encoding_bits_bound (q : ℚ) (B E : ℕ)
    (hm : |q| ≤ (Nat.pow 2 B : ℚ)) (hd : q.den ≤ Nat.pow 2 E) :
    rationalCanonicalEncodingBits q ≤ B+2*E+3 := by
  have hn := natural_log2_bits_bound_of_binary_bound q.num.natAbs (B+E)
    (rational_numerator_binary_bound_from_height q B E hm hd)
  have he := natural_log2_bits_bound_of_binary_bound q.den E hd
  unfold rationalCanonicalEncodingBits
  omega

/-- The divisor premise is the actual canonical denominator invariant to be
earned from input capacities and executed updates. Capacity/skew alone do not
imply it: arbitrary feasible rational flows can have arbitrarily fine denominators. -/
theorem rational_skew_flow_canonical_encoding_bound {n : ℕ}
    (C F : Fin n → Fin n → ℚ)
    (hskew : ∀ u v, F u v = -F v u) (hcap : ∀ u v, F u v ≤ C u v)
    (B E D : ℕ) (hD : 0 < D) (hDb : D ≤ Nat.pow 2 E)
    (hC : ∀ u v, C u v ≤ (Nat.pow 2 B : ℚ))
    (hden : ∀ u v, (F u v).den ∣ D) :
    ∀ u v, rationalCanonicalEncodingBits (F u v) ≤ B+2*E+3 := by
  intro u v
  apply rational_canonical_encoding_bits_bound (F u v) B E
  · exact rational_skew_flow_magnitude C F hskew hcap _ hC u v
  · exact (Nat.le_of_dvd hD (hden u v)).trans hDb

end SparseCompletion
