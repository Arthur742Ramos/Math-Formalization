/- AI-assisted actual graph-flow/decoder value-height continuation.
Exact compilation/audit status is recorded in source-bound receipts.
The original reviewed uncompiled v1 is preserved in source-graph-output-height-v1.
These are value/encoding bounds, not primitive or whole-pipeline runtime claims.
-/
module
public import RationalDemandGraphOutputHeight
public import RationalGaussianCompressionEncoding
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_input_height_of_canonical_budget {q : ℚ} {H : ℕ}
    (h : rationalCanonicalEncodingBits q ≤ H) : RationalInputHeight q H := by
  have hn : Nat.log2 q.num.natAbs+1 ≤ H := by
    unfold rationalCanonicalEncodingBits at h
    omega
  have hd : Nat.log2 q.den+1 ≤ H := by
    unfold rationalCanonicalEncodingBits at h
    omega
  constructor
  · by_cases hz : q.num.natAbs = 0
    · rw [hz]
      exact Nat.zero_le _
    · exact ((Nat.log2_lt hz).mp (by omega)).le
  · exact ((Nat.log2_lt q.den_ne_zero).mp (by omega)).le

def gaussianCompressedInputHeight (d m B Q R : ℕ) : ℕ :=
  R+2*(Q*m+m*(gaussianCompressionDirectionExponent d m B*(m+1)))+3

theorem rational_gaussian_compress_output_input_height {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (B : ℕ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q : Fin m → ℚ) (Q R : ℕ) (r : ℚ)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 Q)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r)
    (hr : r ≤ ((Nat.pow 2 R : ℕ) : ℚ)) :
    ∀ i, RationalInputHeight ((rationalGaussianCompressVector A q).get i)
      (gaussianCompressedInputHeight d m B Q R) := by
  intro i
  exact rational_input_height_of_canonical_budget
    (rational_gaussian_compress_encoding_bits A B hAn hAd q Q R r hqd hq hm hr i)

/-- Nonnegativity is recovered from the actual iterate lattice theorem, even
without a distinguished mass row in the original features. No property of the
returned weights is assumed to feed the graph capacity invariant. -/
theorem rational_gaussian_compress_nonnegative_from_input {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (B : ℕ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q : Fin m → ℚ) (Q : ℕ)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 Q) (hq : ∀ i, 0 ≤ q i) :
    ∀ i, 0 ≤ (rationalGaussianCompressVector A q).get i := by
  let D := rationalDenominatorProduct (List.ofFn q)
  have hD : 0 < D := rational_denominator_product_positive _
  have hql : ∀ i, RationalDenominatorLattice D (q i) := by
    intro i
    exact rational_lattice_input_list _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hDb : D ≤ Nat.pow 2 (Q*m) := by
    have hh := rational_denominator_product_power (List.ofFn q) (Nat.pow 2 Q) (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hqd i)
    have hp : Nat.pow 2 (Q*m) = Nat.pow (Nat.pow 2 Q) m := Nat.pow_mul 2 Q m
    simpa only [D, List.length_ofFn, hp] using hh
  obtain ⟨D', _hDp, _hDb', _hDl, hn, _hm⟩ := rational_gaussian_iterates_encoding_lattice
    A B hAn hAd (List.Vector.ofFn q) D (Q*m) hD hDb
    (by simpa only [Gaussian.vecGet_ofFn] using hql)
    (by simpa only [Gaussian.vecGet_ofFn] using hq) (rationalWeightSupport q).card
  exact hn

/-- Source-only full ACTUAL value-height endpoint: returned Gaussian weights
are passed to the actual graph-fuel demand decoder and materialized B table.
Only original input encoding/nonnegativity/mass hypotheses occur. -/
theorem rational_gaussian_graph_completion_table_output_height {d m B Q R T U E : ℕ}
    (A : Fin d → Fin m → ℚ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q t : Fin m → ℚ) (M ε r : ℚ)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 Q)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r)
    (hr : r ≤ ((Nat.pow 2 R : ℕ) : ℚ))
    (ht : ∀ i, RationalInputHeight (t i) T)
    (hM : RationalInputHeight M U) (hε : RationalInputHeight ε E) (hMn : 0 ≤ M) :
    ∀ i j, RationalInputHeight
      (rationalFlowTableEntry
        (rationalDemandGraphCompletionTable (rationalGaussianCompressVector A q).get t M ε) i j)
      (rationalDemandGraphOutputHeight m (gaussianCompressedInputHeight d m B Q R+T+U+E)) := by
  apply rational_demand_graph_completion_table_separate_input_height _ t M ε
    (rational_gaussian_compress_output_input_height A B hAn hAd q Q R r hqd hq hm hr)
    ht hM hε (rational_gaussian_compress_nonnegative_from_input A B hAn hAd q Q hqd hq) hMn

theorem rational_gaussian_graph_completion_table_canonical_bits {d m B Q R T U E : ℕ}
    (A : Fin d → Fin m → ℚ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q t : Fin m → ℚ) (M ε r : ℚ)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 Q)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r)
    (hr : r ≤ ((Nat.pow 2 R : ℕ) : ℚ))
    (ht : ∀ i, RationalInputHeight (t i) T)
    (hM : RationalInputHeight M U) (hε : RationalInputHeight ε E) (hMn : 0 ≤ M) :
    ∀ i j, rationalCanonicalEncodingBits
      (rationalFlowTableEntry
        (rationalDemandGraphCompletionTable (rationalGaussianCompressVector A q).get t M ε) i j) ≤
      2*rationalDemandGraphOutputHeight m (gaussianCompressedInputHeight d m B Q R+T+U+E)+3 := by
  intro i j
  exact rational_input_height_bits
    (rational_gaussian_graph_completion_table_output_height A hAn hAd q t M ε r
      hqd hq hm hr ht hM hε hMn i j)

end SparseCompletion
