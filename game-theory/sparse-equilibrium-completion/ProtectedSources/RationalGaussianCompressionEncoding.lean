/- AI-assisted separate development; Apache-2.0.
Composes actual Gaussian directions and actual materialized deletions.
Exact-source check status is recorded externally. No arithmetic operation,
primitive bit-time or runtime claim.
-/
module
public import ProtectedSources.RationalDeletionLattice
public import ProtectedSources.GaussianFeatureBits
public import ProtectedSources.RationalGaussianCompress
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def gaussianCompressionDirectionExponent (d m B : ℕ) : ℕ :=
  Gaussian.kernelOutputBitBound (d+(m+1)) m B

/-- The actual reduction, including both keep-input branches, earns its next
common lattice and preserves nonnegativity and mass. Direction bounds come
from original feature entries, independently of the current weight sizes. -/
theorem rational_gaussian_reduce_vector_encoding_lattice {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (B : ℕ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q : Gaussian.QVec m) (D Q : ℕ) (hD : 0 < D) (hDb : D ≤ Nat.pow 2 Q)
    (hql : ∀ i, RationalDenominatorLattice D (q.get i))
    (hq : ∀ i, 0 ≤ q.get i) :
    ∃ D', 0 < D' ∧
      D' ≤ Nat.pow 2 (Q+gaussianCompressionDirectionExponent d m B*(m+1)) ∧
      (∀ i, RationalDenominatorLattice D' ((rationalGaussianReduceVector A q).get i)) ∧
      (∀ i, 0 ≤ (rationalGaussianReduceVector A q).get i) ∧
      (∑ i, (rationalGaussianReduceVector A q).get i) = ∑ i, q.get i := by
  let T := gaussianCompressionDirectionExponent d m B
  have hkeep : ∃ D', 0 < D' ∧ D' ≤ Nat.pow 2 (Q+T*(m+1)) ∧
      (∀ i, RationalDenominatorLattice D' (q.get i)) ∧
      (∀ i, 0 ≤ q.get i) ∧ (∑ i, q.get i) = ∑ i, q.get i := by
    refine ⟨D, hD, hDb.trans ?_, hql, hq, rfl⟩
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right _ _)
  unfold rationalGaussianReduceVector
  split_ifs with hc
  · exact hkeep
  · cases hk : rationalGaussianFeatureKernel A q.get with
    | none =>
      simpa only [rationalGaussianFeatureDelete, hk, Option.map_none]
        using hkeep
    | some w =>
      obtain ⟨⟨_ha, hm, hs⟩, hn⟩ := rational_gaussian_feature_sound A q.get w hk
      have hpos := rational_feature_direction_positive w hm hn
      have hwb := rational_gaussian_feature_direction_bits A B hAn hAd q.get w hk
      have hwn : ∀ i, (w i).num.natAbs ≤ Nat.pow 2 T := by
        intro i
        exact Nat.le_of_lt (Nat.size_le.mp (hwb i).1)
      have hwd : ∀ i, (w i).den ≤ Nat.pow 2 T := by
        intro i
        exact Nat.le_of_lt (Nat.size_le.mp (hwb i).2)
      obtain ⟨D', hDp, hDb', hDl⟩ := rational_feature_delete_binary_lattice_bound
        q.get w D Q T hD hDb hql hwn hwd hpos
      have hnonneg := rational_feature_delete_nonnegative q.get w hq hs hpos
      have hmass := rational_feature_delete_mass q.get w hm
      refine ⟨D', hDp, hDb', ?_, ?_, ?_⟩
      · intro i
        simpa only [rationalGaussianFeatureDelete, hk, Option.map_some,
          Gaussian.vecGet_ofFn] using
          rational_lattice_of_den_divides D' hDp (rationalFeatureDelete q.get w i) (hDl i)
      · simpa only [rationalGaussianFeatureDelete, hk, Option.map_some,
          Gaussian.vecGet_ofFn] using hnonneg
      · simpa only [rationalGaussianFeatureDelete, hk, Option.map_some,
          Gaussian.vecGet_ofFn] using hmass

/-- Induction over the actual materialized vector iteration. The lattice
exponent grows additively per iteration; no bounds on returned weights are
introduced as input fields or premises. -/
theorem rational_gaussian_iterates_encoding_lattice {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (B : ℕ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q : Gaussian.QVec m) (D Q : ℕ) (hD : 0 < D) (hDb : D ≤ Nat.pow 2 Q)
    (hql : ∀ i, RationalDenominatorLattice D (q.get i))
    (hq : ∀ i, 0 ≤ q.get i) (fuel : ℕ) :
    ∃ D', 0 < D' ∧
      D' ≤ Nat.pow 2 (Q+fuel*(gaussianCompressionDirectionExponent d m B*(m+1))) ∧
      (∀ i, RationalDenominatorLattice D' ((rationalGaussianVectorIterates A q fuel).get i)) ∧
      (∀ i, 0 ≤ (rationalGaussianVectorIterates A q fuel).get i) ∧
      (∑ i, (rationalGaussianVectorIterates A q fuel).get i) = ∑ i, q.get i := by
  induction fuel with
  | zero =>
    refine ⟨D, hD, ?_, hql, hq, rfl⟩
    simpa only [Nat.zero_mul, Nat.add_zero] using hDb
  | succ fuel ih =>
    obtain ⟨Dt, hDt, hDtb, hDtl, htn, htm⟩ := ih
    obtain ⟨D', hDp, hDb', hDl, hn, hm⟩ := rational_gaussian_reduce_vector_encoding_lattice
      A B hAn hAd (rationalGaussianVectorIterates A q fuel) Dt
      (Q+fuel*(gaussianCompressionDirectionExponent d m B*(m+1))) hDt hDtb hDtl htn
    rw [rational_gaussian_vector_iterates_succ]
    refine ⟨D', hDp, ?_, hDl, hn, hm.trans htm⟩
    simpa only [Nat.succ_mul, Nat.add_assoc] using hDb'

/-- Value-encoding bound for the actual Gaussian compressor, derived from
original feature heights, original weight denominators, nonnegativity and mass.
The input numerator bound is unnecessary because mass controls magnitudes.
This theorem does not assert arithmetic or bit runtime. -/
theorem rational_gaussian_compress_encoding_bits {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (B : ℕ)
    (hAn : ∀ a i, (A a i).num.natAbs ≤ Nat.pow 2 B)
    (hAd : ∀ a i, (A a i).den ≤ Nat.pow 2 B)
    (q : Fin m → ℚ) (Q R : ℕ) (r : ℚ)
    (hqd : ∀ i, (q i).den ≤ Nat.pow 2 Q)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r)
    (hr : r ≤ ((Nat.pow 2 R : ℕ) : ℚ)) :
    ∀ i, rationalCanonicalEncodingBits ((rationalGaussianCompressVector A q).get i) ≤
      R+2*(Q*m+m*(gaussianCompressionDirectionExponent d m B*(m+1)))+3 := by
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
  obtain ⟨D', hDp, hDb', hDl, hn, hmass⟩ := rational_gaussian_iterates_encoding_lattice
    A B hAn hAd (List.Vector.ofFn q) D (Q*m) hD hDb
    (by simpa only [Gaussian.vecGet_ofFn] using hql)
    (by simpa only [Gaussian.vecGet_ofFn] using hq) (rationalWeightSupport q).card
  have hcount := rational_gaussian_compress_iteration_fuel_le q
  have hDbFinal : D' ≤ Nat.pow 2 (Q*m+m*(gaussianCompressionDirectionExponent d m B*(m+1))) := by
    exact hDb'.trans (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcount) _))
  have hmFinal : (∑ i, (rationalGaussianCompressVector A q).get i) = r := by
    have hm0 : (∑ i, (List.Vector.ofFn q).get i) = r := by
      simpa only [Gaussian.vecGet_ofFn] using hm
    exact hmass.trans hm0
  intro i
  apply rational_canonical_encoding_bits_bound _ R
    (Q*m+m*(gaussianCompressionDirectionExponent d m B*(m+1)))
  · have hni : 0 ≤ (rationalGaussianCompressVector A q).get i := hn i
    rw [abs_of_nonneg hni]
    exact (Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)).trans
      (hmFinal.le.trans hr)
  · exact (rational_lattice_den_le D' hDp _ (hDl i)).trans hDbFinal

end SparseCompletion
