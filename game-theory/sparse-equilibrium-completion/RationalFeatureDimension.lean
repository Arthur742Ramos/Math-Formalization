/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. Finite-dimensional rational linear dependence proves
completeness of the actual FM-based kernel program. Classical reasoning is only
in proofs. No runtime basis selection or polynomial complexity is claimed.
A mass row already present among d features gives the sharp d support threshold;
otherwise the explicitly adjoined mass row costs one additional dimension. -/
module
public import RationalFeatureKernel
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Cardinality forces a nonzero rational relation on current positive support.
The coefficients obtained in this proof need not themselves be executable: the
separate total kernel program finds a normalized witness using LP completeness. -/
theorem rational_feature_relation_of_card {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (hcard : d < (rationalWeightSupport q).card) :
    ∃ w : Fin m → ℚ, (∀ a, ∑ i, A a i * w i = 0) ∧
      (∀ i, w i ≠ 0 → 0 < q i) ∧ ∃ i, w i ≠ 0 := by
  classical
  let s := rationalWeightSupport q
  let V : s → (Fin d → ℚ) := fun i a => A a i.val
  have hdep : ¬ LinearIndependent ℚ V := by
    intro hind
    have hc : s.card ≤ d := by
      simpa using hind.fintype_card_le_finrank
    exact (Nat.not_le_of_gt hcard) hc
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  let w : Fin m → ℚ := fun j => if hj : j ∈ s then g ⟨j, hj⟩ else 0
  have hext : ∀ f : Fin m → ℚ,
      (∑ j, w j * f j) = ∑ j : s, g j * f j.val := by
    intro f
    calc
      (∑ j, w j * f j) = ∑ j ∈ s, w j * f j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        simp only [w, dite_eq_right hj, zero_mul]
      _ = ∑ j : s, w j.val * f j.val := (Finset.sum_coe_sort s _).symm
      _ = ∑ j : s, g j * f j.val := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [w, dite_eq_left j.property]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro a
    have hga := congrFun hg a
    have hzero : (∑ j : s, g j * A a j.val) = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, V]
        using hga
    calc
      (∑ j, A a j * w j) = ∑ j, w j * A a j := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      _ = ∑ j : s, g j * A a j.val := hext (A a)
      _ = 0 := hzero
  · intro j hj
    have hjs : j ∈ s := by
      by_contra hn
      exact hj (by simp only [w, dite_eq_right hn])
    have hqj : q j ≠ 0 := (Finset.mem_filter.mp hjs).2
    exact lt_of_le_of_ne (hq j) (Ne.symm hqj)
  · exact ⟨i.val, by simpa only [w, dite_eq_left i.property] using hi⟩

/-- If the constant-one feature is already included, mass preservation costs no
additional feature coordinate. This is the form for exact sharp support bounds. -/
theorem rational_feature_direction_of_card {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1)
    (hcard : d < (rationalWeightSupport q).card) :
    ∃ w, RationalFeatureDirection A q w ∧ ∃ i, w i ≠ 0 := by
  obtain ⟨w, ha, hs, hn⟩ := rational_feature_relation_of_card A q hq hcard
  have hm : ∑ i, w i = 0 := by
    simpa only [hmass, one_mul] using ha a₀
  exact ⟨w, ⟨ha, hm, hs⟩, hn⟩

theorem rational_feature_kernel_exists_of_card {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1)
    (hcard : d < (rationalWeightSupport q).card) :
    ∃ w, rationalFeatureKernel A q = some w := by
  obtain ⟨w, hw, hn⟩ := rational_feature_direction_of_card A q hq a₀ hmass hcard
  exact rational_feature_kernel_complete A q w hw hn

/-- Without an existing mass feature, append one explicitly. The bound is d+1,
not d; this theorem does not hide the normalization coordinate. -/
theorem rational_feature_kernel_exists_with_mass {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (hcard : d + 1 < (rationalWeightSupport q).card) :
    ∃ w, rationalFeatureKernel A q = some w := by
  let B : Fin (d+1) → Fin m → ℚ :=
    Fin.cons (α := fun _ => Fin m → ℚ) (fun _ => 1) A
  obtain ⟨w, ⟨hb, hm, hs⟩, hn⟩ := rational_feature_direction_of_card B q hq
    0 (fun _ => rfl) hcard
  have ha : ∀ a, ∑ i, A a i * w i = 0 := by
    intro a
    simpa only [B, Fin.cons_succ] using hb a.succ
  exact rational_feature_kernel_complete A q w ⟨ha, hm, hs⟩ hn

/-- Genuine end-to-end deletion above the feature dimension: the program accepts
only the rational features and weights. Dimension/count assumptions appear solely
in its correctness proof, not as a supplied kernel or feasibility oracle. -/
theorem rational_feature_computed_deletion_above_dimension {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q : Fin m → ℚ) (hq : ∀ i, 0 ≤ q i)
    (a₀ : Fin d) (hmass : ∀ i, A a₀ i = 1)
    (hcard : d < (rationalWeightSupport q).card) :
    ∃ v, rationalFeatureKernelDelete A q = some v ∧
      (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = ∑ i, q i ∧
      (∀ a, (∑ i, v i * A a i) = ∑ i, q i * A a i) ∧
      (∀ i, q i = 0 → v i = 0) ∧
      (rationalWeightSupport v).card < (rationalWeightSupport q).card := by
  obtain ⟨w, hw⟩ := rational_feature_kernel_exists_of_card A q hq a₀ hmass hcard
  exact ⟨rationalFeatureDelete q w,
    rational_feature_kernel_deletion_witness A q w hq hw⟩

end SparseCompletion
