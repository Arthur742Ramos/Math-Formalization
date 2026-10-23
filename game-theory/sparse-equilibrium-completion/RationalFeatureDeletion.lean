/- AI-assisted formalization under the repository Apache-2.0 license.
Development source; exact-source verification is recorded separately. A genuinely executable rational minimum-ratio deletion
step for a SUPPLIED zero-moment direction. The direction is input data: this
module does not claim to construct a kernel vector, iterate to a sharp support
bound, or establish polynomial arithmetic/bit cost. Classical reasoning occurs
only in proofs, never in the executable definitions. -/
module
public import RationalGapCompression
public import Mathlib.Tactic
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- Positive-direction ratios are enumerated from the actual finite labels. -/
def rationalFeatureRatios {m : ℕ} (q w : Fin m → ℚ) : Finset ℚ :=
  (Finset.univ.filter fun i => 0 < w i).image fun i => q i / w i

/-- A total finite rational minimum; zero is used only when no positive direction
coordinate exists. Finite rational order and equality are genuine decidable data. -/
def rationalFeatureTheta {m : ℕ} (q w : Fin m → ℚ) : ℚ :=
  if h : (rationalFeatureRatios q w).Nonempty then
    (rationalFeatureRatios q w).min' h
  else 0

/-- Every output coordinate uses the same computed step size. -/
def rationalFeatureDelete {m : ℕ} (q w : Fin m → ℚ) : Fin m → ℚ :=
  fun i => q i - rationalFeatureTheta q w * w i

def rationalWeightSupport {m : ℕ} (q : Fin m → ℚ) : Finset (Fin m) :=
  Finset.univ.filter fun i => q i ≠ 0

theorem rational_feature_ratio_mem {m : ℕ} (q w : Fin m → ℚ) (a : ℚ) :
    a ∈ rationalFeatureRatios q w ↔ ∃ i, 0 < w i ∧ q i / w i = a := by
  simp only [rationalFeatureRatios, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem rational_feature_ratios_nonempty {m : ℕ} (q w : Fin m → ℚ) :
    (rationalFeatureRatios q w).Nonempty ↔ ∃ i, 0 < w i := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨i, hi, _⟩ := (rational_feature_ratio_mem q w a).mp ha
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨q i / w i, (rational_feature_ratio_mem q w _).mpr ⟨i, hi, rfl⟩⟩

theorem rational_feature_theta_mem {m : ℕ} (q w : Fin m → ℚ)
    (hpos : ∃ i, 0 < w i) :
    rationalFeatureTheta q w ∈ rationalFeatureRatios q w := by
  have h := (rational_feature_ratios_nonempty q w).mpr hpos
  simp only [rationalFeatureTheta, dite_eq_left h]
  exact Finset.min'_mem _ _

theorem rational_feature_theta_le_ratio {m : ℕ} (q w : Fin m → ℚ)
    (i : Fin m) (hi : 0 < w i) :
    rationalFeatureTheta q w ≤ q i / w i := by
  have h := (rational_feature_ratios_nonempty q w).mpr ⟨i, hi⟩
  simp only [rationalFeatureTheta, dite_eq_left h]
  exact Finset.min'_le _ _ ((rational_feature_ratio_mem q w _).mpr ⟨i, hi, rfl⟩)

/-- This assumption means that the supplied direction is supported on CURRENTLY
positive weights; it does not assume any desired output property. -/
theorem rational_feature_theta_pos {m : ℕ} (q w : Fin m → ℚ)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hpos : ∃ i, 0 < w i) :
    0 < rationalFeatureTheta q w := by
  obtain ⟨i, hi, he⟩ := (rational_feature_ratio_mem q w _).mp
    (rational_feature_theta_mem q w hpos)
  rw [← he]
  exact div_pos (hs i (ne_of_gt hi)) hi

theorem rational_feature_direction_positive {m : ℕ} (w : Fin m → ℚ)
    (hm : ∑ i, w i = 0) (hn : ∃ i, w i ≠ 0) : ∃ i, 0 < w i := by
  classical
  by_contra h
  have hnonpos : ∀ i, w i ≤ 0 := by
    intro i
    exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hzero : ∀ i, w i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hnonpos j)).mp hm i
      (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := hn
  exact hi (hzero i)

theorem rational_feature_delete_nonnegative {m : ℕ} (q w : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∀ i, w i ≠ 0 → 0 < q i)
    (hpos : ∃ i, 0 < w i) : ∀ i, 0 ≤ rationalFeatureDelete q w i := by
  have ht : 0 ≤ rationalFeatureTheta q w :=
    le_of_lt (rational_feature_theta_pos q w hs hpos)
  intro i
  unfold rationalFeatureDelete
  by_cases hi : 0 < w i
  · exact sub_nonneg.mpr ((le_div_iff₀ hi).mp
      (rational_feature_theta_le_ratio q w i hi))
  · have hw : w i ≤ 0 := le_of_not_gt hi
    exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht hw).trans (hq i))

theorem rational_feature_delete_zero {m : ℕ} (q w : Fin m → ℚ)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (i : Fin m) (hi : q i = 0) :
    rationalFeatureDelete q w i = 0 := by
  have hw : w i = 0 := by
    by_contra hn
    have hp := hs i hn
    rw [hi] at hp
    exact (lt_irrefl (0 : ℚ)) hp
  simp only [rationalFeatureDelete, hi, hw, mul_zero, sub_self]

theorem rational_feature_delete_removes {m : ℕ} (q w : Fin m → ℚ)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hpos : ∃ i, 0 < w i) :
    ∃ i, 0 < q i ∧ rationalFeatureDelete q w i = 0 := by
  obtain ⟨i, hi, he⟩ := (rational_feature_ratio_mem q w _).mp
    (rational_feature_theta_mem q w hpos)
  refine ⟨i, hs i (ne_of_gt hi), ?_⟩
  unfold rationalFeatureDelete
  rw [← he, div_mul_cancel₀ _ (ne_of_gt hi), sub_self]

/-- Exact arbitrary feature preservation for the supplied annihilating vector. -/
theorem rational_feature_delete_moment {m : ℕ} (q w a : Fin m → ℚ)
    (ha : ∑ i, w i * a i = 0) :
    (∑ i, rationalFeatureDelete q w i * a i) = ∑ i, q i * a i := by
  simp only [rationalFeatureDelete, sub_mul, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum, ha, mul_zero, sub_zero]

theorem rational_feature_delete_mass {m : ℕ} (q w : Fin m → ℚ)
    (hm : ∑ i, w i = 0) :
    (∑ i, rationalFeatureDelete q w i) = ∑ i, q i := by
  simp only [rationalFeatureDelete, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hm, mul_zero, sub_zero]

theorem rational_feature_delete_support_subset {m : ℕ} (q w : Fin m → ℚ)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) :
    rationalWeightSupport (rationalFeatureDelete q w) ⊆ rationalWeightSupport q := by
  intro i hi
  have hn : rationalFeatureDelete q w i ≠ 0 := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  intro hz
  exact hn (rational_feature_delete_zero q w hs i hz)

theorem rational_feature_delete_support_strict {m : ℕ} (q w : Fin m → ℚ)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hpos : ∃ i, 0 < w i) :
    rationalWeightSupport (rationalFeatureDelete q w) ⊂ rationalWeightSupport q := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨rational_feature_delete_support_subset q w hs, ?_⟩
  obtain ⟨i, hi, hz⟩ := rational_feature_delete_removes q w hs hpos
  intro he
  have hold : i ∈ rationalWeightSupport q :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, ne_of_gt hi⟩
  have hnew : i ∈ rationalWeightSupport (rationalFeatureDelete q w) := by
    rw [he]
    exact hold
  exact (Finset.mem_filter.mp hnew).2 hz

theorem rational_feature_delete_support_card {m : ℕ} (q w : Fin m → ℚ)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hpos : ∃ i, 0 < w i) :
    (rationalWeightSupport (rationalFeatureDelete q w)).card <
      (rationalWeightSupport q).card :=
  Finset.card_lt_card (rational_feature_delete_support_strict q w hs hpos)

/-- First coherent tranche: supplied kernel DATA is consumed by an actual finite
rational step. Kernel discovery and a terminating full compressor are separate
obligations; they are not assumed to have been implemented by this theorem. -/
theorem rational_feature_delete_contract {d m : ℕ}
    (A : Fin d → Fin m → ℚ) (q w : Fin m → ℚ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, w i = 0)
    (ha : ∀ a, ∑ i, w i * A a i = 0)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hn : ∃ i, w i ≠ 0) :
    (∀ i, 0 ≤ rationalFeatureDelete q w i) ∧
    (∑ i, rationalFeatureDelete q w i) = ∑ i, q i ∧
    (∀ a, (∑ i, rationalFeatureDelete q w i * A a i) = ∑ i, q i * A a i) ∧
    (∀ i, q i = 0 → rationalFeatureDelete q w i = 0) ∧
    (rationalWeightSupport (rationalFeatureDelete q w)).card <
      (rationalWeightSupport q).card := by
  have hp := rational_feature_direction_positive w hm hn
  refine ⟨rational_feature_delete_nonnegative q w hq hs hp,
    rational_feature_delete_mass q w hm,
    fun a => rational_feature_delete_moment q w (A a) (ha a),
    fun i hi => rational_feature_delete_zero q w hs i hi,
    rational_feature_delete_support_card q w hs hp⟩

end SparseCompletion
