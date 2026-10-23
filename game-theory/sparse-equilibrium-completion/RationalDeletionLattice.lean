/- AI-assisted formalization; Apache-2.0, following the parent repository.
Actual minimum-ratio deletion preserves a common denominator whose growth
depends on the direction, rather than multiplying all current weight denominators.
Exact checking status is external. No runtime or primitive bit-cost claim. -/
module
public import RationalFeatureDeletion
public import RationalFlowLattice
public import RationalFlowEncodingBounds
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

/-- The executed minimum ratio is one actual positive-direction coordinate.
This earns the pivot used in the denominator proof, rather than supplying it. -/
theorem rational_feature_theta_selected {m : ℕ} (q w : Fin m → ℚ)
    (hpos : ∃ i, 0 < w i) :
    ∃ j, 0 < w j ∧ rationalFeatureTheta q w = q j / w j := by
  obtain ⟨j, hj, he⟩ := (rational_feature_ratio_mem q w _).mp
    (rational_feature_theta_mem q w hpos)
  exact ⟨j, hj, he.symm⟩

/-- Clearing one shared direction denominator cancels it from the actual
deletion ratio. Only the positive selected integer coordinate enlarges the
weight lattice. The integer vector is input representation data, not an
assumed output bound or preservation contract. -/
theorem rational_feature_delete_integer_lattice {m : ℕ}
    (q w : Fin m → ℚ) (D W : ℕ) (hD : 0 < D) (hW : 0 < W)
    (hq : ∀ i, RationalDenominatorLattice D (q i))
    (z : Fin m → ℤ) (hw : ∀ i, w i = (z i : ℚ)/(W : ℚ))
    (hpos : ∃ i, 0 < w i) :
    ∃ j, 0 < z j ∧
      ∀ i, RationalDenominatorLattice (D*(z j).natAbs)
        (rationalFeatureDelete q w i) := by
  obtain ⟨j, hj, htheta⟩ := rational_feature_theta_selected q w hpos
  have hWQ : (0 : ℚ) < (W : ℚ) := by exact_mod_cast hW
  have hzjQ : (0 : ℚ) < (z j : ℚ) := by
    exact (div_pos_iff_of_pos_right hWQ).mp ((hw j) ▸ hj)
  have hzj : (0 : ℤ) < z j := by exact_mod_cast hzjQ
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hW0 : (W : ℚ) ≠ 0 := ne_of_gt hWQ
  have hz0 : (z j : ℚ) ≠ 0 := ne_of_gt hzjQ
  have habs : ((z j).natAbs : ℚ) = (z j : ℚ) := by
    have hi := congrArg (fun a : ℤ => (a : ℚ))
      (Int.natAbs_of_nonneg (le_of_lt hzj))
    simpa only [Int.cast_natCast] using hi
  refine ⟨j, hzj, ?_⟩
  intro i
  obtain ⟨a, ha⟩ := hq i
  obtain ⟨b, hb⟩ := hq j
  refine ⟨a*z j-b*z i, ?_⟩
  simp only [rationalFeatureDelete, htheta, hw i, hw j, ha, hb,
    Nat.cast_mul, habs, Int.cast_sub, Int.cast_mul]
  field_simp [hD0, hW0, hz0]

/-- A uniform integer-direction bound gives a single positive output lattice
scale, with linear multiplicative growth in the old scale. -/
theorem rational_feature_delete_lattice_bound {m : ℕ}
    (q w : Fin m → ℚ) (D W Z : ℕ) (hD : 0 < D) (hW : 0 < W)
    (hq : ∀ i, RationalDenominatorLattice D (q i))
    (z : Fin m → ℤ) (hw : ∀ i, w i = (z i : ℚ)/(W : ℚ))
    (hz : ∀ i, (z i).natAbs ≤ Z) (hpos : ∃ i, 0 < w i) :
    ∃ D', 0 < D' ∧ D' ≤ D*Z ∧
      ∀ i, (rationalFeatureDelete q w i).den ∣ D' := by
  obtain ⟨j, hj, hl⟩ := rational_feature_delete_integer_lattice q w D W hD hW hq z hw hpos
  refine ⟨D*(z j).natAbs, Nat.mul_pos hD (Int.natAbs_pos.mpr (ne_of_gt hj)),
    Nat.mul_le_mul_left D (hz j), ?_⟩
  intro i
  exact rational_lattice_den_divides _ _ (hl i)

/-- Canonical direction heights give an earned uniform integer direction
bound. The product clears only direction denominators, never all current
weight denominators. The current weights enter only through their OLD common
lattice D. -/
theorem rational_feature_delete_canonical_lattice_bound {m : ℕ}
    (q w : Fin m → ℚ) (D K : ℕ) (hD : 0 < D)
    (hq : ∀ i, RationalDenominatorLattice D (q i))
    (hwn : ∀ i, (w i).num.natAbs ≤ K) (hwd : ∀ i, (w i).den ≤ K)
    (hpos : ∃ i, 0 < w i) :
    ∃ D', 0 < D' ∧ D' ≤ D*Nat.pow K (m+1) ∧
      ∀ i, (rationalFeatureDelete q w i).den ∣ D' := by
  classical
  let W := rationalDenominatorProduct (List.ofFn w)
  have hW : 0 < W := rational_denominator_product_positive _
  have hwl : ∀ i, RationalDenominatorLattice W (w i) := by
    intro i
    exact rational_lattice_input_list _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  choose z hz using fun i => rational_lattice_scaled_integer W hW (w i) (hwl i)
  have hW0 : (W : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hW)
  have hw : ∀ i, w i = (z i : ℚ)/(W : ℚ) := by
    intro i
    apply (eq_div_iff hW0).mpr
    simpa only [mul_comm] using hz i
  have hzbound : ∀ i, (z i).natAbs ≤ K*W := by
    intro i
    have hm : |w i| ≤ (K : ℚ) :=
      (rational_magnitude_le_num_abs _).trans (by exact_mod_cast hwn i)
    have hh : ((z i).natAbs : ℚ) ≤ ((K*W : ℕ) : ℚ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, ←hz i, abs_mul,
        abs_of_pos (show (0 : ℚ) < (W : ℚ) by exact_mod_cast hW), Nat.cast_mul]
      have hWQ : (0 : ℚ) ≤ (W : ℚ) := by exact_mod_cast (le_of_lt hW)
      nlinarith
    exact_mod_cast hh
  have hWbound : W ≤ Nat.pow K m := by
    have hp := rational_denominator_product_power (List.ofFn w) K (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hwd i)
    simpa only [W, List.length_ofFn] using hp
  obtain ⟨D', hDp, hDb, hDl⟩ := rational_feature_delete_lattice_bound
    q w D W (K*W) hD hW hq z hw hzbound hpos
  refine ⟨D', hDp, hDb.trans ?_, hDl⟩
  apply Nat.mul_le_mul_left D
  calc
    K*W ≤ K*Nat.pow K m := Nat.mul_le_mul_left K hWbound
    _ = Nat.pow K (m+1) := by
      have hp : Nat.pow K (m+1) = Nat.pow K m*K := rfl
      rw [hp]
      exact Nat.mul_comm _ _

/-- In binary-exponent form the actual output denominator exponent grows
ADDITIVELY by B*(m+1), independently of the current denominator magnitude. -/
theorem rational_feature_delete_binary_lattice_bound {m : ℕ}
    (q w : Fin m → ℚ) (D Q B : ℕ) (hD : 0 < D) (hDb : D ≤ Nat.pow 2 Q)
    (hq : ∀ i, RationalDenominatorLattice D (q i))
    (hwn : ∀ i, (w i).num.natAbs ≤ Nat.pow 2 B) (hwd : ∀ i, (w i).den ≤ Nat.pow 2 B)
    (hpos : ∃ i, 0 < w i) :
    ∃ D', 0 < D' ∧ D' ≤ Nat.pow 2 (Q+B*(m+1)) ∧
      ∀ i, (rationalFeatureDelete q w i).den ∣ D' := by
  obtain ⟨D', hDp, hDb', hDl⟩ := rational_feature_delete_canonical_lattice_bound
    q w D (Nat.pow 2 B) hD hq hwn hwd hpos
  refine ⟨D', hDp, hDb'.trans ?_, hDl⟩
  calc
    D*Nat.pow (Nat.pow 2 B) (m+1) ≤ Nat.pow 2 Q*Nat.pow (Nat.pow 2 B) (m+1) := Nat.mul_le_mul_right _ hDb
    _ = Nat.pow 2 (Q+B*(m+1)) := by
      have hp : Nat.pow 2 (B*(m+1)) = Nat.pow (Nat.pow 2 B) (m+1) :=
        Nat.pow_mul 2 B (m+1)
      have ha : Nat.pow 2 (Q+B*(m+1)) = Nat.pow 2 Q*Nat.pow 2 (B*(m+1)) :=
        Nat.pow_add 2 Q (B*(m+1))
      rw [←hp, ←ha]

/-- Nonnegative mass and the earned deletion contract bound each actual
coordinate. No magnitude of the returned vector is supplied as a premise. -/
theorem rational_feature_delete_magnitude {m : ℕ}
    (q w : Fin m → ℚ) (r : ℚ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r)
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hw : ∑ i, w i = 0)
    (hpos : ∃ i, 0 < w i) :
    ∀ i, |rationalFeatureDelete q w i| ≤ r := by
  have hn := rational_feature_delete_nonnegative q w hq hs hpos
  have hmass := rational_feature_delete_mass q w hw
  intro i
  rw [abs_of_nonneg (hn i)]
  calc
    rationalFeatureDelete q w i ≤ ∑ j, rationalFeatureDelete q w j :=
      Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    _ = r := hmass.trans hm

/-- Actual canonical value-encoding bound for one executed deletion. Direction
height and current input lattice are explicit input facts; the output lattice,
mass bound, reduced numerators, denominators and bit budget are all derived.
This is not a primitive-arithmetic or runtime statement. -/
theorem rational_feature_delete_encoding_bits {m : ℕ}
    (q w : Fin m → ℚ) (D Q B R : ℕ) (r : ℚ)
    (hD : 0 < D) (hDb : D ≤ Nat.pow 2 Q)
    (hql : ∀ i, RationalDenominatorLattice D (q i))
    (hwn : ∀ i, (w i).num.natAbs ≤ Nat.pow 2 B) (hwd : ∀ i, (w i).den ≤ Nat.pow 2 B)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i = r) (hr : r ≤ ((Nat.pow 2 R : ℕ) : ℚ))
    (hs : ∀ i, w i ≠ 0 → 0 < q i) (hw : ∑ i, w i = 0)
    (hpos : ∃ i, 0 < w i) :
    ∀ i, rationalCanonicalEncodingBits (rationalFeatureDelete q w i) ≤
      R+2*(Q+B*(m+1))+3 := by
  obtain ⟨D', hDp, hDb', hDl⟩ := rational_feature_delete_binary_lattice_bound
    q w D Q B hD hDb hql hwn hwd hpos
  intro i
  apply rational_canonical_encoding_bits_bound _ R (Q+B*(m+1))
  · exact (rational_feature_delete_magnitude q w r hq hm hs hw hpos i).trans hr
  · exact (Nat.le_of_dvd hDp (hDl i)).trans hDb'

end SparseCompletion
