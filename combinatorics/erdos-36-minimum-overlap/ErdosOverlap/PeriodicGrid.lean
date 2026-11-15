/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Periodic

/-!
# Exact cell-dilation and periodic step-weight bridge

The grid lemmas are exact interval-integral identities. They apply to
arbitrary integrable periodic functions, and are subsequently instantiated
with the actual wrapped overlap. No constant-on-cells density assumption
is made.
-/

namespace ErdosOverlap

open MeasureTheory Set Function
open scoped Interval BigOperators

public section
noncomputable section

@[expose] def gridWidth (n : ℕ) : ℝ := 2 / n

@[expose] def gridIntegral (q : ℝ → ℝ) (n i : ℕ) : ℝ :=
  ∫ t in (i : ℝ) * gridWidth n..((i : ℝ) + 1) * gridWidth n, q t

@[expose] def periodicCellWeight (n i : ℕ) : ℝ → ℝ :=
  periodicDensity
    ((Ioc ((i : ℝ) * gridWidth n) (((i : ℝ) + 1) * gridWidth n)).indicator (fun _ => 1))

theorem gridWidth_pos {n : ℕ} (hn : 0 < n) : 0 < gridWidth n := by
  unfold gridWidth
  positivity

theorem gridWidth_mul {n : ℕ} (hn : 0 < n) : (n : ℝ) * gridWidth n = 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold gridWidth
  field_simp

theorem gridIntegral_mod {q : ℝ → ℝ} (hq : Periodic q 2)
    {n : ℕ} (hn : 0 < n) (i : ℕ) :
    gridIntegral q n i = gridIntegral q n (i % n) := by
  have hdecomp : (i : ℝ) = (i % n : ℕ) + (n : ℝ) * (i / n : ℕ) := by
    exact_mod_cast (Nat.mod_add_div i n).symm
  have hstart : (i : ℝ) * gridWidth n =
      (i % n : ℕ) * gridWidth n + (i / n : ℕ) * 2 := by
    rw [hdecomp]
    nlinarith [gridWidth_mul hn]
  have hend : ((i : ℝ) + 1) * gridWidth n =
      ((i % n : ℕ) + 1) * gridWidth n + (i / n : ℕ) * 2 := by
    linarith [hstart]
  unfold gridIntegral
  rw [hstart, hend, ← intervalIntegral.integral_comp_add_right]
  apply intervalIntegral.integral_congr
  intro x _
  exact hq.nat_mul (i / n) x

/-- Multiplication by an integer sends one grid cell to exactly that many
consecutive cells, with the exact inverse-Jacobian factor. -/
theorem integral_dilate_gridCell {q : ℝ → ℝ} (hq : Periodic q 2)
    (hqi : ∀ a b, IntervalIntegrable q volume a b)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : ℕ) :
    (∫ t in (i : ℝ) * gridWidth n..((i : ℝ) + 1) * gridWidth n, q ((k : ℝ) * t)) =
      (k : ℝ)⁻¹ * ∑ j ∈ Finset.range k, gridIntegral q n ((k * i + j) % n) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [intervalIntegral.integral_comp_mul_left q hk', smul_eq_mul]
  congr 1
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => ((k * i + j : ℕ) : ℝ) * gridWidth n)
    (n := k) (fun j _ => hqi _ _)
  calc
    _ = ∫ t in (((k * i + 0 : ℕ) : ℝ) * gridWidth n)..
        (((k * i + k : ℕ) : ℝ) * gridWidth n), q t := by
      congr 1 <;> push_cast <;> ring
    _ = ∑ j ∈ Finset.range k,
        ∫ t in (((k * i + j : ℕ) : ℝ) * gridWidth n)..
          (((k * i + (j + 1) : ℕ) : ℝ) * gridWidth n), q t := hs.symm
    _ = ∑ j ∈ Finset.range k, gridIntegral q n (k * i + j) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold gridIntegral
      congr 1
      all_goals push_cast; ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact gridIntegral_mod hq hn (k * i + j)

theorem periodicCellWeight_periodic (n i : ℕ) : Periodic (periodicCellWeight n i) 2 :=
  periodicDensity_periodic _

theorem periodicCellWeight_measurable (n i : ℕ) : Measurable (periodicCellWeight n i) :=
  periodicDensity_measurable_of_measurable (measurable_const.indicator measurableSet_Ioc)

theorem periodicCellWeight_mem (n i : ℕ) (t : ℝ) :
    periodicCellWeight n i t ∈ Icc (0 : ℝ) 1 := by
  unfold periodicCellWeight periodicDensity
  simp only [indicator]
  split_ifs <;> norm_num

theorem periodicCellWeight_abs_le (n i : ℕ) (t : ℝ) : |periodicCellWeight n i t| ≤ 1 := by
  rw [abs_of_nonneg (periodicCellWeight_mem n i t).1]
  exact (periodicCellWeight_mem n i t).2

theorem intervalIntegral_indicator_subinterval (q : ℝ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ t in (0 : ℝ)..2, (Ioc a b).indicator q t) = ∫ t in a..b, q t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc a b ⊆ Ioc (0 : ℝ) 2 from
      fun t ht => ⟨lt_of_le_of_lt ha ht.1, ht.2.trans hb⟩),
    intervalIntegral.integral_of_le hab]

/-- The exact one-cell coefficient-to-integral bridge. -/
theorem periodicCellWeight_integral (q : ℝ → ℝ) {n i : ℕ}
    (hn : 0 < n) (hi : i < n) :
    (∫ t in (0 : ℝ)..2, periodicCellWeight n i t * q t) = gridIntegral q n i := by
  have hw := (gridWidth_pos hn).le
  have ha : 0 ≤ (i : ℝ) * gridWidth n := mul_nonneg (Nat.cast_nonneg _) hw
  have hab : (i : ℝ) * gridWidth n ≤ ((i : ℝ) + 1) * gridWidth n := by nlinarith
  have hb : ((i : ℝ) + 1) * gridWidth n ≤ 2 := by
    have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hi)
    have hm := mul_le_mul_of_nonneg_right hin hw
    rwa [gridWidth_mul hn] at hm
  calc
    _ = ∫ t in (0 : ℝ)..2,
        (Ioc ((i : ℝ) * gridWidth n) (((i : ℝ) + 1) * gridWidth n)).indicator q t := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
      dsimp only [periodicCellWeight]
      rw [periodicDensity_eq ⟨ht.1.le, ht.2⟩]
      by_cases hc : t ∈ Ioc ((i : ℝ) * gridWidth n) (((i : ℝ) + 1) * gridWidth n)
      · simp only [indicator_of_mem hc, one_mul]
      · simp only [indicator_of_notMem hc, zero_mul]
    _ = _ := intervalIntegral_indicator_subinterval q ha hab hb

theorem squarePairing_periodicCellWeight {h : ℝ → ℝ} (hh : Admissible h)
    {n i : ℕ} (hn : 0 < n) (hi : i < n) :
    squarePairing h (periodicCellWeight n i) = gridIntegral (periodicOverlap h) n i := by
  rw [← periodicOverlap_pairing_eq_squarePairing hh
    (periodicCellWeight_measurable n i) (periodicCellWeight_abs_le n i)
    (periodicCellWeight_periodic n i), periodicCellWeight_integral _ hn hi]

/-- The exact unsymmetrized dilation row. Its coefficient is `1/(k*h)`;
the target cells are read modulo `n`, with multiplicity. -/
@[expose] def periodicDilationWeight (n k i : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) * gridWidth n)⁻¹ *
    ∑ j ∈ Finset.range k, periodicCellWeight n ((k * i + j) % n) t

@[expose] def periodicDilationKernel (n k i : ℕ) : ℝ → ℝ :=
  symmetrizeWeight (periodicDilationWeight n k i)

theorem periodicDilationWeight_measurable (n k i : ℕ) :
    Measurable (periodicDilationWeight n k i) :=
  measurable_const.mul ((Finset.range k).measurable_sum
    (fun j _ => periodicCellWeight_measurable n ((k * i + j) % n)))

theorem periodicDilationWeight_bound (n k i : ℕ) (t : ℝ) :
    |periodicDilationWeight n k i t| ≤ |((k : ℝ) * gridWidth n)⁻¹| * (k : ℝ) := by
  unfold periodicDilationWeight
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ ∑ j ∈ Finset.range k, |periodicCellWeight n ((k * i + j) % n) t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ => periodicCellWeight_abs_le n ((k * i + j) % n) t)
    _ = _ := by simp

theorem periodicDilationWeight_periodic (n k i : ℕ) :
    Periodic (periodicDilationWeight n k i) 2 := by
  intro t
  unfold periodicDilationWeight
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact periodicCellWeight_periodic n ((k * i + j) % n) t

theorem squarePairing_periodicDilationWeight {h : ℝ → ℝ} (hh : Admissible h)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : ℕ) :
    squarePairing h (periodicDilationWeight n k i) =
      (gridWidth n)⁻¹ *
        ∫ t in (i : ℝ) * gridWidth n..((i : ℝ) + 1) * gridWidth n,
          periodicOverlap h ((k : ℝ) * t) := by
  rw [← periodicOverlap_pairing_eq_squarePairing hh
    (periodicDilationWeight_measurable n k i) (periodicDilationWeight_bound n k i)
    (periodicDilationWeight_periodic n k i)]
  have heq : (fun t => periodicDilationWeight n k i t * periodicOverlap h t) =
      fun t => ((k : ℝ) * gridWidth n)⁻¹ *
        ∑ j ∈ Finset.range k, periodicCellWeight n ((k * i + j) % n) t * periodicOverlap h t := by
    funext t
    simp only [periodicDilationWeight, mul_assoc, Finset.sum_mul]
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun j _ =>
      periodicOverlap_weighted_intervalIntegrable hh
        (periodicCellWeight_measurable n ((k * i + j) % n))
        (periodicCellWeight_abs_le n ((k * i + j) % n)) 0 2)]
  simp_rw [periodicCellWeight_integral _ hn (Nat.mod_lt _ hn)]
  rw [integral_dilate_gridCell (periodicOverlap_periodic h)
    (periodicOverlap_intervalIntegrable hh) hn hk]
  rw [mul_inv_rev]
  ring

/-- The native even step kernel has exactly the normalized averaged
periodic overlap as its physical expectation. -/
theorem quartetFunctional_periodicDilationKernel {h : ℝ → ℝ} (hh : Admissible h)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : ℕ) :
    quartetFunctional h (periodicDilationKernel n k i) =
      (gridWidth n)⁻¹ *
        ∫ t in (i : ℝ) * gridWidth n..((i : ℝ) + 1) * gridWidth n,
          periodicOverlap h ((k : ℝ) * t) := by
  unfold periodicDilationKernel
  rw [quartetFunctional_symmetrizeWeight hh
    (periodicDilationWeight_measurable n k i) (periodicDilationWeight_bound n k i)
    (periodicDilationWeight_periodic n k i),
    squarePairing_periodicDilationWeight hh hn hk]

theorem periodic_grid_triangle_row {h : ℝ → ℝ} (hh : Admissible h)
    {n r k : ℕ} (hn : 0 < n) (hr : 0 < r) (hrk : r < k) (i : ℕ) :
    quartetFunctional h (periodicDilationKernel n k i) -
      quartetFunctional h (periodicDilationKernel n r i) -
      quartetFunctional h (periodicDilationKernel n (k - r) i) ≤ 0 := by
  have hk : 0 < k := hr.trans hrk
  have hkr : 0 < k - r := Nat.sub_pos_of_lt hrk
  rw [quartetFunctional_periodicDilationKernel hh hn hk,
    quartetFunctional_periodicDilationKernel hh hn hr,
    quartetFunctional_periodicDilationKernel hh hn hkr]
  have hab : (i : ℝ) * gridWidth n ≤ ((i : ℝ) + 1) * gridWidth n := by
    nlinarith [gridWidth_pos hn]
  have hle := periodicOverlap_averaged_triangle hh (r : ℝ) (k : ℝ) hab
  have hcast : ((k - r : ℕ) : ℝ) = (k : ℝ) - (r : ℝ) := Nat.cast_sub hrk.le
  rw [hcast]
  have hm := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (gridWidth_pos hn).le)
  nlinarith

theorem periodic_grid_perimeter_row {h : ℝ → ℝ} (hh : Admissible h)
    {n r k : ℕ} (hn : 0 < n) (hr : 0 < r) (hrk : r < k) (i : ℕ) :
    quartetFunctional h (periodicDilationKernel n r i) +
      quartetFunctional h (periodicDilationKernel n (k - r) i) +
      quartetFunctional h (periodicDilationKernel n k i) ≤ 2 := by
  have hk : 0 < k := hr.trans hrk
  have hkr : 0 < k - r := Nat.sub_pos_of_lt hrk
  rw [quartetFunctional_periodicDilationKernel hh hn hr,
    quartetFunctional_periodicDilationKernel hh hn hkr,
    quartetFunctional_periodicDilationKernel hh hn hk]
  have hab : (i : ℝ) * gridWidth n ≤ ((i : ℝ) + 1) * gridWidth n := by
    nlinarith [gridWidth_pos hn]
  have hle := periodicOverlap_averaged_perimeter hh (r : ℝ) (k : ℝ) hab
  have hcast : ((k - r : ℕ) : ℝ) = (k : ℝ) - (r : ℝ) := Nat.cast_sub hrk.le
  rw [hcast]
  have hm := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (gridWidth_pos hn).le)
  have hinv := inv_mul_cancel₀ (ne_of_gt (gridWidth_pos hn))
  nlinarith

theorem periodic_grid_triangle_multiplier {h : ℝ → ℝ} (hh : Admissible h)
    {n r k : ℕ} (hn : 0 < n) (hr : 0 < r) (hrk : r < k) (i : ℕ)
    {z : ℝ} (hz : z ≤ 0) :
    0 ≤ z * (quartetFunctional h (periodicDilationKernel n k i) -
      quartetFunctional h (periodicDilationKernel n r i) -
      quartetFunctional h (periodicDilationKernel n (k - r) i)) :=
  mul_nonneg_of_nonpos_of_nonpos hz (periodic_grid_triangle_row hh hn hr hrk i)

theorem periodic_grid_perimeter_multiplier {h : ℝ → ℝ} (hh : Admissible h)
    {n r k : ℕ} (hn : 0 < n) (hr : 0 < r) (hrk : r < k) (i : ℕ)
    {z : ℝ} (hz : z ≤ 0) :
    2 * z ≤ z * (quartetFunctional h (periodicDilationKernel n r i) +
      quartetFunctional h (periodicDilationKernel n (k - r) i) +
      quartetFunctional h (periodicDilationKernel n k i)) := by
  have hle := mul_le_mul_of_nonpos_left (periodic_grid_perimeter_row hh hn hr hrk i) hz
  simpa only [mul_comm z 2] using hle

end
end
end ErdosOverlap
