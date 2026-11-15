/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.PhaseCells
public import ErdosOverlap.Gram.TriangleAssembly
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Physical phase covariance constraints

The covariance entries are exact averages over the grid origin. Their box and
triangle inequalities follow from the actual measurable partition through the
continuous cell averages defined in `PhaseCells`.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open MeasureTheory Set
open scoped Interval BigOperators

noncomputable def covariance (h : ℝ → ℝ) (a : ℝ) (i j : ℕ) : ℝ :=
  (∫ s in (-a)..0, cellAverage h a s i * cellAverage h a s j) / a

theorem covariance_symmetric (h : ℝ → ℝ) (a : ℝ) (i j : ℕ) :
    covariance h a i j = covariance h a j i := by
  unfold covariance
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact mul_comm _ _

theorem cellProduct_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    (a u v : ℝ) (i j : ℕ) :
    IntervalIntegrable (fun s => cellAverage h a s i * cellAverage h a s j) volume u v :=
  ((cellAverage_continuous hh a i).mul (cellAverage_continuous hh a j)).intervalIntegrable _ _

theorem covariance_diagonal_le_one {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) (i : ℕ) : covariance h a i i ≤ 1 := by
  unfold covariance
  apply (div_le_one ha).mpr
  calc
    _ ≤ ∫ _s in (-a)..(0 : ℝ), (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (cellProduct_intervalIntegrable hh _ _ _ _ _) intervalIntegrable_const
      intro s hs
      have hb := abs_le.mp (cellAverage_abs_le_one hh ha s i)
      nlinarith [sq_nonneg (cellAverage h a s i)]
    _ = a := by simp

/-- The elementary cube triangle inequality, proved without an extremum or
vertex enumeration premise. -/
theorem cube_triangle (x y z : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) :
    x * y + y * z - x * z ≤ 1 := by
  rcases abs_le.mp hx with ⟨hx0, hx1⟩
  rcases abs_le.mp hy with ⟨hy0, hy1⟩
  rcases abs_le.mp hz with ⟨hz0, hz1⟩
  have h0 : 0 ≤ (1-y)*(1+x)*(1+z) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h1 : 0 ≤ (1+y)*(1-x)*(1-z) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  nlinarith

theorem Triangle.cell_bound {n : ℕ} (t : Triangle n) (ht : t.Valid)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    (t.s0 : ℝ) * (x t.i * x t.j) + (t.s1 : ℝ) * (x t.j * x t.k) +
      (t.s2 : ℝ) * (x t.i * x t.k) ≤ 1 := by
  rcases ht with ⟨_, _, _, hs | hs | hs | hs⟩
  · rcases hs with ⟨h0, h1, h2⟩
    simp only [h0, h1, h2, Int.cast_one, Int.cast_neg, one_mul, neg_mul]
    have h := cube_triangle (x t.i) (x t.j) (x t.k) (hx _) (hx _) (hx _)
    linarith
  · rcases hs with ⟨h0, h1, h2⟩
    simp only [h0, h1, h2, Int.cast_one, Int.cast_neg, one_mul, neg_mul]
    have h := cube_triangle (x t.j) (x t.i) (x t.k) (hx _) (hx _) (hx _)
    nlinarith
  · rcases hs with ⟨h0, h1, h2⟩
    simp only [h0, h1, h2, Int.cast_one, Int.cast_neg, one_mul, neg_mul]
    have h := cube_triangle (x t.i) (x t.k) (x t.j) (hx _) (hx _) (hx _)
    nlinarith
  · rcases hs with ⟨h0, h1, h2⟩
    simp only [h0, h1, h2, Int.cast_one, Int.cast_neg, one_mul, neg_mul]
    have h := cube_triangle (x t.i) (-(x t.j)) (x t.k) (hx _)
      (by simpa only [abs_neg] using hx t.j) (hx _)
    nlinarith

theorem Triangle.covariance_bound {n : ℕ} (t : Triangle n) (ht : t.Valid)
    {h : ℝ → ℝ} (hh : Admissible h) {a : ℝ} (ha : 0 < a) :
    (t.s0 : ℝ) * covariance h a t.i.val t.j.val +
      (t.s1 : ℝ) * covariance h a t.j.val t.k.val +
      (t.s2 : ℝ) * covariance h a t.i.val t.k.val ≤ 1 := by
  let f0 := fun s => (t.s0 : ℝ) * (cellAverage h a s t.i.val * cellAverage h a s t.j.val)
  let f1 := fun s => (t.s1 : ℝ) * (cellAverage h a s t.j.val * cellAverage h a s t.k.val)
  let f2 := fun s => (t.s2 : ℝ) * (cellAverage h a s t.i.val * cellAverage h a s t.k.val)
  have h0 : IntervalIntegrable f0 volume (-a) 0 :=
    (cellProduct_intervalIntegrable hh _ _ _ _ _).const_mul _
  have h1 : IntervalIntegrable f1 volume (-a) 0 :=
    (cellProduct_intervalIntegrable hh _ _ _ _ _).const_mul _
  have h2 : IntervalIntegrable f2 volume (-a) 0 :=
    (cellProduct_intervalIntegrable hh _ _ _ _ _).const_mul _
  have hb : (∫ s in (-a)..0, f0 s + f1 s + f2 s) ≤ a := by
    calc
      _ ≤ ∫ _s in (-a)..(0 : ℝ), (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by linarith) ((h0.add h1).add h2)
          intervalIntegrable_const
        intro s hs
        exact t.cell_bound ht (fun i => cellAverage h a s i.val)
          (fun i => cellAverage_abs_le_one hh ha s i.val)
      _ = a := by simp
  have heq : (∫ s in (-a)..0, f0 s + f1 s + f2 s) / a =
      (t.s0 : ℝ) * covariance h a t.i.val t.j.val +
        (t.s1 : ℝ) * covariance h a t.j.val t.k.val +
        (t.s2 : ℝ) * covariance h a t.i.val t.k.val := by
    rw [intervalIntegral.integral_add (h0.add h1) h2, intervalIntegral.integral_add h0 h1]
    simp only [f0, f1, f2, covariance, intervalIntegral.integral_const_mul]
    ring
  rw [← heq]
  exact (div_le_one ha).mpr hb

theorem cellAverage_first_abs_le {h : ℝ → ℝ} (hh : Admissible h)
    {a s : ℝ} (ha : 0 < a) (hs : s ∈ Icc (-a) 0) :
    |cellAverage h a s 0| ≤ (s+a)/a := by
  have hl := (primitive_lipschitz hh).dist_le_mul (s+a) 0
  simp only [Real.dist_eq, primitive_zero, sub_zero, NNReal.coe_one, one_mul] at hl
  rw [abs_of_nonneg (by linarith [hs.1] : 0 ≤ s+a)] at hl
  unfold cellAverage
  simp only [Nat.cast_zero, Nat.zero_add, Nat.cast_one, one_mul, zero_mul, add_zero,
    primitive_eq_zero_of_nonpos h hs.2, sub_zero, abs_div, abs_of_pos ha]
  exact (div_le_div_iff_of_pos_right ha).mpr hl

theorem cellAverage_last_abs_le {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a s : ℝ} (ha : 0 < a) (hNa : (N : ℝ)*a = 2)
    (hs : s ∈ Icc (-a) 0) : |cellAverage h a s N| ≤ (-s)/a := by
  have hl := (primitive_lipschitz hh).dist_le_mul (s+2) 2
  simp only [Real.dist_eq, primitive_two hh, sub_zero, NNReal.coe_one, one_mul,
    add_sub_cancel_right] at hl
  rw [abs_of_nonpos hs.2] at hl
  have hu : s + (N+1 : ℕ)*a = s+2+a := by push_cast; rw [add_mul, hNa]; ring
  have hlo : s + (N : ℝ)*a = s+2 := by rw [hNa]
  unfold cellAverage
  rw [hu, hlo, primitive_eq_zero_of_two_le hh (by linarith [hs.1]), zero_sub,
    abs_div, abs_neg, abs_of_pos ha]
  exact (div_le_div_iff_of_pos_right ha).mpr hl

theorem phase_first_square_integral {a : ℝ} (ha : a ≠ 0) :
    (∫ s in (-a)..(0 : ℝ), ((s+a)/a)^2) / a = 1/3 := by
  have hshift : (∫ s in (-a)..(0 : ℝ), (s+a)^2) = ∫ u in (0 : ℝ)..a, u^2 := by
    simpa only [neg_add_cancel, zero_add] using
      intervalIntegral.integral_comp_add_right (fun u : ℝ => u^2) (a := -a) (b := 0) a
  simp only [div_pow, intervalIntegral.integral_div]
  rw [hshift, integral_pow]
  norm_num
  field_simp

theorem phase_last_square_integral {a : ℝ} (ha : a ≠ 0) :
    (∫ s in (-a)..(0 : ℝ), ((-s)/a)^2) / a = 1/3 := by
  simp only [div_pow, neg_sq, intervalIntegral.integral_div, integral_pow]
  norm_num
  field_simp

theorem covariance_first_diagonal_le_third {h : ℝ → ℝ} (hh : Admissible h)
    {a : ℝ} (ha : 0 < a) : covariance h a 0 0 ≤ 1/3 := by
  rw [← phase_first_square_integral ha.ne']
  unfold covariance
  apply (div_le_div_iff_of_pos_right ha).mpr
  apply intervalIntegral.integral_mono_on (by linarith)
    (cellProduct_intervalIntegrable hh _ _ _ _ _)
    ((((continuous_id.add_const a).div_const a).pow 2).intervalIntegrable _ _)
  intro s hs
  have hb := cellAverage_first_abs_le hh ha hs
  have hr : 0 ≤ (s+a)/a := div_nonneg (by linarith [hs.1]) ha.le
  have hsq := (sq_le_sq₀ (abs_nonneg (cellAverage h a s 0)) hr).mpr hb
  rw [sq_abs] at hsq
  change cellAverage h a s 0 * cellAverage h a s 0 ≤ ((s+a)/a)^2
  simpa only [pow_two] using hsq

theorem covariance_last_diagonal_le_third {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ)*a = 2) :
    covariance h a N N ≤ 1/3 := by
  rw [← phase_last_square_integral ha.ne']
  unfold covariance
  apply (div_le_div_iff_of_pos_right ha).mpr
  apply intervalIntegral.integral_mono_on (by linarith)
    (cellProduct_intervalIntegrable hh _ _ _ _ _)
    (((continuous_id.neg.div_const a).pow 2).intervalIntegrable _ _)
  intro s hs
  have hb := cellAverage_last_abs_le hh ha hNa hs
  have hr : 0 ≤ (-s)/a := div_nonneg (by linarith [hs.2]) ha.le
  have hsq := (sq_le_sq₀ (abs_nonneg (cellAverage h a s N)) hr).mpr hb
  rw [sq_abs] at hsq
  change cellAverage h a s N * cellAverage h a s N ≤ ((-s)/a)^2
  simpa only [pow_two] using hsq

end ErdosOverlap.Gram
