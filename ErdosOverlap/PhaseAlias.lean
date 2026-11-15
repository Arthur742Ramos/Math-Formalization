/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.PeriodicVariance
public import ErdosOverlap.Moment
public import ErdosOverlap.Gram.PhaseCells

/-!
# Physical phase alias and its sharp mean-square constraint

The alias is a finite sum of translates of the actual cumulative contrast.
The proof uses its global Lipschitz bound, exact endpoint telescoping and
an exact tiling of the physical interval; no numerical quadrature enters.
-/

open MeasureTheory Set

namespace ErdosOverlap.Gram

public section
noncomputable section

@[expose] def gridAlias (F : ℝ → ℝ) (N : ℕ) (a m s : ℝ) : ℝ :=
  m - a * ∑ j ∈ Finset.range N, F (s + (j + 1 : ℕ) * a)

@[expose] def phaseAlias (h : ℝ → ℝ) (N : ℕ) (a s : ℝ) : ℝ :=
  gridAlias (primitive h) N a (profileMean (overlapProfile h)) s

@[expose] def weightedCells (h : ℝ → ℝ) (N : ℕ) (a s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), (i : ℝ) * a * cellAverage h a s i

/-- Finite summation by parts, including both partially occupied endpoint cells. -/
theorem sum_weighted_differences (F : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), (i : ℝ) * (F (i + 1) - F i)) =
      (N : ℝ) * F (N + 1) - ∑ j ∈ Finset.range N, F (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

theorem sum_shifted_values (F : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, F j) + F N =
      F 0 + ∑ j ∈ Finset.range N, F (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

theorem translated_sum_abs_sub_le {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    (N : ℕ) (a x y : ℝ) :
    |(∑ j ∈ Finset.range N, F (x + (j + 1 : ℕ) * a)) -
      ∑ j ∈ Finset.range N, F (y + (j + 1 : ℕ) * a)| ≤
      (N : ℝ) * |x - y| := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := hF.dist_le_mul (x + (N + 1 : ℕ) * a) (y + (N + 1 : ℕ) * a)
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, add_sub_add_right_eq_sub] at h
    have htri := abs_add_le
      ((∑ j ∈ Finset.range N, F (x + (j + 1 : ℕ) * a)) -
        ∑ j ∈ Finset.range N, F (y + (j + 1 : ℕ) * a))
      (F (x + (N + 1 : ℕ) * a) - F (y + (N + 1 : ℕ) * a))
    rw [show (∑ j ∈ Finset.range N, F (x + (j + 1 : ℕ) * a)) +
        F (x + (N + 1 : ℕ) * a) -
        ((∑ j ∈ Finset.range N, F (y + (j + 1 : ℕ) * a)) +
          F (y + (N + 1 : ℕ) * a)) =
        ((∑ j ∈ Finset.range N, F (x + (j + 1 : ℕ) * a)) -
          ∑ j ∈ Finset.range N, F (y + (j + 1 : ℕ) * a)) +
        (F (x + (N + 1 : ℕ) * a) - F (y + (N + 1 : ℕ) * a)) by ring]
    push_cast at htri h ih ⊢
    linarith

theorem gridAlias_lipschitz {F : ℝ → ℝ} (hF : LipschitzWith 1 F)
    {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (hNa : (N : ℝ) * a = 2) (m : ℝ) :
    LipschitzWith 2 (gridAlias F N a m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := translated_sum_abs_sub_le hF N a x y
  simp only [gridAlias, Real.dist_eq, NNReal.coe_ofNat]
  rw [show m - a * (∑ j ∈ Finset.range N, F (x + (j + 1 : ℕ) * a)) -
      (m - a * (∑ j ∈ Finset.range N, F (y + (j + 1 : ℕ) * a))) =
      -a * ((∑ j ∈ Finset.range N, F (x + (j + 1 : ℕ) * a)) -
        ∑ j ∈ Finset.range N, F (y + (j + 1 : ℕ) * a)) by ring]
  rw [abs_mul, abs_neg, abs_of_nonneg ha]
  calc
    _ ≤ a * ((N : ℝ) * |x - y|) := mul_le_mul_of_nonneg_left h ha
    _ = 2 * |x - y| := by
      rw [← mul_assoc, mul_comm a (N : ℝ), hNa]

theorem gridAlias_endpoints {F : ℝ → ℝ} {N : ℕ} {a : ℝ}
    (hF0 : F 0 = 0) (hFa : F ((N : ℝ) * a) = 0) (m : ℝ) :
    gridAlias F N a m (-a) = gridAlias F N a m 0 := by
  have hsum := sum_shifted_values (fun j => F ((j : ℝ) * a)) N
  simp only [Nat.cast_zero, zero_mul, hF0, hFa, zero_add, add_zero] at hsum
  dsimp [gridAlias]
  congr 1
  congr 1
  calc
    _ = ∑ j ∈ Finset.range N, F ((j : ℝ) * a) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      push_cast
      ring
    _ = ∑ j ∈ Finset.range N, F (0 + (j + 1 : ℕ) * a) := by
      simpa using hsum

/-- The translated phase cells exactly tile the physical interval. -/
theorem integral_translated_sum {F : ℝ → ℝ} (hF : Continuous F)
    (N : ℕ) (a : ℝ) :
    (∫ s in -a..(0 : ℝ), ∑ j ∈ Finset.range N,
      F (s + (j + 1 : ℕ) * a)) = ∫ t in (0 : ℝ)..((N : ℝ) * a), F t := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsum : IntervalIntegrable
        (fun s => ∑ j ∈ Finset.range N, F (s + (j + 1 : ℕ) * a)) volume (-a) 0 := by
      apply Continuous.intervalIntegrable
      exact continuous_finsetSum _ (fun j _ => hF.comp (continuous_id.add continuous_const))
    have hone : IntervalIntegrable (fun s => F (s + (N + 1 : ℕ) * a)) volume (-a) 0 :=
      (hF.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    simp only [Finset.sum_range_succ]
    rw [intervalIntegral.integral_add hsum hone, ih]
    have hshift : (∫ s in -a..(0 : ℝ), F (s + (N + 1 : ℕ) * a)) =
        ∫ t in ((N : ℝ) * a)..((N + 1 : ℕ) * a), F t := by
      have hc := intervalIntegral.integral_comp_add_right F
        (a := -a) (b := 0) ((N + 1 : ℕ) * a)
      have hl : -a + (N + 1 : ℕ) * a = (N : ℝ) * a := by push_cast; ring
      rw [hl, zero_add] at hc
      convert! hc using 1
    rw [hshift]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable _ _) (hF.intervalIntegrable _ _)

theorem gridAlias_integral_zero {F : ℝ → ℝ} (hF : Continuous F)
    {N : ℕ} {a m : ℝ} (hm : (∫ t in (0 : ℝ)..((N : ℝ) * a), F t) = m) :
    (∫ s in -a..(0 : ℝ), gridAlias F N a m s) = 0 := by
  have hsum : IntervalIntegrable
      (fun s => ∑ j ∈ Finset.range N, F (s + (j + 1 : ℕ) * a)) volume (-a) 0 := by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun j _ => hF.comp (continuous_id.add continuous_const))
  unfold gridAlias
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hsum.const_mul a),
    intervalIntegral.integral_const_mul, integral_translated_sum hF N a, hm]
  simp

/-- The cumulative contrast and its reflection recover the physical odd profile. -/
theorem primitive_reflection_sum {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    primitive h t + primitive h (2 - t) = 2 * overlapProfile h t := by
  have htr : 2 - t ∈ Icc (0 : ℝ) 2 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [primitive_eq_on_support hh ht, primitive_eq_on_support hh htr,
    overlapProfile_cumulative hh ht]
  ring

/-- The alias uses the same physical mean as the overlap certificate. -/
theorem integral_primitive_eq_profileMean {h : ℝ → ℝ} (hh : Admissible h) :
    (∫ t in (0 : ℝ)..2, primitive h t) = profileMean (overlapProfile h) := by
  have hc := primitive_continuous hh
  have hi01 := hc.intervalIntegrable (μ := volume) 0 1
  have hi12 := hc.intervalIntegrable (μ := volume) 1 2
  have hir : IntervalIntegrable (fun t => primitive h (2 - t)) volume 0 1 :=
    (hc.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hreflect : (∫ t in (1 : ℝ)..2, primitive h t) =
      ∫ t in (0 : ℝ)..1, primitive h (2 - t) := by
    convert! (intervalIntegral.integral_comp_sub_left
      (primitive h) (a := 0) (b := 1) 2).symm using 1
    norm_num
  calc
    _ = (∫ t in (0 : ℝ)..1, primitive h t) +
        (∫ t in (1 : ℝ)..2, primitive h t) :=
      (intervalIntegral.integral_add_adjacent_intervals hi01 hi12).symm
    _ = ∫ t in (0 : ℝ)..1, primitive h t + primitive h (2 - t) := by
      rw [hreflect, intervalIntegral.integral_add hi01 hir]
    _ = ∫ t in (0 : ℝ)..1, 2 * overlapProfile h t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact primitive_reflection_sum hh ⟨ht.1, by linarith [ht.2]⟩
    _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl

theorem phaseAlias_lipschitz {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (hNa : (N : ℝ) * a = 2) :
    LipschitzWith 2 (phaseAlias h N a) :=
  gridAlias_lipschitz (primitive_lipschitz hh) ha hNa _

theorem phaseAlias_endpoints {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (hNa : (N : ℝ) * a = 2) :
    phaseAlias h N a (-a) = phaseAlias h N a 0 := by
  apply gridAlias_endpoints (primitive_zero h)
  rw [hNa, primitive_two hh]

theorem phaseAlias_integral_zero {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (hNa : (N : ℝ) * a = 2) :
    (∫ s in -a..(0 : ℝ), phaseAlias h N a s) = 0 := by
  apply gridAlias_integral_zero (primitive_continuous hh)
  rw [hNa]
  exact integral_primitive_eq_profileMean hh

/-- Exact sharp variance of the physical phase alias. -/
theorem phaseAlias_variance {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2) :
    (∫ s in -a..(0 : ℝ), phaseAlias h N a s ^ 2) / a ≤ a ^ 2 / 12 :=
  closedLoop_alias_variance_shifted ha (phaseAlias_lipschitz hh ha.le hNa)
    (phaseAlias_endpoints hh hNa) (phaseAlias_integral_zero hh hNa)

theorem weightedCells_continuous {h : ℝ → ℝ} (hh : Admissible h)
    (N : ℕ) (a : ℝ) : Continuous (weightedCells h N a) := by
  unfold weightedCells
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (cellAverage_continuous hh a i)

/-- The error term has the required plus-mean normalization. -/
theorem phaseAlias_eq_weightedCells {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a s : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2)
    (hs : s ∈ Icc (-a) 0) :
    phaseAlias h N a s = a * weightedCells h N a s + profileMean (overlapProfile h) := by
  have hend : primitive h (s + (N + 1 : ℕ) * a) = 0 := by
    apply primitive_eq_zero_of_two_le hh
    push_cast
    nlinarith [hs.1, hNa]
  have hsum := sum_weighted_differences (fun i => primitive h (s + (i : ℝ) * a)) N
  rw [hend, mul_zero, zero_sub] at hsum
  have hnormalize : weightedCells h N a s =
      ∑ i ∈ Finset.range (N + 1), (i : ℝ) *
        (primitive h (s + (i + 1 : ℕ) * a) - primitive h (s + (i : ℝ) * a)) := by
    unfold weightedCells cellAverage
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  unfold phaseAlias gridAlias
  rw [hnormalize, hsum]
  ring

theorem weightedCells_integral {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2) :
    (∫ s in -a..(0 : ℝ), weightedCells h N a s) = -profileMean (overlapProfile h) := by
  have hi := (weightedCells_continuous hh N a).intervalIntegrable (μ := volume) (-a) 0
  have heq : (∫ s in -a..(0 : ℝ), phaseAlias h N a s) =
      a * (∫ s in -a..(0 : ℝ), weightedCells h N a s) +
        a * profileMean (overlapProfile h) := by
    calc
      _ = ∫ s in -a..(0 : ℝ), a * weightedCells h N a s + profileMean (overlapProfile h) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : -a ≤ (0 : ℝ))] at hs
        exact phaseAlias_eq_weightedCells hh ha hNa hs
      _ = _ := by
        rw [intervalIntegral.integral_add (hi.const_mul a) intervalIntegrable_const,
          intervalIntegral.integral_const_mul]
        simp
  rw [phaseAlias_integral_zero hh hNa] at heq
  nlinarith [ha]

/-- Exact expansion of the physical phase error, using its zero mean. -/
theorem phaseAlias_square_integral {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2) :
    (∫ s in -a..(0 : ℝ), phaseAlias h N a s ^ 2) =
      a ^ 2 * (∫ s in -a..(0 : ℝ), weightedCells h N a s ^ 2) -
        a * profileMean (overlapProfile h) ^ 2 := by
  let m := profileMean (overlapProfile h)
  have hc := weightedCells_continuous hh N a
  have hi := hc.intervalIntegrable (μ := volume) (-a) 0
  have hi₂ : IntervalIntegrable (fun s : ℝ => weightedCells h N a s ^ 2) volume (-a) 0 := by
    convert! (hc.pow 2).intervalIntegrable (μ := volume) (-a) 0 using 1
  calc
    _ = ∫ s in -a..(0 : ℝ),
        (a ^ 2 * weightedCells h N a s ^ 2 + (2 * a * m) * weightedCells h N a s) + m ^ 2 := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by linarith : -a ≤ (0 : ℝ))] at hs
      change phaseAlias h N a s ^ 2 = _
      rw [phaseAlias_eq_weightedCells hh ha hNa hs]
      dsimp [m]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((hi₂.const_mul (a ^ 2)).add (hi.const_mul (2 * a * m)))
          intervalIntegrable_const,
        intervalIntegral.integral_add (hi₂.const_mul (a ^ 2)) (hi.const_mul (2 * a * m)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        weightedCells_integral hh ha hNa]
      simp only [intervalIntegral.integral_const, sub_neg_eq_add, zero_add, smul_eq_mul]
      dsimp [m]
      ring

/-- The sharp phase Gram mean constraint for every measurable admissible partition. -/
theorem weightedCells_meanSquare_le {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2) :
    (∫ s in -a..(0 : ℝ), weightedCells h N a s ^ 2) / a ≤
      1 / 12 + (profileMean (overlapProfile h) / a) ^ 2 := by
  have hv := phaseAlias_variance hh ha hNa
  have hsq := phaseAlias_square_integral hh ha hNa
  rw [hsq] at hv
  have ha₂ : 0 < a ^ 2 := sq_pos_of_pos ha
  have hv' := (div_le_iff₀ ha).mp hv
  apply (div_le_iff₀ ha).mpr
  have hmul : a ^ 2 * (∫ s in -a..(0 : ℝ), weightedCells h N a s ^ 2) ≤
      a ^ 2 * ((1 / 12 + (profileMean (overlapProfile h) / a) ^ 2) * a) := by
    have halgebra : a ^ 2 * ((1 / 12 + (profileMean (overlapProfile h) / a) ^ 2) * a) =
        a ^ 3 / 12 + a * profileMean (overlapProfile h) ^ 2 := by
      field_simp
    rw [halgebra]
    nlinarith
  exact (mul_le_mul_iff_of_pos_left ha₂).mp hmul

theorem sum_differences (F : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N, (F (i + 1) - F i)) = F N - F 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- The phase cell vector is exactly orthogonal to the constant vector. -/
theorem sum_cellAverage_eq_zero {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a s : ℝ} (hNa : (N : ℝ) * a = 2) (hs : s ∈ Icc (-a) 0) :
    (∑ i ∈ Finset.range (N + 1), cellAverage h a s i) = 0 := by
  have hend : primitive h (s + (N + 1 : ℕ) * a) = 0 := by
    apply primitive_eq_zero_of_two_le hh
    push_cast
    linarith [hs.1, hNa]
  have hstart : primitive h (s + (0 : ℝ) * a) = 0 := by
    simp only [zero_mul, add_zero]
    exact primitive_eq_zero_of_nonpos h hs.2
  unfold cellAverage
  rw [← Finset.sum_div, sum_differences (fun i => primitive h (s + (i : ℝ) * a))]
  rw [hend]
  simp only [Nat.cast_zero, hstart, sub_self, zero_div]

theorem sum_fin_cellAverage_eq_zero {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a s : ℝ} (hNa : (N : ℝ) * a = 2) (hs : s ∈ Icc (-a) 0) :
    (∑ i : Fin (N + 1), cellAverage h a s i.val) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_cellAverage_eq_zero hh hNa hs

theorem weightedCells_eq_fin (h : ℝ → ℝ) (N : ℕ) (a s : ℝ) :
    weightedCells h N a s =
      ∑ i : Fin (N + 1), (i.val : ℝ) * a * cellAverage h a s i.val := by
  exact (Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (i : ℝ) * a * cellAverage h a s i) (n := N + 1)).symm

theorem fin_weightedCells_meanSquare_le {h : ℝ → ℝ} (hh : Admissible h)
    {N : ℕ} {a : ℝ} (ha : 0 < a) (hNa : (N : ℝ) * a = 2) :
    (∫ s in -a..(0 : ℝ),
      (∑ i : Fin (N + 1), (i.val : ℝ) * a * cellAverage h a s i.val) ^ 2) / a ≤
      1 / 12 + (profileMean (overlapProfile h) / a) ^ 2 := by
  simp_rw [← weightedCells_eq_fin]
  exact weightedCells_meanSquare_le hh ha hNa

end
end
end ErdosOverlap.Gram
