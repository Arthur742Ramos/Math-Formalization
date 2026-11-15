/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.AffineCompiler
public import ErdosOverlap.KernelAssembly

/-! # Exact affine-jump representations of periodic cells and phase hats -/

namespace ErdosOverlap

open Set
open scoped BigOperators

public section

@[expose] def rationalGridWidth (n : ℕ) : ℚ := 2 / n

theorem cast_rationalGridWidth (n : ℕ) : (rationalGridWidth n : ℝ) = gridWidth n := by
  simp only [rationalGridWidth, gridWidth, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]

@[expose] def cellJumps (n i : ℕ) (weight : ℚ) : List AffineJump :=
  [⟨(i : ℚ) * rationalGridWidth n, weight, 0⟩,
   ⟨((i : ℚ) + 1) * rationalGridWidth n, -weight, 0⟩]

@[expose] noncomputable def positiveCellIndicator (n i : ℕ) : ℝ → ℝ :=
  (Ioc ((i : ℝ) * gridWidth n) (((i : ℝ) + 1) * gridWidth n)).indicator (fun _ => 1)

theorem affineJumpSum_cellJumps {n : ℕ} (hn : 0 < n) (i : ℕ) (weight : ℚ) (t : ℝ) :
    affineJumpSum (cellJumps n i weight) t = (weight : ℝ) * positiveCellIndicator n i t := by
  have hw := gridWidth_pos hn
  have hends : (i : ℝ) * gridWidth n ≤ ((i : ℝ) + 1) * gridWidth n := by nlinarith
  simp only [cellJumps, affineJumpSum, AffineJump.value, Rat.cast_mul, Rat.cast_add,
    Rat.cast_one, Rat.cast_zero, Rat.cast_neg, Rat.cast_natCast, cast_rationalGridWidth,
    zero_mul, add_zero]
  unfold positiveCellIndicator
  by_cases hl : (i : ℝ) * gridWidth n < t
  · by_cases hr : ((i : ℝ) + 1) * gridWidth n < t
    · rw [ite_eq_left hl, ite_eq_left hr, indicator_of_notMem (by intro ht; linarith [ht.2])]
      ring
    · rw [ite_eq_left hl, ite_eq_right hr,
        indicator_of_mem (show t ∈ Ioc ((i : ℝ) * gridWidth n) (((i : ℝ) + 1) * gridWidth n)
          from ⟨hl, le_of_not_gt hr⟩)]
      ring
  · have hr : ¬((i : ℝ) + 1) * gridWidth n < t := by linarith
    rw [ite_eq_right hl, ite_eq_right hr, indicator_of_notMem (by intro ht; exact hl ht.1)]
    ring

theorem periodicCellWeight_eq_positive {n i : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 2) : periodicCellWeight n i t = positiveCellIndicator n i t := by
  unfold periodicCellWeight
  exact periodicDensity_eq ⟨ht.1.le, ht.2⟩

@[expose] def GridRegular (n : ℕ) (t : ℝ) : Prop :=
  t ∈ Ioo (0 : ℝ) 2 ∧ ∀ j : ℕ, t ≠ (j : ℝ) * gridWidth n

theorem ae_gridRegular (n : ℕ) :
    ∀ᵐ t : ℝ, t ∈ Ioo (0 : ℝ) 2 → GridRegular n t := by
  have h : ∀ᵐ t : ℝ, ∀ j : ℕ, t ≠ (j : ℝ) * gridWidth n :=
    MeasureTheory.ae_all_iff.mpr (fun j => MeasureTheory.Measure.ae_ne _ _)
  filter_upwards [h] with t ht hmem
  exact ⟨hmem, ht⟩

/-- Reversal of a grid indicator is exact away from the grid boundary
points. Those points form a countable null set. -/
theorem periodicCellWeight_reflection {n i : ℕ} (hn : 0 < n) (hi : i < n)
    {t : ℝ} (ht : GridRegular n t) :
    periodicCellWeight n i (-t) = positiveCellIndicator n (n - 1 - i) t := by
  let j := n - 1 - i
  have hj : j + i + 1 = n := by dsimp [j]; omega
  have hjr : (j : ℝ) + (i : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hj
  have hleft : (j : ℝ) * gridWidth n = 2 - ((i : ℝ) + 1) * gridWidth n := by
    nlinarith [gridWidth_mul hn]
  have hright : ((j : ℝ) + 1) * gridWidth n = 2 - (i : ℝ) * gridWidth n := by
    nlinarith [gridWidth_mul hn]
  have hshift : periodicCellWeight n i (2 - t) = periodicCellWeight n i (-t) := by
    have heq : 2 - t = -t + 2 := by ring
    rw [heq, periodicCellWeight_periodic]
  rw [← hshift, periodicCellWeight_eq_positive ⟨by linarith [ht.1.2], by linarith [ht.1.1]⟩]
  change positiveCellIndicator n i (2 - t) = positiveCellIndicator n j t
  have hneleft : t ≠ (j : ℝ) * gridWidth n := ht.2 j
  have hneright : t ≠ ((j : ℝ) + 1) * gridWidth n := by
    simpa only [Nat.cast_add, Nat.cast_one] using ht.2 (j + 1)
  have hiff : 2 - t ∈ Ioc ((i : ℝ) * gridWidth n) (((i : ℝ) + 1) * gridWidth n) ↔
      t ∈ Ioc ((j : ℝ) * gridWidth n) (((j : ℝ) + 1) * gridWidth n) := by
    constructor
    · intro hx
      constructor
      · have hle : (j : ℝ) * gridWidth n ≤ t := by linarith [hx.2]
        exact lt_of_le_of_ne hle (Ne.symm hneleft)
      · linarith [hx.1]
    · intro hx
      have hlt : t < ((j : ℝ) + 1) * gridWidth n := lt_of_le_of_ne hx.2 hneright
      constructor <;> linarith [hx.1]
  unfold positiveCellIndicator
  by_cases hm : t ∈ Ioc ((j : ℝ) * gridWidth n) (((j : ℝ) + 1) * gridWidth n)
  · rw [indicator_of_mem hm, indicator_of_mem (hiff.mpr hm)]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun hx => hm (hiff.mp hx))]

@[expose] def dilationJumps (n k i : ℕ) : List AffineJump :=
  let c : ℚ := ((k : ℚ) * rationalGridWidth n)⁻¹ / 2
  (List.range k).flatMap fun j =>
    let index := (k * i + j) % n
    cellJumps n index c ++ cellJumps n (n - 1 - index) c

theorem affineJumpSum_dilationJumps {n k : ℕ} (hn : 0 < n) (_hk : 0 < k)
    (i : ℕ) {t : ℝ} (ht : GridRegular n t) :
    affineJumpSum (dilationJumps n k i) t = periodicDilationKernel n k i t := by
  let c : ℚ := ((k : ℚ) * rationalGridWidth n)⁻¹ / 2
  have heq (j : ℕ) :
      affineJumpSum
        (cellJumps n ((k * i + j) % n) c ++
          cellJumps n (n - 1 - ((k * i + j) % n)) c) t =
        (c : ℝ) * (periodicCellWeight n ((k * i + j) % n) t +
          periodicCellWeight n ((k * i + j) % n) (-t)) := by
    rw [affineJumpSum_append, affineJumpSum_cellJumps hn, affineJumpSum_cellJumps hn,
      ← periodicCellWeight_eq_positive ht.1,
      ← periodicCellWeight_reflection hn (Nat.mod_lt _ hn) ht]
    ring
  unfold dilationJumps
  change affineJumpSum ((List.range k).flatMap (fun j =>
    cellJumps n ((k * i + j) % n) c ++ cellJumps n (n - 1 - ((k * i + j) % n)) c)) t = _
  rw [affineJumpSum_flatMap, sum_list_range_eq_finset]
  simp_rw [heq]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  unfold periodicDilationKernel symmetrizeWeight periodicDilationWeight
  simp only [c, Rat.cast_div, Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, cast_rationalGridWidth]
  ring

@[expose] def PeriodicCellRow.jumps (n : ℕ) (row : PeriodicCellRow) : List AffineJump :=
  (if row.perimeter then
    dilationJumps n row.firstPosition row.cell ++
      dilationJumps n (row.lastPosition - row.firstPosition) row.cell ++
      dilationJumps n row.lastPosition row.cell
  else
    dilationJumps n row.lastPosition row.cell ++
      (dilationJumps n row.firstPosition row.cell).map (AffineJump.scale (-1)) ++
      (dilationJumps n (row.lastPosition - row.firstPosition) row.cell).map (AffineJump.scale (-1)))
    |>.map (AffineJump.scale row.weight)

theorem PeriodicCellRow.jumps_value {n : ℕ} (hn : 0 < n) (row : PeriodicCellRow)
    (hv : row.valid n = true) {t : ℝ} (ht : GridRegular n t) :
    affineJumpSum (row.jumps n) t = row.value n t := by
  have hh : 0 < row.firstPosition ∧ row.firstPosition < row.lastPosition ∧
      row.cell < n ∧ row.weight ≤ 0 := of_decide_eq_true hv
  have hk := hh.1.trans hh.2.1
  have hkr := Nat.sub_pos_of_lt hh.2.1
  unfold PeriodicCellRow.jumps PeriodicCellRow.value
  split_ifs
  all_goals simp only [affineJumpSum_scale, affineJumpSum_append,
    affineJumpSum_dilationJumps hn hh.1 _ ht, affineJumpSum_dilationJumps hn hk _ ht,
    affineJumpSum_dilationJumps hn hkr _ ht, Rat.cast_neg, Rat.cast_one]
  all_goals ring

@[expose] def periodicRowsJumps (n : ℕ) : List PeriodicCellRow → List AffineJump
  | [] => []
  | row :: rest => row.jumps n ++ periodicRowsJumps n rest

theorem periodicRowsJumps_value {n : ℕ} (hn : 0 < n) (rows : List PeriodicCellRow)
    (hv : rows.all (PeriodicCellRow.valid n) = true) {t : ℝ} (ht : GridRegular n t) :
    affineJumpSum (periodicRowsJumps n rows) t = periodicRowsKernel n rows t := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have hv' : row.valid n = true ∧ rest.all (PeriodicCellRow.valid n) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hv
    rw [periodicRowsJumps, affineJumpSum_append, row.jumps_value hn hv'.1 ht, ih hv'.2]
    rfl

theorem phaseHat_eq_ramps {a : ℝ} (ha : 0 < a) (center t : ℝ) :
    phaseHat a center t =
      (max (t - (center - a)) 0 - 2 * max (t - center) 0 +
        max (t - (center + a)) 0) / a := by
  have ha' := ne_of_gt ha
  by_cases hleft : t ≤ center - a
  · have habs : |t - center| = center - t := by
      rw [abs_of_nonpos (by linarith : t - center ≤ 0)]
      ring
    have hratio : 1 ≤ (center - t) / a := (le_div_iff₀ ha).mpr (by linarith)
    unfold phaseHat
    rw [habs, max_eq_right (by linarith : 1 - (center - t) / a ≤ 0),
      max_eq_right (by linarith : t - (center - a) ≤ 0),
      max_eq_right (by linarith : t - center ≤ 0),
      max_eq_right (by linarith : t - (center + a) ≤ 0)]
    simp
  · by_cases hcenter : t ≤ center
    · have habs : |t - center| = center - t := by
        rw [abs_of_nonpos (by linarith : t - center ≤ 0)]
        ring
      have hratio : (center - t) / a ≤ 1 := (div_le_iff₀ ha).mpr (by linarith)
      unfold phaseHat
      rw [habs, max_eq_left (by linarith : 0 ≤ 1 - (center - t) / a),
        max_eq_left (by linarith : 0 ≤ t - (center - a)),
        max_eq_right (by linarith : t - center ≤ 0),
        max_eq_right (by linarith : t - (center + a) ≤ 0)]
      field_simp
      ring
    · by_cases hright : t ≤ center + a
      · have habs : |t - center| = t - center := abs_of_nonneg (by linarith)
        have hratio : (t - center) / a ≤ 1 := (div_le_iff₀ ha).mpr (by linarith)
        unfold phaseHat
        rw [habs, max_eq_left (by linarith : 0 ≤ 1 - (t - center) / a),
          max_eq_left (by linarith : 0 ≤ t - (center - a)),
          max_eq_left (by linarith : 0 ≤ t - center),
          max_eq_right (by linarith : t - (center + a) ≤ 0)]
        field_simp
        ring
      · have habs : |t - center| = t - center := abs_of_nonneg (by linarith)
        have hratio : 1 ≤ (t - center) / a := (le_div_iff₀ ha).mpr (by linarith)
        unfold phaseHat
        rw [habs, max_eq_right (by linarith : 1 - (t - center) / a ≤ 0),
          max_eq_left (by linarith : 0 ≤ t - (center - a)),
          max_eq_left (by linarith : 0 ≤ t - center),
          max_eq_left (by linarith : 0 ≤ t - (center + a))]
        ring

@[expose] def rampJump (center : ℚ) : AffineJump := ⟨center, -center, 1⟩

theorem rampJump_value (center : ℚ) (t : ℝ) :
    (rampJump center).value t = max (t - (center : ℝ)) 0 := by
  unfold rampJump AffineJump.value
  simp only [Rat.cast_neg, Rat.cast_one, one_mul]
  by_cases ht : (center : ℝ) < t
  · rw [ite_eq_left ht, max_eq_left (by linarith : 0 ≤ t - (center : ℝ))]
    ring
  · rw [ite_eq_right ht, max_eq_right (by linarith : t - (center : ℝ) ≤ 0)]

@[expose] def hatJumps (a center weight : ℚ) : List AffineJump :=
  [(rampJump (center - a)).scale (weight / a),
   (rampJump center).scale (-2 * weight / a),
   (rampJump (center + a)).scale (weight / a)]

theorem affineJumpSum_hatJumps {a : ℚ} (ha : 0 < a) (center weight : ℚ) (t : ℝ) :
    affineJumpSum (hatJumps a center weight) t =
      (weight : ℝ) * phaseHat (a : ℝ) (center : ℝ) t := by
  rw [phaseHat_eq_ramps (by exact_mod_cast ha)]
  simp only [hatJumps, affineJumpSum, AffineJump.value_scale, rampJump_value,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat]
  ring

@[expose] def phaseJumps (N : ℕ) (gamma : Array ℚ) : List AffineJump :=
  let a : ℚ := 2 / N
  hatJumps a 0 (gamma.getD 0 0 / a) ++
    (List.range N).flatMap (fun k =>
      hatJumps a ((k + 1 : ℕ) * a) (gamma.getD (k + 1) 0 / (2 * a)))

theorem affineJumpSum_phaseJumps {N : ℕ} (hN : 0 < N) (gamma : Array ℚ)
    {t : ℝ} (ht : 0 ≤ t) :
    affineJumpSum (phaseJumps N gamma) t = phaseKernel N gamma t := by
  have ha : (0 : ℚ) < 2 / N := by positivity
  unfold phaseJumps
  rw [affineJumpSum_append, affineJumpSum_hatJumps ha, affineJumpSum_flatMap,
    sum_list_range_eq_finset]
  simp_rw [affineJumpSum_hatJumps ha]
  unfold phaseKernel
  rw [abs_of_nonneg ht]
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_zero]

@[expose] def PhaseFunctionalRow.jumps (row : PhaseFunctionalRow) : List AffineJump :=
  (phaseJumps row.cells row.gamma).map (AffineJump.scale row.multiplier)

theorem PhaseFunctionalRow.jumps_value (row : PhaseFunctionalRow)
    (hv : row.valid = true) {t : ℝ} (ht : 0 ≤ t) :
    affineJumpSum row.jumps t = row.value t := by
  have hh : 0 < row.cells ∧ row.gamma.size = row.cells + 1 ∧ 0 ≤ row.multiplier :=
    of_decide_eq_true hv
  rw [PhaseFunctionalRow.jumps, affineJumpSum_scale, affineJumpSum_phaseJumps hh.1 row.gamma ht]
  rfl

@[expose] def phaseRowsJumps : List PhaseFunctionalRow → List AffineJump
  | [] => []
  | row :: rest => row.jumps ++ phaseRowsJumps rest

theorem periodicRowsJumps_append (n : ℕ) (as bs : List PeriodicCellRow) :
    periodicRowsJumps n (as ++ bs) = periodicRowsJumps n as ++ periodicRowsJumps n bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, periodicRowsJumps, ih, List.append_assoc]

theorem phaseRowsJumps_append (as bs : List PhaseFunctionalRow) :
    phaseRowsJumps (as ++ bs) = phaseRowsJumps as ++ phaseRowsJumps bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, phaseRowsJumps, ih, List.append_assoc]

@[expose] def compiledPeriodicRows (n : ℕ) (rows : List PeriodicCellRow) : List AffineJump :=
  compiledJumpBlocks (rows.map (fun row => row.jumps n))

theorem periodicRowsJumps_eq_flatten (n : ℕ) (rows : List PeriodicCellRow) :
    periodicRowsJumps n rows = (rows.map (fun row => row.jumps n)).flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [periodicRowsJumps, List.map_cons, List.flatten_cons, ih]

theorem affineJumpSum_compiledPeriodicRows (n : ℕ) (rows : List PeriodicCellRow) (t : ℝ) :
    affineJumpSum (compiledPeriodicRows n rows) t = affineJumpSum (periodicRowsJumps n rows) t := by
  rw [compiledPeriodicRows, affineJumpSum_compiledBlocks, periodicRowsJumps_eq_flatten]

theorem phaseRowsJumps_value (rows : List PhaseFunctionalRow)
    (hv : rows.all PhaseFunctionalRow.valid = true) {t : ℝ} (ht : 0 ≤ t) :
    affineJumpSum (phaseRowsJumps rows) t = phaseRowsKernel rows t := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have hv' : row.valid = true ∧ rest.all PhaseFunctionalRow.valid = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hv
    rw [phaseRowsJumps, affineJumpSum_append, row.jumps_value hv'.1 ht, ih hv'.2]
    rfl

end
end ErdosOverlap
