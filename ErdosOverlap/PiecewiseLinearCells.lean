/-
Copyright (c) 2026. Released under the BSD-3-Clause license.

Exact nodal interpolation and cellwise derivatives for the sparse witnesses.
-/
module

public import ErdosOverlap.PiecewiseLinear

open MeasureTheory Set

namespace ErdosOverlap

public section

noncomputable section

/-- The exact value prescribed at a grid node; absent entries contribute zero. -/
@[expose] def plNodalValue (den : ℕ) (nodes : List PLNode) (k : ℕ) : ℝ :=
  (nodes.map (fun p => if p.index = k then (p.numerator : ℝ) / den else 0)).sum

/-- Computable integer numerator of a nodal value. -/
@[expose] def plNodalNumerator (nodes : List PLNode) (k : ℕ) : ℕ :=
  (nodes.map (fun p => if p.index = k then p.numerator else 0)).sum

theorem plNodalValue_eq_quotient (den : ℕ) (nodes : List PLNode) (k : ℕ) :
    plNodalValue den nodes k = (plNodalNumerator nodes k : ℝ) / den := by
  induction nodes with
  | nil => simp [plNodalValue, plNodalNumerator]
  | cons p ps ih =>
      change (if p.index = k then (p.numerator : ℝ) / den else 0) +
        plNodalValue den ps k =
        (((if p.index = k then p.numerator else 0) + plNodalNumerator ps k : ℕ) : ℝ) / den
      rw [ih, Nat.cast_add]
      by_cases hp : p.index = k
      · simp only [ite_eq_left hp]
        ring
      · simp only [ite_eq_right hp, Nat.cast_zero, zero_add]

/-- Computable exact rational slope of the interpolant on one cell. -/
@[expose] def plCellSlope (n den : ℕ) (nodes : List PLNode) (k : ℕ) : ℚ :=
  (n : ℚ) * ((plNodalNumerator nodes (k + 1) : ℚ) - plNodalNumerator nodes k) / den

theorem plCellSlope_cast (n den : ℕ) (nodes : List PLNode) (k : ℕ) :
    (plCellSlope n den nodes k : ℝ) =
      (n : ℝ) * (plNodalValue den nodes (k + 1) - plNodalValue den nodes k) := by
  rw [plNodalValue_eq_quotient, plNodalValue_eq_quotient]
  unfold plCellSlope
  push_cast
  ring

/-- On a grid cell only its two endpoint tents can contribute. -/
theorem gridTent_eq_on_cell (n i k : ℕ) (t : ℝ)
    (htlo : (k : ℝ) ≤ (n : ℝ) * t)
    (hthi : (n : ℝ) * t ≤ (k : ℝ) + 1) :
    gridTent n i t =
      if i = k then (k : ℝ) + 1 - (n : ℝ) * t
      else if i = k + 1 then (n : ℝ) * t - k else 0 := by
  by_cases hik : i = k
  · subst i
    rw [ite_eq_left rfl]
    unfold gridTent unitTent
    rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    ring
  · rw [ite_eq_right hik]
    by_cases hik1 : i = k + 1
    · subst i
      rw [ite_eq_left rfl]
      unfold gridTent unitTent
      simp only [Nat.cast_add, Nat.cast_one]
      rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    · rw [ite_eq_right hik1]
      apply unitTent_eq_zero_of_one_le_abs
      rcases lt_or_ge i k with hiklo | hikhi
      · have hcast : (i : ℝ) + 1 ≤ k := by exact_mod_cast hiklo
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hkn : k + 2 ≤ i := by omega
        have hcast : (k : ℝ) + 2 ≤ i := by exact_mod_cast hkn
        rw [abs_of_nonpos (by linarith)]
        linarith

/-- The sparse tent representation is precisely linear interpolation of its
nodal values on every cell. This identity also permits endpoint evaluation. -/
theorem plWitness_eq_on_cell (n den : ℕ) (nodes : List PLNode) (k : ℕ) (t : ℝ)
    (htlo : (k : ℝ) ≤ (n : ℝ) * t)
    (hthi : (n : ℝ) * t ≤ (k : ℝ) + 1) :
    plWitness n den nodes t =
      ((k : ℝ) + 1 - (n : ℝ) * t) * plNodalValue den nodes k +
      ((n : ℝ) * t - k) * plNodalValue den nodes (k + 1) := by
  induction nodes with
  | nil => simp [plWitness, plNodalValue]
  | cons p ps ih =>
      change ((p.numerator : ℝ) / den) * gridTent n p.index t + plWitness n den ps t = _
      rw [gridTent_eq_on_cell n p.index k t htlo hthi, ih]
      simp only [plNodalValue, List.map_cons, List.sum_cons]
      by_cases hp : p.index = k
      · have hneq : k ≠ k + 1 := by omega
        simp only [hp, hneq, ite_true, ite_false]
        ring
      · by_cases hp1 : p.index = k + 1
        · have hneq : k + 1 ≠ k := by omega
          simp only [hp1, hneq, ite_false, ite_true]
          ring
        · simp only [hp, hp1, ite_false]
          ring

theorem plWitness_at_grid {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ) :
    plWitness n den nodes ((k : ℝ) / n) = plNodalValue den nodes k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have heq : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
  rw [plWitness_eq_on_cell n den nodes k ((k : ℝ) / n)
    (by rw [heq]) (by rw [heq]; linarith)]
  rw [heq]
  ring

/-- The exact derivative on the open interior of any grid cell. -/
theorem plWitness_hasDerivAt_on_cell {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ) (t : ℝ)
    (htlo : (k : ℝ) < (n : ℝ) * t)
    (hthi : (n : ℝ) * t < (k : ℝ) + 1) :
    HasDerivAt (plWitness n den nodes)
      ((n : ℝ) * (plNodalValue den nodes (k + 1) - plNodalValue den nodes k)) t := by
  let A := plNodalValue den nodes k
  let B := plNodalValue den nodes (k + 1)
  have hder : HasDerivAt
      (fun x : ℝ => (n : ℝ) * (B - A) * x + ((k : ℝ) + 1) * A - k * B)
      ((n : ℝ) * (B - A)) t := by
    convert (((hasDerivAt_id t).const_mul ((n : ℝ) * (B - A))).add_const
      (((k : ℝ) + 1) * A)).sub_const ((k : ℝ) * B) using 1 <;> simp
  apply hder.congr_of_eventuallyEq
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (k : ℝ) / n < t := (div_lt_iff₀ hnreal).mpr (by nlinarith)
  have hhi : t < ((k : ℝ) + 1) / n := (lt_div_iff₀ hnreal).mpr (by nlinarith)
  filter_upwards [Ioo_mem_nhds hlo hhi] with x hx
  have hxlo : (k : ℝ) ≤ (n : ℝ) * x := by
    have h := (div_lt_iff₀ hnreal).mp hx.1
    nlinarith
  have hxhi : (n : ℝ) * x ≤ (k : ℝ) + 1 := by
    have h := (lt_div_iff₀ hnreal).mp hx.2
    nlinarith
  rw [plWitness_eq_on_cell n den nodes k x hxlo hxhi]
  dsimp [A, B]
  ring

theorem plWitness_deriv_on_cell {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ) (t : ℝ)
    (htlo : (k : ℝ) < (n : ℝ) * t)
    (hthi : (n : ℝ) * t < (k : ℝ) + 1) :
    deriv (plWitness n den nodes) t =
      (n : ℝ) * (plNodalValue den nodes (k + 1) - plNodalValue den nodes k) :=
  (plWitness_hasDerivAt_on_cell hn den nodes k t htlo hthi).deriv

/-- The derivative equality holds almost everywhere on the closed cell, so
it can be substituted under real interval integrals without assuming anything
about the classical derivative at the two knots. -/
theorem plWitness_ae_deriv_on_cell {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ) :
    ∀ᵐ t ∂volume,
      t ∈ Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) →
      deriv (plWitness n den nodes) t = (plCellSlope n den nodes k : ℝ) := by
  have hne₀ : ∀ᵐ t : ℝ ∂volume, t ≠ (k : ℝ) / n := by
    simp [ae_iff, measure_singleton]
  have hne₁ : ∀ᵐ t : ℝ ∂volume, t ≠ ((k : ℝ) + 1) / n := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne₀, hne₁] with t ht₀ ht₁
  intro ht
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (k : ℝ) / n < t := lt_of_le_of_ne ht.1 (Ne.symm ht₀)
  have hhi : t < ((k : ℝ) + 1) / n := lt_of_le_of_ne ht.2 ht₁
  have hscaled₀ : (k : ℝ) < (n : ℝ) * t := by
    have hh := (div_lt_iff₀ hnreal).mp hlo
    nlinarith
  have hscaled₁ : (n : ℝ) * t < (k : ℝ) + 1 := by
    have hh := (lt_div_iff₀ hnreal).mp hhi
    nlinarith
  rw [plWitness_deriv_on_cell hn den nodes k t hscaled₀ hscaled₁,
    plCellSlope_cast]

theorem plWitness_ae_dualSlope_on_cell {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ) (τ : ℝ) :
    ∀ᵐ t ∂volume,
      t ∈ Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) →
      dualSlope τ (plWitness n den nodes) t =
        2 * τ + (plCellSlope n den nodes k : ℝ) := by
  filter_upwards [plWitness_ae_deriv_on_cell hn den nodes k] with t ht
  intro hti
  rw [dualSlope, ht hti]

/-- The initial zero block can be handled as one interval, independently of
how many zero grid nodes were omitted from the sparse representation. -/
theorem plWitness_zero_before (n den : ℕ) (nodes : List PLNode) (k : ℕ)
    (hstart : ∀ p ∈ nodes, k + 1 ≤ p.index)
    (t : ℝ) (ht : (n : ℝ) * t ≤ k) : plWitness n den nodes t = 0 := by
  induction nodes with
  | nil => simp [plWitness]
  | cons p ps ih =>
      have hp : (k : ℝ) + 1 ≤ p.index := by
        exact_mod_cast hstart p List.mem_cons_self
      have hps : ∀ q ∈ ps, k + 1 ≤ q.index :=
        fun q hq => hstart q (List.mem_cons_of_mem _ hq)
      have htent : gridTent n p.index t = 0 := by
        apply unitTent_eq_zero_of_one_le_abs
        rw [abs_of_nonpos (by linarith)]
        linarith
      change (p.numerator : ℝ) / den * gridTent n p.index t + plWitness n den ps t = 0
      rw [htent, mul_zero, zero_add, ih hps]

theorem plWitness_hasDerivAt_zero_before {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ)
    (hstart : ∀ p ∈ nodes, k + 1 ≤ p.index)
    (t : ℝ) (ht : (n : ℝ) * t < k) :
    HasDerivAt (plWitness n den nodes) 0 t := by
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : t < (k : ℝ) / n := (lt_div_iff₀ hnreal).mpr (by nlinarith)
  filter_upwards [Iio_mem_nhds hlt] with x hx
  have hscaled : (n : ℝ) * x ≤ k := by
    have hh := (lt_div_iff₀ hnreal).mp hx
    nlinarith
  exact plWitness_zero_before n den nodes k hstart x hscaled

end

end

end ErdosOverlap
