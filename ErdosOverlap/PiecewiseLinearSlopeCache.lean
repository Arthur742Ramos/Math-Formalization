/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.PiecewiseLinearCells

/-!
# Exact cached dual slopes of sparse piecewise linear witnesses

A cache stores integer numerators of `2*tau + v'` on consecutive grid
cells. Its finite check compares every entry with the actual sparse nodal
data. The initial zero segment has one analytic proof, irrespective of its
number of omitted zero nodes. Leaf applications then use only cached array
lookups and interval containment; they never reevaluate a sparse nodal sum.
-/

@[expose] public section

namespace ErdosOverlap

open MeasureTheory Set

/-- Integer numerator of the exact dual slope, when `tau=tauNumerator/den`. -/
def plDualNumerator (n : ℕ) (nodes : List PLNode) (tauNumerator : ℤ) (k : ℕ) : ℤ :=
  2*tauNumerator + (n : ℤ)*
    ((plNodalNumerator nodes (k+1) : ℤ) - (plNodalNumerator nodes k : ℤ))

theorem plDualNumerator_div_cast (n den : ℕ) (nodes : List PLNode)
    (tauNumerator : ℤ) (k : ℕ) :
    (plDualNumerator n nodes tauNumerator k : ℝ) / (den : ℝ) =
      2*((tauNumerator : ℝ)/(den : ℝ)) + (plCellSlope n den nodes k : ℝ) := by
  simp only [plDualNumerator, plCellSlope, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, Int.cast_sub,
    Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast]
  ring

structure PLSlopeCache where
  firstCell : ℕ
  numerators : Array ℤ

def PLSlopeCache.check (cache : PLSlopeCache) (n : ℕ) (nodes : List PLNode)
    (tauNumerator : ℤ) : Bool :=
  (List.range cache.numerators.size).all (fun j =>
    decide (plDualNumerator n nodes tauNumerator (cache.firstCell+j) =
      cache.numerators.getD j 0))

def PLSlopeCache.value (cache : PLSlopeCache) (den j : ℕ) : ℚ :=
  (cache.numerators.getD j 0 : ℚ) / den

theorem PLSlopeCache.entry_correct (cache : PLSlopeCache) (n : ℕ)
    (nodes : List PLNode) (tauNumerator : ℤ)
    (hcheck : cache.check n nodes tauNumerator = true)
    {j : ℕ} (hj : j < cache.numerators.size) :
    plDualNumerator n nodes tauNumerator (cache.firstCell+j) =
      cache.numerators.getD j 0 := by
  exact of_decide_eq_true (List.all_eq_true.mp hcheck j (List.mem_range.mpr hj))

theorem PLSlopeCache.ae_dualSlope_on_cell (cache : PLSlopeCache)
    {n : ℕ} (hn : 0 < n) (den : ℕ) (nodes : List PLNode) (tauNumerator : ℤ)
    (hcheck : cache.check n nodes tauNumerator = true)
    {j : ℕ} (hj : j < cache.numerators.size) :
    ∀ᵐ t ∂volume,
      t ∈ Icc (((cache.firstCell+j : ℕ) : ℝ)/n)
        ((((cache.firstCell+j : ℕ) : ℝ)+1)/n) →
      dualSlope ((tauNumerator : ℝ)/(den : ℝ)) (plWitness n den nodes) t =
        (cache.value den j : ℝ) := by
  have hc := plWitness_ae_dualSlope_on_cell hn den nodes (cache.firstCell+j)
    ((tauNumerator : ℝ)/(den : ℝ))
  filter_upwards [hc] with t ht
  intro hti
  rw [ht hti, ← plDualNumerator_div_cast,
    cache.entry_correct n nodes tauNumerator hcheck hj]
  simp only [PLSlopeCache.value, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]

theorem PLSlopeCache.ae_dualSlope_on_leaf (cache : PLSlopeCache)
    {n : ℕ} (hn : 0 < n) (den : ℕ) (nodes : List PLNode) (tauNumerator : ℤ)
    (hcheck : cache.check n nodes tauNumerator = true)
    {j : ℕ} (hj : j < cache.numerators.size) {l r : ℝ}
    (hl : (((cache.firstCell+j : ℕ) : ℝ)/n) ≤ l)
    (hr : r ≤ ((((cache.firstCell+j : ℕ) : ℝ)+1)/n)) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope ((tauNumerator : ℝ)/(den : ℝ)) (plWitness n den nodes) t =
        (cache.value den j : ℝ) := by
  have hc := cache.ae_dualSlope_on_cell hn den nodes tauNumerator hcheck hj
  filter_upwards [ae_restrict_of_ae hc, self_mem_ae_restrict measurableSet_Ioo] with t ht hti
  exact ht ⟨hl.trans hti.1.le, hti.2.le.trans hr⟩

/-- Any open leaf wholly before the first tent has exactly the constant dual
slope. In particular a long initial zero block need not be split into cells. -/
theorem plWitness_ae_dualSlope_before {n : ℕ} (hn : 0 < n)
    (den : ℕ) (nodes : List PLNode) (k : ℕ) (tau : ℝ)
    (hstart : ∀ p ∈ nodes, k+1 ≤ p.index) {l r : ℝ}
    (hr : r ≤ (k : ℝ)/n) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope tau (plWitness n den nodes) t = 2*tau := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled : (n : ℝ)*t < k := by
    have hlt := (lt_div_iff₀ hnreal).mp (ht.2.trans_le hr)
    nlinarith
  rw [dualSlope, (plWitness_hasDerivAt_zero_before hn den nodes k hstart t hscaled).deriv]
  ring

end ErdosOverlap
