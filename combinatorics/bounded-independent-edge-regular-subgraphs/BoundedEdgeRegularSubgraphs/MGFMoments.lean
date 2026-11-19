module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# First and second moments from a finite exponential bound
-/

public section

open Filter
open scoped BigOperators Topology

namespace BoundedEdgeRegularSubgraphs

private theorem one_add_half_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (fun (j : ℕ) _ ↦ div_nonneg (Even.pow_nonneg (even_two_mul j) x) (by positivity))
  rw [← Real.cosh_eq_tsum] at h
  simpa [Finset.sum_range_succ] using h

/-- A Gaussian exponential bound for a finite population forces zero mean
and the corresponding bound on its second moment. -/
theorem moments_of_sum_exp_le {α : Type*} (S : Finset α) (z : α → ℝ) {v : ℝ}
    (h : ∀ u : ℝ, (∑ i ∈ S, Real.exp (u * z i)) ≤ (S.card : ℝ) * Real.exp (v * u ^ 2 / 2)) :
    (∑ i ∈ S, z i) = 0 ∧ (∑ i ∈ S, z i ^ 2) ≤ (S.card : ℝ) * v := by
  let m : ℝ := S.card
  let F (u : ℝ) := m * Real.exp (v * u ^ 2 / 2) - ∑ i ∈ S, Real.exp (u * z i)
  have hF₀ : F 0 = 0 := by simp [F, m]
  have hmin : IsLocalMin F 0 := Filter.Eventually.of_forall (fun u ↦
    hF₀.trans_le (sub_nonneg.mpr (h u)))
  have hF : HasDerivAt F (-(∑ i ∈ S, z i)) 0 := by
    have hfirst : HasDerivAt (fun u : ℝ ↦ m * Real.exp (v * u ^ 2 / 2)) 0 0 := by
      have hd₀ : HasDerivAt (fun u : ℝ ↦ v * u ^ 2 / 2) 0 0 := by
        simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_mul v).div_const (2 : ℝ)
      simpa [Function.comp_apply] using
        ((Real.hasDerivAt_exp (v * 0 ^ 2 / 2)).comp (0 : ℝ) hd₀).const_mul m
    have hsum : HasDerivAt (fun u : ℝ ↦ ∑ i ∈ S, Real.exp (u * z i)) (∑ i ∈ S, z i) 0 := by
      apply HasDerivAt.fun_sum
      intro i _
      have hd : HasDerivAt (fun u : ℝ ↦ u * z i) (z i) 0 := by
        simpa only [one_mul, id_eq] using (hasDerivAt_id (0 : ℝ)).mul_const (z i)
      change HasDerivAt (Real.exp ∘ fun u : ℝ ↦ u * z i) (z i) 0
      simpa only [zero_mul, Real.exp_zero, one_mul] using
        (Real.hasDerivAt_exp (0 * z i)).comp (0 : ℝ) hd
    change HasDerivAt ((fun u : ℝ ↦ m * Real.exp (v * u ^ 2 / 2)) -
      (fun u : ℝ ↦ ∑ i ∈ S, Real.exp (u * z i))) _ 0
    simpa only [zero_sub] using hfirst.sub hsum
  constructor
  · exact neg_eq_zero.mp (hF.deriv.symm.trans hmin.deriv_eq_zero)
  let Q := ∑ i ∈ S, z i ^ 2
  have hcos (u : ℝ) : (∑ i ∈ S, Real.cosh (u * z i)) ≤ m * Real.exp (v * u ^ 2 / 2) := by
    simp_rw [Real.cosh_eq, ← neg_mul]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    have h₁ := h u
    have h₂ := h (-u)
    rw [neg_sq] at h₂
    linarith only [h₁, h₂]
  have hlower (u : ℝ) : m + (u ^ 2 / 2) * Q ≤ ∑ i ∈ S, Real.cosh (u * z i) := by
    have hs := Finset.sum_le_sum (s := S) (fun i _ ↦ one_add_half_sq_le_cosh (u * z i))
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, mul_pow,
      mul_div_right_comm, ← Finset.mul_sum] at hs
    exact hs
  let G (t : ℝ) := m * (Real.exp (v * t / 2) - 1)
  have hq (t : ℝ) (ht : 0 < t) : Q / 2 ≤ G t / t := by
    have hh := (hlower (Real.sqrt t)).trans (hcos (Real.sqrt t))
    rw [Real.sq_sqrt ht.le] at hh
    apply (le_div_iff₀ ht).mpr
    dsimp only [G]
    nlinarith only [hh]
  have hderiv : HasDerivAt G (m * (v / 2)) 0 := by
    have hs : HasDerivAt (fun t : ℝ ↦ v * t / 2) (v / 2) 0 := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id (0 : ℝ)).const_mul v).div_const (2 : ℝ)
    have he := (Real.hasDerivAt_exp (v * 0 / 2)).comp (0 : ℝ) hs
    simpa [G, Function.comp_apply] using (he.sub_const 1).const_mul m
  have hG₀ : G 0 = 0 := by simp [G]
  have hlim : Tendsto (fun t ↦ G t / t) (𝓝[>] (0 : ℝ)) (𝓝 (m * (v / 2))) := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ :=
      fun _ ht ↦ Set.mem_compl_singleton_iff.mpr (ne_of_gt ht)
    have hh := hderiv.tendsto_slope_zero.mono_left (nhdsWithin_mono (0 : ℝ) hsub)
    simpa only [zero_add, hG₀, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh
  have hmem : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
  have hlimit : Q / 2 ≤ m * (v / 2) :=
    ge_of_tendsto hlim (hmem.mono (fun t ht ↦ hq t ht))
  linarith only [hlimit]

end BoundedEdgeRegularSubgraphs
