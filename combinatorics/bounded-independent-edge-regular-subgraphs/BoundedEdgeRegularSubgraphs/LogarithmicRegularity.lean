module

public import BoundedEdgeRegularSubgraphs.LogarithmicFailureRates
public import BoundedEdgeRegularSubgraphs.MeanSquareInducedRegularity
public import BoundedEdgeRegularSubgraphs.OrderEventTransport
public import BoundedEdgeRegularSubgraphs.Theorem11
import Mathlib.Tactic

/-!
# The universal logarithmic lower bound
-/

public section

open Filter MeasureTheory Set Function
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Theorem 5.3. The threshold and the starting size depend only on
the common edge floor. -/
theorem eventually_logarithmic_regular_induced_subgraph {ξ : ℝ} (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ p : Edge (Fin n) → Icc (0 : ℝ) 1, HasFloor ξ p →
        (graphLaw p).real (atLeastOrderEvent ⌈c * Real.log n ^ 2⌉₊)ᶜ ≤ (n : ℝ)⁻¹ := by
  obtain ⟨a₀, μ₀, c, C, ha₀, hμ₀, hc, hC, hMean⟩ :=
    eventually_exactOrder_failure_le_of_meanSquare hξ hξ₁
  let a := c / 384
  have ha : 0 < a := by dsimp only [a]; positivity
  have hac : 192 * a ≤ c / 2 := by dsimp only [a]; linarith
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [eventually_logarithmic_extraction_scale a₀ ha₀,
    eventually_logarithmic_failure_rates ha hc hμ₀ hC hac,
    eventually_logarithmicEvenOrder_bounds ha,
    (tendsto_logarithmicEvenOrder ha).eventually hMean,
    (tendsto_logarithmicEvenOrder ha).eventually_ge_atTop (2 : ℕ),
    eventually_ge_atTop (1 : ℕ)] with n hEx hRates hK hMean' hk hn
  intro p hp
  let L := Real.log n
  let η := Real.sqrt (32 / L)
  let k := logarithmicEvenOrder a n
  obtain ⟨hL, hη, hη₁, hηa, hη₂, hP, hPM⟩ := hEx
  obtain ⟨U, hU, hDrift, hEnergy⟩ := exists_nearBalanced_subdomain p hη hη₁
    (by simpa only [Fintype.card_fin] using hPM)
  let N := U.card
  let q := induce U p
  let f : Fin N ≃o U := U.orderIsoOfFin rfl
  let q' := q ∘ edgeEquiv f
  let τ := Real.sqrt (192 / L)
  have hτ : 0 < τ := Real.sqrt_pos.mpr (div_pos (by norm_num) hL)
  have hτ₂ : τ ^ 2 = 192 / L := Real.sq_sqrt (by positivity)
  let P : ℝ := (4 : ℝ) ^ (⌈2 / η ^ 2⌉₊ : ℕ)
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hSize : (n : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ (N : ℝ) := by
    calc
      _ = (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) / 2 := by
        rw [show (n : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) =
          (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) by rw [Real.rpow_one],
          ← Real.rpow_sub hn₀]
        norm_num
      _ ≤ (n : ℝ) / P / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact div_le_div_of_nonneg_left hn₀.le (by dsimp only [P]; positivity) hP
      _ ≤ _ := by simpa only [Fintype.card_fin] using hU
  obtain ⟨hkN, hμ, hTol, hRate⟩ := hRates N hSize
  have hN₂ : 2 ≤ N := hk.trans hkN
  have hN₂' : (2 : ℝ) ≤ N := by exact_mod_cast hN₂
  have hDen : 0 < (N : ℝ) - 1 := by linarith only [hN₂']
  have hN₀ : (0 : ℝ) < N := by linarith only [hN₂']
  have hq' : HasFloor ξ q' := fun e ↦ hp (inducedEdge U (edgeEquiv f e))
  have hq (e : Edge U) : ξ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - ξ := hp (inducedEdge U e)
  have hDensity : arrayDensity q ∈ Icc ξ (1 - ξ) :=
    (row_density_mem_Icc q ((Fintype.card_coe U).symm ▸ hN₂)
      (fun e ↦ (hq e).1) (fun e ↦ (hq e).2)).1
  let d := degreeSum (fun e ↦ (q e : ℝ))
  let m := vertexMean d
  let w := symmetricEdgeWeight (fun e ↦ (q' e : ℝ))
  have hNorm (i : Fin N) : sampleRowMean Finset.univ w i - arrayDensity q =
      (d (f i) - m) / ((N : ℝ) - 1) := by
    rw [sampleRowMean_univ_eq_degree _ (by rw [Fintype.card_fin]; omega),
      Fintype.card_fin, arrayDensity_eq_normalized_vertexMean, Fintype.card_coe]
    have h := degreeSum_reindex f (fun e ↦ (q e : ℝ)) i
    change degreeSum (fun e ↦ (q' e : ℝ)) i = d (f i) at h
    rw [h, sub_div]
  have hMax (i : Fin N) : |sampleRowMean Finset.univ w i - arrayDensity q| ≤ 3 * Real.sqrt η := by
    rw [hNorm, abs_div, abs_of_pos hDen]
    exact (div_le_iff₀ hDen).2 (hDrift (f i))
  have hMS : (∑ i, (sampleRowMean Finset.univ w i - arrayDensity q) ^ 2) ≤ (N : ℝ) * τ ^ 2 := by
    simp_rw [hNorm, div_pow, ← Finset.sum_div]
    have hs : (∑ i : Fin N, (d (f i) - m) ^ 2) = ∑ i : U, (d i - m) ^ 2 :=
      f.toEquiv.sum_comp (fun i ↦ (d i - m) ^ 2)
    rw [hs]
    have h := (div_le_iff₀ hN₀).1 hEnergy
    have he : 6 * η ^ 2 = τ ^ 2 := by rw [hη₂, hτ₂]; ring
    apply (div_le_iff₀ (sq_pos_of_pos hDen)).2
    exact h.trans_eq (by rw [← he]; ring)
  have hFail := hMean' N hkN q' (arrayDensity q) (3 * Real.sqrt η) τ hq' hDensity
    (by positivity) hηa hMax hMS hμ (by rw [hτ₂]; exact hTol)
  rw [ite_eq_right hτ.ne', probability_exactOrder_failure_reindex f q k] at hFail
  have hThreshold : ⌈a / 2 * Real.log n ^ 2⌉₊ ≤ k := Nat.ceil_le.mpr hK.1
  have hSub : (exactOrderEvent k : Set (Edge (Fin n) → ℝ)) ⊆
      atLeastOrderEvent ⌈a / 2 * Real.log n ^ 2⌉₊ := exactOrderEvent_subset_atLeastOrderEvent hThreshold
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  exact (measureReal_mono (compl_subset_compl.mpr hSub)).trans
    ((probability_exactOrder_failure_le_induced p U k).trans (hFail.trans hRate))

end BoundedEdgeRegularSubgraphs
