module

public import BoundedEdgeRegularSubgraphs.RegularAtomUpper
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-!
# Independent flips and mixtures of edge arrays
-/

public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Edge probabilities after independent flips of the underlying bits. -/
def noisyEdgeArray (B : Edge α → Bool) {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1 / 2) :
    Edge α → Icc (0 : ℝ) 1 := fun e ↦
  if B e then ⟨1 - ξ, by constructor <;> linarith⟩ else ⟨ξ, by constructor <;> linarith⟩

theorem noisyEdgeArray_floor (B : Edge α → Bool) {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1 / 2) :
    ∀ e, ξ ≤ (noisyEdgeArray B hξ hξ' e : ℝ) ∧ (noisyEdgeArray B hξ hξ' e : ℝ) ≤ 1 - ξ := by
  intro e
  cases h : B e
  · simp only [noisyEdgeArray, h, Bool.false_eq_true, ite_false]
    exact ⟨le_rfl, by linarith only [hξ']⟩
  · simp only [noisyEdgeArray, h, ite_true]
    exact ⟨by linarith only [hξ'], le_rfl⟩

/-- The expected degree under independent flips is affine in the
degree of the deterministic graph, as in Corollary 7.1. -/
theorem degreeSum_noisyEdgeArray (B : Edge α → Bool) {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1 / 2) (i : α) :
    degreeSum (fun e ↦ (noisyEdgeArray B hξ hξ' e : ℝ)) i =
      ξ * ((Fintype.card α : ℝ) - 1) +
        (1 - 2 * ξ) * degreeSum (fun e ↦ if B e then 1 else 0) i := by
  have he (e : Edge α) : (noisyEdgeArray B hξ hξ' e : ℝ) =
      ξ + (1 - 2 * ξ) * (if B e then 1 else 0) := by
    cases h : B e <;> simp [noisyEdgeArray, h] <;> ring
  simp_rw [he]
  rw [← degreeSum_one i]
  unfold degreeSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

theorem noisyEdgeArray_equal_degree_means (B : Edge α → Bool) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1 / 2)
    (hB : ∀ i j, degreeSum (fun e ↦ if B e then 1 else 0) i =
      degreeSum (fun e ↦ if B e then 1 else 0) j) :
    ∀ i j, degreeSum (fun e ↦ (noisyEdgeArray B hξ hξ' e : ℝ)) i =
      degreeSum (fun e ↦ (noisyEdgeArray B hξ hξ' e : ℝ)) j := by
  intro i j
  rw [degreeSum_noisyEdgeArray, degreeSum_noisyEdgeArray, hB i j]

/-- A uniform conditional probability bound survives averaging over any
random environment, as in Corollary 7.3. -/
theorem probability_bind_graphLaw_le_of_ae {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (p : Θ → Edge α → Icc (0 : ℝ) 1)
    (hm : AEMeasurable (fun t ↦ graphLaw (p t)) ν) (E : Set (Edge α → ℝ)) (hE : MeasurableSet E)
    {b : ℝ} (hb : 0 ≤ b) (h : ∀ᵐ t ∂ν, (graphLaw (p t)).real E ≤ b) :
    (ν.bind (fun t ↦ graphLaw (p t))).real E ≤ b := by
  have h₁ : ∀ᵐ t ∂ν, graphLaw (p t) E ≤ ENNReal.ofReal b := by
    filter_upwards [h] with t ht
    have : IsProbabilityMeasure (graphLaw (p t)) := by unfold graphLaw; infer_instance
    rw [← ofReal_measureReal (μ := graphLaw (p t)) (s := E)]
    exact ENNReal.ofReal_le_ofReal ht
  have h₂ : (ν.bind (fun t ↦ graphLaw (p t))) E ≤ ENNReal.ofReal b := by
    rw [Measure.bind_apply hE hm]
    exact (lintegral_mono_ae h₁).trans_eq (by simp)
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h₂
  rw [measureReal_def, ← ENNReal.toReal_ofReal hb]
  exact (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr h₂

end BoundedEdgeRegularSubgraphs
