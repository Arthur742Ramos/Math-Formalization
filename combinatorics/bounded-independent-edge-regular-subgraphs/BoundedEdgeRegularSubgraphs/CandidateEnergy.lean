module

public import BoundedEdgeRegularSubgraphs.CandidateSharedLikelihood
import Mathlib.Tactic

/-!
# Energy and pointwise bounds for the ambient candidate potential
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem extendCandidateTilt_eq_of_mem (S : Finset α) (θ : S → ℝ) {i : α} (hi : i ∈ S) :
    extendCandidateTilt S θ i = θ ⟨i, hi⟩ := by
  rw [extendCandidateTilt, dite_eq_left hi]

theorem sum_extendCandidateTilt_sq_eq (S : Finset α) (θ : S → ℝ) :
    (∑ i ∈ S, extendCandidateTilt S θ i ^ 2) = ∑ i : S, θ i ^ 2 := by
  rw [← Finset.attach_eq_univ]
  rw [← Finset.sum_attach S (fun i ↦ extendCandidateTilt S θ i ^ 2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [extendCandidateTilt_eq_of_mem S θ i.property]

theorem sum_extendCandidateTilt_sq_le (S J : Finset α) (θ : S → ℝ) (hJ : J ⊆ S) :
    (∑ i ∈ J, extendCandidateTilt S θ i ^ 2) ≤ ∑ i : S, θ i ^ 2 := by
  rw [← sum_extendCandidateTilt_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg hJ (fun _ _ _ ↦ sq_nonneg _)

end BoundedEdgeRegularSubgraphs
