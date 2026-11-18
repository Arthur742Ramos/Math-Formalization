module

public import BoundedEdgeRegularSubgraphs.RegularAtomUpper
import BoundedEdgeRegularSubgraphs.Incidence
import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.Tactic

/-!
# Loss of expected degree upon deleting vertices
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem degreeSum_sub_induce_eq (S : Finset α) (i : S) (w : Edge α → ℝ) :
    degreeSum w i - degreeSum (induce S w) i =
      ∑ e ∈ edgesOutsideOverlap S, if (i : α) = e.val.1 ∨ (i : α) = e.val.2 then w e else 0 := by
  classical
  let f (e : Edge α) := if (i : α) = e.val.1 ∨ (i : α) = e.val.2 then w e else 0
  have h : degreeSum (induce S w) i = ∑ e ∈ edgesInside S, f e := by
    unfold degreeSum
    refine Finset.sum_bij (fun e _ ↦ inducedEdge S e) ?_ ?_ ?_ ?_
    · intro e _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.val.1.property, e.val.2.property⟩
    · intro e _ e' _ he
      exact inducedEdge_injective S he
    · intro e he
      obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp he).2
      exact ⟨⟨(⟨e.val.1, h₁⟩, ⟨e.val.2, h₂⟩), e.property⟩, Finset.mem_univ _, Subtype.ext rfl⟩
    · intro e _
      simp only [f, induce, inducedEdge, Subtype.coe_inj]
      by_cases h : i = e.val.1 ∨ i = e.val.2 <;> simp [h]
  change (∑ e : Edge α, f e) - degreeSum (induce S w) i = ∑ e ∈ edgesOutsideOverlap S, f e
  rw [h]
  have hh := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S) f
  change (∑ e ∈ edgesInside S, f e) + (∑ e ∈ edgesOutsideOverlap S, f e) = ∑ e, f e at hh
  linarith only [hh]

/-- A retained vertex loses at most one unit of expected degree per
deleted vertex. -/
theorem degreeSum_induce_loss (q : Edge α → Set.Icc (0 : ℝ) 1) (S : Finset α) (i : S) :
    degreeSum (fun e ↦ (q e : ℝ)) i -
      degreeSum (fun e ↦ (q (inducedEdge S e) : ℝ)) i ∈
        Set.Icc 0 ((Fintype.card α : ℝ) - S.card) := by
  have h := degreeSum_sub_induce_eq S i (fun e ↦ (q e : ℝ))
  have h₁ := degreeSum_sub_induce_eq S i (fun _ ↦ (1 : ℝ))
  change degreeSum (fun e ↦ (q e : ℝ)) i -
      degreeSum (fun e ↦ (q (inducedEdge S e) : ℝ)) i = _ at h
  change degreeSum (fun _ ↦ (1 : ℝ)) (i : α) - degreeSum (fun _ ↦ (1 : ℝ)) i = _ at h₁
  rw [degreeSum_one, degreeSum_one, Fintype.card_coe,
    show ((Fintype.card α : ℝ) - 1) - ((S.card : ℝ) - 1) =
      (Fintype.card α : ℝ) - S.card by ring] at h₁
  rw [h]
  constructor
  · exact Finset.sum_nonneg (fun e _ ↦ by split_ifs; exacts [(q e).property.1, le_rfl])
  · rw [h₁]
    exact Finset.sum_le_sum (fun e _ ↦ by split_ifs; exacts [(q e).property.2, le_rfl])

end BoundedEdgeRegularSubgraphs
