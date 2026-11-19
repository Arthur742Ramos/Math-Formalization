module

public import BoundedEdgeRegularSubgraphs.InducedOverlap
public import BoundedEdgeRegularSubgraphs.OverlapReindex
public import BoundedEdgeRegularSubgraphs.ConditionalDegreeRatio
import Mathlib.Tactic

/-!
# Centred conditional ratios on the candidate vertex sets
-/

public section

open Filter MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The uniform conditional-ratio bound applies to any of the finite
ordered vertex sets used by the candidates. -/
theorem eventually_probability_conditional_degreeAtom_ratio_finite {δ ρ : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ < 1 / 2) (hρ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ {β : Type*} [Fintype β] [LinearOrder β], Fintype.card β = k →
      ∀ (S : Finset β) (q : Edge β → Icc (0 : ℝ) 1) (h : Edge β → ℝ) (d : β → ℤ),
        (S.card : ℝ) ≤ ρ * k →
        (∀ e, δ ≤ (q e : ℝ) ∧ (q e : ℝ) ≤ 1 - δ) →
        (∀ e ∈ edgesInside S, h e = 0 ∨ h e = 1) →
        (∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i) → Even (∑ i, d i) →
        (((graphLaw q).real (degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h) /
          (graphLaw q).real (overlapAssignmentEvent S h)) /
          (graphLaw q).real (degreeAtom Finset.univ d)) ≤ K * Real.exp (K * (S.card : ℝ) ^ 2 / k) := by
  obtain ⟨K, hK, h⟩ := probability_conditional_degreeAtom_ratio_uniform hδ hδ₁ hρ hρ₁
  refine ⟨K, hK, ?_⟩
  filter_upwards [h] with k hk
  intro β _ _ hcard S q h d hS hq hh hd hEven
  let f := Fintype.orderIsoFinOfCardEq β hcard
  let S' := reindexVertices f S
  let q' := q ∘ edgeEquiv f
  let h' := h ∘ edgeEquiv f
  let d' := d ∘ f
  have hS' : S'.card = S.card := card_reindexVertices f S
  have hEven' : Even (∑ i, d' i) := by
    change Even (∑ i, d (f.toEquiv i))
    rw [f.toEquiv.sum_comp d]
    exact hEven
  have hd' (i : Fin k) : (d' i : ℝ) = degreeSum (fun e ↦ (q' e : ℝ)) i := by
    change (d (f i) : ℝ) = degreeSum ((fun e ↦ (q e : ℝ)) ∘ edgeEquiv f) i
    rw [degreeSum_reindex f]
    exact hd (f i)
  have hh' (e : Edge (Fin k)) (he : e ∈ edgesInside S') : h' e = 0 ∨ h' e = 1 :=
    hh _ ((edgeEquiv_mem_edgesInside_reindex f S e).mp he)
  have hBound := hk S' q' h' d' (by rwa [hS']) (fun e ↦ hq (edgeEquiv f e)) hh' hd' hEven'
  rw [hS'] at hBound
  have he := conditional_degreeAtom_ratio_graph_reindex f q S h d
  exact he.ge.trans hBound

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- For a candidate set, the conditional ratio in the ambient measure
equals the ratio computed on that candidate's own edge array. -/
theorem conditional_inducedDegreeAtom_ratio_eq (p : Edge α → Icc (0 : ℝ) 1)
    (S T : Finset α) (h : Edge α → ℝ) (d : ℤ) :
    let H := overlapAssignmentEvent (S ∩ T) h
    let E := inducedDegreeAtom S d
    let q := induce S p
    let H' := overlapAssignmentEvent (overlapVertices S T) (induce S h)
    let E' := degreeAtom Finset.univ (fun _ : S ↦ d)
    (((graphLaw p).real (E ∩ H) / (graphLaw p).real H) / (graphLaw p).real E) =
      (((graphLaw q).real (E' ∩ H') / (graphLaw q).real H') / (graphLaw q).real E') := by
  let H := overlapAssignmentEvent (S ∩ T) h
  let E := inducedDegreeAtom S d
  let q := induce S p
  let H' := overlapAssignmentEvent (overlapVertices S T) (induce S h)
  let E' := degreeAtom Finset.univ (fun _ : S ↦ d)
  have hμ := measurePreserving_induce p S
  have hHr : MeasurableSet H' := measurableSet_overlapAssignmentEvent _ _
  have hEr : MeasurableSet E' := measurableSet_degreeAtom _ _
  have hH := hμ.measure_preimage hHr.nullMeasurableSet
  have hI := hμ.measure_preimage (hEr.inter hHr).nullMeasurableSet
  rw [preimage_inter, preimage_overlapAssignment_induce S T h] at hI
  rw [preimage_overlapAssignment_induce S T h] at hH
  have h₁ : (graphLaw p).real (E ∩ H) = (graphLaw q).real (E' ∩ H') := congrArg ENNReal.toReal hI
  have h₂ : (graphLaw p).real H = (graphLaw q).real H' := congrArg ENNReal.toReal hH
  have h₃ : (graphLaw p).real E = (graphLaw q).real E' := probability_inducedDegreeAtom_eq p S d
  change (((graphLaw p).real (E ∩ H) / (graphLaw p).real H) / (graphLaw p).real E) =
    (((graphLaw q).real (E' ∩ H') / (graphLaw q).real H') / (graphLaw q).real E')
  rw [h₁, h₂, h₃]

end BoundedEdgeRegularSubgraphs
