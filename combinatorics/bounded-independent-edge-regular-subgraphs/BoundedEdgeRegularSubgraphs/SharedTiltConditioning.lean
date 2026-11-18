module

public import BoundedEdgeRegularSubgraphs.SharedTiltMoment
public import BoundedEdgeRegularSubgraphs.OverlapConditioning
public import BoundedEdgeRegularSubgraphs.MeanDrift
public import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Changing measure on a fixed overlap assignment
-/

public section

open Set MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Conditioning and tilting a fixed degree atom commute with the
likelihood factor of the specified shared edges. -/
theorem probability_degreeAtom_conditional_ratio_eq_shared_tilt
    (q : Edge α → Icc (0 : ℝ) 1) (θ : α → ℝ) (S : Finset α)
    (h : Edge α → ℝ) (d : α → ℤ) (hh : ∀ e ∈ edgesInside S, h e = 0 ∨ h e = 1)
    (hE : 0 < (graphLaw q).real (degreeAtom Finset.univ d))
    (hH : 0 < (graphLaw q).real (overlapAssignmentEvent S h)) :
    let E := degreeAtom Finset.univ d
    let H := overlapAssignmentEvent S h
    let L := ∏ e ∈ edgesInside S, Real.exp ((θ e.val.1 + θ e.val.2) * h e) /
      tiltNormalizer (q e) (θ e.val.1 + θ e.val.2)
    (((graphLaw q).real (E ∩ H) / (graphLaw q).real H) / (graphLaw q).real E) =
      L * (((graphLaw (vertexTilt q θ)).real (E ∩ H) /
        (graphLaw (vertexTilt q θ)).real H) / (graphLaw (vertexTilt q θ)).real E) := by
  let E := degreeAtom Finset.univ d
  let H := overlapAssignmentEvent S h
  let L := ∏ e ∈ edgesInside S, Real.exp ((θ e.val.1 + θ e.val.2) * h e) /
    tiltNormalizer (q e) (θ e.val.1 + θ e.val.2)
  let K := (∑ i, θ i * (d i : ℝ)) - logPartition q θ
  let μ := graphLaw q
  let ν := graphLaw (vertexTilt q θ)
  have hL : 0 < L := Finset.prod_pos (fun e _ ↦ div_pos (Real.exp_pos _) (tiltNormalizer_pos _ _))
  have hE' : ν.real E = Real.exp K * μ.real E := real_graphLaw_vertexTilt_degreeAtom q θ d
  have hH' : ν.real H = L * μ.real H :=
    real_graphLaw_vertexTilt_specified_edges q θ (edgesInside S) h hh
  have hJ : ν.real (E ∩ H) = Real.exp K * μ.real (E ∩ H) :=
    real_graphLaw_vertexTilt_sub_degreeAtom q θ d _ inter_subset_left
  change (μ.real (E ∩ H) / μ.real H) / μ.real E =
    L * ((ν.real (E ∩ H) / ν.real H) / ν.real E)
  rw [hE', hH', hJ]
  field_simp [hL.ne', hE.ne', hH.ne', (Real.exp_pos K).ne']

/-- The induced edges exhaust exactly the edge coordinates inside a
vertex set. -/
theorem map_inducedEdge_univ (S : Finset α) :
    (Finset.univ : Finset (Edge ↥S)).map ⟨inducedEdge S, inducedEdge_injective S⟩ = edgesInside S := by
  classical
  ext e
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    edgesInside, Finset.mem_filter]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val.1.property, f.val.2.property⟩
  · intro he
    exact ⟨⟨(⟨e.val.1, he.1⟩, ⟨e.val.2, he.2⟩), e.property⟩, Subtype.ext rfl⟩

/-- Squared logit shifts on a shared clique are controlled by the
number of shared vertices and their squared potentials. -/
theorem sum_shared_tilt_shift_sq_le (S : Finset α) (θ : α → ℝ) :
    (∑ e ∈ edgesInside S, (θ e.val.1 + θ e.val.2) ^ 2) ≤
      2 * (S.card : ℝ) * ∑ i ∈ S, θ i ^ 2 := by
  classical
  let v (i : S) := θ i.val
  rw [← map_inducedEdge_univ S, Finset.sum_map]
  change (∑ e : Edge ↥S, (v e.val.1 + v e.val.2) ^ 2) ≤ _
  rw [sum_edge_squares, Fintype.card_coe]
  have h : (∑ i : S, v i) ^ 2 ≤ (S.card : ℝ) * ∑ i : S, v i ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ↥S)) (f := v))
  have hv : (∑ i : S, v i ^ 2) = ∑ i ∈ S, θ i ^ 2 := by
    rw [← Finset.attach_eq_univ]
    exact Finset.sum_attach S (fun i ↦ θ i ^ 2)
  rw [hv] at h ⊢
  have hs : 0 ≤ ∑ i ∈ S, θ i ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  linarith only [h, hs]

end BoundedEdgeRegularSubgraphs
