module

public import BoundedEdgeRegularSubgraphs.InducedDegreeTargets
public import BoundedEdgeRegularSubgraphs.LocalEdgeEvents
public import BoundedEdgeRegularSubgraphs.SharedTiltConditioning
import Mathlib.Tactic

/-!
# Joint induced degree atoms conditioned on the shared edges
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The vertices of the overlap viewed inside the first candidate. -/
def overlapVertices (S T : Finset α) : Finset ↥S :=
  Finset.univ.filter (fun i ↦ i.val ∈ T)

theorem map_overlapVertices (S T : Finset α) :
    (overlapVertices S T).map ⟨Subtype.val, Subtype.val_injective⟩ = S ∩ T := by
  ext i
  simp only [overlapVertices, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.property, hj⟩
  · rintro ⟨hS, hT⟩
    exact ⟨⟨i, hS⟩, hT, rfl⟩

theorem card_overlapVertices (S T : Finset α) : (overlapVertices S T).card = (S ∩ T).card := by
  rw [← map_overlapVertices, Finset.card_map]

def ambientInducedEdge (S : Finset α) : Edge ↥S ↪ Edge α :=
  ⟨inducedEdge S, inducedEdge_injective S⟩

theorem map_edgesInside_overlapVertices (S T : Finset α) :
    (edgesInside (overlapVertices S T)).map (ambientInducedEdge S) = edgesInside (S ∩ T) := by
  ext e
  simp only [Finset.mem_map, ambientInducedEdge, Function.Embedding.coeFn_mk, edgesInside,
    overlapVertices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨f, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨⟨f.val.1.property, h₁⟩, ⟨f.val.2.property, h₂⟩⟩
  · rintro ⟨⟨hS₁, hT₁⟩, ⟨hS₂, hT₂⟩⟩
    let f : Edge ↥S := ⟨(⟨e.val.1, hS₁⟩, ⟨e.val.2, hS₂⟩), e.property⟩
    exact ⟨f, ⟨hT₁, hT₂⟩, Subtype.ext rfl⟩

private theorem edgesOutsideOverlap_eq_sdiff {β : Type*} [Fintype β] [LinearOrder β]
    [DecidableEq (Edge β)] (S : Finset β) :
    edgesOutsideOverlap S = Finset.univ \ edgesInside S := by
  ext e
  simp [edgesOutsideOverlap, edgesInside]

theorem map_edgesOutsideOverlap_overlapVertices [DecidableEq (Edge α)] (S T : Finset α) :
    (edgesOutsideOverlap (overlapVertices S T)).map (ambientInducedEdge S) =
      edgesInside S \ edgesInside (S ∩ T) := by
  classical
  rw [edgesOutsideOverlap_eq_sdiff, Finset.map_sdiff, map_edgesInside_overlapVertices]
  exact congrArg (fun A : Finset (Edge α) ↦ A \ edgesInside (S ∩ T)) (map_inducedEdge_univ S)

theorem preimage_overlapAssignment_induce (S T : Finset α) (h : Edge α → ℝ) :
    induce S ⁻¹' overlapAssignmentEvent (overlapVertices S T) (induce S h) =
      overlapAssignmentEvent (S ∩ T) h := by
  ext w
  change (∀ e ∈ edgesInside (overlapVertices S T), w (inducedEdge S e) = h (inducedEdge S e)) ↔
    ∀ e ∈ edgesInside (S ∩ T), w e = h e
  rw [← map_edgesInside_overlapVertices]
  constructor
  · intro h' e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    exact h' f hf
  · intro h' f hf
    exact h' _ (Finset.mem_map.mpr ⟨f, hf, rfl⟩)

private theorem inducedResidual_eventOnEdges (S : Finset α) (A : Finset (Edge ↥S)) (d : S → ℤ) :
    EventOnEdges (A.map (ambientInducedEdge S)) (induce S ⁻¹' degreeAtom A d) := by
  classical
  let F := A.map (ambientInducedEdge S)
  let f (x : F → ℝ) (e : Edge ↥S) :=
    if he : e ∈ A then x ⟨inducedEdge S e, Finset.mem_map.mpr ⟨e, he, rfl⟩⟩ else 0
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro e
    by_cases he : e ∈ A
    · simpa only [f, dif_pos he] using
        (measurable_pi_apply (⟨inducedEdge S e, Finset.mem_map.mpr ⟨e, he, rfl⟩⟩ : F))
    · simp only [f, dif_neg he, measurable_const]
  refine ⟨f ⁻¹' degreeAtom A d, (measurableSet_degreeAtom A d).preimage hf, ?_⟩
  ext w
  change degreeVector A (f (fun e : F ↦ w e.val)) = d ↔ degreeVector A (induce S w) = d
  have heq : degreeVector A (f (fun e : F ↦ w e.val)) = degreeVector A (induce S w) := by
    unfold degreeVector
    exact Finset.sum_congr rfl (fun e he ↦ by simp only [f, dif_pos he, induce])
  rw [heq]

private theorem overlapAssignment_eventOnEdges (S : Finset α) (h : Edge α → ℝ) :
    EventOnEdges (edgesInside S) (overlapAssignmentEvent S h) := by
  refine ⟨{fun e : edgesInside S ↦ h e.val}, measurableSet_singleton _, ?_⟩
  ext w
  change ((fun e : edgesInside S ↦ w e.val) = (fun e : edgesInside S ↦ h e.val)) ↔
    ∀ e ∈ edgesInside S, w e = h e
  exact ⟨fun H e he ↦ congrFun H ⟨e, he⟩, fun H ↦ funext (fun e ↦ H e.val e.property)⟩

private theorem degreeAtom_inter_overlap_parts {β : Type*} [Fintype β] [LinearOrder β]
    (S : Finset β) (h : Edge β → ℝ) (d : β → ℤ) :
    degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h =
      degreeAtom (edgesOutsideOverlap S) (d - degreeVector (edgesInside S) h) ∩
        overlapAssignmentEvent S h := by
  classical
  ext w
  change (degreeVector Finset.univ w = d ∧ ∀ e ∈ edgesInside S, w e = h e) ↔
    (degreeVector (edgesOutsideOverlap S) w = d - degreeVector (edgesInside S) h ∧
      ∀ e ∈ edgesInside S, w e = h e)
  apply and_congr_left
  intro hh
  have hShift : degreeVector (edgesInside S) w = degreeVector (edgesInside S) h :=
    Finset.sum_congr rfl (fun e he ↦ by rw [hh e he])
  have hSum : degreeVector Finset.univ w =
      degreeVector (edgesOutsideOverlap S) w + degreeVector (edgesInside S) w := by
    unfold degreeVector
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun e : Edge β ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S)
      (fun e ↦ sampledIncidence e (w e))).symm
  rw [hSum, hShift, eq_sub_iff_add_eq]

private theorem inducedDegreeAtom_inter_eq (S T : Finset α) (h : Edge α → ℝ) (d : ℤ) :
    inducedDegreeAtom S d ∩ overlapAssignmentEvent (S ∩ T) h =
      (induce S ⁻¹' degreeAtom (edgesOutsideOverlap (overlapVertices S T))
        ((fun _ ↦ d) - degreeVector (edgesInside (overlapVertices S T)) (induce S h))) ∩
        overlapAssignmentEvent (S ∩ T) h := by
  rw [← preimage_overlapAssignment_induce S T h, inducedDegreeAtom, ← preimage_inter, ← preimage_inter,
    degreeAtom_inter_overlap_parts]

/-- The joint probability on a shared assignment factors into the two
conditional probabilities, multiplied by the assignment probability. -/
theorem probability_inducedDegreeAtom_joint_conditioned
    (p : Edge α → Icc (0 : ℝ) 1) (S T : Finset α) (h : Edge α → ℝ) (d e : ℤ) :
    let H := overlapAssignmentEvent (S ∩ T) h
    let E := inducedDegreeAtom S d
    let F := inducedDegreeAtom T e
    (graphLaw p).real ((E ∩ F) ∩ H) * (graphLaw p).real H =
      (graphLaw p).real (E ∩ H) * (graphLaw p).real (F ∩ H) := by
  classical
  let C := edgesInside (S ∩ T)
  let A := edgesInside S \ C
  let B := edgesInside T \ C
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨haS, haC⟩ := Finset.mem_sdiff.mp ha
    obtain ⟨hbT, _⟩ := Finset.mem_sdiff.mp hb
    exact haC (by
      simp only [C, edgesInside, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter] at *
      exact ⟨⟨haS.1, hbT.1⟩, ⟨haS.2, hbT.2⟩⟩)
  have hC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro a ha hc
    exact (Finset.mem_union.mp ha).elim (fun ha ↦ (Finset.mem_sdiff.mp ha).2 hc)
      (fun hb ↦ (Finset.mem_sdiff.mp hb).2 hc)
  have hS := inducedResidual_eventOnEdges S (edgesOutsideOverlap (overlapVertices S T))
    ((fun _ ↦ d) - degreeVector (edgesInside (overlapVertices S T)) (induce S h))
  have hT := inducedResidual_eventOnEdges T (edgesOutsideOverlap (overlapVertices T S))
    ((fun _ ↦ e) - degreeVector (edgesInside (overlapVertices T S)) (induce T h))
  rw [map_edgesOutsideOverlap_overlapVertices] at hS hT
  rw [Finset.inter_comm T S] at hT
  have hE := inducedDegreeAtom_inter_eq S T h d
  have hF := inducedDegreeAtom_inter_eq T S h e
  rw [Finset.inter_comm T S] at hF
  exact probability_conditional_inter_eq_mul_of_disjoint_residuals p hAB
    (hC.mono_left Finset.subset_union_left) (hC.mono_left Finset.subset_union_right) hS hT
    (overlapAssignment_eventOnEdges (S ∩ T) h) hE hF

end BoundedEdgeRegularSubgraphs
