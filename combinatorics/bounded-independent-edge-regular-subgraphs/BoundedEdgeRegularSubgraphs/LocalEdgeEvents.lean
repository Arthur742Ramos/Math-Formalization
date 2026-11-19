module

public import BoundedEdgeRegularSubgraphs.Model
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Events determined by a finite set of edge coordinates
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
/-- An event is determined by the specified coordinates if it is the
preimage of a measurable event under their projection. -/
def EventOnEdges (A : Finset (Edge α)) (E : Set (Edge α → ℝ)) : Prop :=
  ∃ U : Set (A → ℝ), MeasurableSet U ∧ (fun (w : Edge α → ℝ) e ↦ w e.val) ⁻¹' U = E

omit [Fintype α] in
theorem EventOnEdges.mono {A B : Finset (Edge α)} {E : Set (Edge α → ℝ)}
    (hE : EventOnEdges A E) (hA : A ⊆ B) : EventOnEdges B E := by
  obtain ⟨U, hU, hEq⟩ := hE
  let f (x : B → ℝ) (e : A) := x ⟨e.val, hA e.property⟩
  have hf : Measurable f := measurable_pi_iff.mpr (fun e ↦ measurable_pi_apply _)
  exact ⟨f ⁻¹' U, hU.preimage hf, hEq⟩

omit [Fintype α] in
theorem EventOnEdges.inter {A : Finset (Edge α)} {E F : Set (Edge α → ℝ)}
    (hE : EventOnEdges A E) (hF : EventOnEdges A F) : EventOnEdges A (E ∩ F) := by
  obtain ⟨U, hU, he⟩ := hE
  obtain ⟨V, hV, hf⟩ := hF
  exact ⟨U ∩ V, hU.inter hV, by rw [preimage_inter, he, hf]⟩

/-- Events determined by disjoint coordinate sets are independent. -/
theorem probability_inter_eq_mul_of_eventOnEdges
    (q : Edge α → Icc (0 : ℝ) 1) {A B : Finset (Edge α)} {E F : Set (Edge α → ℝ)}
    (hAB : Disjoint A B) (hE : EventOnEdges A E) (hF : EventOnEdges B F) :
    (graphLaw q).real (E ∩ F) = (graphLaw q).real E * (graphLaw q).real F := by
  obtain ⟨U, hU, he⟩ := hE
  obtain ⟨V, hV, hf⟩ := hF
  have hind : iIndepFun (fun (e : Edge α) (w : Edge α → ℝ) ↦ w e) (graphLaw q) := by
    unfold graphLaw
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hh := iIndepFun.indepFun_finset A B hAB hind (fun e ↦ measurable_pi_apply e)
  have h := hh.measure_inter_preimage_eq_mul U V hU hV
  change graphLaw q (((fun (w : Edge α → ℝ) (e : A) ↦ w e.val) ⁻¹' U) ∩
    ((fun (w : Edge α → ℝ) (e : B) ↦ w e.val) ⁻¹' V)) = _ at h
  rw [he, hf] at h
  simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

/-- On an assignment of shared coordinates, events that reduce to
disjoint residual coordinate sets have a product conditional probability. -/
theorem probability_conditional_inter_eq_mul_of_disjoint_residuals
    (q : Edge α → Icc (0 : ℝ) 1) {A B C : Finset (Edge α)}
    {E F H U V : Set (Edge α → ℝ)}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hU : EventOnEdges A U) (hV : EventOnEdges B V) (hH : EventOnEdges C H)
    (he : E ∩ H = U ∩ H) (hf : F ∩ H = V ∩ H) :
    (graphLaw q).real ((E ∩ F) ∩ H) * (graphLaw q).real H =
      (graphLaw q).real (E ∩ H) * (graphLaw q).real (F ∩ H) := by
  classical
  have hJoint : E ∩ F ∩ H = U ∩ V ∩ H := by
    rw [show E ∩ F ∩ H = (E ∩ H) ∩ (F ∩ H) by ext; simp only [mem_inter_iff]; tauto, he, hf]
    ext
    simp only [mem_inter_iff]
    tauto
  have hC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro e he hc
    exact (Finset.mem_union.mp he).elim
      (fun ha ↦ (Finset.disjoint_left.mp hAC) ha hc)
      (fun hb ↦ (Finset.disjoint_left.mp hBC) hb hc)
  have hUV : EventOnEdges (A ∪ B) (U ∩ V) :=
    (hU.mono Finset.subset_union_left).inter (hV.mono Finset.subset_union_right)
  rw [hJoint, he, hf, probability_inter_eq_mul_of_eventOnEdges q hC hUV hH,
    probability_inter_eq_mul_of_eventOnEdges q hAB hU hV,
    probability_inter_eq_mul_of_eventOnEdges q hAC hU hH,
    probability_inter_eq_mul_of_eventOnEdges q hBC hV hH]
  ring

end BoundedEdgeRegularSubgraphs
