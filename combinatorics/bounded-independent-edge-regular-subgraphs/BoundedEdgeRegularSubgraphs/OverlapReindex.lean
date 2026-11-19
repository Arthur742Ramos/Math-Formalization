module

public import BoundedEdgeRegularSubgraphs.InducedDegreeTargets
public import BoundedEdgeRegularSubgraphs.OverlapConditioning
import Mathlib.Tactic

/-!
# Reindexing a conditional degree ratio
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace BoundedEdgeRegularSubgraphs

variable {α β : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]

def reindexVertices (f : α ≃o β) (S : Finset β) : Finset α :=
  S.map f.symm.toEquiv.toEmbedding

theorem card_reindexVertices (f : α ≃o β) (S : Finset β) :
    (reindexVertices f S).card = S.card := Finset.card_map _

theorem mem_reindexVertices (f : α ≃o β) (S : Finset β) (i : α) :
    i ∈ reindexVertices f S ↔ f i ∈ S := by
  unfold reindexVertices
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, h⟩
    have hi : f.symm j = i := h
    rw [← hi, f.apply_symm_apply]
    exact hj
  · intro hi
    exact ⟨f i, hi, f.symm_apply_apply i⟩

theorem edgeEquiv_mem_edgesInside_reindex (f : α ≃o β) (S : Finset β) (e : Edge α) :
    e ∈ edgesInside (reindexVertices f S) ↔ edgeEquiv f e ∈ edgesInside S := by
  classical
  simp only [edgesInside, Finset.mem_filter, Finset.mem_univ, true_and, mem_reindexVertices]
  rfl

theorem measurableSet_overlapAssignmentEvent (S : Finset β) (h : Edge β → ℝ) :
    MeasurableSet (overlapAssignmentEvent S h) := by
  have he : overlapAssignmentEvent S h = ⋂ e : {e // e ∈ edgesInside S}, {w | w e.val = h e.val} := by
    ext w
    simp only [overlapAssignmentEvent, mem_iInter, mem_setOf_eq, Subtype.forall, Set.mem_ofPred_eq]
  rw [he]
  exact MeasurableSet.iInter (fun i ↦ measurableSet_eq_fun (measurable_pi_apply i.val) measurable_const)

theorem measurePreserving_graph_reindex (f : α ≃o β) (p : Edge β → Icc (0 : ℝ) 1) :
    MeasurePreserving (fun w : Edge β → ℝ ↦ w ∘ edgeEquiv f) (graphLaw p)
      (graphLaw (p ∘ edgeEquiv f)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Edge β ↦ ℝ) (edgeEquiv f)
  exact (measurePreserving_piCongrLeft (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (p i)) (edgeEquiv f)).symm e

theorem preimage_degreeAtom_graph_reindex (f : α ≃o β) (d : β → ℤ) :
    (fun w : Edge β → ℝ ↦ w ∘ edgeEquiv f) ⁻¹'
        degreeAtom Finset.univ (d ∘ f) = degreeAtom Finset.univ d := by
  ext w
  change (degreeVector Finset.univ (w ∘ edgeEquiv f) = d ∘ f) ↔ degreeVector Finset.univ w = d
  constructor
  · intro h
    funext i
    have hh := congrFun h (f.symm i)
    rw [degreeVector_univ_reindex f w, Function.comp_apply, f.apply_symm_apply] at hh
    exact hh
  · intro h
    funext i
    rw [degreeVector_univ_reindex f w, h]
    rfl

theorem preimage_overlapAssignment_graph_reindex (f : α ≃o β) (S : Finset β) (h : Edge β → ℝ) :
    (fun w : Edge β → ℝ ↦ w ∘ edgeEquiv f) ⁻¹'
        overlapAssignmentEvent (reindexVertices f S) (h ∘ edgeEquiv f) =
      overlapAssignmentEvent S h := by
  ext w
  change (∀ e ∈ edgesInside (reindexVertices f S), w (edgeEquiv f e) = h (edgeEquiv f e)) ↔
    ∀ e ∈ edgesInside S, w e = h e
  constructor
  · intro hW e he
    let f' := edgeEquiv f
    have hpre : f'.symm e ∈ edgesInside (reindexVertices f S) := by
      apply (edgeEquiv_mem_edgesInside_reindex f S _).mpr
      simpa only [show edgeEquiv f = f' from rfl, f'.apply_symm_apply] using he
    simpa only [show edgeEquiv f = f' from rfl, f'.apply_symm_apply] using hW (f'.symm e) hpre
  · intro hW e he
    exact hW _ ((edgeEquiv_mem_edgesInside_reindex f S e).mp he)

/-- Reindexing transports each measure in the conditional ratio, including
the probability of the specified overlap itself. -/
theorem conditional_degreeAtom_ratio_graph_reindex (f : α ≃o β)
    (p : Edge β → Icc (0 : ℝ) 1) (S : Finset β) (h : Edge β → ℝ) (d : β → ℤ) :
    let p' := p ∘ edgeEquiv f
    let H' := overlapAssignmentEvent (reindexVertices f S) (h ∘ edgeEquiv f)
    let D' := degreeAtom Finset.univ (d ∘ f)
    let H := overlapAssignmentEvent S h
    let D := degreeAtom Finset.univ d
    (((graphLaw p').real (D' ∩ H') / (graphLaw p').real H') / (graphLaw p').real D') =
      (((graphLaw p).real (D ∩ H) / (graphLaw p).real H) / (graphLaw p).real D) := by
  let p' := p ∘ edgeEquiv f
  let H' := overlapAssignmentEvent (reindexVertices f S) (h ∘ edgeEquiv f)
  let D' := degreeAtom Finset.univ (d ∘ f)
  let H := overlapAssignmentEvent S h
  let D := degreeAtom Finset.univ d
  have hPres := measurePreserving_graph_reindex f p
  have hH' : MeasurableSet H' := measurableSet_overlapAssignmentEvent _ _
  have hD' : MeasurableSet D' := measurableSet_degreeAtom _ _
  have h₁ := hPres.measure_preimage (hD'.inter hH').nullMeasurableSet
  have h₂ := hPres.measure_preimage hH'.nullMeasurableSet
  have h₃ := hPres.measure_preimage hD'.nullMeasurableSet
  rw [preimage_inter, preimage_degreeAtom_graph_reindex f d, preimage_overlapAssignment_graph_reindex f S h] at h₁
  rw [preimage_overlapAssignment_graph_reindex f S h] at h₂
  rw [preimage_degreeAtom_graph_reindex f d] at h₃
  have h₁' : (graphLaw p).real (D ∩ H) = (graphLaw p').real (D' ∩ H') := congrArg ENNReal.toReal h₁
  have h₂' : (graphLaw p).real H = (graphLaw p').real H' := congrArg ENNReal.toReal h₂
  have h₃' : (graphLaw p).real D = (graphLaw p').real D' := congrArg ENNReal.toReal h₃
  change ((graphLaw p').real (D' ∩ H') / (graphLaw p').real H') / (graphLaw p').real D' =
    ((graphLaw p).real (D ∩ H) / (graphLaw p).real H) / (graphLaw p).real D
  rw [h₁', h₂', h₃']

end BoundedEdgeRegularSubgraphs
