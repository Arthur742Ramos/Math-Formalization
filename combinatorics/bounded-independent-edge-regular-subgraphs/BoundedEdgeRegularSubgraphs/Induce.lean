module

public import BoundedEdgeRegularSubgraphs.Model
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
theorem inducedEdge_injective (S : Finset α) :
    Function.Injective (inducedEdge S) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun a : Edge α ↦ a.val.1) h
  · exact congrArg (fun a : Edge α ↦ a.val.2) h

theorem measurePreserving_induce (p : Edge α → Set.Icc (0 : ℝ) 1) (S : Finset α) :
    MeasurePreserving (induce S) (graphLaw p) (graphLaw (induce S p)) := by
  classical
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  have hm (e : Edge ↥S) : Measurable (fun w : Edge α → ℝ ↦ w (inducedEdge S e)) :=
    measurable_pi_apply _
  refine ⟨measurable_pi_iff.mpr hm, ?_⟩
  have hind : iIndepFun (fun (e : Edge α) (w : Edge α → ℝ) ↦ w e) (graphLaw p) := by
    unfold graphLaw
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have h := (hind.precomp (inducedEdge_injective S)).map_fun_eq_pi_map
    (fun e ↦ (hm e).aemeasurable)
  change (graphLaw p).map (induce S) =
    Measure.pi (fun e ↦ (graphLaw p).map (Function.eval (inducedEdge S e))) at h
  rw [h]
  unfold graphLaw
  congr 1
  funext e
  exact (measurePreserving_eval (fun e ↦ bernoulliMeasure (1 : ℝ) 0 (p e))
    (inducedEdge S e)).map_eq

private theorem measurable_degreeSum (i : α) :
    Measurable (fun w : Edge α → ℝ ↦ degreeSum w i) := by
  classical
  unfold degreeSum
  exact Finset.measurable_sum _ (fun e _ ↦ by
    split_ifs
    · exact measurable_pi_apply e
    · exact measurable_const)

theorem measurableSet_regularEvent :
    MeasurableSet (regularEvent : Set (Edge α → ℝ)) := by
  classical
  have h : (regularEvent : Set (Edge α → ℝ)) =
      ⋂ (i : α) (j : α), {w | degreeSum w i = degreeSum w j} := by
    ext w
    simp [regularEvent]
  rw [h]
  exact MeasurableSet.iInter (fun i ↦ MeasurableSet.iInter (fun j ↦
    measurableSet_eq_fun (measurable_degreeSum i) (measurable_degreeSum j)))

theorem probability_induced_regular_eq (p : Edge α → Set.Icc (0 : ℝ) 1) (S : Finset α) :
    (graphLaw p).real (inducedRegularEvent S) = (graphLaw (induce S p)).real regularEvent := by
  simp only [measureReal_def, inducedRegularEvent]
  rw [← (measurePreserving_induce p S).measure_preimage measurableSet_regularEvent.nullMeasurableSet]

end BoundedEdgeRegularSubgraphs
