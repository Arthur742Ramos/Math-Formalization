module

public import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.MeasureTheory.Constructions.Pi
import BoundedEdgeRegularSubgraphs.PrefixProduct
import Mathlib.Tactic

/-!
# Product laws on disjoint edge coordinate families
-/

public section

open Function MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Injectively selecting an indexed family of edge coordinates gives the
product of their Bernoulli laws, grouped by the family index. -/
theorem measurePreserving_edge_families {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (p : Edge α → Icc (0 : ℝ) 1) (e : ∀ i, κ i → Edge α)
    (he : Function.Injective (fun z : Σ i, κ i ↦ e z.1 z.2)) :
    MeasurePreserving (fun (w : Edge α → ℝ) i j ↦ w (e i j)) (graphLaw p)
      (Measure.pi fun i ↦ Measure.pi fun j ↦ bernoulliMeasure (1 : ℝ) 0 (p (e i j))) := by
  let E (z : Σ i, κ i) := e z.1 z.2
  let Y (w : Edge α → ℝ) (z : Σ i, κ i) := w (E z)
  let μ (z : Σ i, κ i) := bernoulliMeasure (1 : ℝ) 0 (p (E z))
  have hm (z : Σ i, κ i) : Measurable (fun w ↦ Y w z) := measurable_pi_apply (E z)
  have hind : iIndepFun (fun (a : Edge α) (w : Edge α → ℝ) ↦ w a) (graphLaw p) := by
    unfold graphLaw
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hY : MeasurePreserving Y (graphLaw p) (Measure.pi μ) := by
    refine ⟨measurable_pi_iff.mpr hm, ?_⟩
    rw [(hind.precomp he).map_fun_eq_pi_map (fun z ↦ (hm z).aemeasurable)]
    congr 1
    funext z
    exact (measurePreserving_eval (fun a ↦ bernoulliMeasure (1 : ℝ) 0 (p a)) (E z)).map_eq
  exact (measurePreserving_piCurry (fun (i : ι) (_ : κ i) ↦ ℝ) (fun i j ↦ μ ⟨i, j⟩)).comp hY

/-- Induced arrays on pairwise disjoint vertex sets have their joint product law. -/
theorem measurePreserving_induce_disjoint_family {ι : Type*} [Fintype ι]
    (p : Edge α → Icc (0 : ℝ) 1) (S : ι → Finset α) (hS : Pairwise (Disjoint on S)) :
    MeasurePreserving (fun w i ↦ induce (S i) w) (graphLaw p)
      (Measure.pi fun i ↦ graphLaw (induce (S i) p)) := by
  classical
  apply measurePreserving_edge_families p (fun i ↦ inducedEdge (S i))
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := by
    by_contra hne
    have ht : a.val.1.val = b.val.1.val := congrArg (fun e : Edge α ↦ e.val.1) h
    exact (Finset.disjoint_left.mp (hS hne)) a.val.1.property
      (by simpa only [ht] using b.val.1.property)
  subst j
  cases inducedEdge_injective (S i) h
  rfl

/-- Measurable events in pairwise disjoint induced arrays multiply exactly. -/
theorem probability_induced_disjoint_family {ι : Type*} [Fintype ι]
    (p : Edge α → Icc (0 : ℝ) 1) (S : ι → Finset α) (hS : Pairwise (Disjoint on S))
    (E : ∀ i, Set (Edge ↥(S i) → ℝ)) (hE : ∀ i, MeasurableSet (E i)) :
    (graphLaw p).real {w | ∀ i, induce (S i) w ∈ E i} =
      ∏ i, (graphLaw (induce (S i) p)).real (E i) := by
  classical
  let P := Set.pi Set.univ E
  letI : ∀ i, SigmaFinite (graphLaw (induce (S i) p)) := fun i ↦ by unfold graphLaw; infer_instance
  have hP : MeasurableSet P := MeasurableSet.pi Set.countable_univ (fun i _ ↦ hE i)
  have h := (measurePreserving_induce_disjoint_family p S hS).measure_preimage hP.nullMeasurableSet
  change graphLaw p ((fun w i ↦ induce (S i) w) ⁻¹' P) =
    (Measure.pi fun i ↦ graphLaw (induce (S i) p)) P at h
  have he : (fun w i ↦ induce (S i) w) ⁻¹' P = {w | ∀ i, induce (S i) w ∈ E i} := by
    ext w
    simp [P, Set.mem_pi]
  rw [he, show P = Set.pi Set.univ E by rfl, Measure.pi_pi] at h
  exact (congrArg ENNReal.toReal h).trans (ENNReal.toReal_prod _ _)

end BoundedEdgeRegularSubgraphs
