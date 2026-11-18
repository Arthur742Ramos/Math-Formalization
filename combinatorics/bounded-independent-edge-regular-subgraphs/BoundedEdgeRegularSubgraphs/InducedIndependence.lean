module

public import BoundedEdgeRegularSubgraphs.Induce
import BoundedEdgeRegularSubgraphs.Incidence

/-!
# Induced graphs with at most one common vertex

The induced graphs then depend on disjoint collections of edge coordinates.
-/

public section

open MeasureTheory ProbabilityTheory

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]


private theorem edgesInside_disjoint (S T : Finset α) (h : (S ∩ T).card ≤ 1) :
    Disjoint (edgesInside S) (edgesInside T) := by
  rw [Finset.disjoint_left]
  intro e heS heT
  have hS := (Finset.mem_filter.mp heS).2
  have hT := (Finset.mem_filter.mp heT).2
  have hone : 1 < (S ∩ T).card := Finset.one_lt_card_iff.mpr
    ⟨e.val.1, e.val.2, Finset.mem_inter.mpr ⟨hS.1, hT.1⟩,
      Finset.mem_inter.mpr ⟨hS.2, hT.2⟩, ne_of_lt e.property⟩
  exact (not_lt_of_ge h) hone

private def fromInside (S : Finset α) (w : edgesInside S → ℝ) (e : Edge ↥S) : ℝ :=
  w ⟨inducedEdge S e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.val.1.property, e.val.2.property⟩⟩

private theorem measurable_fromInside (S : Finset α) : Measurable (fromInside S) := by
  apply measurable_pi_iff.mpr
  intro e
  exact measurable_pi_apply _

/-- The two induced edge arrays are independent when the vertex overlap has size at most one. -/
theorem indepFun_induce_of_small_overlap (p : Edge α → Set.Icc (0 : ℝ) 1)
    (S T : Finset α) (h : (S ∩ T).card ≤ 1) :
    IndepFun (induce S) (induce T) (graphLaw p : Measure (Edge α → ℝ)) := by
  have hind : iIndepFun (fun (e : Edge α) (w : Edge α → ℝ) ↦ w e) (graphLaw p) := by
    unfold graphLaw
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hcoords := iIndepFun.indepFun_finset (edgesInside S) (edgesInside T)
    (edgesInside_disjoint S T h) hind (fun e ↦ measurable_pi_apply e)
  exact hcoords.comp (measurable_fromInside S) (measurable_fromInside T)

/-- The regularity events have the product probability in the zero- and one-vertex overlap cases. -/
theorem probability_induced_regular_inter_of_small_overlap
    (p : Edge α → Set.Icc (0 : ℝ) 1) (S T : Finset α) (h : (S ∩ T).card ≤ 1) :
    (graphLaw p).real (inducedRegularEvent S ∩ inducedRegularEvent T) =
      (graphLaw p).real (inducedRegularEvent S) * (graphLaw p).real (inducedRegularEvent T) := by
  have hmeasure := (indepFun_induce_of_small_overlap p S T h).measure_inter_preimage_eq_mul
    regularEvent regularEvent measurableSet_regularEvent measurableSet_regularEvent
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal hmeasure

end BoundedEdgeRegularSubgraphs
