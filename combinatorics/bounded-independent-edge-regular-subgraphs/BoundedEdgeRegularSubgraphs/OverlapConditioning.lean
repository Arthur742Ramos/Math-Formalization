module

public import BoundedEdgeRegularSubgraphs.Incidence
import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Conditioning on a fixed assignment of the common edges
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The event specifying all edge coordinates within the overlap. -/
def overlapAssignmentEvent (S : Finset α) (h : Edge α → ℝ) : Set (Edge α → ℝ) :=
  {w | ∀ e ∈ edgesInside S, w e = h e}

private noncomputable def extendEdgeData (A : Finset (Edge α)) (x : A → ℝ) (e : Edge α) : ℝ := by
  classical
  exact if h : e ∈ A then x ⟨e, h⟩ else 0

omit [Fintype α] in
private theorem measurable_extendEdgeData (A : Finset (Edge α)) : Measurable (extendEdgeData A) := by
  apply measurable_pi_iff.mpr
  intro e
  by_cases he : e ∈ A
  · simpa [extendEdgeData, he] using (measurable_pi_apply (⟨e, he⟩ : ↥A) :
      Measurable (fun x : A → ℝ ↦ x ⟨e, he⟩))
  · simp [extendEdgeData, he, measurable_const]

omit [Fintype α] in
private theorem degreeVector_extendEdgeData (A : Finset (Edge α)) (w : Edge α → ℝ) :
    degreeVector A (extendEdgeData A (fun e : ↥A ↦ w e.val)) = degreeVector A w := by
  unfold degreeVector
  exact Finset.sum_congr rfl (fun e he ↦ by simp [extendEdgeData, he])

private theorem degreeVector_split_overlap (S : Finset α) (w : Edge α → ℝ) :
    degreeVector Finset.univ w =
      degreeVector (edgesOutsideOverlap S) w + degreeVector (edgesInside S) w := by
  classical
  unfold degreeVector
  rw [add_comm]
  exact (Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S)
    (fun e ↦ sampledIncidence e (w e))).symm

private theorem probability_residual_inter_overlap_eq
    (p : Edge α → Set.Icc (0 : ℝ) 1) (S : Finset α) (h : Edge α → ℝ) (z : α → ℤ) :
    (graphLaw p).real (degreeAtom (edgesOutsideOverlap S) z ∩ overlapAssignmentEvent S h) =
      (graphLaw p).real (degreeAtom (edgesOutsideOverlap S) z) *
        (graphLaw p).real (overlapAssignmentEvent S h) := by
  classical
  let A := edgesOutsideOverlap S
  let I := edgesInside S
  have hAI : Disjoint A I := by
    rw [Finset.disjoint_left]
    intro e he he'
    exact (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp he').2
  have hind : iIndepFun (fun (e : Edge α) (w : Edge α → ℝ) ↦ w e) (graphLaw p) := by
    unfold graphLaw
    exact iIndepFun_pi (X := fun _ ↦ id) (fun _ ↦ aemeasurable_id)
  have hcoords := iIndepFun.indepFun_finset A I hAI hind (fun e ↦ measurable_pi_apply e)
  let E : Set (A → ℝ) := extendEdgeData A ⁻¹' degreeAtom A z
  let H : Set (I → ℝ) := {fun e : ↥I ↦ h e.val}
  have hE : MeasurableSet E := (measurableSet_degreeAtom A z).preimage (measurable_extendEdgeData A)
  have hH : MeasurableSet H := measurableSet_singleton _
  have heq : (fun (w : Edge α → ℝ) (e : ↥A) ↦ w e.val) ⁻¹' E = degreeAtom A z := by
    ext w
    change degreeVector A (extendEdgeData A (fun e : ↥A ↦ w e.val)) = z ↔ degreeVector A w = z
    rw [degreeVector_extendEdgeData]
  have hheq : (fun (w : Edge α → ℝ) (e : ↥I) ↦ w e.val) ⁻¹' H = overlapAssignmentEvent S h := by
    ext w
    change ((fun e : ↥I ↦ w e.val) = fun e : ↥I ↦ h e.val) ↔ ∀ e ∈ I, w e = h e
    constructor
    · intro hh e he
      exact congrFun hh ⟨e, he⟩
    · intro hh
      funext e
      exact hh e.val e.property
  have hprob := hcoords.measure_inter_preimage_eq_mul E H hE hH
  change graphLaw p (((fun (w : Edge α → ℝ) (e : ↥A) ↦ w e.val) ⁻¹' E) ∩
    ((fun (w : Edge α → ℝ) (e : ↥I) ↦ w e.val) ⁻¹' H)) = _ at hprob
  rw [heq, hheq] at hprob
  simp only [measureReal_def, ← ENNReal.toReal_mul]
  exact congrArg ENNReal.toReal hprob

/-- Every binary assignment on the overlap has positive probability under
strictly interior edge probabilities. -/
theorem probability_overlapAssignment_pos (p : Edge α → Set.Icc (0 : ℝ) 1)
    (S : Finset α) (h : Edge α → ℝ)
    (hp : ∀ e ∈ edgesInside S, 0 < (p e : ℝ) ∧ (p e : ℝ) < 1)
    (hh : ∀ e ∈ edgesInside S, h e = 0 ∨ h e = 1) :
    0 < (graphLaw p).real (overlapAssignmentEvent S h) := by
  classical
  have he : overlapAssignmentEvent S h =
      Set.pi (edgesInside S : Set (Edge α)) (fun e ↦ ({h e} : Set ℝ)) := by
    ext w
    simp [overlapAssignmentEvent, Set.mem_pi]
  rw [he, measureReal_def, graphLaw, Measure.pi_pi_finset, ENNReal.toReal_prod]
  apply Finset.prod_pos
  intro e he
  change 0 < (bernoulliMeasure (1 : ℝ) 0 (p e)).real {h e}
  rcases hh e he with h0 | h1
  · rw [h0, bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    exact sub_pos.mpr (hp e he).2
  · rw [h1, bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    exact (hp e he).1


/-- The conditional degree atom equals the residual atom when the overlap
assignment has positive probability. -/
theorem probability_degreeAtom_given_overlap_eq
    (p : Edge α → Set.Icc (0 : ℝ) 1) (S : Finset α) (h : Edge α → ℝ) (d : α → ℤ)
    (hpos : 0 < (graphLaw p).real (overlapAssignmentEvent S h)) :
    (graphLaw p).real (degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h) /
        (graphLaw p).real (overlapAssignmentEvent S h) =
      (graphLaw p).real (degreeAtom (edgesOutsideOverlap S) (d - degreeVector (edgesInside S) h)) := by
  have he :
      degreeAtom Finset.univ d ∩ overlapAssignmentEvent S h =
        degreeAtom (edgesOutsideOverlap S) (d - degreeVector (edgesInside S) h) ∩
          overlapAssignmentEvent S h := by
    ext w
    change (degreeVector Finset.univ w = d ∧ ∀ e ∈ edgesInside S, w e = h e) ↔
      (degreeVector (edgesOutsideOverlap S) w = d - degreeVector (edgesInside S) h ∧
        ∀ e ∈ edgesInside S, w e = h e)
    apply and_congr_left
    intro hh
    have hw : degreeVector (edgesInside S) w = degreeVector (edgesInside S) h :=
      Finset.sum_congr rfl (fun e he ↦ by rw [hh e he])
    rw [degreeVector_split_overlap, hw, eq_sub_iff_add_eq]
  rw [he, probability_residual_inter_overlap_eq, mul_div_cancel_right₀ _ hpos.ne']

end BoundedEdgeRegularSubgraphs
