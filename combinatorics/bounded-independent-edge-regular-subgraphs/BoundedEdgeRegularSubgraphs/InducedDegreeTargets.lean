module

public import BoundedEdgeRegularSubgraphs.EdgeNeighbours
public import BoundedEdgeRegularSubgraphs.OrderUpper
public import BoundedEdgeRegularSubgraphs.Induce
import Mathlib.Tactic

/-!
# Degree sums and fixed targets on induced vertex sets
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]

omit [Fintype α] in
/-- Extend the weight of an unordered pair to both orientations. -/
noncomputable def symmetricEdgeWeight (w : Edge α → ℝ) (i j : α) : ℝ :=
  if h : i ≠ j then w ⟨(min i j, max i j), min_lt_max.mpr h⟩ else 0

omit [Fintype α] in
theorem symmetricEdgeWeight_eq_of_lt (w : Edge α → ℝ) {i j : α} (h : i < j) :
    symmetricEdgeWeight w i j = w ⟨(i, j), h⟩ := by
  simp [symmetricEdgeWeight, h.ne, min_eq_left h.le, max_eq_right h.le]

omit [Fintype α] in
theorem symmetricEdgeWeight_eq_of_gt (w : Edge α → ℝ) {i j : α} (h : j < i) :
    symmetricEdgeWeight w i j = w ⟨(j, i), h⟩ := by
  simp [symmetricEdgeWeight, h.ne.symm, min_eq_right h.le, max_eq_left h.le]

/-- The incident-edge sum of a vertex in an induced array is the sum
over the other vertices in its set. -/
theorem degreeSum_induce_eq_sum_erase (S : Finset α) (w : Edge α → ℝ) (i : S) :
    degreeSum (induce S w) i = ∑ j ∈ S.erase i.val, symmetricEdgeWeight w i.val j := by
  classical
  have h : degreeSum (induce S w) i = ∑ e ∈ incidentEdges Finset.univ i, induce S w e := by
    rw [incidentEdges, Finset.sum_filter]
    unfold degreeSum
    apply Finset.sum_congr rfl
    intro e _
    have he : (e.val.1 = i ∨ e.val.2 = i) ↔ (i = e.val.1 ∨ i = e.val.2) :=
      ⟨fun h ↦ h.imp Eq.symm Eq.symm, fun h ↦ h.imp Eq.symm Eq.symm⟩
    by_cases hx : e.val.1 = i ∨ e.val.2 = i
    · rw [ite_eq_left (he.mp hx), ite_eq_left hx]
    · rw [ite_eq_right (fun h ↦ hx (he.mpr h)), ite_eq_right hx]
  rw [h]
  have hMem (e : Edge ↥S) : e ∈ incidentEdges Finset.univ i ↔ e.val.1 = i ∨ e.val.2 = i := by
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  refine Finset.sum_bij (fun e _ ↦ (otherEndpoint i e).val) ?_ ?_ ?_ ?_
  · intro e he
    apply Finset.mem_erase.mpr
    exact ⟨fun h ↦ otherEndpoint_ne he (Subtype.ext h), (otherEndpoint i e).property⟩
  · intro e he f hf h
    exact otherEndpoint_injOn Finset.univ i he hf (Subtype.ext h)
  · intro j hj
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    let j' : S := ⟨j, hj⟩
    have hne' : i ≠ j' := fun h ↦ hne (congrArg Subtype.val h).symm
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · refine ⟨⟨(i, j'), hlt⟩, ?_, ?_⟩
      · exact (hMem _).2 (Or.inl rfl)
      · simp only [otherEndpoint, if_true, j']
    · refine ⟨⟨(j', i), hlt⟩, ?_, ?_⟩
      · exact (hMem _).2 (Or.inr rfl)
      · simp only [otherEndpoint, ite_eq_right hlt.ne, j']
  · intro e he
    have hinc : e.val.1 = i ∨ e.val.2 = i := (hMem e).1 he
    rcases hinc with h₁ | h₂
    · rw [otherEndpoint, if_pos h₁]
      have he' : i < e.val.2 := h₁ ▸ e.property
      rw [symmetricEdgeWeight_eq_of_lt w (show i.val < e.val.2.val from he')]
      exact congrArg w (Subtype.ext (Prod.ext (congrArg Subtype.val h₁) rfl))
    · have he' : e.val.1 < i := h₂ ▸ e.property
      rw [otherEndpoint, if_neg he'.ne, symmetricEdgeWeight_eq_of_gt w (show e.val.1.val < i.val from he')]
      exact congrArg w (Subtype.ext (Prod.ext rfl (congrArg Subtype.val h₂)))

/-- The induced graph on the specified vertices has the prescribed common degree. -/
noncomputable def inducedDegreeAtom (S : Finset α) (d : ℤ) : Set (Edge α → ℝ) :=
  induce S ⁻¹' degreeAtom Finset.univ (fun _ ↦ d)

theorem measurableSet_inducedDegreeAtom (S : Finset α) (d : ℤ) :
    MeasurableSet (inducedDegreeAtom S d) :=
  (measurableSet_degreeAtom _ _).preimage
    (measurable_pi_iff.mpr (fun e ↦ measurable_pi_apply (inducedEdge S e)))

theorem probability_inducedDegreeAtom_eq (p : Edge α → Icc (0 : ℝ) 1) (S : Finset α) (d : ℤ) :
    (graphLaw p).real (inducedDegreeAtom S d) =
      (graphLaw (induce S p)).real (degreeAtom Finset.univ (fun _ ↦ d)) := by
  simp only [measureReal_def, inducedDegreeAtom]
  rw [(measurePreserving_induce p S).measure_preimage
    (measurableSet_degreeAtom _ _).nullMeasurableSet]

theorem degreeVector_univ_reindex (f : α ≃o β) (w : Edge β → ℝ) (i : α) :
    degreeVector Finset.univ (w ∘ edgeEquiv f) i = degreeVector Finset.univ w (f i) := by
  classical
  simp only [degreeVector, Finset.sum_apply]
  rw [← Equiv.sum_comp (edgeEquiv f)]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : w (edgeEquiv f e) = 1
  · simp only [sampledIncidence, Function.comp_apply, he, if_pos]
    change (if i = e.val.1 then 1 else 0) + (if i = e.val.2 then 1 else 0) =
      (if f i = f e.val.1 then 1 else 0) + (if f i = f e.val.2 then 1 else 0)
    simp only [f.injective.eq_iff]
  · simp only [sampledIncidence, Function.comp_apply, he, if_false, Pi.zero_apply]

theorem probability_degreeAtom_reindex (f : α ≃o β) (p : Edge β → Icc (0 : ℝ) 1) (d : β → ℤ) :
    (graphLaw (p ∘ edgeEquiv f)).real (degreeAtom Finset.univ (d ∘ f)) =
      (graphLaw p).real (degreeAtom Finset.univ d) := by
  classical
  let e := MeasurableEquiv.piCongrLeft (fun _ : Edge β ↦ ℝ) (edgeEquiv f)
  have hmap : MeasurePreserving e (graphLaw (p ∘ edgeEquiv f)) (graphLaw p) :=
    measurePreserving_piCongrLeft (fun i ↦ bernoulliMeasure (1 : ℝ) 0 (p i)) (edgeEquiv f)
  have hpre : e.symm ⁻¹' (degreeAtom Finset.univ (d ∘ f)) = degreeAtom Finset.univ d := by
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
  rw [measureReal_def, measureReal_def, ← (hmap.symm e).measure_preimage
    (measurableSet_degreeAtom _ _).nullMeasurableSet, hpre]

end BoundedEdgeRegularSubgraphs
