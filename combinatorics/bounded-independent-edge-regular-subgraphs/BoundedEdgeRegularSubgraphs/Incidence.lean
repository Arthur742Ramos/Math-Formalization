module

public import BoundedEdgeRegularSubgraphs.Model
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Integer degree vectors

An available edge set permits the full array and the array after exposing the
edges within an overlap to use the same degree vector.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The vector with a one in each of the two endpoint coordinates. -/
def edgeIncidence (e : Edge α) (i : α) : ℤ :=
  (if i = e.val.1 then 1 else 0) + (if i = e.val.2 then 1 else 0)

/-- The contribution of a single edge to the sampled integer degree vector. -/
noncomputable def sampledIncidence (e : Edge α) (x : ℝ) : α → ℤ :=
  if x = 1 then edgeIncidence e else 0

/-- The integer degrees from just the available edges. -/
noncomputable def degreeVector (A : Finset (Edge α)) (w : Edge α → ℝ) : α → ℤ :=
  ∑ e ∈ A, sampledIncidence e (w e)

/-- The event that the available edges give the specified degree vector. -/
noncomputable def degreeAtom (A : Finset (Edge α)) (d : α → ℤ) : Set (Edge α → ℝ) :=
  {w | degreeVector A w = d}

/-- The edges with both endpoints in the overlap. -/
def edgesInside (S : Finset α) : Finset (Edge α) :=
  Finset.univ.filter (fun e ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S)

/-- Delete the edge coordinates with both endpoints in the given overlap. -/
def edgesOutsideOverlap (S : Finset α) : Finset (Edge α) :=
  Finset.univ.filter (fun e ↦ ¬ (e.val.1 ∈ S ∧ e.val.2 ∈ S))

omit [Fintype α] in
theorem measurable_degreeVector (A : Finset (Edge α)) : Measurable (degreeVector A) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  simp only [degreeVector, Finset.sum_apply]
  refine Finset.measurable_sum _ (fun e _ ↦ ?_)
  change Measurable (fun w : Edge α → ℝ ↦ (sampledIncidence e (w e)) i)
  have h : Measurable (fun x : ℝ ↦ if x = 1 then edgeIncidence e i else (0 : ℤ)) :=
    Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
  have hm : Measurable (fun w : Edge α → ℝ ↦ w e) := measurable_pi_apply e
  convert h.comp hm using 1
  funext w
  by_cases hw : w e = 1 <;> simp [sampledIncidence, hw]

theorem measurableSet_degreeAtom (A : Finset (Edge α)) (d : α → ℤ) :
    MeasurableSet (degreeAtom A d) := by
  exact measurableSet_eq_fun (measurable_degreeVector A) measurable_const

private theorem sum_edgeIncidence (e : Edge α) : ∑ i, edgeIncidence e i = 2 := by
  simp [edgeIncidence, Finset.sum_add_distrib]

/-- Every integer degree vector satisfies the handshake parity condition. -/
theorem even_sum_degreeVector (A : Finset (Edge α)) (w : Edge α → ℝ) :
    Even (∑ i, degreeVector A w i) := by
  classical
  refine ⟨∑ e ∈ A, if w e = 1 then (1 : ℤ) else 0, ?_⟩
  simp only [degreeVector, Finset.sum_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ ↦ ?_)
  by_cases h : w e = 1 <;> simp [sampledIncidence, h, sum_edgeIncidence]

/-- On binary outcomes the full integer degree agrees with the original degree sum. -/
theorem degreeVector_univ_eq_degreeSum (w : Edge α → ℝ)
    (hw : ∀ e, w e = 0 ∨ w e = 1) (i : α) :
    (degreeVector Finset.univ w i : ℝ) = degreeSum w i := by
  classical
  simp only [degreeVector, degreeSum, Finset.sum_apply, Int.cast_sum]
  refine Finset.sum_congr rfl (fun e _ ↦ ?_)
  rcases hw e with h | h
  · simp [sampledIncidence, h]
  · have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
    by_cases h₁ : i = e.val.1
    · subst i
      simp [sampledIncidence, edgeIncidence, h, hne]
    · by_cases h₂ : i = e.val.2 <;> simp [sampledIncidence, edgeIncidence, h, h₁, h₂, hne.symm]

/-- The degree bridge holds almost surely under the independent-edge law. -/
theorem ae_degreeVector_univ_eq_degreeSum (p : Edge α → Set.Icc (0 : ℝ) 1) :
    ∀ᵐ w ∂graphLaw p, ∀ i, (degreeVector Finset.univ w i : ℝ) = degreeSum w i := by
  filter_upwards [graphLaw_ae_binary p] with w hw
  exact degreeVector_univ_eq_degreeSum w hw

end BoundedEdgeRegularSubgraphs
