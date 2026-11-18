module

public import BoundedEdgeRegularSubgraphs.InducedConditionalRatio
public import BoundedEdgeRegularSubgraphs.OverlapAssignmentPartition
public import BoundedEdgeRegularSubgraphs.FreshEdgeAtoms
public import BoundedEdgeRegularSubgraphs.InducedIndependence
import Mathlib.Tactic

/-!
# Joint induced atoms at arbitrary overlaps
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Specified common degrees on candidates sharing at most one vertex
are independent. -/
theorem probability_inducedDegreeAtom_inter_of_small_overlap
    (p : Edge α → Icc (0 : ℝ) 1) (S T : Finset α) (d e : ℤ) (h : (S ∩ T).card ≤ 1) :
    (graphLaw p).real (inducedDegreeAtom S d ∩ inducedDegreeAtom T e) =
      (graphLaw p).real (inducedDegreeAtom S d) * (graphLaw p).real (inducedDegreeAtom T e) := by
  have h' := (indepFun_induce_of_small_overlap p S T h).measure_inter_preimage_eq_mul
    (degreeAtom Finset.univ (fun _ ↦ d)) (degreeAtom Finset.univ (fun _ ↦ e))
    (measurableSet_degreeAtom _ _) (measurableSet_degreeAtom _ _)
  simpa only [inducedDegreeAtom, measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h'

theorem probability_inducedDegreeAtom_inter_div_mul_le_of_lower
    (p : Edge α → Icc (0 : ℝ) 1) (S T : Finset α) (d e : ℤ) (B : ℝ)
    (hS : 0 < (graphLaw p).real (inducedDegreeAtom S d))
    (hT : Real.exp (-B) ≤ (graphLaw p).real (inducedDegreeAtom T e)) :
    (graphLaw p).real (inducedDegreeAtom S d ∩ inducedDegreeAtom T e) /
      ((graphLaw p).real (inducedDegreeAtom S d) * (graphLaw p).real (inducedDegreeAtom T e)) ≤ Real.exp B := by
  have : IsProbabilityMeasure (graphLaw p) := by unfold graphLaw; infer_instance
  let μ := graphLaw p
  let E := inducedDegreeAtom S d
  let F := inducedDegreeAtom T e
  have hF : 0 < μ.real F := (Real.exp_pos _).trans_le hT
  apply (div_le_iff₀ (mul_pos hS hF)).2
  refine (measureReal_mono inter_subset_left).trans ?_
  have hh := mul_le_mul_of_nonneg_left hT (Real.exp_nonneg B)
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hS.le
  nlinarith only [hh']

/-- The fresh-edge joint bound (3.1) before division by the two
candidate probabilities. -/
theorem probability_inducedDegreeAtom_inter_le_fresh_edges {ξ : ℝ}
    (hξ : 0 < ξ) (hξ₁ : ξ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Edge α → Icc (0 : ℝ) 1), (∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) →
      ∀ (S T : Finset α) (d e : ℤ),
        (graphLaw p).real (inducedDegreeAtom S d ∩ inducedDegreeAtom T e) ≤
          ((C / Real.sqrt ((T.card - (S ∩ T).card : ℕ) + 1)) ^ (S ∩ T).card) *
            (graphLaw p).real (inducedDegreeAtom S d) := by
  classical
  obtain ⟨C, hC, hScalar⟩ := probability_countAtom_le_inv_sqrt ξ hξ hξ₁
  refine ⟨C, hC, ?_⟩
  intro p hp S T d e
  let μ := graphLaw p
  let J := S ∩ T
  let E := inducedDegreeAtom S d
  let F := inducedDegreeAtom T e
  let b := (C / Real.sqrt ((T.card - J.card : ℕ) + 1)) ^ J.card
  have hE : MeasurableSet E := measurableSet_inducedDegreeAtom _ _
  have hF : MeasurableSet F := measurableSet_inducedDegreeAtom _ _
  have hpoint (a : edgesInside J → Bool) : μ.real ((E ∩ F) ∩ overlapAssignmentEvent J (binaryOverlap J a)) ≤
      b * μ.real (E ∩ overlapAssignmentEvent J (binaryOverlap J a)) := by
    let h := binaryOverlap J a
    let H := overlapAssignmentEvent J h
    have hpos : 0 < μ.real H := probability_overlapAssignment_pos p J h
      (fun e _ ↦ ⟨hξ.trans_le (hp e).1, (hp e).2.trans_lt (by linarith only [hξ])⟩)
      (fun e _ ↦ binaryOverlap_binary J a e)
    have he := probability_inducedDegreeAtom_joint_conditioned p S T h d e
    have hf : μ.real (F ∩ H) / μ.real H ≤ b := by
      -- The local residual rows can be handled independently on the second candidate.
      let q := induce T p
      let I := overlapVertices T S
      let H' := overlapAssignmentEvent I (induce T h)
      let F' := degreeAtom Finset.univ (fun _ : T ↦ e)
      have hpre : induce T ⁻¹' H' = H := by
        rw [show H' = overlapAssignmentEvent (overlapVertices T S) (induce T h) from rfl,
          preimage_overlapAssignment_induce, Finset.inter_comm T S]
      have hμ := measurePreserving_induce p T
      have hH := hμ.measure_preimage (measurableSet_overlapAssignmentEvent I (induce T h)).nullMeasurableSet
      have hF₀ := hμ.measure_preimage
        ((measurableSet_degreeAtom Finset.univ (fun _ : T ↦ e)).inter
          (measurableSet_overlapAssignmentEvent I (induce T h))).nullMeasurableSet
      change graphLaw p (induce T ⁻¹' H') = graphLaw q H' at hH
      change graphLaw p (induce T ⁻¹' (F' ∩ H')) = graphLaw q (F' ∩ H') at hF₀
      rw [hpre] at hH
      rw [preimage_inter, hpre] at hF₀
      have hL : μ.real (F ∩ H) = (graphLaw q).real (F' ∩ H') := congrArg ENNReal.toReal hF₀
      have hD : μ.real H = (graphLaw q).real H' := congrArg ENNReal.toReal hH
      rw [hL, hD]
      have hpos' : 0 < (graphLaw q).real H' := hD ▸ hpos
      rw [probability_degreeAtom_given_overlap_eq q I (induce T h) (fun _ ↦ e) hpos']
      have hR := probability_residual_degreeAtom_le_fresh_edges_of_scalar hScalar q
        (fun e ↦ hp (inducedEdge T e)) I ((fun _ ↦ e) - degreeVector (edgesInside I) (induce T h))
      have heq : I.card = J.card := by
        rw [show I = overlapVertices T S from rfl, card_overlapVertices, Finset.inter_comm T S]
      simpa only [b, Fintype.card_coe, heq] using hR
    have ht := (div_le_iff₀ hpos).mp hf
    change μ.real ((E ∩ F) ∩ H) ≤ b * μ.real (E ∩ H)
    apply (le_of_mul_le_mul_right _ hpos)
    change μ.real ((E ∩ F) ∩ H) * μ.real H = μ.real (E ∩ H) * μ.real (F ∩ H) at he
    rw [he]
    exact (mul_le_mul_of_nonneg_left ht measureReal_nonneg).trans_eq (by ring)
  rw [probability_sum_overlapAssignment p J _ (hE.inter hF), probability_sum_overlapAssignment p J _ hE,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ ↦ hpoint a)

end BoundedEdgeRegularSubgraphs
