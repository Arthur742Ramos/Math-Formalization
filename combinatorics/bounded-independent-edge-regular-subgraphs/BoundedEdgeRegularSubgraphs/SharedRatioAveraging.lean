module

public import BoundedEdgeRegularSubgraphs.InducedOverlap
public import BoundedEdgeRegularSubgraphs.OverlapAssignmentPartition
import Mathlib.Tactic

/-!
# Averaging conditional candidate ratios
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- A pair of bounds on the conditional candidate ratios passes to the
joint ratio by averaging the product over the shared coordinates. -/
theorem inducedDegreeAtom_joint_ratio_le_of_shared_bounds
    (p : Edge α → Icc (0 : ℝ) 1) (S T : Finset α) (d e : ℤ)
    {a : ℝ} (ha : 0 ≤ a) (L R : (Edge α → ℝ) → ℝ)
    (hL : ∀ w, 0 ≤ L w) (hR : ∀ w, 0 ≤ R w)
    (hLR : ∀ w h : Edge α → ℝ, w ∈ overlapAssignmentEvent (S ∩ T) h → L w * R w = L h * R h)
    (hE : 0 < (graphLaw p).real (inducedDegreeAtom S d))
    (hF : 0 < (graphLaw p).real (inducedDegreeAtom T e))
    (hH : ∀ b : edgesInside (S ∩ T) → Bool,
      0 < (graphLaw p).real (overlapAssignmentEvent (S ∩ T) (binaryOverlap (S ∩ T) b)))
    (hLeft : ∀ b : edgesInside (S ∩ T) → Bool,
      let h := binaryOverlap (S ∩ T) b
      let H := overlapAssignmentEvent (S ∩ T) h
      ((graphLaw p).real (inducedDegreeAtom S d ∩ H) / (graphLaw p).real H) /
        (graphLaw p).real (inducedDegreeAtom S d) ≤ a * L h)
    (hRight : ∀ b : edgesInside (S ∩ T) → Bool,
      let h := binaryOverlap (S ∩ T) b
      let H := overlapAssignmentEvent (S ∩ T) h
      ((graphLaw p).real (inducedDegreeAtom T e ∩ H) / (graphLaw p).real H) /
        (graphLaw p).real (inducedDegreeAtom T e) ≤ a * R h) :
    (graphLaw p).real (inducedDegreeAtom S d ∩ inducedDegreeAtom T e) /
      ((graphLaw p).real (inducedDegreeAtom S d) * (graphLaw p).real (inducedDegreeAtom T e)) ≤
        a ^ 2 * ∫ w, L w * R w ∂graphLaw p := by
  let μ := graphLaw p
  let J := S ∩ T
  let E := inducedDegreeAtom S d
  let F := inducedDegreeAtom T e
  have hpoint (b : edgesInside J → Bool) :
      μ.real ((E ∩ F) ∩ overlapAssignmentEvent J (binaryOverlap J b)) / (μ.real E * μ.real F) ≤
        a ^ 2 * (μ.real (overlapAssignmentEvent J (binaryOverlap J b)) * (L (binaryOverlap J b) * R (binaryOverlap J b))) := by
    let h := binaryOverlap J b
    let H := overlapAssignmentEvent J h
    let u := (μ.real (E ∩ H) / μ.real H) / μ.real E
    let v := (μ.real (F ∩ H) / μ.real H) / μ.real F
    have hpos : 0 < μ.real H := hH b
    have hr := probability_inducedDegreeAtom_joint_conditioned p S T h d e
    change μ.real ((E ∩ F) ∩ H) * μ.real H = μ.real (E ∩ H) * μ.real (F ∩ H) at hr
    have heq : μ.real ((E ∩ F) ∩ H) / (μ.real E * μ.real F) = μ.real H * (u * v) := by
      dsimp only [u, v]
      field_simp [hpos.ne', hE.ne', hF.ne']
      rw [hr]
    rw [heq]
    have h₁ : u ≤ a * L h := hLeft b
    have h₂ : v ≤ a * R h := hRight b
    have hv : 0 ≤ v := div_nonneg (div_nonneg measureReal_nonneg hpos.le) hF.le
    have h := mul_le_mul h₁ h₂ hv (mul_nonneg ha (hL _))
    exact (mul_le_mul_of_nonneg_left h hpos.le).trans_eq (by ring)
  have hEF : MeasurableSet (E ∩ F) :=
    (measurableSet_inducedDegreeAtom _ _).inter (measurableSet_inducedDegreeAtom _ _)
  rw [probability_sum_overlapAssignment p J _ hEF, Finset.sum_div,
    integral_eq_sum_binaryOverlap J (fun w ↦ L w * R w) hLR, Finset.mul_sum]
  exact Finset.sum_le_sum (fun b _ ↦ hpoint b)

end BoundedEdgeRegularSubgraphs
