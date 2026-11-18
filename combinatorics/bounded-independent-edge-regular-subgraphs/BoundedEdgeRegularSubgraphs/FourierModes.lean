module

public import BoundedEdgeRegularSubgraphs.Fourier
public import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic

/-!
# Localisation to the two Fourier modes
-/

public section

namespace BoundedEdgeRegularSubgraphs

/-- If twice a phase is close to zero, the phase is close to zero or to π. -/
theorem phase_near_zero_or_pi (t : PhaseCircle) {r : ℝ} (ht : ‖t + t‖ ≤ r) :
    ∃ b : PhaseCircle, (b = 0 ∨ b = (Real.pi : PhaseCircle)) ∧ ‖t - b‖ ≤ r / 2 := by
  obtain ⟨x⟩ := t
  change ‖(x : PhaseCircle) + (x : PhaseCircle)‖ ≤ r at ht
  let m : ℤ := round (Real.pi⁻¹ * x)
  have hπ : 0 < Real.pi := Real.pi_pos
  have hround : round ((2 * Real.pi)⁻¹ * (2 * x)) = m := by
    dsimp only [m]
    congr 1
    field_simp
  rw [← AddCircle.coe_add, ← two_mul, AddCircle.norm_eq, hround] at ht
  have hr : |x - (m : ℝ) * Real.pi| ≤ r / 2 := by
    rw [show 2 * x - (m : ℝ) * (2 * Real.pi) =
      2 * (x - (m : ℝ) * Real.pi) by ring, abs_mul, abs_two] at ht
    linarith
  let b : PhaseCircle := ((m : ℝ) * Real.pi : ℝ)
  have hb : b = 0 ∨ b = (Real.pi : PhaseCircle) := by
    have hz (j : ℤ) : (((j : ℝ) * (2 * Real.pi) : ℝ) : PhaseCircle) = 0 := by
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      change (((m : ℝ) * Real.pi : ℝ) : PhaseCircle) = 0
      have he : (m : ℝ) * Real.pi = (j : ℝ) * (2 * Real.pi) := by
        rw [hj]
        push_cast
        ring
      rw [he, hz]
    · right
      change (((m : ℝ) * Real.pi : ℝ) : PhaseCircle) = (Real.pi : PhaseCircle)
      have he : (m : ℝ) * Real.pi = (j : ℝ) * (2 * Real.pi) + Real.pi := by
        rw [hj]
        push_cast
        ring
      rw [he, AddCircle.coe_add, hz, zero_add]
  refine ⟨b, hb, ?_⟩
  change ‖(x : PhaseCircle) - (((m : ℝ) * Real.pi : ℝ) : PhaseCircle)‖ ≤ r / 2
  rw [← AddCircle.coe_sub]
  refine (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (2 * Real.pi))).trans ?_
  rwa [Real.norm_eq_abs]

/-- A triangle of good pairs puts its first coordinate within 3η/2 of one of the two modes. -/
theorem phase_good_triangle (x y z : PhaseCircle) {η : ℝ}
    (hxy : ‖x + y‖ ≤ η) (hxz : ‖x + z‖ ≤ η) (hyz : ‖y + z‖ ≤ η) :
    ∃ b : PhaseCircle, (b = 0 ∨ b = (Real.pi : PhaseCircle)) ∧ ‖x - b‖ ≤ 3 * η / 2 := by
  apply phase_near_zero_or_pi
  calc
    ‖x + x‖ = ‖(x + y) + (x + z) - (y + z)‖ := by congr 1; abel
    _ ≤ ‖(x + y) + (x + z)‖ + ‖y + z‖ := norm_sub_le _ _
    _ ≤ _ := by linarith [norm_add_le (x + y) (x + z)]

/-- Every good neighbour of a phase close to a mode is also close to that mode. -/
theorem phase_good_neighbour (x y b : PhaseCircle) {η : ℝ}
    (hb : b = 0 ∨ b = (Real.pi : PhaseCircle))
    (hx : ‖x - b‖ ≤ 3 * η / 2) (hxy : ‖x + y‖ ≤ η) :
    ‖y - b‖ ≤ 5 * η / 2 := by
  have hbb : b + b = 0 := by
    rcases hb with rfl | rfl
    · simp
    · rw [← AddCircle.coe_add, ← two_mul, AddCircle.coe_period]
  calc
    ‖y - b‖ = ‖(x + y) - (x - b)‖ := by
      congr 1
      have hneg : -b = b := by
        apply neg_eq_iff_add_eq_zero.mpr
        exact hbb
      rw [sub_eq_add_neg y b, hneg]
      abel
    _ ≤ ‖x + y‖ + ‖x - b‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

end BoundedEdgeRegularSubgraphs
