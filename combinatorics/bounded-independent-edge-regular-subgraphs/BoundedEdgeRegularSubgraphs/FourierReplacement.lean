module

public import BoundedEdgeRegularSubgraphs.TorusBernoulli
import Mathlib.Tactic

/-!
# Comparing Fourier products after replacing a coordinate
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem fourier_one_phase_add (t u : PhaseCircle) :
    fourier 1 (t + u) = fourier 1 t * fourier 1 u := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The modulus of the full integrand is the product of the Bernoulli moduli
on the torus, independently of the target degree vector. -/
theorem degreeFourier_norm_eq_phase_product (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → PhaseCircle) :
    ‖degreeFourier A q d t‖ =
      ∏ e ∈ A, ‖phaseBernoulliFactor (q e) (t e.val.1 + t e.val.2)‖ := by
  have hχ : ‖latticeCharacter (-d) t‖ = 1 := by
    simp [latticeCharacter, norm_prod]
  unfold degreeFourier
  rw [norm_mul, hχ, one_mul, Complex.norm_prod]
  apply Finset.prod_congr rfl
  intro e _
  rw [phaseBernoulliFactor, fourier_one_phase_add, edgeCharacter]

/-- A pointwise replacement-factor inequality multiplies over all available
edges, including when a factor vanishes. -/
theorem degreeFourier_norm_le_of_factor_comparison (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t s : α → PhaseCircle)
    (c : Edge α → ℝ)
    (h : ∀ e ∈ A, ‖phaseBernoulliFactor (q e) (t e.val.1 + t e.val.2)‖ ≤
      c e * ‖phaseBernoulliFactor (q e) (s e.val.1 + s e.val.2)‖) :
    ‖degreeFourier A q d t‖ ≤ (∏ e ∈ A, c e) * ‖degreeFourier A q d s‖ := by
  rw [degreeFourier_norm_eq_phase_product, degreeFourier_norm_eq_phase_product,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) h

/-- Replacing an exceptional coordinate by one close to a mode makes a
uniform gain on each edge to a coordinate close to that mode. -/
theorem phaseBernoulliFactor_compare_exceptional {η lower : ℝ}
    (hη : 0 < η) (hη' : 7 * η ≤ Real.pi) (hlower : 0 < lower) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (q : ℝ) (x y z b : PhaseCircle),
      lower ≤ q * (1 - q) → (b = 0 ∨ b = (Real.pi : PhaseCircle)) →
      10 * η ≤ ‖x - b‖ → ‖y - b‖ ≤ 3 * η → ‖z - b‖ ≤ η →
      ‖phaseBernoulliFactor q (x + y)‖ ≤ Real.exp (-γ) * ‖phaseBernoulliFactor q (z + y)‖ := by
  obtain ⟨γ, hγ, h⟩ := phaseBernoulliFactor_compare_replacement hη hη' hlower
  refine ⟨γ, hγ, ?_⟩
  intro q x y z b hq hb hx hy hz
  have hbb : b + b = 0 := by
    rcases hb with rfl | rfl
    · simp
    · rw [← AddCircle.coe_add, ← two_mul, AddCircle.coe_period]
  have hsum (a : PhaseCircle) : (a - b) + (y - b) = a + y := by
    calc
      _ = a + y - (b + b) := by abel
      _ = _ := by rw [hbb, sub_zero]
  have hlo : 7 * η ≤ ‖x + y‖ := by
    have hh : ‖x - b‖ ≤ ‖x + y‖ + ‖y - b‖ := by
      have hstep := norm_sub_le ((x - b) + (y - b)) (y - b)
      rw [add_sub_cancel_right, hsum x] at hstep
      exact hstep
    linarith only [hh, hx, hy]
  have hhi : ‖z + y‖ ≤ 4 * η := by
    have hh := norm_add_le (z - b) (y - b)
    rw [hsum z] at hh
    linarith only [hh, hy, hz]
  exact h q (x + y) (z + y) hq hlo hhi

end BoundedEdgeRegularSubgraphs
