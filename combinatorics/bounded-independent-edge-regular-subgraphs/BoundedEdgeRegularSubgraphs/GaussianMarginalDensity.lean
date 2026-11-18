module

public import BoundedEdgeRegularSubgraphs.GaussianMarginalTail
import BoundedEdgeRegularSubgraphs.Vendor.PrekopaLeindler
import Mathlib.Tactic

/-!
# Log-concavity of a marginal
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace BoundedEdgeRegularSubgraphs

/-- Integrating out the remaining coordinates preserves convex superlevel
sets of a log-concave density. -/
theorem convex_superlevel_lintegral_of_joint_logConcave {ι : Type*} [Fintype ι]
    (F : ℝ → (ι → ℝ) → ℝ≥0∞) (hF : ∀ t, Measurable (F t))
    (hfin : ∀ t, (∫⁻ x, F t x) ≠ ∞)
    (hshape : ∀ t s : ℝ, ∀ a : ℝ, 0 < a → a < 1 → ∀ u v,
      F t u ^ a * F s v ^ (1 - a) ≤ F (a * t + (1 - a) * s) (a • u + (1 - a) • v)) :
    ∀ z : ℝ, Convex ℝ {t | z ≤ (∫⁻ x, F t x).toReal} := by
  intro z x hx y hy a b ha hb hab
  change z ≤ (∫⁻ u, F x u).toReal at hx
  change z ≤ (∫⁻ u, F y u).toReal at hy
  change z ≤ (∫⁻ u, F (a * x + b * y) u).toReal
  rcases ha.eq_or_lt with ha₀ | ha₀
  · have h : b = 1 := by linarith only [hab, ha₀]
    simpa only [← ha₀, h, zero_mul, one_mul, zero_add] using hy
  rcases hb.eq_or_lt with hb₀ | hb₀
  · have h : a = 1 := by linarith only [hab, hb₀]
    simpa only [← hb₀, h, zero_mul, one_mul, add_zero] using hx
  have hab' : b = 1 - a := by linarith only [hab]
  have hPL := AsymptoticStatistics.prekopaLeindler (hF x) (hF y) (hF (a * x + b * y))
    ha₀ (by linarith only [hab, hb₀]) (by
      intro u v
      rw [hab']
      exact hshape x y a ha₀ (by linarith only [hab, hb₀]) u v)
  rw [← hab'] at hPL
  by_cases hz : 0 ≤ z
  · have hx' := ENNReal.ofReal_le_ofReal hx
    have hy' := ENNReal.ofReal_le_ofReal hy
    rw [ENNReal.ofReal_toReal (hfin x)] at hx'
    rw [ENNReal.ofReal_toReal (hfin y)] at hy'
    have hbound : ENNReal.ofReal z ≤ ∫⁻ u, F (a * x + b * y) u := calc
      _ = ENNReal.ofReal z ^ a * ENNReal.ofReal z ^ b := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ ha hb, hab, ENNReal.rpow_one]
      _ ≤ _ := (mul_le_mul' (ENNReal.rpow_le_rpow hx' ha) (ENNReal.rpow_le_rpow hy' hb)).trans hPL
    have h := ENNReal.toReal_mono (hfin _) hbound
    rwa [ENNReal.toReal_ofReal hz] at h
  · exact (le_of_lt (lt_of_not_ge hz)).trans ENNReal.toReal_nonneg

/-- Simultaneous reflection of the coordinates preserves the real-valued
marginal of a jointly even nonnegative density. -/
theorem even_lintegral_of_joint_even {ι : Type*} [Fintype ι] (F : ℝ → (ι → ℝ) → ℝ≥0∞)
    (hF : ∀ t, Measurable (F t)) (he : ∀ t x, F (-t) (-x) = F t x) :
    ∀ t, (∫⁻ x, F (-t) x).toReal = (∫⁻ x, F t x).toReal := by
  intro t
  congr 1
  have h := (Measure.measurePreserving_neg (volume : Measure (ι → ℝ))).lintegral_comp
    (hF (-t))
  simpa only [he] using h.symm

end BoundedEdgeRegularSubgraphs
