module
public import GeometricPathModes
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ResonanceObstruction ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.Arclength

/-- The constructed resonant shifts strictly increase with the natural frequency. -/
theorem curvedFrequency_strictMono (ρ : RegularDensity) : StrictMono (curvedFrequency ρ) := by
  intro m n hmn
  have hmn' : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hm : 0 ≤ angular m := by unfold angular; positivity
  have hn : 0 ≤ angular n := by unfold angular; positivity
  unfold curvedFrequency frequencyN
  apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos (inv_pos.mpr (mean_pos ρ.val)))
  exact (sq_lt_sq₀ hm hn).2 (mul_lt_mul_of_pos_left hmn' (by positivity : 0 < 2 * Real.pi))

/-- The independent sine mode is also period-compatible and obstructs the shifted equation. -/
theorem curvedSine_obstruction (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) :
    (∀ p : Trace 0 0, lineIntegral (ρ.val.val * (curvedSine ρ n).val) (fromTrace p) = 0) ∧
    (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * (curvedSine ρ n).val)).val = 0) ∧
    ¬ ∃ u : C2Coefficient,
      laplacian ρ u - curvedFrequency ρ n • u.val = (curvedSine ρ n).val := by
  let v : Domain ρ := ⟨curvedSine ρ n, eigen_mean_zero ρ _ _
    (ne_of_gt (curvedFrequency_positive ρ hn)) (curvedSine_eigen ρ n)⟩
  exact ⟨(mode_periods ρ v).1, (mode_periods ρ v).2,
    mode_obstructed ρ _ _ (curvedSine_nonzero ρ hn) (curvedSine_eigen ρ n)⟩
end ComputationalHodge.ArclengthSpectrum
