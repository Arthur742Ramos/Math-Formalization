module
public import Conjugacy
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ResonanceObstruction ComputationalHodge.Arclength

noncomputable def geometricCosine (ρ : RegularDensity) : C2Coefficient := pullbackC2 ρ cosineC2
noncomputable def geometricFrequency (ρ : RegularDensity) : ℝ :=
  (mean ρ.val.val)⁻¹ ^ 2 * frequency

theorem geometricFrequency_positive (ρ : RegularDensity) : 0 < geometricFrequency ρ := by
  unfold geometricFrequency
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr (mean_pos ρ.val))) frequency_positive

theorem geometricCosine_eigen (ρ : RegularDensity) :
    laplacian ρ (geometricCosine ρ) = geometricFrequency ρ • (geometricCosine ρ).val := by
  rw [show geometricCosine ρ = pullbackC2 ρ cosineC2 from rfl, laplacian_pullback, cosine_eigen]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change (mean ρ.val.val)⁻¹ ^ 2 * cover (pullback ρ (frequency • cosine)) x =
    geometricFrequency ρ * cover (pullback ρ cosine) x
  rw [cover_pullback, cover_pullback]
  change (mean ρ.val.val)⁻¹ ^ 2 * (frequency * cover cosine (coordinate ρ.val x)) = _
  unfold geometricFrequency
  ring

theorem geometricCosine_nonzero (ρ : RegularDensity) : (geometricCosine ρ).val ≠ 0 := by
  intro h
  have he := congrArg (fun f : Coefficient => f 0) h
  change cover (pullback ρ cosine) 0 = 0 at he
  rw [cover_pullback, coordinate_zero, cosine_cover] at he
  norm_num at he

theorem geometricCosine_mean_zero (ρ : RegularDensity) :
    weightedMean ρ (geometricCosine ρ).val = 0 := by
  have h := weightedMean_laplacian ρ (geometricCosine ρ)
  rw [geometricCosine_eigen, weightedMean_smul] at h
  exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (geometricFrequency_positive ρ))

noncomputable def geometricCosineMode (ρ : RegularDensity) : Domain ρ :=
  ⟨geometricCosine ρ, geometricCosine_mean_zero ρ⟩

/-- The actual arclength mode supplies a nonzero period-compatible obstruction for every density. -/
theorem geometricCosine_obstruction (ρ : RegularDensity) :
    (geometricCosine ρ).val ≠ 0 ∧
    (∀ p : Trace 0 0, lineIntegral (ρ.val.val * (geometricCosine ρ).val) (fromTrace p) = 0) ∧
    (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * (geometricCosine ρ).val)).val = 0) ∧
    ¬ ∃ u : C2Coefficient,
      laplacian ρ u - geometricFrequency ρ • u.val = (geometricCosine ρ).val :=
  ⟨geometricCosine_nonzero ρ, (mode_periods ρ (geometricCosineMode ρ)).1,
    (mode_periods ρ (geometricCosineMode ρ)).2,
    mode_obstructed ρ (geometricFrequency ρ) (geometricCosine ρ)
      (geometricCosine_nonzero ρ) (geometricCosine_eigen ρ)⟩
end ComputationalHodge.ArclengthSpectrum
