module
public import FourierModes
public import Conjugacy
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ResonanceObstruction ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters

noncomputable def curvedFrequency (ρ : RegularDensity) (n : ℕ) : ℝ :=
  (mean ρ.val.val)⁻¹ ^ 2 * frequencyN n
noncomputable def curvedCosine (ρ : RegularDensity) (n : ℕ) : C2Coefficient :=
  pullbackC2 ρ (cosineNC2 n)
noncomputable def curvedSine (ρ : RegularDensity) (n : ℕ) : C2Coefficient :=
  pullbackC2 ρ (sineNC2 n)

theorem curvedFrequency_positive (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) :
    0 < curvedFrequency ρ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < mean ρ.val.val := mean_pos ρ.val
  unfold curvedFrequency frequencyN angular
  positivity

theorem transfer_eigen (ρ : RegularDensity) (u : C2Coefficient) (μ : ℝ)
    (hu : laplacian flatDensity u = μ • u.val) :
    laplacian ρ (pullbackC2 ρ u) = ((mean ρ.val.val)⁻¹ ^ 2 * μ) • (pullbackC2 ρ u).val := by
  rw [laplacian_pullback, hu]
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change (mean ρ.val.val)⁻¹ ^ 2 * cover (pullback ρ (μ • u.val)) x =
    ((mean ρ.val.val)⁻¹ ^ 2 * μ) * cover (pullback ρ u.val) x
  rw [cover_pullback, cover_pullback]
  change (mean ρ.val.val)⁻¹ ^ 2 * (μ * cover u.val (coordinate ρ.val x)) = _
  ring

theorem curvedCosine_eigen (ρ : RegularDensity) (n : ℕ) :
    laplacian ρ (curvedCosine ρ n) = curvedFrequency ρ n • (curvedCosine ρ n).val :=
  transfer_eigen ρ (cosineNC2 n) (frequencyN n) (cosineN_eigen n)

theorem curvedSine_eigen (ρ : RegularDensity) (n : ℕ) :
    laplacian ρ (curvedSine ρ n) = curvedFrequency ρ n • (curvedSine ρ n).val :=
  transfer_eigen ρ (sineNC2 n) (frequencyN n) (sineN_eigen n)

theorem curvedCosine_zero (ρ : RegularDensity) (n : ℕ) : (curvedCosine ρ n).val 0 = 1 := by
  change cover (pullback ρ (cosineN n)) 0 = 1
  rw [cover_pullback, coordinate_zero, cosineN_cover]
  simp

theorem curvedSine_zero (ρ : RegularDensity) (n : ℕ) : (curvedSine ρ n).val 0 = 0 := by
  change cover (pullback ρ (sineN n)) 0 = 0
  rw [cover_pullback, coordinate_zero, sineN_cover]
  simp

theorem curvedSine_quarter (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) :
    (curvedSine ρ n).val ((inverse ρ.val (1 / (4 * (n : ℝ))) : ℝ) : CircleHodge.Circle) = 1 := by
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  change cover (pullback ρ (sineN n)) (inverse ρ.val (1 / (4 * (n : ℝ)))) = 1
  rw [cover_pullback, coordinate_inverse, sineN_cover]
  have h : 2 * Real.pi * ((n : ℝ) * (1 / (4 * (n : ℝ)))) = Real.pi / 2 := by
    field_simp [hne]; ring
  rw [h, Real.sin_pi_div_two]

theorem curvedModes_independent (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) (a b : ℝ)
    (h : a • (curvedCosine ρ n).val + b • (curvedSine ρ n).val = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrArg (fun f : Coefficient => f 0) h
  change a * (curvedCosine ρ n).val 0 + b * (curvedSine ρ n).val 0 = 0 at h0
  rw [curvedCosine_zero, curvedSine_zero] at h0
  have ha : a = 0 := by linarith
  have h1 := congrArg (fun f : Coefficient => f ((inverse ρ.val (1 / (4 * (n : ℝ))) : ℝ) : CircleHodge.Circle)) h
  change a * (curvedCosine ρ n).val _ + b * (curvedSine ρ n).val _ = 0 at h1
  rw [ha, curvedSine_quarter ρ hn] at h1
  exact ⟨ha, by linarith⟩

theorem curvedCosine_nonzero (ρ : RegularDensity) (n : ℕ) : (curvedCosine ρ n).val ≠ 0 := by
  intro h
  have h0 := congrArg (fun f : Coefficient => f 0) h
  rw [curvedCosine_zero] at h0
  norm_num at h0

theorem curvedSine_nonzero (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) : (curvedSine ρ n).val ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : Coefficient => f ((inverse ρ.val (1 / (4 * (n : ℝ))) : ℝ) : CircleHodge.Circle)) h
  rw [curvedSine_quarter ρ hn] at h1
  norm_num at h1

theorem eigen_mean_zero (ρ : RegularDensity) (u : C2Coefficient) (μ : ℝ) (hμ : μ ≠ 0)
    (hu : laplacian ρ u = μ • u.val) : weightedMean ρ u.val = 0 := by
  have h := weightedMean_laplacian ρ u
  rw [hu, weightedMean_smul] at h
  exact (mul_eq_zero.mp h).resolve_left hμ

theorem curvedCosine_obstruction (ρ : RegularDensity) {n : ℕ} (hn : 0 < n) :
    (∀ p : Trace 0 0, lineIntegral (ρ.val.val * (curvedCosine ρ n).val) (fromTrace p) = 0) ∧
    (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * (curvedCosine ρ n).val)).val = 0) ∧
    ¬ ∃ u : C2Coefficient,
      laplacian ρ u - curvedFrequency ρ n • u.val = (curvedCosine ρ n).val := by
  let v : Domain ρ := ⟨curvedCosine ρ n, eigen_mean_zero ρ _ _
    (ne_of_gt (curvedFrequency_positive ρ hn)) (curvedCosine_eigen ρ n)⟩
  exact ⟨(mode_periods ρ v).1, (mode_periods ρ v).2,
    mode_obstructed ρ _ _ (curvedCosine_nonzero ρ n) (curvedCosine_eigen ρ n)⟩
end ComputationalHodge.ArclengthSpectrum
