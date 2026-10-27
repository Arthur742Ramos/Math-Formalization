module
public import CircleCoordinate
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength

theorem cosine_half : cosine ((1 / 2 : ℝ) : CircleHodge.Circle) = -1 := by
  have h := cosine_cover (1 / 2)
  change cosine ((1 / 2 : ℝ) : CircleHodge.Circle) = _ at h
  rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.cos_pi] at h
  exact h

/-- A positive, nonconstant C¹ density from the existing circle construction. -/
noncomputable def sampleDensity : RegularDensity := ⟨⟨constant 2 + cosine, by
  intro q
  have h : |cosine q| ≤ 1 := by simpa [cosine] using Complex.abs_re_le_norm (AddCircle.toCircle q : ℂ)
  change 0 < 2 + cosine q
  linarith [(abs_le.mp h).1]⟩, by
  change ContDiff ℝ 1 (fun x => 2 + cover cosine x)
  exact contDiff_const.add (c2_c1 cosineC2)⟩

theorem sampleDensity_nonconstant : ¬ ∃ c : ℝ, sampleDensity.val.val = constant c := by
  rintro ⟨c, h⟩
  have h0 := congrArg (fun f : Coefficient => f 0) h
  have h1 := congrArg (fun f : Coefficient => f ((1 / 2 : ℝ) : CircleHodge.Circle)) h
  change 2 + cosine 0 = c at h0
  change 2 + cosine ((1 / 2 : ℝ) : CircleHodge.Circle) = c at h1
  rw [cosine_zero] at h0
  rw [cosine_half] at h1
  linarith

/-- If the real arclength coordinate were the identity, the density would be constant. -/
theorem coordinate_id_implies_constant (ρ : RegularDensity) (h : coordinate ρ.val = id) :
    ρ.val.val = constant (mean ρ.val.val) := by
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change cover ρ.val.val x = mean ρ.val.val
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) h
  rw [(coordinate_hasDerivAt ρ.val x).deriv, (hasDerivAt_id x).deriv] at hd
  exact (div_eq_one_iff_eq (ne_of_gt (mean_pos ρ.val))).mp hd

theorem sample_coordinate_nonidentity : coordinate sampleDensity.val ≠ id := by
  intro h
  exact sampleDensity_nonconstant ⟨mean sampleDensity.val.val, coordinate_id_implies_constant sampleDensity h⟩
end ComputationalHodge.ArclengthSpectrum
