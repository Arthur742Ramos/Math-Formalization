module

public import SamplingPlan
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Sampling

/-- Choose a single host spectral accuracy after the tolerance for atypical
vertices and the number of tester groups have been fixed. -/
theorem spectral_accuracy (g η δ z : ℝ) (gp : 0 < g) (hp : 0 < η) (dp : 0 < δ) (zp : 0 < z) :
    ∃ ε : ℝ, 0 < ε ∧ 625*9*ε^2 ≤ z^2/16 ∧ 5*g*(24*g)*ε^2 ≤ η*δ^2/128 := by
  let v := min (z^2/(16*625*9)) (η*δ^2/(128*(5*g*(24*g))))
  have vp : 0 < v := by dsimp [v]; positivity
  refine ⟨Real.sqrt v,Real.sqrt_pos.mpr vp,?_,?_⟩
  · rw [Real.sq_sqrt vp.le]
    have h := min_le_left (z^2/(16*625*9)) (η*δ^2/(128*(5*g*(24*g))))
    change 625*9*v ≤ z^2/16
    change v ≤ _ at h
    linarith
  · rw [Real.sq_sqrt vp.le]
    have h := min_le_right (z^2/(16*625*9)) (η*δ^2/(128*(5*g*(24*g))))
    change v ≤ _ at h
    have e := (le_div_iff₀ (by positivity)).mp h
    linarith only [e]

theorem variance_budget (M T b g m n L ε : ℝ) (Mp : 0 ≤ M) (tp : 0 < T) (bp : 0 < b)
    (gp : 0 ≤ g) (mp : 0 ≤ m) (nle : n ≤ m) (pool : M ≤ 4*g*m*b) (test : M ≤ 3*T) :
    2*n*L^2+2*(ε*M)^2*m/(b*T) ≤ 2*m*L^2+24*ε^2*g*m^2 := by
  apply add_le_add
  · nlinarith only [mul_le_mul_of_nonneg_right nle (sq_nonneg L)]
  · rw [div_le_iff₀ (mul_pos bp tp)]
    have prod := mul_le_mul pool test Mp (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left prod (mul_nonneg (sq_nonneg ε) mp)]

theorem reference_budget (h r g m L ε η δ : ℝ) (hr : 0 ≤ r) (hg : 0 ≤ g) (hm : 0 < m) (hd : 0 < δ)
    (lh : h ≤ 5*r) (bias : 5*g*(24*g)*ε^2 ≤ η*δ^2/128)
    (large : 1280*g*L^2 ≤ η*δ^2*m) :
    h*(g*((2*m*L^2+24*ε^2*g*m^2)/(δ*m)^2)) ≤ (η*r/8)/8 := by
  have nn : 0 ≤ g*((2*m*L^2+24*ε^2*g*m^2)/(δ*m)^2) := by positivity
  apply (mul_le_mul_of_nonneg_right lh nn).trans
  rw [← mul_assoc,← mul_div_assoc,le_div_iff₀ (by norm_num : (0:ℝ)<8)]
  have x := mul_le_mul_of_nonneg_right bias (mul_nonneg hr hm.le)
  have y := mul_le_mul_of_nonneg_right large hr
  field_simp [hd.ne',hm.ne']
  nlinarith only [x,y]

theorem tester_budget (h r z ε : ℝ) (hn : 0 ≤ h) (hr : 0 ≤ r) (cap : h ≤ 5*r)
    (small : 625*9*ε^2 ≤ z^2/16) (large : 12000 ≤ z^2*r) :
    h^4*(9*ε^2)+6*h^3 ≤ (z*r^2)^2/8 := by
  have q := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn cap 4) (mul_nonneg (by norm_num : (0:ℝ)≤9) (sq_nonneg ε))
  have c := pow_le_pow_left₀ hn cap 3
  have big := mul_le_mul_of_nonneg_right large (pow_nonneg hr 3)
  have acc := mul_le_mul_of_nonneg_right small (pow_nonneg hr 4)
  nlinarith only [q,c,big,acc]

end InducedDegreeRepetition.Sampling
