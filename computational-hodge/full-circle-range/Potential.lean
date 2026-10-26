module
public import ACPeriods
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.Calculus.MeanValue
@[expose] public section
namespace ComputationalHodge.CircleHodge
open Set
/-- A genuine real primitive with its mean term removed. -/
noncomputable def realPotential (α : Coefficient) (x : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..x,cover α t)-x*mean α

theorem realPotential_hasDerivAt (α : Coefficient) (x : ℝ) :
    HasDerivAt (realPotential α) (cover α x-mean α) x := (intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
    (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter (cover_continuous α).continuousAt).sub
    (by simpa using (hasDerivAt_id x).mul_const (mean α))

theorem realPotential_contDiff (α : Coefficient) : ContDiff ℝ 1 (realPotential α) := contDiff_one_iff_deriv.mpr ⟨fun x => (realPotential_hasDerivAt α x).differentiableAt,
    ((cover_continuous α).sub continuous_const).congr (fun x => (realPotential_hasDerivAt α x).deriv.symm)⟩

theorem realPotential_periodic (α : Coefficient) : Function.Periodic (realPotential α) 1 := by
  intro x
  have h := (cover_periodic α).intervalIntegral_add_eq_add 0 x
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  simp only [zero_add] at h
  change (∫ t in (0 : ℝ)..(x+1),cover α t)-(x+1)*mean α = _
  rw [h]
  change ((∫ t in (0 : ℝ)..x,cover α t)+mean α)-(x+1)*mean α = _
  unfold realPotential
  ring

/-- The primitive descends to an actual continuous function on the circle. -/
noncomputable def potential (α : Coefficient) : Coefficient where
  toFun := (realPotential_periodic α).lift
  continuous_toFun := (realPotential_contDiff α).continuous.quotient_liftOn' _

theorem potential_contDiff (α : Coefficient) : ContDiff ℝ 1 (cover (potential α)) :=
  realPotential_contDiff α

theorem potential_deriv (α : Coefficient) (x : ℝ) :
    deriv (cover (potential α)) x=cover α x-mean α :=
  (realPotential_hasDerivAt α x).deriv

/-- Exactness requires an actual circle potential and its actual C¹ derivative. -/
def ExactCoefficient (α : Coefficient) : Prop :=
  ∃ F : Coefficient, ContDiff ℝ 1 (cover F) ∧ ∀ x,deriv (cover F) x=cover α x
theorem mean_sub (α β : Coefficient) : mean (α-β)=mean α-mean β := by
  change (∫ x in (0 : ℝ)..1,cover α x-cover β x)=_
  exact intervalIntegral.integral_sub ((cover_continuous α).intervalIntegrable 0 1)
    ((cover_continuous β).intervalIntegrable 0 1)

theorem exact_mean_zero {α : Coefficient} (h : ExactCoefficient α) : mean α=0 := by
  obtain ⟨F,hF,hd⟩ := h
  exact (intervalIntegral.integral_congr (fun x _ => (hd x).symm)).trans
    ((intervalIntegral.integral_deriv_of_contDiffOn_Icc hF.contDiffOn (by norm_num : (0 : ℝ)≤1)).trans
      (sub_eq_zero.mpr (by simpa only [zero_add] using cover_periodic F 0)))
end ComputationalHodge.CircleHodge
