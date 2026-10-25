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
    HasDerivAt (realPotential α) (cover α x-mean α) x := by
  have hi : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u,cover α t) (cover α x) x :=
    intervalIntegral.integral_hasDerivAt_right
      ((cover_continuous α).intervalIntegrable 0 x)
      (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (cover_continuous α).continuousAt
  have hm : HasDerivAt (fun u : ℝ => u*mean α) (mean α) x := by
    simpa using (hasDerivAt_id x).mul_const (mean α)
  exact hi.sub hm

theorem realPotential_contDiff (α : Coefficient) : ContDiff ℝ 1 (realPotential α) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (realPotential_hasDerivAt α x).differentiableAt,?_⟩
  have h : deriv (realPotential α)=fun x => cover α x-mean α :=
    funext (fun x => (realPotential_hasDerivAt α x).deriv)
  rw [h]
  exact (cover_continuous α).sub continuous_const

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

theorem potential_cover (α : Coefficient) : cover (potential α)=realPotential α := rfl

theorem potential_zero (α : Coefficient) : potential α 0=0 := by
  change realPotential α 0=0
  simp [realPotential]

theorem potential_contDiff (α : Coefficient) : ContDiff ℝ 1 (cover (potential α)) :=
  realPotential_contDiff α

theorem potential_deriv (α : Coefficient) (x : ℝ) :
    deriv (cover (potential α)) x=cover α x-mean α :=
  (realPotential_hasDerivAt α x).deriv

/-- Exactness requires an actual circle potential and its actual C¹ derivative. -/
def ExactCoefficient (α : Coefficient) : Prop :=
  ∃ F : Coefficient, ContDiff ℝ 1 (cover F) ∧ ∀ x,deriv (cover F) x=cover α x

/-- Differentiability is essential: `deriv` is totalized at nonsmooth points. -/
def HarmonicCoefficient (α : Coefficient) : Prop :=
  Differentiable ℝ (cover α) ∧ ∀ x,deriv (cover α) x=0

theorem mean_constant (c : ℝ) : mean (constant c)=c := by
  simp [mean,cover,constant]

theorem mean_sub (α β : Coefficient) : mean (α-β)=mean α-mean β := by
  change (∫ x in (0 : ℝ)..1,cover α x-cover β x)=_
  exact intervalIntegral.integral_sub ((cover_continuous α).intervalIntegrable 0 1)
    ((cover_continuous β).intervalIntegrable 0 1)

theorem exact_mean_zero {α : Coefficient} (h : ExactCoefficient α) : mean α=0 := by
  obtain ⟨F,hF,hd⟩ := h
  have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc hF.contDiffOn (by norm_num : (0 : ℝ)≤1)
  have he : (∫ x in (0 : ℝ)..1,deriv (cover F) x)=mean α :=
    intervalIntegral.integral_congr (fun x _ => hd x)
  rw [he] at h
  have hp := cover_periodic F 0
  simp only [zero_add] at hp
  exact h.trans (sub_eq_zero.mpr hp)

theorem mean_zero_iff_exact (α : Coefficient) : mean α=0 ↔ ExactCoefficient α := by
  constructor
  · intro h
    exact ⟨potential α,potential_contDiff α,fun x => by simpa [h] using potential_deriv α x⟩
  · exact exact_mean_zero

theorem harmonic_iff_constant (α : Coefficient) :
    HarmonicCoefficient α ↔ ∃ c,α=constant c := by
  constructor
  · rintro ⟨hd,hzero⟩
    refine ⟨cover α 0,?_⟩
    apply ContinuousMap.ext
    intro q
    induction q using Quotient.inductionOn with | _ x =>
    exact is_const_of_deriv_eq_zero hd hzero x 0
  · rintro ⟨c,rfl⟩
    exact ⟨differentiable_const c,fun x => deriv_const x c⟩


end ComputationalHodge.CircleHodge
