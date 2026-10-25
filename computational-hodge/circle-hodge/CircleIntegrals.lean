module
public import CirclePotential
public import Mathlib.Analysis.Calculus.ContDiff.Operations
@[expose] public section

namespace ComputationalHodge.CircleHodge
open ComputationalHodge.LoopCharacters

/-- An actual C¹ real lift of a based circle loop; corners are not admitted here. -/
structure C1Lift where
  curve : ℝ → ℝ
  smooth : ContDiff ℝ 1 curve
  source : curve 0=0
  target : ((curve 1 : ℝ) : Circle)=0

def projectedLoop (L : C1Lift) : _root_.Path (0 : Circle) 0 where
  toFun t := ((L.curve (t : ℝ) : ℝ) : Circle)
  continuous_toFun := by
    have := L.smooth.continuous
    fun_prop
  source' := by simpa using congrArg (fun x : ℝ => (x : Circle)) L.source
  target' := L.target

theorem projectedLoop_winding (L : C1Lift) : winding (projectedLoop L)=L.curve 1 := by
  have hc : Continuous (fun t : unitInterval => L.curve (t : ℝ)) :=
    L.smooth.continuous.comp continuous_subtype_val
  have h : (⟨fun t : unitInterval => L.curve (t : ℝ),hc⟩ : C(unitInterval,ℝ))=
      circleLift (projectedLoop L) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,L.source⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f 1) h).symm

theorem lift_endpoint_integral (L : C1Lift) : ∃ n : ℤ,(n : ℝ)=L.curve 1 := by
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp L.target
  exact ⟨n,by simpa using hn⟩

/-- Ordinary interval integration of the pulled-back coefficient against velocity. -/
noncomputable def lineIntegral (α : Coefficient) (L : C1Lift) : ℝ :=
  ∫ t in (0 : ℝ)..1,cover α (L.curve t)*deriv L.curve t

theorem lineIntegral_eq_endpoint_integral (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=∫ x in (0 : ℝ)..L.curve 1,cover α x := by
  let A : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u,cover α x
  have ha (x : ℝ) : HasDerivAt A (cover α x) x :=
    intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
      (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (cover_continuous α).continuousAt
  have hd (x : ℝ) : HasDerivAt (fun t => A (L.curve t))
      (cover α (L.curve x)*deriv L.curve x) x :=
    (ha (L.curve x)).comp x ((L.smooth.differentiable (by norm_num)).differentiableAt.hasDerivAt)
  have hc : Continuous (fun t => cover α (L.curve t)*deriv L.curve t) :=
    ((cover_continuous α).comp L.smooth.continuous).mul
      (L.smooth.continuous_deriv (by norm_num))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable 0 1)
  change lineIntegral α L=A (L.curve 1)-A (L.curve 0) at h
  simpa [A,L.source] using h

theorem lineIntegral_eq_mean_endpoint (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=mean α*L.curve 1 := by
  obtain ⟨n,hn⟩ := lift_endpoint_integral L
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq n 0
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  rw [lineIntegral_eq_endpoint_integral,← hn]
  simpa [mean,zsmul_eq_mul,mul_comm] using h

theorem lineIntegral_eq_winding (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=mean α*(windingCharacter
      (_root_.Path.Homotopic.Quotient.mk (projectedLoop L))).toAdd := by
  change lineIntegral α L=mean α*winding (projectedLoop L)
  rw [projectedLoop_winding]
  exact lineIntegral_eq_mean_endpoint α L

theorem lineIntegral_class_independent (α : Coefficient) (L M : C1Lift)
    (h : _root_.Path.Homotopic.Quotient.mk (projectedLoop L)=
      _root_.Path.Homotopic.Quotient.mk (projectedLoop M)) :
    lineIntegral α L=lineIntegral α M := by
  rw [lineIntegral_eq_winding,lineIntegral_eq_winding,h]

def straightLift (n : ℤ) : C1Lift where
  curve t := (n : ℝ)*t
  smooth := (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (n : ℝ))).mul contDiff_id
  source := by simp
  target := by simp

/-- Every actual ambient class has a smooth representative, proved from winding. -/
theorem smooth_representative (g : FundamentalGroup Circle 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=g := by
  obtain ⟨n,hn⟩ := circle_winding_integral g
  refine ⟨straightLift n,?_⟩
  apply circle_winding_injective
  apply Multiplicative.toAdd.injective
  change winding (projectedLoop (straightLift n))=(windingCharacter g).toAdd
  rw [projectedLoop_winding]
  change (n : ℝ)*1=(windingCharacter g).toAdd
  rw [mul_one]
  exact hn

theorem smooth_period_realization (α : Coefficient) (g : FundamentalGroup Circle 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=g ∧
      lineIntegral α L=mean α*(windingCharacter g).toAdd := by
  obtain ⟨L,hL⟩ := smooth_representative g
  exact ⟨L,hL,by rw [lineIntegral_eq_winding,hL]⟩

theorem exact_lineIntegral_zero {α : Coefficient} (h : ExactCoefficient α) (L : C1Lift) :
    lineIntegral α L=0 := by
  rw [lineIntegral_eq_winding,exact_mean_zero h,zero_mul]

end ComputationalHodge.CircleHodge
