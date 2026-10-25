module
public import RawLift
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section

namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open MeasureTheory Set
open scoped NNReal Topology

/-- Ordinary integration on the actual realized path and its actual covering lift. -/
noncomputable def rawIntegral (α : Coefficient) (p : Trace 0 0) : ℝ :=
  ∫ t in (0 : ℝ)..1,α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))*
    deriv (actualLift p) t

theorem actual_coefficient (α : Coefficient) (p : Trace 0 0) (t : ℝ) :
    α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))=cover α (actualLift p t) := by
  apply congrArg α
  exact (congrFun (circleCover.liftPath_lifts
    (GeometricTrace.realize p).toContinuousMap 0 (by simp))
    (Set.projIcc 0 1 zero_le_one t)).symm

theorem actualLift_lipschitz (p : Trace 0 0) : ∃ K : ℝ≥0,LipschitzWith K (actualLift p) := by
  rw [actualLift_eq_rawLift]
  exact rawLift_lipschitz p

theorem actualLift_finite_corners (p : Trace 0 0) :
    ∃ s : Set ℝ,s.Finite ∧ ∀ x ∉ s,DifferentiableAt ℝ (actualLift p) x := by
  rw [actualLift_eq_rawLift]
  exact rawLift_finite_corners p

theorem cover_integrand_integrable (α : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable (fun t => cover α (actualLift p t)*deriv (actualLift p) t) volume 0 1 := by
  obtain ⟨K,hK⟩ := actualLift_lipschitz p
  obtain ⟨C,hC⟩ := (isCompact_range α.continuous).isBounded.exists_norm_le
  have hb (t : ℝ) : ‖cover α (actualLift p t)*deriv (actualLift p) t‖≤C*(K : ℝ) := by
    rw [norm_mul]
    exact mul_le_mul (hC _ ⟨(actualLift p t : Circle),rfl⟩)
      (norm_deriv_le_of_lipschitz hK) (norm_nonneg _) (by
        exact (norm_nonneg (α 0)).trans (hC _ ⟨0,rfl⟩))
  have hm : AEStronglyMeasurable
      (fun t => cover α (actualLift p t)*deriv (actualLift p) t) (volume.restrict (Icc 0 1)) :=
    (((cover_continuous α).comp hK.continuous).aestronglyMeasurable).mul
      (aestronglyMeasurable_deriv (actualLift p) _)
  have hi : IntegrableOn (fun t => cover α (actualLift p t)*deriv (actualLift p) t)
      (Icc 0 1) volume :=
    IntegrableOn.of_bound (by simp) hm (C*(K : ℝ)) (Filter.Eventually.of_forall hb)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    (hi.mono_set Ioc_subset_Icc_self)

theorem raw_integrand_integrable (α : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable
      (fun t => α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))*
        deriv (actualLift p) t) volume 0 1 := by
  simpa only [actual_coefficient] using cover_integrand_integrable α p

theorem rawIntegral_eq_cover (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=∫ t in (0 : ℝ)..1,cover α (actualLift p t)*deriv (actualLift p) t := by
  simp only [rawIntegral,actual_coefficient]

theorem rawIntegral_eq_endpoint (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=∫ x in (0 : ℝ)..(count p : ℝ),cover α x := by
  let A : ℝ → ℝ := fun u => ∫ x in (0 : ℝ)..u,cover α x
  have ha (x : ℝ) : HasDerivAt A (cover α x) x :=
    intervalIntegral.integral_hasDerivAt_right ((cover_continuous α).intervalIntegrable 0 x)
      (cover_continuous α).aestronglyMeasurable.stronglyMeasurableAtFilter
      (cover_continuous α).continuousAt
  obtain ⟨K,hK⟩ := actualLift_lipschitz p
  obtain ⟨s,hs,hd⟩ := actualLift_finite_corners p
  have hA : Continuous A := (show Differentiable ℝ A from fun x => (ha x).differentiableAt).continuous
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun t => A (actualLift p t))
    (fun t => cover α (actualLift p t)*deriv (actualLift p) t)
    zero_le_one hs.countable (hA.comp hK.continuous).continuousOn
    (fun x hx => (ha (actualLift p x)).comp x ((hd x hx.2).hasDerivAt))
    (cover_integrand_integrable α p)
  rw [rawIntegral_eq_cover]
  simpa [A,actualLift_eq_rawLift,rawLift_zero,rawLift_one] using h

theorem rawIntegral_eq_mean_count (α : Coefficient) (p : Trace 0 0) :
    rawIntegral α p=mean α*(count p : ℝ) := by
  rw [rawIntegral_eq_endpoint]
  have h := (cover_periodic α).intervalIntegral_add_zsmul_eq (count p) 0
    (fun a b => (cover_continuous α).intervalIntegrable a b)
  simpa [mean,mul_comm] using h

theorem winding_realize_count (p : Trace 0 0) : winding (GeometricTrace.realize p)=(count p : ℝ) := by
  exact (rawLift_eq_cover p 1).symm.trans (rawLift_one p)

end ComputationalHodge.TraceIntegrals
