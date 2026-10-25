module
public import CirclePeriods
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
@[expose] public section
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals
open MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- A real lift with regularity only on the interval, not a presumed period formula. -/
abbrev ACLift := {f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧
  f 0=0 ∧ ((f 1 : ℝ) : Circle)=0}
def projectedLoop (L : ACLift) : _root_.Path (0 : Circle) 0 where
  toFun t := ((L.val (t : ℝ) : ℝ) : Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    exact L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)
  source' := by simpa using congrArg (fun x : ℝ => (x : Circle)) L.property.2.1
  target' := L.property.2.2
theorem actual_lift_on_interval (L : ACLift) (t : unitInterval) :
    circleLift (projectedLoop L) t=L.val (t : ℝ) := by
  let F : C(unitInterval,ℝ) := ⟨fun t => L.val (t : ℝ),
    L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)⟩
  have h : F=circleLift (projectedLoop L) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,L.property.2.1⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f t) h).symm
theorem projected_winding (L : ACLift) : winding (projectedLoop L)=L.val 1 :=
  actual_lift_on_interval L 1
/-- Clamped actual covering lift; no equality with L outside the interval is asserted. -/
noncomputable def coveringLift (L : ACLift) (t : ℝ) : ℝ :=
  circleLift (projectedLoop L) (Set.projIcc 0 1 zero_le_one t)
theorem coveringLift_eq_on (L : ACLift) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    coveringLift L t=L.val t := by
  simp only [coveringLift,actual_lift_on_interval,Set.projIcc_of_mem zero_le_one ht]
theorem coveringLift_deriv (L : ACLift) {t : ℝ} (ht : t∈Ioo (0 : ℝ) 1) :
    deriv (coveringLift L) t=deriv L.val t := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact coveringLift_eq_on L ⟨hx.1.le,hx.2.le⟩
end ComputationalHodge.ACLifts
