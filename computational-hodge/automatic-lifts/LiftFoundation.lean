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
  f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0}
def projectedLoop (L : ACLift) : _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := ((L.val (t : ℝ) : ℝ) : CircleHodge.Circle)
  continuous_toFun := by
    apply (AddCircle.continuous_mk' (1 : ℝ)).comp
    exact L.property.1.continuousOn.comp_continuous continuous_subtype_val
      (fun _ => by simp)
  source' := by simpa using congrArg (fun x : ℝ => (x : CircleHodge.Circle)) L.property.2.1
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
end ComputationalHodge.ACLifts
