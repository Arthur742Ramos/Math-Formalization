module
public import RawLift
@[expose] public section

namespace ComputationalHodge.TraceIntegrals
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge

def unitTrace : Trace 0 0 := .single ()
noncomputable def meanCochain (α : Coefficient) : Cochain Unit := WithLp.toLp 2 (fun _ => mean α)

theorem period_mean_count (α : Coefficient) {a b : CircleHodge.Circle} (p : Trace a b) :
    period p (meanCochain α)=mean α*(count p : ℝ) := by
  induction p with
  | refl _ => simp [period,count]
  | single _ => change mean α=mean α*((1 : ℤ) : ℝ);rw [Int.cast_one,mul_one]
  | trans p q hp hq => change period p _+period q _=_;rw [hp,hq,count,Int.cast_add];ring
  | symm p hp => change -period p _=_;rw [hp,count,Int.cast_neg];ring
theorem count_zero_of_source_ne {a b : CircleHodge.Circle} (p : Trace a b) : a≠0 → count p=0 := by
  induction p with
  | refl _ => exact fun _ => rfl
  | single _ => exact fun h => (h rfl).elim
  | trans p q hp hq => exact fun h => by rw [count,hp h,hq (fun hb => h ((trace_endpoints p).trans hb)),zero_add]
  | symm p hp => exact fun h => by rw [count,hp (fun ha => h ((trace_endpoints p).symm.trans ha)),neg_zero]

theorem winding_realize_count (p : Trace 0 0) : winding (GeometricTrace.realize p)=(count p : ℝ) := (rawLift_eq_cover p 1).symm.trans (rawLift_one p)
theorem count_homotopic {a b : CircleHodge.Circle} (p q : Trace a b)
    (h : _root_.Path.Homotopic (GeometricTrace.realize p) (GeometricTrace.realize q)) : count p=count q := by
  by_cases ha : a=0
  · subst a
    have hb := trace_endpoints p
    subst b
    have hw : (count p : ℝ)=(count q : ℝ) :=
      (winding_realize_count p).symm.trans ((winding_homotopic h).trans (winding_realize_count q))
    exact_mod_cast hw
  · rw [count_zero_of_source_ne p ha,count_zero_of_source_ne q ha]

theorem meanCochain_closed (α : Coefficient) : meanCochain α∈Closed (geometricPresentation circleSystem) := by
  change d1 (geometricPresentation circleSystem) (meanCochain α)=0
  funext c
  change period c.left (meanCochain α)-period c.right (meanCochain α)=0
  rw [period_mean_count,period_mean_count,count_homotopic c.left c.right c.rule,sub_self]

theorem circle_exact_eq_bot : Exact circleSystem=⊥ := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    change d0 circleSystem.toGeometricStepSystem f=0
    ext e
    exact sub_self (f 0)
  · exact bot_le

noncomputable def meanHarmonic (α : Coefficient) : Harmonic (geometricPresentation circleSystem) :=
  ⟨meanCochain α,meanCochain_closed α,
    by rw [circle_exact_eq_bot,Submodule.bot_orthogonal_eq_top];trivial⟩

end ComputationalHodge.TraceIntegrals
