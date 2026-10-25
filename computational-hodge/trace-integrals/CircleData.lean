module
public import CircleWinding
public import Harmonic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
@[expose] public section

namespace ComputationalHodge.CircleHodge
open Set
abbrev Circle := AddCircle (1 : ℝ)
abbrev Coefficient := C(Circle,ℝ)

def cover (α : Coefficient) (x : ℝ) : ℝ := α (x : Circle)

theorem cover_continuous (α : Coefficient) : Continuous (cover α) := by
  unfold cover
  fun_prop

theorem cover_periodic (α : Coefficient) : Function.Periodic (cover α) 1 := by
  intro x
  simp [cover,Circle]

def constant (c : ℝ) : Coefficient := ContinuousMap.const Circle c

noncomputable def mean (α : Coefficient) : ℝ := ∫ x in (0 : ℝ)..1,cover α x

end ComputationalHodge.CircleHodge

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
/-- One actual circle loop as a finite computational generator. -/
def circleSystem : ContinuousGeometricStepSystem (AddCircle (1 : ℝ)) Unit where
  src _ := 0
  tgt _ := 0
  realize _ := onceAround
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_const

end ComputationalHodge.LoopCharacters
