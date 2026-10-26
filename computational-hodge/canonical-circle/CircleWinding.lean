module
public import LoopImage
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
@[expose] public section

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
open scoped unitInterval

/-- The ordinary covering of the unit additive circle by the real line. -/
theorem circleCover : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

noncomputable def circleLift (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) : C(unitInterval,ℝ) :=
  circleCover.liftPath p.toContinuousMap 0 (by simp)

noncomputable def winding (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) : ℝ := circleLift p 1

theorem winding_homotopic {p q : _root_.Path (0 : AddCircle (1 : ℝ)) 0}
    (h : _root_.Path.Homotopic p q) : winding p = winding q :=
  circleCover.liftPath_apply_one_eq_of_homotopicRel h 0 (by simp) (by simp)

def onceAround : _root_.Path (0 : AddCircle (1 : ℝ)) 0 where
  toFun t := ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := by simp
  target' := by simp

end ComputationalHodge.LoopCharacters
