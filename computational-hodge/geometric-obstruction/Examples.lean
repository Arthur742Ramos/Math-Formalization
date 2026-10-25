module
public import Harmonic
@[expose] public section
namespace ComputationalHodge.PresentationHomology.OneLoop
open ComputationalPaths.Path.GeometricTopology

def system : ContinuousGeometricStepSystem Unit Unit where
  src _ := (); tgt _ := (); realize _ := _root_.Path.refl ()
  continuous_src := continuous_const
  continuous_tgt := continuous_const
  continuous_realize := continuous_const
def presentation : ScopedGeometricRewritePresentation system where
  rule _ _ := False
  sound_rule h := False.elim h
noncomputable def coefficient : Cochain Unit := EuclideanSpace.basisFun Unit ℝ ()
noncomputable def closedCoefficient : Closed presentation :=
  ⟨coefficient, by funext c; exact False.elim c.rule⟩

theorem primitive_period : period (GeometricTrace.single (S := system.toGeometricStepSystem) ())
    coefficient = 1 := by
  change ((EuclideanSpace.basisFun Unit ℝ) ()) () = 1
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, ↓reduceIte]


end ComputationalHodge.PresentationHomology.OneLoop
