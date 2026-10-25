module
public import Duality
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
noncomputable def cohomologyClass : H1 presentation := (Boundaries presentation).mkQ closedCoefficient
noncomputable def generator : ChainH1 presentation :=
  loopClass presentation () (Quotient.mk _ (.single ()))

theorem primitive_period : period (GeometricTrace.single (S := system.toGeometricStepSystem) ())
    coefficient = 1 := by
  change ((EuclideanSpace.basisFun Unit ℝ) ()) () = 1
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, ↓reduceIte]

theorem evaluates_generator : pairing presentation cohomologyClass generator = 1 := by
  rw [generator, pairing_loopClass]
  exact primitive_period

theorem generator_nonzero : generator ≠ 0 := by
  intro h
  have he := evaluates_generator
  rw [h, map_zero] at he
  norm_num at he

end ComputationalHodge.PresentationHomology.OneLoop
