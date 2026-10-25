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

theorem integral_period {a b : Unit} (p : GeometricTrace system.toGeometricStepSystem a b) :
    ∃ n : ℤ, period p coefficient = (n : ℝ) := by
  induction p with
  | refl a => exact ⟨0, by simp [period]⟩
  | single e => exact ⟨1, by cases e; simpa using primitive_period⟩
  | trans p q hp hq =>
    obtain ⟨n,hn⟩ := hp; obtain ⟨m,hm⟩ := hq
    exact ⟨n+m, by change period p coefficient + period q coefficient = _; rw [hn,hm,Int.cast_add]⟩
  | symm p hp =>
    obtain ⟨n,hn⟩ := hp
    exact ⟨-n, by change -period p coefficient = _; rw [hn,Int.cast_neg]⟩

theorem fractional_not_single_loop :
    ¬ ∃ p : PathClass presentation () (), loopClass presentation () p = (1/2 : ℝ) • generator := by
  rintro ⟨p,hp⟩
  induction p using Quotient.inductionOn with | _ p =>
  have he := congrArg (pairing presentation cohomologyClass) hp
  rw [map_smul, evaluates_generator, pairing_loopClass] at he
  change period p coefficient = (1/2 : ℝ) * 1 at he
  obtain ⟨n,hn⟩ := integral_period p
  have hr : (n : ℝ) = 1/2 := by linarith
  have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < (n : ℝ) by rw [hr]; norm_num)
  have hn1 : n < 1 := by exact_mod_cast (show (n : ℝ) < (1 : ℝ) by rw [hr]; norm_num)
  omega

end ComputationalHodge.PresentationHomology.OneLoop
