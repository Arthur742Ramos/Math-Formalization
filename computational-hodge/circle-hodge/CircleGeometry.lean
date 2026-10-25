module
public import Reconstruction
public import Mathlib.Analysis.Convex.Contractible
@[expose] public section

namespace ComputationalHodge.CircleHodge
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters

theorem circle_winding_injective : Function.Injective windingCharacter := by
  let hp := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  let e : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨0,by simp⟩
  intro g h hh
  apply hp.monodromyPerm_injective
  apply Equiv.ext
  have hm : hp.isCoveringMap.monodromy g e = hp.isCoveringMap.monodromy h e := by
    apply Subtype.ext
    induction g using Quotient.inductionOn with | _ p =>
    induction h using Quotient.inductionOn with | _ q =>
    exact congrArg Multiplicative.toAdd hh
  exact congrFun ((hp.monodromy_ext_iff e).mp hm)

theorem circle_winding_integral (g : FundamentalGroup (AddCircle (1 : ℝ)) 0) :
    ∃ n : ℤ, (n : ℝ) = (windingCharacter g).toAdd := by
  induction g using Quotient.inductionOn with | _ p =>
  have h : ((winding p : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) 1).trans p.target
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h
  refine ⟨n,?_⟩
  change (n : ℝ) = winding p
  simpa using hn

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

def circleRooting : Rooting circleSystem 0 where
  trace x hx := by
    have h : x = 0 := hx.elim id (by rintro ⟨e,h|h⟩ <;> exact h.symm)
    subst x
    exact GeometricTrace.refl 0
  at_root := rfl

noncomputable def circleCharacter : Characters circleSystem 0 :=
  (characterEquivHom 0).symm (windingCharacter.comp (representedGroup circleSystem 0).subtype)

theorem circle_character_generator :
    circleCharacter.val (representedLoop (.single (S := circleSystem.toGeometricStepSystem) ())) = 1 :=
  winding_onceAround

end ComputationalHodge.LoopCharacters
