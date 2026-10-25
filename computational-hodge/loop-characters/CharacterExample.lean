module
public import HarmonicCharacters
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

theorem winding_refl : winding (_root_.Path.refl (0 : AddCircle (1 : ℝ))) = 0 := by
  exact congrArg (fun f : C(unitInterval,ℝ) => f 1)
    (circleCover.liftPath_const (e := (0 : ℝ)) (x := (0 : AddCircle (1 : ℝ))) (by simp))

theorem circleLift_translate (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) (u : ℝ)
    (hu : (u : AddCircle (1 : ℝ)) = 0) :
    (⟨fun t => u + circleLift p t,continuous_const.add (circleLift p).continuous⟩ :
      C(unitInterval,ℝ)) = circleCover.liftPath p.toContinuousMap u (by simp [hu]) := by
  apply (circleCover.eq_liftPath_iff' _).mpr
  constructor
  · funext t
    change ((u + circleLift p t : ℝ) : AddCircle (1 : ℝ)) = p t
    rw [AddCircle.coe_add,hu,zero_add]
    exact congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) t
  · change u + circleCover.liftPath p.toContinuousMap 0 _ 0 = u
    rw [circleCover.liftPath_zero,add_zero]

theorem winding_trans (p q : _root_.Path (0 : AddCircle (1 : ℝ)) 0) :
    winding (p.trans q) = winding p + winding q := by
  have hu : ((circleLift p 1 : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (congrFun (circleCover.liftPath_lifts p.toContinuousMap 0 (by simp)) 1).trans p.target
  have ht := congrArg (fun f : C(unitInterval,ℝ) => f 1)
    (circleCover.liftPath_trans (e := (0 : ℝ)) (by simp) p q)
  simp only [ContinuousMap.coe_coe,_root_.Path.trans_apply] at ht
  norm_num at ht
  change winding (p.trans q) = circleCover.liftPath q.toContinuousMap (circleLift p 1) _ 1 at ht
  rw [ht,← circleLift_translate q (circleLift p 1) hu]
  rfl

/-- A real character of the actual ambient fundamental group, constructed by lifting. -/
noncomputable def windingCharacter : FundamentalGroup (AddCircle (1 : ℝ)) 0 →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (g.lift winding (fun _ _ h => winding_homotopic h))
  map_one' := winding_refl
  map_mul' g h := by
    induction g using Quotient.inductionOn with | _ p =>
    induction h using Quotient.inductionOn with | _ q =>
    exact (winding_trans q p).trans (add_comm _ _)

def onceAround : _root_.Path (0 : AddCircle (1 : ℝ)) 0 where
  toFun t := ((t : ℝ) : AddCircle (1 : ℝ))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := by simp
  target' := by simp

theorem winding_onceAround : winding onceAround = 1 := by
  have h : (⟨fun t : unitInterval => (t : ℝ),continuous_subtype_val⟩ : C(unitInterval,ℝ)) =
      circleLift onceAround := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    exact ⟨rfl,rfl⟩
  exact (congrArg (fun f : C(unitInterval,ℝ) => f 1) h).symm

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

theorem circle_harmonic_nonzero :
    (harmonicCharacterEquiv circleRooting).symm circleCharacter ≠ 0 := by
  intro h
  have hp := harmonicCharacterEquiv_loop circleRooting
    ((harmonicCharacterEquiv circleRooting).symm circleCharacter)
    (.single ())
  rw [LinearEquiv.apply_symm_apply,circle_character_generator,h] at hp
  norm_num [period,evaluation] at hp

end ComputationalHodge.LoopCharacters
