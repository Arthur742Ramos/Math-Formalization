module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.LoopCharacters.Semantics
open ComputationalPaths.Path.GeometricTopology
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E} {a : A}

example (g : FundamentalGroup A a) :
    g ∈ representedGroup S a ↔
      ∃ p : GeometricTrace S.toGeometricStepSystem a a, traceClass p = g := Iff.rfl

example (x : A) : Active S a x ↔ x = a ∨ ∃ e : E, S.src e = x ∨ S.tgt e = x := Iff.rfl

example (T : Rooting S a) (x : A) (hx : Active S a x) :
    GeometricTrace S.toGeometricStepSystem a x := T.trace x hx

example (T : Rooting S a) : T.trace a (Or.inl rfl) = .refl a := T.at_root

example (x y : ℝ) : Multiplicative.ofAdd (x+y) =
    Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl

example : DiscreteTopology (AddSubgroup.zmultiples (1 : ℝ)) := inferInstance

example (χ : representedGroup S a → ℝ) : χ ∈ Characters S a ↔
    χ 1 = 0 ∧ ∀ x y,χ (x*y)=χ x+χ y := Iff.rfl

example (χ : Characters S a) (g : representedGroup S a) :
    (characterEquivHom a χ) g = Multiplicative.ofAdd (χ.val g) := rfl

example (g h : FundamentalGroup A a) : g*h = h.trans g := rfl

example (p q : _root_.Path a a) :
    _root_.Path.Homotopic.Quotient.mk p = _root_.Path.Homotopic.Quotient.mk q ↔
      Nonempty (ContinuousMap.HomotopyRel p.toContinuousMap q.toContinuousMap {0,1}) :=
  _root_.Path.Homotopic.Quotient.eq

example (ω : Cochain E) : ω ∈ Harmonic (geometricPresentation S) ↔
    (∀ c : Cell (geometricPresentation S),period c.left ω-period c.right ω=0) ∧
      ∀ z ∈ Exact S,inner ℝ z ω=0 := by
  constructor
  · intro h
    exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,horth⟩
    exact ⟨funext h,horth⟩

example (ω : Cochain E) : ω ∈ Exact S ↔
    ∃ f : A → ℝ, d0 S.toGeometricStepSystem f=ω := Iff.rfl

example (T : Rooting S a) (χ : Characters S a) (e : E) :
    characterCochain T χ e = χ.val (representedLoop (basedTrace T (.single e)
      (Or.inr ⟨e,Or.inl rfl⟩) (Or.inr ⟨e,Or.inr rfl⟩))) := rfl

example (T : Rooting S a) (h : Harmonic (geometricPresentation S)) :
    harmonicCharacterEquiv T h = harmonicCharacterMap a h := rfl

example (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) :
    winding p = circleCover.liftPath p.toContinuousMap 0 (by simp) 1 := rfl

example : AddCircle (1 : ℝ) = (ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl

example (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) :
    windingCharacter (_root_.Path.Homotopic.Quotient.mk p) = Multiplicative.ofAdd (winding p) := rfl

example (t : unitInterval) : onceAround t = ((t : ℝ) : AddCircle (1 : ℝ)) := rfl

example : period (.single (S := circleSystem.toGeometricStepSystem) ())
    ((harmonicCharacterEquiv circleRooting).symm circleCharacter : Cochain Unit) = 1 := by
  have h := harmonicCharacterEquiv_loop circleRooting
    ((harmonicCharacterEquiv circleRooting).symm circleCharacter) (.single ())
  rw [LinearEquiv.apply_symm_apply,circle_character_generator] at h
  exact h.symm

end ComputationalHodge.LoopCharacters.Semantics
-- END material-imported-definition audit
