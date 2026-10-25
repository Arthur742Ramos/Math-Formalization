module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.TorusPeriods.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
open scoped InnerProductSpace
variable {E : Type} [Fintype E] [TopologicalSpace E] [DiscreteTopology E] [DecidableEq E]

example : Torus E = (E → (ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ))) := rfl
example (e : E) (t : unitInterval) (j : E) :
    coordinateLoop e t j = if j=e then ((t : ℝ) : AddCircle (1 : ℝ)) else 0 := rfl
example (e : E) : (torusSystem E).src e=0 ∧ (torusSystem E).tgt e=0 := ⟨rfl,rfl⟩
example (g : FundamentalGroup (Torus E) 0) :
    g ∈ representedGroup (torusSystem E) 0 ↔
      ∃ p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0,traceClass p=g := Iff.rfl
example (g h : FundamentalGroup (Torus E) 0) : g*h=h.trans g := rfl
example (χ : FundamentalGroup (Torus E) 0 → ℝ) : χ ∈ AmbientCharacters E ↔
    χ 1=0 ∧ ∀ g h,χ (g*h)=χ g+χ h := Iff.rfl
example (χ : AmbientCharacters E) (g : FundamentalGroup (Torus E) 0) :
    (ambientCharacterEquivHom χ) g=Multiplicative.ofAdd (χ.val g) := rfl
example (g : FundamentalGroup (Torus E) 0) (e : E) :
    windingVector g e=(windingCharacter (coordinateMap e g)).toAdd := rfl
example (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) :
    winding p=circleCover.liftPath p.toContinuousMap 0 (by simp) 1 := rfl
example : DiscreteTopology (AddSubgroup.zmultiples (1 : ℝ)) := inferInstance
example : SimplyConnectedSpace ℝ := inferInstance
example : ContractibleSpace ℝ := inferInstance
example (p : _root_.Path (0 : AddCircle (1 : ℝ)) 0) :
    (circleCover.monodromy (_root_.Path.Homotopic.Quotient.mk p) ⟨0,by simp⟩).val=winding p := rfl
example (ω : Cochain E) : ω ∈ Exact (torusSystem E) ↔
    ∃ f : Torus E → ℝ,d0 (torusSystem E).toGeometricStepSystem f=ω := Iff.rfl
example (ω : Cochain E) : ω ∈ Harmonic (geometricPresentation (torusSystem E)) ↔
    (∀ c : Cell (geometricPresentation (torusSystem E)),period c.left ω-period c.right ω=0) ∧
      ∀ z ∈ Exact (torusSystem E),inner ℝ z ω=0 := by
  constructor
  · intro h; exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,horth⟩; exact ⟨funext h,horth⟩
example (ω : Cochain E) (g : FundamentalGroup (Torus E) 0) :
    (ambientPeriod ω).val g=∑ e,ω e*windingVector g e := rfl
example (h : Harmonic (geometricPresentation (torusSystem E))) :
    harmonicAmbientEquiv h=ambientPeriod (h : Cochain E) := rfl
example (χ : AmbientCharacters E) :
    ∃! h : Harmonic (geometricPresentation (torusSystem E)),
      ∀ p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0,
        period p h=χ.val (traceClass p) := unique_harmonic_loop_periods χ

end ComputationalHodge.TorusPeriods.Semantics
-- END material-imported-definition audit
