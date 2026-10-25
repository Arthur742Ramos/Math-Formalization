module
public import TorusReconstruction
@[expose] public section

namespace ComputationalHodge.TorusPeriods
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
variable {E : Type} [finiteE : Fintype E] [topE : TopologicalSpace E]
  [discreteE : DiscreteTopology E] [decidableE : DecidableEq E]

/-- Ordinary algebraic real characters of the entire ambient fundamental group. -/
def AmbientCharacters (E : Type) : Submodule ℝ (FundamentalGroup (Torus E) 0 → ℝ) where
  carrier f := f 1=0 ∧ ∀ g h,f (g*h)=f g+f h
  zero_mem' := ⟨rfl,fun _ _ => (add_zero _).symm⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨by change f 1+g 1=0; rw [hf.1,hg.1,add_zero],
      fun x y => by change f (x*y)+g (x*y)=(f x+g x)+(f y+g y); rw [hf.2,hg.2]; ring⟩
  smul_mem' := by
    intro r f hf
    exact ⟨by change r*f 1=0; rw [hf.1,mul_zero],
      fun x y => by change r*f (x*y)=r*f x+r*f y; rw [hf.2,mul_add]⟩

def ambientCharacterEquivHom :
    AmbientCharacters E ≃ (FundamentalGroup (Torus E) 0 →* Multiplicative ℝ) where
  toFun χ := {toFun := fun g => Multiplicative.ofAdd (χ.val g)
              map_one' := χ.property.1
              map_mul' := χ.property.2}
  invFun f := ⟨fun g => (f g).toAdd,f.map_one,f.map_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def ambientPeriod (ω : Cochain E) : AmbientCharacters E :=
  ⟨fun g => ∑ e,ω e * windingVector g e,
   by
     change (∑ e,ω e*windingVector (1 : FundamentalGroup (Torus E) 0) e)=0
     simp only [windingVector_one,mul_zero,Finset.sum_const_zero],
   by
     intro g h
     change (∑ e,ω e*windingVector (g*h) e) =
       (∑ e,ω e*windingVector g e)+(∑ e,ω e*windingVector h e)
     simp only [windingVector_mul,mul_add,Finset.sum_add_distrib]⟩

theorem ambientPeriod_coordinate (ω : Cochain E) (e : E) :
    (ambientPeriod ω).val (traceClass (S := torusSystem E) (.single e)) = ω e := by
  simp [ambientPeriod,coordinate_winding]

noncomputable def torusRooting : Rooting (torusSystem E) 0 where
  trace x hx := by
    have h : x=0 := hx.elim id (by rintro ⟨e,h|h⟩ <;> exact h.symm)
    subst x
    exact .refl 0
  at_root := rfl

noncomputable def restrictCharacter (χ : AmbientCharacters E) : Characters (torusSystem E) 0 :=
  ⟨fun g => χ.val g.val,χ.property.1,fun g h => χ.property.2 g.val h.val⟩

noncomputable def reconstructed (χ : AmbientCharacters E) : Cochain E :=
  characterCochain torusRooting (restrictCharacter χ)

theorem reconstructed_coordinate (χ : AmbientCharacters E) (e : E) :
    reconstructed χ e = χ.val (traceClass (S := torusSystem E) (.single e)) :=
  characterCochain_loop torusRooting (restrictCharacter χ) (.single e)

theorem reconstructed_period (χ : AmbientCharacters E)
    (p : GeometricTrace (torusSystem E).toGeometricStepSystem 0 0) :
    period p (reconstructed χ) = χ.val (traceClass p) :=
  characterCochain_loop torusRooting (restrictCharacter χ) p

theorem reconstructed_ambientPeriod (ω : Cochain E) : reconstructed (ambientPeriod ω) = ω := by
  ext e
  exact (reconstructed_coordinate _ e).trans (ambientPeriod_coordinate ω e)

theorem torus_closed_eq_top : Closed (geometricPresentation (torusSystem E)) = ⊤ := by
  apply top_unique
  intro ω _
  rw [← reconstructed_ambientPeriod ω]
  exact characterCochain_closed torusRooting (restrictCharacter (ambientPeriod ω))

theorem torus_exact_eq_bot : Exact (torusSystem E) = ⊥ := by
  apply le_antisymm
  · rintro ω ⟨f,rfl⟩
    change d0 (torusSystem E).toGeometricStepSystem f = 0
    ext e
    exact sub_self (f 0)
  · exact bot_le

theorem torus_harmonic_eq_top : Harmonic (geometricPresentation (torusSystem E)) = ⊤ := by
  rw [Harmonic,torus_closed_eq_top,torus_exact_eq_bot]
  simp

noncomputable def harmonicCoefficients (ω : Cochain E) : Harmonic (geometricPresentation (torusSystem E)) :=
  ⟨ω,by rw [torus_harmonic_eq_top]; trivial⟩

end ComputationalHodge.TorusPeriods
