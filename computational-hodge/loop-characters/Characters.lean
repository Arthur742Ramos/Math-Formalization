module
public import LoopImage
@[expose] public section

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

/-- Algebraic real characters, with the ordinary pointwise vector-space structure. -/
def Characters (S : ContinuousGeometricStepSystem A E) (a : A) :
    Submodule ℝ (representedGroup S a → ℝ) where
  carrier f := f 1 = 0 ∧ ∀ x y, f (x*y) = f x + f y
  zero_mem' := ⟨rfl,fun _ _ => (add_zero _).symm⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨by change f 1 + g 1 = 0; rw [hf.1,hg.1,add_zero],
      fun x y => by change f (x*y)+g (x*y) = (f x+g x)+(f y+g y)
                    rw [hf.2,hg.2]; ring⟩
  smul_mem' := by
    intro r f hf
    exact ⟨by change r*f 1=0; rw [hf.1,mul_zero],
      fun x y => by change r*f (x*y)=r*f x+r*f y; rw [hf.2,mul_add]⟩

/-- These are exactly the usual group homomorphisms to the additive reals. -/
def characterEquivHom (a : A) :
    Characters S a ≃ (representedGroup S a →* Multiplicative ℝ) where
  toFun χ := { toFun := fun g => Multiplicative.ofAdd (χ.val g)
               map_one' := χ.property.1
               map_mul' := χ.property.2 }
  invFun f := ⟨fun g => (f g).toAdd,f.map_one,f.map_mul⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem character_inv {a : A} (χ : Characters S a) (g : representedGroup S a) :
    χ.val g⁻¹ = -χ.val g := by
  have h := χ.property.2 g g⁻¹
  rw [mul_inv_cancel,χ.property.1] at h
  linarith

noncomputable def loopRepresentative {a : A} (g : representedGroup S a) :
    GeometricTrace S.toGeometricStepSystem a a := Classical.choose g.property

theorem loopRepresentative_class {a : A} (g : representedGroup S a) :
    traceClass (loopRepresentative g) = g.val := Classical.choose_spec g.property

variable [Fintype E]

noncomputable def periodCharacter {a : A} (ω : Closed (geometricPresentation S)) :
    Characters S a := by
  let f := fun g : representedGroup S a => period (loopRepresentative g) ω
  have eval (p : GeometricTrace S.toGeometricStepSystem a a) :
      f (representedLoop p) = period p ω :=
    closed_period_homotopic ω _ p (loopRepresentative_class _)
  refine ⟨f,?_,?_⟩
  · exact (eval (.refl a)).trans rfl
  · intro g h
    obtain ⟨p,hp⟩ := g.property
    obtain ⟨q,hq⟩ := h.property
    have gp : g = representedLoop p := Subtype.ext hp.symm
    have hq' : h = representedLoop q := Subtype.ext hq.symm
    rw [gp,hq',← representedLoop_trans,eval,eval,eval]
    exact add_comm _ _

theorem periodCharacter_loop {a : A} (ω : Closed (geometricPresentation S))
    (p : GeometricTrace S.toGeometricStepSystem a a) :
    (periodCharacter ω : Characters S a).val (representedLoop p) = period p ω :=
  closed_period_homotopic ω _ p (loopRepresentative_class _)

noncomputable def characterMap (a : A) :
    Closed (geometricPresentation S) →ₗ[ℝ] Characters S a where
  toFun := periodCharacter
  map_add' ω η := by
    apply Subtype.ext
    funext g
    exact (period (loopRepresentative g)).map_add _ _
  map_smul' r ω := by
    apply Subtype.ext
    funext g
    exact (period (loopRepresentative g)).map_smul r _

end ComputationalHodge.LoopCharacters
