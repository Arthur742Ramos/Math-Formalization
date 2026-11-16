module
public import Mathlib.Topology.Homotopy.Equiv

/-! SOURCE ONLY / UNCOMPILED. Algebraic descent of an equivalence through
an exactly commuting square of equivalences. The forward map is preserved. -/
@[expose] public noncomputable section
open scoped Topology
open ContinuousMap
namespace AutomaticCoherence.HomotopyEquivalenceDescent01

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Replace only the forward map by a homotopic specified map. -/
def withForward (e : X ≃ₕ Y) (f : C(X,Y)) (h : f.Homotopic e.toFun) : X ≃ₕ Y where
  toFun := f
  invFun := e.invFun
  left_inv := (Homotopic.comp (Homotopic.refl e.invFun) h).trans e.left_inv
  right_inv := (Homotopic.comp h (Homotopic.refl e.invFun)).trans e.right_inv

@[simp] lemma withForward_toFun (e : X ≃ₕ Y) (f : C(X,Y))
    (h : f.Homotopic e.toFun) : (withForward e f h).toFun = f := rfl

/-- The commutation hypothesis is a literal equality of continuous maps.
It is intended to be discharged by actual collapse naturality, never assumed
as a replacement for the geometric or double-cylinder equivalence theorem. -/
def descend (e : X ≃ₕ Y) (e' : X' ≃ₕ Y') (d : X ≃ₕ X') (f : C(Y,Y'))
    (commute : f.comp e.toFun = e'.toFun.comp d.toFun) : Y ≃ₕ Y' := by
  let E : Y ≃ₕ Y' := (e.symm.trans d).trans e'
  have hE : E.toFun.Homotopic f := by
    change ((e'.toFun.comp d.toFun).comp e.invFun).Homotopic f
    rw [← commute]
    exact Homotopic.comp (Homotopic.refl f) e.right_inv
  exact withForward E f hE.symm

@[simp] lemma descend_toFun (e : X ≃ₕ Y) (e' : X' ≃ₕ Y') (d : X ≃ₕ X')
    (f : C(Y,Y')) (commute : f.comp e.toFun = e'.toFun.comp d.toFun) :
    (descend e e' d f commute).toFun = f := rfl

end AutomaticCoherence.HomotopyEquivalenceDescent01
