import SplitDoubleCylinderInverse
import MappingCylinderStrictMap
import DoubleCylinderComparison
import HomotopyEquivalenceDescent

/-! SOURCE ONLY / UNCOMPILED. Convert genuine vertical homotopy equivalences
with exact forward-map identities into arbitrary inverse data. No triangle,
compatible inverse square, or gluing equivalence is assumed. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology
namespace AutomaticCoherence.StrictSpanEquivalenceData01
open DoubleCylinderComparison01 (SpanMap)

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}

structure VerticalEquivalences (f : SpanMap i j i' j') where
  a : A ≃ₕ A'
  b : B ≃ₕ B'
  c : C ≃ₕ C'
  a_toFun : a.toFun = f.a.hom
  b_toFun : b.toFun = f.b.hom
  c_toFun : c.toFun = f.c.hom

variable (f : SpanMap i j i' j') (e : VerticalEquivalences f)

def exactA : A ≃ₕ A' :=
  HomotopyEquivalenceDescent01.withForward e.a f.a.hom (by
    rw [← e.a_toFun])

def exactB : B ≃ₕ B' :=
  HomotopyEquivalenceDescent01.withForward e.b f.b.hom (by
    rw [← e.b_toFun])

def exactC : C ≃ₕ C' :=
  HomotopyEquivalenceDescent01.withForward e.c f.c.hom (by
    rw [← e.c_toFun])

/-- Choose actual witnesses from the genuine HomotopyEquiv fields. These
choices are arbitrary and satisfy no additional compatibility axiom. -/
def inverseData : SplitDoubleCylinderInverse01.SpanInverseData i j i' j' where
  a := f.a
  b := f.b
  c := f.c
  a' := TopCat.ofHom (exactA f e).invFun
  b' := TopCat.ofHom (exactB f e).invFun
  c' := TopCat.ofHom (exactC f e).invFun
  squareLeft := MappingCylinderStrictMap01.constantComparison f.a f.b f.left
  squareRight := MappingCylinderStrictMap01.constantComparison f.a f.c f.right
  leftA := Classical.choice (exactA f e).left_inv
  rightA := Classical.choice (exactA f e).right_inv
  leftB := Classical.choice (exactB f e).left_inv
  rightB := Classical.choice (exactB f e).right_inv
  leftC := Classical.choice (exactC f e).left_inv
  rightC := Classical.choice (exactC f e).right_inv

end AutomaticCoherence.StrictSpanEquivalenceData01
