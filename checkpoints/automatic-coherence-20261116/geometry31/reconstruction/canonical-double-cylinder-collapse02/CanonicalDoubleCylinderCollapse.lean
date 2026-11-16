import DoubleCylinderCollapse
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-! SOURCE ONLY / UNCOMPILED. Canonical actual-pushout specialization. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology
namespace AutomaticCoherence.DoubleCylinderCollapse01

variable {A B C : TopCat.{0}} (i : A ⟶ B) (j : A ⟶ C)

def canonicalDoubleCylinder : DoubleCylinder i j := by
  let M := pushout i (endpoint A 0)
  let c : cylinderSpace A ⟶ M := pushout.inr i (endpoint A 0)
  let k : A ⟶ M := endpoint A 1 ≫ c
  exact {
    M := M
    D := pushout k j
    b := pushout.inl i (endpoint A 0)
    c := c
    m := pushout.inl k j
    d := pushout.inr k j
    first := IsPushout.of_hasPushout i (endpoint A 0)
    second := IsPushout.of_hasPushout k j }

/-- The only homotopical hypothesis is the original bare HEP on i. -/
def canonicalCollapseEquivalence (hi : TopologicalHEPClosure01.HasHEP i) :
    (canonicalDoubleCylinder i j).D ≃ₕ (pushout i j : TopCat.{0}) :=
  collapseEquivalence (IsPushout.of_hasPushout i j) (canonicalDoubleCylinder i j) hi

@[simp] lemma canonicalCollapseEquivalence_toFun (hi : TopologicalHEPClosure01.HasHEP i) :
    (canonicalCollapseEquivalence i j hi).toFun =
      (collapse (IsPushout.of_hasPushout i j) (canonicalDoubleCylinder i j)).hom := rfl

end AutomaticCoherence.DoubleCylinderCollapse01
