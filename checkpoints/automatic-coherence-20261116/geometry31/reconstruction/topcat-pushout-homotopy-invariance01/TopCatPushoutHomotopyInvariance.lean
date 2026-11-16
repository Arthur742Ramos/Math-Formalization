import SplitFullDoubleCylinderNaturality
import StrictSpanEquivalenceData
import CanonicalDoubleCylinderCollapse
import HomotopyEquivalenceDescent

/-! SOURCE ONLY / UNCOMPILED. Actual homotopy invariance of strict double
cylinders, and of ordinary pushouts along the two given bare HEP maps.
Vertical equivalences and literal span commutation are the only input data;
compatible inverse homotopies, naturality, and the output equivalence are proved. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology
namespace AutomaticCoherence.TopCatPushoutHomotopyInvariance01
open MappingCylinderFoundation01
open SplitDoubleCylinderFoundation01
open DoubleCylinderCollapse01
open DoubleCylinderComparison01
open StrictSpanEquivalenceData01

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}
  (f : SpanMap i j i' j') (e : VerticalEquivalences f)

/-- The exact strict split-cylinder map, obtained from arbitrary inverse witnesses. -/
def splitEquivalence (sd : SplitDoubleCylinder i j) (sd' : SplitDoubleCylinder i' j') :
    sd.S ≃ₕ sd'.S :=
  SplitDoubleCylinderStrictMap01.equivalence sd sd' (inverseData f e) f.left f.right

lemma splitEquivalence_toFun (sd : SplitDoubleCylinder i j)
    (sd' : SplitDoubleCylinder i' j') :
    (splitEquivalence f e sd sd').toFun =
      (SplitDoubleCylinderStrictMap01.strictMap f sd sd').hom := rfl

/-- Both split models are constructed canonically. Their homeomorphisms to
actual full cylinders have proved literal strict-span naturality. -/
def doubleEquivalence (fd : DoubleCylinder i j) (fd' : DoubleCylinder i' j') :
    fd.D ≃ₕ fd'.D := by
  let sd := canonicalSplitDoubleCylinder i j
  let sd' := canonicalSplitDoubleCylinder i' j'
  refine HomotopyEquivalenceDescent01.descend
    (SplitFullDoubleCylinder01.homeomorph sd fd).toHomotopyEquiv
    (SplitFullDoubleCylinder01.homeomorph sd' fd').toHomotopyEquiv
    (splitEquivalence f e sd sd') (doubleMap f fd fd').hom ?_
  change (doubleMap f fd fd').hom.comp (SplitFullDoubleCylinder01.toFull sd fd).hom =
    (SplitFullDoubleCylinder01.toFull sd' fd').hom.comp
      (SplitDoubleCylinderStrictMap01.strictMap f sd sd').hom
  exact congrArg (fun q : sd.S ⟶ fd'.D => q.hom)
    (SplitFullDoubleCylinderNaturality01.toFull_naturality f sd sd' fd fd').symm

lemma doubleEquivalence_toFun (fd : DoubleCylinder i j) (fd' : DoubleCylinder i' j') :
    (doubleEquivalence f e fd fd').toFun = (doubleMap f fd fd').hom := rfl

variable {P P' : TopCat.{0}} {L : B ⟶ P} {R : C ⟶ P}
  {L' : B' ⟶ P'} {R' : C' ⟶ P'}
  (hp : IsPushout i j L R) (hp' : IsPushout i' j' L' R')
  (hi : TopologicalHEPClosure01.HasHEP i)
  (hi' : TopologicalHEPClosure01.HasHEP i')

/-- The two cylinders and both collapse inverses are constructed here. The
forward map is the literal map between the given actual pushouts. -/
def ordinaryEquivalence : P ≃ₕ P' := by
  let fd := canonicalDoubleCylinder i j
  let fd' := canonicalDoubleCylinder i' j'
  refine HomotopyEquivalenceDescent01.descend
    (collapseEquivalence hp fd hi) (collapseEquivalence hp' fd' hi')
    (doubleEquivalence f e fd fd') (ordinaryMap f hp hp').hom ?_
  change (ordinaryMap f hp hp').hom.comp (collapse hp fd).hom =
    (collapse hp' fd').hom.comp (doubleMap f fd fd').hom
  exact congrArg (fun q : fd.D ⟶ P' => q.hom)
    (collapse_naturality f fd fd' hp hp').symm

lemma ordinaryEquivalence_toFun :
    (ordinaryEquivalence f e hp hp' hi hi').toFun = (ordinaryMap f hp hp').hom := rfl

end AutomaticCoherence.TopCatPushoutHomotopyInvariance01
