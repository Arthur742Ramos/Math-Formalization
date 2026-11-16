import MappingCylinderStrictMap
import SplitDoubleCylinderInverse
import DoubleCylinderComparison
import HomotopyEquivalenceDescent

/-! SOURCE ONLY / UNCOMPILED. Literal strict maps of split double cylinders.
The constant comparison collar is removed by two matching actual homotopies.
The resulting equivalence preserves the literal strict forward map. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology
namespace AutomaticCoherence.SplitDoubleCylinderStrictMap01
open MappingCylinderFoundation01 SplitDoubleCylinderFoundation01
open DoubleCylinderComparison01 (SpanMap)

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}
  (f : SpanMap i j i' j') (dc : SplitDoubleCylinder i j) (dc' : SplitDoubleCylinder i' j')

def leftStrict : dc.leftCylinder.M ⟶ dc'.S :=
  MappingCylinderStrictMap01.strictMap dc.leftCylinder dc'.leftCylinder f.a f.b f.left ≫ dc'.left

def rightStrict : dc.rightCylinder.M ⟶ dc'.S :=
  MappingCylinderStrictMap01.strictMap dc.rightCylinder dc'.rightCylinder f.a f.c f.right ≫ dc'.right

lemma strict_agrees (x : A) :
    leftStrict f dc dc' (dc.leftCylinder.free x) =
      rightStrict f dc dc' (dc.rightCylinder.free x) := by
  change dc'.left (MappingCylinderStrictMap01.strictMap dc.leftCylinder dc'.leftCylinder
    f.a f.b f.left (dc.leftCylinder.free x)) =
    dc'.right (MappingCylinderStrictMap01.strictMap dc.rightCylinder dc'.rightCylinder
      f.a f.c f.right (dc.rightCylinder.free x))
  rw [MappingCylinderStrictMap01.strictMap_free, MappingCylinderStrictMap01.strictMap_free]
  exact ConcreteCategory.congr_hom dc'.square.w (f.a x)

def strictMap : dc.S ⟶ dc'.S :=
  dc.desc (leftStrict f dc dc') (rightStrict f dc dc') (strict_agrees f dc dc')

lemma strictMap_left (x : dc.leftCylinder.M) :
    strictMap f dc dc' (dc.left x) = leftStrict f dc dc' x := dc.desc_left _ _ _ x

lemma strictMap_right (x : dc.rightCylinder.M) :
    strictMap f dc dc' (dc.right x) = rightStrict f dc dc' x := dc.desc_right _ _ _ x

lemma strictMap_common (x : A) : strictMap f dc dc' (dc.common x) = dc'.common (f.a x) :=
  (strictMap_left f dc dc' (dc.leftCylinder.free x)).trans
    (congrArg dc'.left (MappingCylinderStrictMap01.strictMap_free
      dc.leftCylinder dc'.leftCylinder f.a f.b f.left x))

lemma strictMap_baseLeft (x : B) :
    strictMap f dc dc' (dc.baseLeft x) = dc'.baseLeft (f.b x) :=
  (strictMap_left f dc dc' (dc.leftCylinder.base x)).trans
    (congrArg dc'.left (MappingCylinderStrictMap01.strictMap_base
      dc.leftCylinder dc'.leftCylinder f.a f.b f.left x))

lemma strictMap_baseRight (x : C) :
    strictMap f dc dc' (dc.baseRight x) = dc'.baseRight (f.c x) :=
  (strictMap_right f dc dc' (dc.rightCylinder.base x)).trans
    (congrArg dc'.right (MappingCylinderStrictMap01.strictMap_base
      dc.rightCylinder dc'.rightCylinder f.a f.c f.right x))

lemma strictMap_leftInterval (s : I) (x : A) :
    strictMap f dc dc' (dc.left (dc.leftCylinder.interval (s,x))) =
      dc'.left (dc'.leftCylinder.interval (s,f.a x)) :=
  (strictMap_left f dc dc' (dc.leftCylinder.interval (s,x))).trans
    (congrArg dc'.left (MappingCylinderStrictMap01.strictMap_interval
      dc.leftCylinder dc'.leftCylinder f.a f.b f.left s x))

lemma strictMap_rightInterval (s : I) (x : A) :
    strictMap f dc dc' (dc.right (dc.rightCylinder.interval (s,x))) =
      dc'.right (dc'.rightCylinder.interval (s,f.a x)) :=
  (strictMap_right f dc dc' (dc.rightCylinder.interval (s,x))).trans
    (congrArg dc'.right (MappingCylinderStrictMap01.strictMap_interval
      dc.rightCylinder dc'.rightCylinder f.a f.c f.right s x))

def collaredMap : dc.S ⟶ dc'.S :=
  generalizedMap dc dc' f.a f.b f.c
    (MappingCylinderStrictMap01.constantComparison f.a f.b f.left)
    (MappingCylinderStrictMap01.constantComparison f.a f.c f.right)

/-- The actual left half collar homotopy, with exact global endpoint types. -/
def leftCollar :
    ((collaredMap f dc dc').hom.comp dc.left.hom).Homotopy
      ((strictMap f dc dc').hom.comp dc.left.hom) where
  toContinuousMap := dc'.left.hom.comp
    (MappingCylinderStrictMap01.collarRemoval
      dc.leftCylinder dc'.leftCylinder f.a f.b f.left).toContinuousMap
  map_zero_left x :=
    (congrArg dc'.left (MappingCylinderStrictMap01.collarRemoval
      dc.leftCylinder dc'.leftCylinder f.a f.b f.left |>.map_zero_left x)).trans
      (generalizedMap_left dc dc' f.a f.b f.c _ _ x).symm
  map_one_left x :=
    (congrArg dc'.left (MappingCylinderStrictMap01.collarRemoval
      dc.leftCylinder dc'.leftCylinder f.a f.b f.left |>.map_one_left x)).trans
      (strictMap_left f dc dc' x).symm

def rightCollar :
    ((collaredMap f dc dc').hom.comp dc.right.hom).Homotopy
      ((strictMap f dc dc').hom.comp dc.right.hom) where
  toContinuousMap := dc'.right.hom.comp
    (MappingCylinderStrictMap01.collarRemoval
      dc.rightCylinder dc'.rightCylinder f.a f.c f.right).toContinuousMap
  map_zero_left x :=
    (congrArg dc'.right (MappingCylinderStrictMap01.collarRemoval
      dc.rightCylinder dc'.rightCylinder f.a f.c f.right |>.map_zero_left x)).trans
      (generalizedMap_right dc dc' f.a f.b f.c _ _ x).symm
  map_one_left x :=
    (congrArg dc'.right (MappingCylinderStrictMap01.collarRemoval
      dc.rightCylinder dc'.rightCylinder f.a f.c f.right |>.map_one_left x)).trans
      (strictMap_right f dc dc' x).symm

lemma collar_agrees (t : I) (x : A) :
    leftCollar f dc dc' (t,dc.leftCylinder.free x) =
      rightCollar f dc dc' (t,dc.rightCylinder.free x) := by
  change dc'.left (MappingCylinderStrictMap01.collarRemoval
    dc.leftCylinder dc'.leftCylinder f.a f.b f.left (t,dc.leftCylinder.free x)) =
    dc'.right (MappingCylinderStrictMap01.collarRemoval
      dc.rightCylinder dc'.rightCylinder f.a f.c f.right (t,dc.rightCylinder.free x))
  rw [MappingCylinderStrictMap01.collarRemoval_free,
    MappingCylinderStrictMap01.collarRemoval_free]
  exact ConcreteCategory.congr_hom dc'.square.w (f.a x)

def collarHomotopy : (collaredMap f dc dc').hom.Homotopy (strictMap f dc dc').hom :=
  dc.homotopy _ _ (leftCollar f dc dc') (rightCollar f dc dc') (collar_agrees f dc dc')

variable (d : SplitDoubleCylinderInverse01.SpanInverseData i j i' j')
  (hL : i ≫ d.b = d.a ≫ i') (hR : j ≫ d.c = d.a ≫ j')

def spanMapOfData : SpanMap i j i' j' where
  a := d.a
  b := d.b
  c := d.c
  left := hL
  right := hR

/-- Keep all inverse data; specialize only the supplied comparison paths to constants. -/
def constantInverseData : SplitDoubleCylinderInverse01.SpanInverseData i j i' j' :=
  { d with
    squareLeft := MappingCylinderStrictMap01.constantComparison d.a d.b hL
    squareRight := MappingCylinderStrictMap01.constantComparison d.a d.c hR }

/-- The exact strict forward map is a homotopy equivalence. -/
def equivalence : dc.S ≃ₕ dc'.S :=
  HomotopyEquivalenceDescent01.withForward
    (SplitDoubleCylinderInverse01.equivalence (constantInverseData d hL hR) dc dc')
    (strictMap (spanMapOfData d hL hR) dc dc').hom
    ⟨(collarHomotopy (spanMapOfData d hL hR) dc dc').symm⟩

lemma equivalence_toFun :
    (equivalence dc dc' d hL hR).toFun = (strictMap (spanMapOfData d hL hR) dc dc').hom := rfl

end AutomaticCoherence.SplitDoubleCylinderStrictMap01
