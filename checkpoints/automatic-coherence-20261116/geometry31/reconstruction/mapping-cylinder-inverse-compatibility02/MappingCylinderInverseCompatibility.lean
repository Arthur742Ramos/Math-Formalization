import MappingCylinderVariation
import MappingCylinderComposition
import ThreeSidedSquareFiller

/-! SOURCE ONLY / UNCOMPILED.
Construct the comparison compatibility from arbitrary inverse homotopies.
The actual filled square has a residual top loop, not an assumed constant.
No HEP, compatible inverses, synchronized schedule or invariance is asserted. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology

namespace AutomaticCoherence.MappingCylinderInverseCompatibility01
open MappingCylinderFoundation01
open MappingCylinderComposition01 (whiskerLeft whiskerRight)

section FilledComparison
variable {A B : TopCat.{0}} {f : A ⟶ B} {p : A ⟶ A} {q : B ⟶ B}
  (HA : p.hom.Homotopy (𝟙 A : A ⟶ A).hom) (HB : q.hom.Homotopy (𝟙 B : B ⟶ B).hom)
  (Ω : (p ≫ f).hom.Homotopy (f ≫ q).hom)

def leftBoundary : C(I × A,B) := f.hom.comp HA.toContinuousMap

def rightBoundary : C(I × A,B) :=
  HB.toContinuousMap.comp ⟨fun z => (z.1,f z.2), by fun_prop⟩

lemma left_corner (x : A) : leftBoundary (f := f) HA (0,x) = Ω (0,x) :=
  (congrArg f (HA.map_zero_left x)).trans (Ω.map_zero_left x).symm

lemma right_corner (x : A) : rightBoundary (f := f) HB (0,x) = Ω (1,x) :=
  (HB.map_zero_left (f x)).trans (Ω.map_one_left x).symm

/-- Actual closed pasting followed by the actual three-sided retraction. -/
def filledSquare : C((I × I) × A,B) :=
  ThreeSidedSquareFiller01.fill Ω.toContinuousMap
    (leftBoundary (f := f) HA) (rightBoundary (f := f) HB)
    (left_corner HA Ω) (right_corner HB Ω)

lemma filledSquare_bottom (s : I) (x : A) :
    filledSquare HA HB Ω ((0,s),x) = Ω (s,x) :=
  ThreeSidedSquareFiller01.fill_bottom _ _ _ _ _ s x

lemma filledSquare_left (v : I) (x : A) :
    filledSquare HA HB Ω ((v,0),x) = f (HA (v,x)) :=
  ThreeSidedSquareFiller01.fill_left _ _ _ _ _ v x

lemma filledSquare_right (v : I) (x : A) :
    filledSquare HA HB Ω ((v,1),x) = HB (v,f x) :=
  ThreeSidedSquareFiller01.fill_right _ _ _ _ _ v x

/-- The top is an actual loop at f. No assertion that its interior is constant. -/
def residualLoop : f.hom.Homotopy f.hom where
  toContinuousMap := ⟨fun z => filledSquare HA HB Ω ((1,z.1),z.2), by fun_prop⟩
  map_zero_left x := (filledSquare_left HA HB Ω 1 x).trans
    (congrArg f (HA.map_one_left x))
  map_one_left x := (filledSquare_right HA HB Ω 1 x).trans
    (HB.map_one_left (f x))

variable (mc : MappingCylinder f)

/-- Joint variation with moving free-end map HA and moving base map HB. -/
def comparisonFamily : C(I × mc.M,mc.M) :=
  MappingCylinderVariation01.family mc mc HA.toContinuousMap HB.toContinuousMap
    (filledSquare HA HB Ω)
    (filledSquare_left HA HB Ω) (filledSquare_right HA HB Ω)

lemma comparisonFamily_base (v : I) (y : B) :
    comparisonFamily HA HB Ω mc (v,mc.base y) = mc.base (HB (v,y)) :=
  MappingCylinderVariation01.family_base _ _ _ _ _ _ _ v y

lemma comparisonFamily_free (v : I) (x : A) :
    comparisonFamily HA HB Ω mc (v,mc.free x) = mc.free (HA (v,x)) :=
  MappingCylinderVariation01.family_free _ _ _ _ _ _ _ v x

/-- Literal source and target generalized maps. Compatibility was constructed above. -/
def deformation :
    (generalized mc p q Ω mc).hom.Homotopy
      (generalized mc (𝟙 A) (𝟙 B) (residualLoop HA HB Ω) mc).hom where
  toContinuousMap := comparisonFamily HA HB Ω mc
  map_zero_left z := ConcreteCategory.congr_hom
    (MappingCylinderVariation01.family_at mc mc HA.toContinuousMap HB.toContinuousMap
      (filledSquare HA HB Ω) (filledSquare_left HA HB Ω) (filledSquare_right HA HB Ω)
      0 p q Ω (fun x => HA.map_zero_left x) (fun y => HB.map_zero_left y)
      (fun s x => filledSquare_bottom HA HB Ω s x)) z
  map_one_left z := ConcreteCategory.congr_hom
    (MappingCylinderVariation01.family_at mc mc HA.toContinuousMap HB.toContinuousMap
      (filledSquare HA HB Ω) (filledSquare_left HA HB Ω) (filledSquare_right HA HB Ω)
      1 (𝟙 A) (𝟙 B) (residualLoop HA HB Ω)
      (fun x => HA.map_one_left x) (fun y => HB.map_one_left y)
      (fun _ _ => rfl)) z

lemma deformation_base (v : I) (y : B) :
    deformation HA HB Ω mc (v,mc.base y) = mc.base (HB (v,y)) :=
  comparisonFamily_base HA HB Ω mc v y

lemma deformation_free (v : I) (x : A) :
    deformation HA HB Ω mc (v,mc.free x) = mc.free (HA (v,x)) :=
  comparisonFamily_free HA HB Ω mc v x
end FilledComparison

section ArbitraryInverses
variable {A B A' B' : TopCat.{0}} {f : A ⟶ B} {f' : A' ⟶ B'}
  (a : A ⟶ A') (b : B ⟶ B')
  (φ : (a ≫ f').hom.Homotopy (f ≫ b).hom)
  (a' : A' ⟶ A) (b' : B' ⟶ B)
  (EA : (a' ≫ a).hom.Homotopy (𝟙 A' : A' ⟶ A').hom)
  (HB : (b ≫ b').hom.Homotopy (𝟙 B : B ⟶ B).hom)

/-- Reverse B, reverse the given square, then follow the other inverse homotopy.
Binary concatenation gives quarter/quarter/half slots, not the prose thirds. -/
def reverseSquare : (a' ≫ f).hom.Homotopy (f' ≫ b').hom :=
  (((whiskerLeft (a' ≫ f) HB.symm).trans
    (whiskerLeft a' (whiskerRight b' φ.symm))).trans
      (whiskerRight (f' ≫ b') EA)).cast rfl rfl

/-- Exactly the square occurring in normalization of the generalized composite. -/
def compositeSquare :
    (a ≫ a' ≫ f).hom.Homotopy (f ≫ b ≫ b').hom :=
  ((whiskerLeft a (reverseSquare a b φ a' b' EA HB)).trans
    (whiskerRight b' φ)).cast rfl rfl

variable (HA : (a ≫ a').hom.Homotopy (𝟙 A : A ⟶ A).hom) (mc : MappingCylinder f)

local notation "Ω" => compositeSquare a b φ a' b' EA HB

/-- No compatible inverse homotopies supplied: the residual loop is constructed. -/
def inverseCompatibility :
    (generalized mc (a ≫ a') (b ≫ b') Ω mc).hom.Homotopy
      (generalized mc (𝟙 A) (𝟙 B) (residualLoop HA HB Ω) mc).hom :=
  deformation HA HB Ω mc

lemma inverseCompatibility_base (v : I) (y : B) :
    inverseCompatibility a b φ a' b' EA HB HA mc (v,mc.base y) =
      mc.base (HB (v,y)) :=
  deformation_base HA HB Ω mc v y

lemma inverseCompatibility_free (v : I) (x : A) :
    inverseCompatibility a b φ a' b' EA HB HA mc (v,mc.free x) =
      mc.free (HA (v,x)) :=
  deformation_free HA HB Ω mc v x

end ArbitraryInverses
end AutomaticCoherence.MappingCylinderInverseCompatibility01
