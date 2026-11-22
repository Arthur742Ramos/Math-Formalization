import SixStageSchedule
import MappingCylinderInverseCompatibility
import MappingCylinderLoopLift

/-! SOURCE ONLY / UNCOMPILED.
A corrected single-cylinder left inverse, with a literal common endpoint
schedule. All inverse homotopies are arbitrary. No right-inverse, double
pushout gluing or strict-span transport theorem is asserted here. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology

namespace AutomaticCoherence.MappingCylinderLeftInverse01
open MappingCylinderFoundation01
open MappingCylinderComposition01
open MappingCylinderInverseCompatibility01
open MappingCylinderLoopLift01
open MappingCylinderCollar01 (collaredIdentity collarRemoval)

/-- Only inverse data, not compatible homotopies. A right inverse homotopy for b
is unnecessary for the single-cylinder left inverse. -/
structure InverseData {A B A' B' : TopCat.{0}} (f : A ⟶ B) (f' : A' ⟶ B') where
  a : A ⟶ A'
  b : B ⟶ B'
  a' : A' ⟶ A
  b' : B' ⟶ B
  square : (a ≫ f').hom.Homotopy (f ≫ b).hom
  leftA : (a ≫ a').hom.Homotopy (𝟙 A : A ⟶ A).hom
  rightA : (a' ≫ a).hom.Homotopy (𝟙 A' : A' ⟶ A').hom
  leftB : (b ≫ b').hom.Homotopy (𝟙 B : B ⟶ B).hom

variable {A B A' B' : TopCat.{0}} {f : A ⟶ B} {f' : A' ⟶ B'}
  (d : InverseData f f') (mc : MappingCylinder f) (mc' : MappingCylinder f')

local notation "ψ" => reverseSquare d.a d.b d.square d.a' d.b' d.rightA d.leftB
local notation "Ω" => compositeSquare d.a d.b d.square d.a' d.b' d.rightA d.leftB
local notation "ℓ" => residualLoop d.leftA d.leftB Ω

def forward : mc.M ⟶ mc'.M :=
  generalized mc' d.a d.b d.square mc

def reverse : mc'.M ⟶ mc.M :=
  generalized mc d.a' d.b' ψ mc'

def correction : mc.M ⟶ mc.M :=
  generalized mc (𝟙 A) (𝟙 B) (ℓ).symm mc

/-- The actual normalized square for reverse followed by the loop correction. -/
def correctedSquare : (d.a' ≫ f).hom.Homotopy (f' ≫ d.b').hom :=
  ((whiskerLeft d.a' (ℓ).symm).trans (whiskerRight (𝟙 B) ψ)).cast rfl rfl

def corrected : mc'.M ⟶ mc.M :=
  generalized mc d.a' d.b' (correctedSquare d) mc'

lemma corrected_base (y : B') : corrected d mc mc' (mc'.base y) = mc.base (d.b' y) :=
  generalized_base mc d.a' d.b' (correctedSquare d) mc' y

lemma corrected_free (x : A') : corrected d mc mc' (mc'.free x) = mc.free (d.a' x) :=
  generalized_free mc d.a' d.b' (correctedSquare d) mc' x

def compositeNormal : mc.M ⟶ mc.M :=
  generalized mc (d.a ≫ d.a') (d.b ≫ d.b') Ω mc

def loopMap : mc.M ⟶ mc.M :=
  generalized mc (𝟙 A) (𝟙 B) ℓ mc

def cancellingMap : mc.M ⟶ mc.M :=
  generalized mc (𝟙 A) (𝟙 B) ((ℓ).symm.trans ℓ) mc

/-- WG → CSG, reversing composition normalization for S then C. -/
def stage1 :
    (forward d mc mc' ≫ corrected d mc mc').hom.Homotopy
      (forward d mc mc' ≫ reverse d mc mc' ≫ correction d mc).hom :=
  (whiskerLeft (forward d mc mc')
    (compositionHomotopy mc' mc mc d.a' d.b' ψ
      (𝟙 A) (𝟙 B) (ℓ).symm).symm).cast rfl rfl

/-- CSG → C G(a'a,b'b,Ω). -/
def stage2 :
    (forward d mc mc' ≫ reverse d mc mc' ≫ correction d mc).hom.Homotopy
      (compositeNormal d mc ≫ correction d mc).hom :=
  (whiskerRight (correction d mc)
    (compositionHomotopy mc mc' mc d.a d.b d.square d.a' d.b' ψ)).cast rfl rfl

/-- The only stage moving the outer restrictions, along the given HA and HB. -/
def stage3 :
    (compositeNormal d mc ≫ correction d mc).hom.Homotopy
      (loopMap d mc ≫ correction d mc).hom :=
  (whiskerRight (correction d mc) (deformation d.leftA d.leftB Ω mc)).cast rfl rfl

def stage4 :
    (loopMap d mc ≫ correction d mc).hom.Homotopy (cancellingMap d mc).hom :=
  oppositeLoopComposition mc ℓ

def stage5 :
    (cancellingMap d mc).hom.Homotopy (collaredIdentity mc).hom :=
  cancel mc ℓ

def stage6 :
    (collaredIdentity mc).hom.Homotopy (ContinuousMap.id mc.M) :=
  collarRemoval mc

lemma stage1_base (v : I) (y : B) :
    stage1 d mc mc' (v,mc.base y) = mc.base (d.b' (d.b y)) := by
  change MappingCylinderComposition01.comparisonFamily mc' mc d.a' d.b' ψ
    (𝟙 A) (𝟙 B) (ℓ).symm
    (unitInterval.symm v,generalized mc' d.a d.b d.square mc (mc.base y)) = _
  rw [generalized_base]
  exact MappingCylinderComposition01.comparisonFamily_base mc' mc d.a' d.b' ψ
    (𝟙 A) (𝟙 B) (ℓ).symm (unitInterval.symm v) (d.b y)

lemma stage1_free (v : I) (x : A) :
    stage1 d mc mc' (v,mc.free x) = mc.free (d.a' (d.a x)) := by
  change MappingCylinderComposition01.comparisonFamily mc' mc d.a' d.b' ψ
    (𝟙 A) (𝟙 B) (ℓ).symm
    (unitInterval.symm v,generalized mc' d.a d.b d.square mc (mc.free x)) = _
  rw [generalized_free]
  exact MappingCylinderComposition01.comparisonFamily_free mc' mc d.a' d.b' ψ
    (𝟙 A) (𝟙 B) (ℓ).symm (unitInterval.symm v) (d.a x)

lemma stage2_base (v : I) (y : B) :
    stage2 d mc mc' (v,mc.base y) = mc.base (d.b' (d.b y)) := by
  change generalized mc (𝟙 A) (𝟙 B) (ℓ).symm mc
    (MappingCylinderComposition01.comparisonFamily mc mc d.a d.b d.square d.a' d.b' ψ
      (v,mc.base y)) = _
  rw [MappingCylinderComposition01.comparisonFamily_base]
  exact generalized_base mc (𝟙 A) (𝟙 B) (ℓ).symm mc (d.b' (d.b y))

lemma stage2_free (v : I) (x : A) :
    stage2 d mc mc' (v,mc.free x) = mc.free (d.a' (d.a x)) := by
  change generalized mc (𝟙 A) (𝟙 B) (ℓ).symm mc
    (MappingCylinderComposition01.comparisonFamily mc mc d.a d.b d.square d.a' d.b' ψ
      (v,mc.free x)) = _
  rw [MappingCylinderComposition01.comparisonFamily_free]
  exact generalized_free mc (𝟙 A) (𝟙 B) (ℓ).symm mc (d.a' (d.a x))

lemma stage3_base (v : I) (y : B) :
    stage3 d mc (v,mc.base y) = mc.base (d.leftB (v,y)) := by
  change generalized mc (𝟙 A) (𝟙 B) (ℓ).symm mc
    (deformation d.leftA d.leftB Ω mc (v,mc.base y)) = _
  rw [deformation_base]
  exact generalized_base mc (𝟙 A) (𝟙 B) (ℓ).symm mc (d.leftB (v,y))

lemma stage3_free (v : I) (x : A) :
    stage3 d mc (v,mc.free x) = mc.free (d.leftA (v,x)) := by
  change generalized mc (𝟙 A) (𝟙 B) (ℓ).symm mc
    (deformation d.leftA d.leftB Ω mc (v,mc.free x)) = _
  rw [deformation_free]
  exact generalized_free mc (𝟙 A) (𝟙 B) (ℓ).symm mc (d.leftA (v,x))

lemma stage4_base (v : I) (y : B) :
    stage4 d mc (v,mc.base y) = mc.base y := oppositeLoopComposition_base mc ℓ v y

lemma stage4_free (v : I) (x : A) :
    stage4 d mc (v,mc.free x) = mc.free x := oppositeLoopComposition_free mc ℓ v x

lemma stage5_base (v : I) (y : B) :
    stage5 d mc (v,mc.base y) = mc.base y := cancel_base mc ℓ v y

lemma stage5_free (v : I) (x : A) :
    stage5 d mc (v,mc.free x) = mc.free x := cancel_free mc ℓ v x

lemma stage6_base (v : I) (y : B) :
    stage6 mc (v,mc.base y) = mc.base y := MappingCylinderCollar01.family_base mc v y

lemma stage6_free (v : I) (x : A) :
    stage6 mc (v,mc.free x) = mc.free x := MappingCylinderCollar01.family_free mc v x

/-- A complete left-inverse homotopy, with the same tree as the closed scalar clock. -/
def leftInverse :
    (forward d mc mc' ≫ corrected d mc mc').hom.Homotopy (ContinuousMap.id mc.M) :=
  SixStageSchedule01.concatenate (stage1 d mc mc') (stage2 d mc mc')
    (stage3 d mc) (stage4 d mc) (stage5 d mc) (stage6 mc)

/-- Literal common-A restriction, derived from all six stages.
The schedule has no dependence on f, B, φ, inverse choices or the residual loop. -/
lemma leftInverse_free (t : I) (x : A) :
    leftInverse d mc mc' (t,mc.free x) =
      mc.free (d.leftA (SixStageSchedule01.schedule t,x)) := by
  apply SixStageSchedule01.concatenate_restriction
    (stage1 d mc mc') (stage2 d mc mc')
    (stage3 d mc) (stage4 d mc) (stage5 d mc) (stage6 mc)
    (mc.free x) (fun v => mc.free (d.leftA (v,x)))
  · intro v
    exact (stage1_free d mc mc' v x).trans
      (congrArg mc.free (d.leftA.map_zero_left x)).symm
  · intro v
    exact (stage2_free d mc mc' v x).trans
      (congrArg mc.free (d.leftA.map_zero_left x)).symm
  · intro v
    exact stage3_free d mc v x
  · intro v
    exact (stage4_free d mc v x).trans
      (congrArg mc.free (d.leftA.map_one_left x)).symm
  · intro v
    exact (stage5_free d mc v x).trans
      (congrArg mc.free (d.leftA.map_one_left x)).symm
  · intro v
    exact (stage6_free mc v x).trans
      (congrArg mc.free (d.leftA.map_one_left x)).symm

lemma leftInverse_base (t : I) (y : B) :
    leftInverse d mc mc' (t,mc.base y) =
      mc.base (d.leftB (SixStageSchedule01.schedule t,y)) := by
  apply SixStageSchedule01.concatenate_restriction
    (stage1 d mc mc') (stage2 d mc mc')
    (stage3 d mc) (stage4 d mc) (stage5 d mc) (stage6 mc)
    (mc.base y) (fun v => mc.base (d.leftB (v,y)))
  · intro v
    exact (stage1_base d mc mc' v y).trans
      (congrArg mc.base (d.leftB.map_zero_left y)).symm
  · intro v
    exact (stage2_base d mc mc' v y).trans
      (congrArg mc.base (d.leftB.map_zero_left y)).symm
  · intro v
    exact stage3_base d mc v y
  · intro v
    exact (stage4_base d mc v y).trans
      (congrArg mc.base (d.leftB.map_one_left y)).symm
  · intro v
    exact (stage5_base d mc v y).trans
      (congrArg mc.base (d.leftB.map_one_left y)).symm
  · intro v
    exact (stage6_base mc v y).trans
      (congrArg mc.base (d.leftB.map_one_left y)).symm

end AutomaticCoherence.MappingCylinderLeftInverse01
