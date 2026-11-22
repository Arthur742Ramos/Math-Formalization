import MappingCylinderVariation
import MappingCylinderComposition
import MappingCylinderCollar
import LoopCancellation

/-! SOURCE ONLY / UNCOMPILED.
The two final normalization steps before literal collar removal:
composition of opposite loop maps, then the parametric loop cancellation
lifted through the actual generalized-cylinder family. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology

namespace AutomaticCoherence.MappingCylinderLoopLift01
open MappingCylinderFoundation01
open MappingCylinderComposition01
open MappingCylinderCollar01 (collaredIdentity constantSquare)

variable {A B : TopCat.{0}} {f : A ⟶ B}
  (mc : MappingCylinder f) (H : f.hom.Homotopy f.hom)

lemma identity_square :
    (whiskerLeft (𝟙 A) H.symm).trans (whiskerRight (𝟙 B) H) = H.symm.trans H := by
  apply ContinuousMap.Homotopy.ext
  intro p
  rfl

def oppositeLoopComposition :
    (generalized mc (𝟙 A) (𝟙 B) H mc ≫
      generalized mc (𝟙 A) (𝟙 B) H.symm mc).hom.Homotopy
    (generalized mc (𝟙 A) (𝟙 B) (H.symm.trans H) mc).hom :=
  (compositionHomotopy mc mc mc (𝟙 A) (𝟙 B) H (𝟙 A) (𝟙 B) H.symm).cast rfl
    (congrArg (fun K : f.hom.Homotopy f.hom =>
      (generalized mc (𝟙 A) (𝟙 B) K mc).hom) (identity_square H))

lemma oppositeLoopComposition_base (v : I) (y : B) :
    oppositeLoopComposition mc H (v,mc.base y) = mc.base y :=
  comparisonFamily_base mc mc (𝟙 A) (𝟙 B) H (𝟙 A) (𝟙 B) H.symm v y

lemma oppositeLoopComposition_free (v : I) (x : A) :
    oppositeLoopComposition mc H (v,mc.free x) = mc.free x :=
  comparisonFamily_free mc mc (𝟙 A) (𝟙 B) H (𝟙 A) (𝟙 B) H.symm v x

def cancellationSquare : C((I × I) × A,B) :=
  (LoopCancellation01.cancellationFamily H).comp
    ⟨fun p => (p.1.1,(p.1.2,p.2)), by fun_prop⟩

lemma cancellationSquare_left (v : I) (x : A) :
    cancellationSquare H ((v,0),x) = f x :=
  LoopCancellation01.cancellationFamily_left H v x

lemma cancellationSquare_right (v : I) (x : A) :
    cancellationSquare H ((v,1),x) = f x :=
  LoopCancellation01.cancellationFamily_right H v x

def cancellationFamily : C(I × mc.M,mc.M) :=
  MappingCylinderVariation01.family mc mc ContinuousMap.snd ContinuousMap.snd
    (cancellationSquare H) (cancellationSquare_left H) (cancellationSquare_right H)

lemma cancellationFamily_base (v : I) (y : B) :
    cancellationFamily mc H (v,mc.base y) = mc.base y :=
  MappingCylinderVariation01.family_base _ _ _ _ _ _ _ v y

lemma cancellationFamily_free (v : I) (x : A) :
    cancellationFamily mc H (v,mc.free x) = mc.free x :=
  MappingCylinderVariation01.family_free _ _ _ _ _ _ _ v x

/-- The target is precisely the collared identity used by collarRemoval. -/
def cancel :
    (generalized mc (𝟙 A) (𝟙 B) (H.symm.trans H) mc).hom.Homotopy
      (collaredIdentity mc).hom where
  toContinuousMap := cancellationFamily mc H
  map_zero_left z := ConcreteCategory.congr_hom
    (MappingCylinderVariation01.family_at mc mc ContinuousMap.snd ContinuousMap.snd
      (cancellationSquare H) (cancellationSquare_left H) (cancellationSquare_right H)
      0 (𝟙 A) (𝟙 B) (H.symm.trans H) (fun _ => rfl) (fun _ => rfl)
      (fun s x => LoopCancellation01.cancellationFamily_zero H s x)) z
  map_one_left z := ConcreteCategory.congr_hom
    (MappingCylinderVariation01.family_at mc mc ContinuousMap.snd ContinuousMap.snd
      (cancellationSquare H) (cancellationSquare_left H) (cancellationSquare_right H)
      1 (𝟙 A) (𝟙 B) (constantSquare f) (fun _ => rfl) (fun _ => rfl)
      (fun s x => LoopCancellation01.cancellationFamily_one H s x)) z

lemma cancel_base (v : I) (y : B) :
    cancel mc H (v,mc.base y) = mc.base y := cancellationFamily_base mc H v y

lemma cancel_free (v : I) (x : A) :
    cancel mc H (v,mc.free x) = mc.free x := cancellationFamily_free mc H v x

end AutomaticCoherence.MappingCylinderLoopLift01
