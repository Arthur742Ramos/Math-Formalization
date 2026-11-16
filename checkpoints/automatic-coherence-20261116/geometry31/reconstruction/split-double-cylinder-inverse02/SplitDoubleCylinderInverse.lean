import SplitDoubleCylinderFoundation
import MappingCylinderLeftInverse
import Mathlib.Topology.Homotopy.Equiv

/-! SOURCE ONLY / UNCOMPILED.
Assemble two independently corrected single-cylinder inverses. The common-A
restriction is derived from one shared inverse homotopy and one fixed scalar
schedule. No matching homotopies or double-cylinder equivalence is assumed. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology
namespace AutomaticCoherence.SplitDoubleCylinderInverse01
open MappingCylinderFoundation01
open SplitDoubleCylinderFoundation01

/-- Inverse data for the three vertical maps, with arbitrary inverse homotopies. -/
structure SpanInverseData {A B C A' B' C' : TopCat.{0}}
    (i : A ⟶ B) (j : A ⟶ C) (i' : A' ⟶ B') (j' : A' ⟶ C') where
  a : A ⟶ A'
  b : B ⟶ B'
  c : C ⟶ C'
  a' : A' ⟶ A
  b' : B' ⟶ B
  c' : C' ⟶ C
  squareLeft : (a ≫ i').hom.Homotopy (i ≫ b).hom
  squareRight : (a ≫ j').hom.Homotopy (j ≫ c).hom
  leftA : (a ≫ a').hom.Homotopy (𝟙 A : A ⟶ A).hom
  rightA : (a' ≫ a).hom.Homotopy (𝟙 A' : A' ⟶ A').hom
  leftB : (b ≫ b').hom.Homotopy (𝟙 B : B ⟶ B).hom
  rightB : (b' ≫ b).hom.Homotopy (𝟙 B' : B' ⟶ B').hom
  leftC : (c ≫ c').hom.Homotopy (𝟙 C : C ⟶ C).hom
  rightC : (c' ≫ c).hom.Homotopy (𝟙 C' : C' ⟶ C').hom

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}
  (d : SpanInverseData i j i' j')

def leftData : MappingCylinderLeftInverse01.InverseData i i' where
  a := d.a
  b := d.b
  a' := d.a'
  b' := d.b'
  square := d.squareLeft
  leftA := d.leftA
  rightA := d.rightA
  leftB := d.leftB

def rightData : MappingCylinderLeftInverse01.InverseData j j' where
  a := d.a
  b := d.c
  a' := d.a'
  b' := d.c'
  square := d.squareRight
  leftA := d.leftA
  rightA := d.rightA
  leftB := d.leftC

variable (dc : SplitDoubleCylinder i j) (dc' : SplitDoubleCylinder i' j')

def forward : dc.S ⟶ dc'.S :=
  generalizedMap dc dc' d.a d.b d.c d.squareLeft d.squareRight

def backward : dc'.S ⟶ dc.S :=
  generalizedMap dc' dc d.a' d.b' d.c'
    (MappingCylinderLeftInverse01.correctedSquare (leftData d))
    (MappingCylinderLeftInverse01.correctedSquare (rightData d))

lemma forward_left (x : dc.leftCylinder.M) :
    forward d dc dc' (dc.left x) =
      dc'.left (MappingCylinderLeftInverse01.forward (leftData d)
        dc.leftCylinder dc'.leftCylinder x) :=
  generalizedMap_left dc dc' d.a d.b d.c d.squareLeft d.squareRight x

lemma forward_right (x : dc.rightCylinder.M) :
    forward d dc dc' (dc.right x) =
      dc'.right (MappingCylinderLeftInverse01.forward (rightData d)
        dc.rightCylinder dc'.rightCylinder x) :=
  generalizedMap_right dc dc' d.a d.b d.c d.squareLeft d.squareRight x

lemma backward_left (x : dc'.leftCylinder.M) :
    backward d dc dc' (dc'.left x) =
      dc.left (MappingCylinderLeftInverse01.corrected (leftData d)
        dc.leftCylinder dc'.leftCylinder x) :=
  generalizedMap_left dc' dc d.a' d.b' d.c' _ _ x

lemma backward_right (x : dc'.rightCylinder.M) :
    backward d dc dc' (dc'.right x) =
      dc.right (MappingCylinderLeftInverse01.corrected (rightData d)
        dc.rightCylinder dc'.rightCylinder x) :=
  generalizedMap_right dc' dc d.a' d.b' d.c' _ _ x

/-- Postcompose the actual local homotopy; endpoint equalities use the actual descents. -/
def localLeft :
    ((forward d dc dc' ≫ backward d dc dc').hom.comp dc.left.hom).Homotopy
      dc.left.hom where
  toContinuousMap := dc.left.hom.comp
    (MappingCylinderLeftInverse01.leftInverse (leftData d)
      dc.leftCylinder dc'.leftCylinder).toContinuousMap
  map_zero_left x := by
    change dc.left (MappingCylinderLeftInverse01.leftInverse (leftData d)
      dc.leftCylinder dc'.leftCylinder (0,x)) =
        backward d dc dc' (forward d dc dc' (dc.left x))
    rw [forward_left, backward_left]
    exact congrArg dc.left (MappingCylinderLeftInverse01.leftInverse (leftData d)
      dc.leftCylinder dc'.leftCylinder |>.map_zero_left x)
  map_one_left x := congrArg dc.left
    (MappingCylinderLeftInverse01.leftInverse (leftData d)
      dc.leftCylinder dc'.leftCylinder |>.map_one_left x)

def localRight :
    ((forward d dc dc' ≫ backward d dc dc').hom.comp dc.right.hom).Homotopy
      dc.right.hom where
  toContinuousMap := dc.right.hom.comp
    (MappingCylinderLeftInverse01.leftInverse (rightData d)
      dc.rightCylinder dc'.rightCylinder).toContinuousMap
  map_zero_left x := by
    change dc.right (MappingCylinderLeftInverse01.leftInverse (rightData d)
      dc.rightCylinder dc'.rightCylinder (0,x)) =
        backward d dc dc' (forward d dc dc' (dc.right x))
    rw [forward_right, backward_right]
    exact congrArg dc.right (MappingCylinderLeftInverse01.leftInverse (rightData d)
      dc.rightCylinder dc'.rightCylinder |>.map_zero_left x)
  map_one_left x := congrArg dc.right
    (MappingCylinderLeftInverse01.leftInverse (rightData d)
      dc.rightCylinder dc'.rightCylinder |>.map_one_left x)

lemma localLeft_common (t : I) (x : A) :
    localLeft d dc dc' (t,dc.leftCylinder.free x) =
      dc.common (d.leftA (SixStageSchedule01.schedule t,x)) :=
  congrArg dc.left (MappingCylinderLeftInverse01.leftInverse_free (leftData d)
    dc.leftCylinder dc'.leftCylinder t x)

lemma localRight_common (t : I) (x : A) :
    localRight d dc dc' (t,dc.rightCylinder.free x) =
      dc.common (d.leftA (SixStageSchedule01.schedule t,x)) :=
  (congrArg dc.right (MappingCylinderLeftInverse01.leftInverse_free (rightData d)
    dc.rightCylinder dc'.rightCylinder t x)).trans
      (dc.common_right (d.leftA (SixStageSchedule01.schedule t,x))).symm

/-- Literal agreement for every time, not just at endpoints, is now a theorem. -/
lemma local_agreement (t : I) (x : A) :
    localLeft d dc dc' (t,dc.leftCylinder.free x) =
      localRight d dc dc' (t,dc.rightCylinder.free x) :=
  (localLeft_common d dc dc' t x).trans (localRight_common d dc dc' t x).symm

def leftInverse :
    (forward d dc dc' ≫ backward d dc dc').hom.Homotopy (ContinuousMap.id dc.S) :=
  dc.homotopy _ _ (localLeft d dc dc') (localRight d dc dc')
    (local_agreement d dc dc')

/-- Swap the genuine inverse data, using the corrected squares, not an assumed
right-inverse homotopy for the newly constructed backward map. -/
def reverseData : SpanInverseData i' j' i j where
  a := d.a'
  b := d.b'
  c := d.c'
  a' := d.a
  b' := d.b
  c' := d.c
  squareLeft := MappingCylinderLeftInverse01.correctedSquare (leftData d)
  squareRight := MappingCylinderLeftInverse01.correctedSquare (rightData d)
  leftA := d.rightA
  rightA := d.leftA
  leftB := d.rightB
  rightB := d.leftB
  leftC := d.rightC
  rightC := d.leftC

lemma reverseData_forward : forward (reverseData d) dc' dc = backward d dc dc' := rfl

/-- Two left-inverse constructions suffice algebraically; V need not equal G. -/
def twiceLeftInverse {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (G : C(X,Y)) (W : C(Y,X)) (V : C(X,Y))
    (L : (W.comp G).Homotopic (ContinuousMap.id X))
    (K : (V.comp W).Homotopic (ContinuousMap.id Y)) : X ≃ₕ Y where
  toFun := G
  invFun := W
  left_inv := L
  right_inv := by
    have h₀ : (G.comp W).Homotopic ((V.comp W).comp (G.comp W)) :=
      Homotopic.comp K.symm (Homotopic.refl (G.comp W))
    have h₁ : ((V.comp W).comp (G.comp W)).Homotopic (V.comp W) :=
      Homotopic.comp (Homotopic.refl V) (Homotopic.comp L (Homotopic.refl W))
    exact h₀.trans (h₁.trans K)

/-- Homotopy equivalence with the exact generalized forward map, not a replacement. -/
def equivalence : dc.S ≃ₕ dc'.S :=
  twiceLeftInverse (forward d dc dc').hom (backward d dc dc').hom
    (backward (reverseData d) dc' dc).hom
    ⟨leftInverse d dc dc'⟩ ⟨leftInverse (reverseData d) dc' dc⟩

lemma equivalence_toFun : (equivalence d dc dc').toFun = (forward d dc dc').hom := rfl

end AutomaticCoherence.SplitDoubleCylinderInverse01
