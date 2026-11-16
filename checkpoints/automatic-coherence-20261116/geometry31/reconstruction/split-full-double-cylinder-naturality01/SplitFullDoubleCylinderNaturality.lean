import SplitFullDoubleCylinder
import SplitDoubleCylinderStrictMap

/-! SOURCE ONLY / UNCOMPILED.
Literal strict-span naturality of the actual split/full homeomorphism.
This uses the exact existing SpanMap, split strictMap and full doubleMap.
No naturality, inverse compatibility or equivalence premise is supplied. -/
noncomputable section
open CategoryTheory
open scoped Topology

namespace AutomaticCoherence.SplitFullDoubleCylinderNaturality01
open SplitDoubleCylinderFoundation01 (SplitDoubleCylinder)
open DoubleCylinderCollapse01 (DoubleCylinder)
open DoubleCylinderComparison01 (SpanMap doubleMap doubleMap_left doubleMap_interval doubleMap_right)
open SplitDoubleCylinderStrictMap01
open SplitFullDoubleCylinder01

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}
  (f : SpanMap i j i' j')
  (sd : SplitDoubleCylinder i j) (sd' : SplitDoubleCylinder i' j')
  (fd : DoubleCylinder i j) (fd' : DoubleCylinder i' j')

/-- Both full interval coordinates are preserved literally by strict comparison. -/
lemma toFull_naturality :
    strictMap f sd sd' ≫ toFull sd' fd' = toFull sd fd ≫ doubleMap f fd fd' := by
  have hL : sd.left ≫ strictMap f sd sd' ≫ toFull sd' fd' =
      sd.left ≫ toFull sd fd ≫ doubleMap f fd fd' := by
    apply sd.leftCylinder.hom_ext
    · intro b
      change toFull sd' fd' (strictMap f sd sd' (sd.baseLeft b)) =
        doubleMap f fd fd' (toFull sd fd (sd.baseLeft b))
      rw [strictMap_baseLeft, toFull_leftBase, toFull_leftBase, doubleMap_left]
    · rintro ⟨s,a⟩
      change toFull sd' fd' (strictMap f sd sd'
        (sd.left (sd.leftCylinder.interval (s,a)))) =
        doubleMap f fd fd' (toFull sd fd (sd.left (sd.leftCylinder.interval (s,a))))
      rw [strictMap_leftInterval, toFull_leftInterval, toFull_leftInterval,
        doubleMap_interval]
  have hR : sd.right ≫ strictMap f sd sd' ≫ toFull sd' fd' =
      sd.right ≫ toFull sd fd ≫ doubleMap f fd fd' := by
    apply sd.rightCylinder.hom_ext
    · intro c
      change toFull sd' fd' (strictMap f sd sd' (sd.baseRight c)) =
        doubleMap f fd fd' (toFull sd fd (sd.baseRight c))
      rw [strictMap_baseRight, toFull_rightBase, toFull_rightBase, doubleMap_right]
    · rintro ⟨s,a⟩
      change toFull sd' fd' (strictMap f sd sd'
        (sd.right (sd.rightCylinder.interval (s,a)))) =
        doubleMap f fd fd' (toFull sd fd (sd.right (sd.rightCylinder.interval (s,a))))
      rw [strictMap_rightInterval, toFull_rightInterval, toFull_rightInterval,
        doubleMap_interval]
  apply sd.hom_ext
  · intro x
    exact ConcreteCategory.congr_hom hL x
  · intro x
    exact ConcreteCategory.congr_hom hR x

/-- Inverse naturality follows from the proved forward square and actual inverse identities. -/
lemma toSplit_naturality :
    doubleMap f fd fd' ≫ toSplit sd' fd' = toSplit sd fd ≫ strictMap f sd sd' := by
  apply ConcreteCategory.hom_ext
  intro z
  have h := ConcreteCategory.congr_hom (toFull_naturality f sd sd' fd fd')
    (toSplit sd fd z)
  change toFull sd' fd' (strictMap f sd sd' (toSplit sd fd z)) =
    doubleMap f fd fd' (toFull sd fd (toSplit sd fd z)) at h
  have hs : toFull sd fd (toSplit sd fd z) = z :=
    ConcreteCategory.congr_hom (toSplit_toFull sd fd) z
  have ht : toSplit sd' fd' (toFull sd' fd'
      (strictMap f sd sd' (toSplit sd fd z))) =
      strictMap f sd sd' (toSplit sd fd z) :=
    ConcreteCategory.congr_hom (toFull_toSplit sd' fd')
      (strictMap f sd sd' (toSplit sd fd z))
  have h' := congrArg (fun y : fd'.D => toSplit sd' fd' y) h
  rw [hs] at h'
  exact h'.symm.trans ht

lemma homeomorph_naturality (z : sd.S) :
    homeomorph sd' fd' (strictMap f sd sd' z) =
      doubleMap f fd fd' (homeomorph sd fd z) :=
  ConcreteCategory.congr_hom (toFull_naturality f sd sd' fd fd') z

lemma homeomorph_symm_naturality (z : fd.D) :
    (homeomorph sd' fd').symm (doubleMap f fd fd' z) =
      strictMap f sd sd' ((homeomorph sd fd).symm z) :=
  ConcreteCategory.congr_hom (toSplit_naturality f sd sd' fd fd') z

end AutomaticCoherence.SplitFullDoubleCylinderNaturality01
