import MappingCylinderFoundation

/-! SOURCE ONLY / UNCOMPILED.
The split double cylinder is an actual pushout of the two free ends.
Joint homotopies glue only after an explicit all-time common-A equation.
No inverse, invariance theorem, or product-colimit preservation is assumed. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology

namespace AutomaticCoherence.SplitDoubleCylinderFoundation01
open MappingCylinderFoundation01

structure SplitDoubleCylinder {A B C : TopCat.{0}} (i : A ⟶ B) (j : A ⟶ C) where
  leftCylinder : MappingCylinder i
  rightCylinder : MappingCylinder j
  S : TopCat.{0}
  left : leftCylinder.M ⟶ S
  right : rightCylinder.M ⟶ S
  square : IsPushout leftCylinder.free rightCylinder.free left right

namespace SplitDoubleCylinder

variable {A B C : TopCat.{0}} {i : A ⟶ B} {j : A ⟶ C}
  (dc : SplitDoubleCylinder i j)

abbrev baseLeft : B ⟶ dc.S := dc.leftCylinder.base ≫ dc.left
abbrev baseRight : C ⟶ dc.S := dc.rightCylinder.base ≫ dc.right
abbrev common : A ⟶ dc.S := dc.leftCylinder.free ≫ dc.left

lemma common_right (a : A) : dc.common a = dc.right (dc.rightCylinder.free a) :=
  ConcreteCategory.congr_hom dc.square.w a

variable {T : TopCat.{0}} (fL : dc.leftCylinder.M ⟶ T)
  (fR : dc.rightCylinder.M ⟶ T)
  (agree : ∀ a, fL (dc.leftCylinder.free a) = fR (dc.rightCylinder.free a))

def desc : dc.S ⟶ T :=
  dc.square.desc fL fR (ConcreteCategory.hom_ext _ _ agree)

lemma desc_left (x : dc.leftCylinder.M) :
    dc.desc fL fR agree (dc.left x) = fL x :=
  ConcreteCategory.congr_hom (dc.square.inl_desc _ _ _) x

lemma desc_right (x : dc.rightCylinder.M) :
    dc.desc fL fR agree (dc.right x) = fR x :=
  ConcreteCategory.congr_hom (dc.square.inr_desc _ _ _) x

lemma desc_common (a : A) :
    dc.desc fL fR agree (dc.common a) = fL (dc.leftCylinder.free a) :=
  dc.desc_left fL fR agree (dc.leftCylinder.free a)

lemma hom_ext {u v : dc.S ⟶ T}
    (hl : ∀ x, u (dc.left x) = v (dc.left x))
    (hr : ∀ x, u (dc.right x) = v (dc.right x)) : u = v := by
  apply dc.square.hom_ext
  · exact ConcreteCategory.hom_ext _ _ hl
  · exact ConcreteCategory.hom_ext _ _ hr

variable (HL : C(I × dc.leftCylinder.M,T))
  (HR : C(I × dc.rightCylinder.M,T))
  (matchTime : ∀ t a,
    HL (t,dc.leftCylinder.free a) = HR (t,dc.rightCylinder.free a))

def timeDesc : C(I × dc.S,T) :=
  IntervalSkeletalDescent01.cylinder dc.square HL HR matchTime

lemma timeDesc_left (t : I) (x : dc.leftCylinder.M) :
    dc.timeDesc HL HR matchTime (t,dc.left x) = HL (t,x) :=
  IntervalSkeletalDescent01.cylinder_left dc.square HL HR matchTime t x

lemma timeDesc_right (t : I) (x : dc.rightCylinder.M) :
    dc.timeDesc HL HR matchTime (t,dc.right x) = HR (t,x) :=
  IntervalSkeletalDescent01.cylinder_right dc.square HL HR matchTime t x

lemma timeDesc_common (t : I) (a : A) :
    dc.timeDesc HL HR matchTime (t,dc.common a) = HL (t,dc.leftCylinder.free a) :=
  dc.timeDesc_left HL HR matchTime t (dc.leftCylinder.free a)

/-- Both local homotopies are joint and must agree for every time on the free A. -/
def homotopy (u v : C(dc.S,T))
    (HL : (u.comp dc.left.hom).Homotopy (v.comp dc.left.hom))
    (HR : (u.comp dc.right.hom).Homotopy (v.comp dc.right.hom))
    (agree : ∀ t a, HL (t,dc.leftCylinder.free a) = HR (t,dc.rightCylinder.free a)) :
    u.Homotopy v :=
  IntervalSkeletalDescent01.homotopy dc.square u v HL HR agree

/-- An explicit identical common-A schedule discharges, rather than replaces,
the gluing compatibility. Its actual construction remains the caller's task. -/
def homotopyOfCommon (u v : C(dc.S,T))
    (HL : (u.comp dc.left.hom).Homotopy (v.comp dc.left.hom))
    (HR : (u.comp dc.right.hom).Homotopy (v.comp dc.right.hom))
    (κ : C(I × A,T))
    (hL : ∀ t a, HL (t,dc.leftCylinder.free a) = κ (t,a))
    (hR : ∀ t a, HR (t,dc.rightCylinder.free a) = κ (t,a)) : u.Homotopy v :=
  dc.homotopy u v HL HR (fun t a => (hL t a).trans (hR t a).symm)

end SplitDoubleCylinder

variable {A B C : TopCat.{0}} (i : A ⟶ B) (j : A ⟶ C)

def canonicalSplitDoubleCylinder : SplitDoubleCylinder i j :=
  let lc := canonicalMappingCylinder i
  let rc := canonicalMappingCylinder j
  { leftCylinder := lc
    rightCylinder := rc
    S := pushout lc.free rc.free
    left := pushout.inl lc.free rc.free
    right := pushout.inr lc.free rc.free
    square := IsPushout.of_hasPushout lc.free rc.free }

variable {i j} {A' B' C' : TopCat.{0}} {i' : A' ⟶ B'} {j' : A' ⟶ C'}
  (dc : SplitDoubleCylinder i j) (dc' : SplitDoubleCylinder i' j')
  (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
  (φ : (α ≫ i').hom.Homotopy (i ≫ β).hom)
  (ψ : (α ≫ j').hom.Homotopy (j ≫ γ).hom)

def leftGeneralized : dc.leftCylinder.M ⟶ dc'.S :=
  generalized dc'.leftCylinder α β φ dc.leftCylinder ≫ dc'.left

def rightGeneralized : dc.rightCylinder.M ⟶ dc'.S :=
  generalized dc'.rightCylinder α γ ψ dc.rightCylinder ≫ dc'.right

lemma generalized_agrees (a : A) :
    leftGeneralized dc dc' α β φ (dc.leftCylinder.free a) =
      rightGeneralized dc dc' α γ ψ (dc.rightCylinder.free a) := by
  change dc'.left (generalized dc'.leftCylinder α β φ dc.leftCylinder
      (dc.leftCylinder.free a)) =
    dc'.right (generalized dc'.rightCylinder α γ ψ dc.rightCylinder
      (dc.rightCylinder.free a))
  rw [generalized_free, generalized_free]
  exact ConcreteCategory.congr_hom dc'.square.w (α a)

/-- No inverse assumptions: the actual map determined by two comparison paths. -/
def generalizedMap : dc.S ⟶ dc'.S :=
  dc.desc (leftGeneralized dc dc' α β φ) (rightGeneralized dc dc' α γ ψ)
    (generalized_agrees dc dc' α β γ φ ψ)

lemma generalizedMap_left (x : dc.leftCylinder.M) :
    generalizedMap dc dc' α β γ φ ψ (dc.left x) =
      dc'.left (generalized dc'.leftCylinder α β φ dc.leftCylinder x) :=
  dc.desc_left _ _ _ x

lemma generalizedMap_right (x : dc.rightCylinder.M) :
    generalizedMap dc dc' α β γ φ ψ (dc.right x) =
      dc'.right (generalized dc'.rightCylinder α γ ψ dc.rightCylinder x) :=
  dc.desc_right _ _ _ x

lemma generalizedMap_common (a : A) :
    generalizedMap dc dc' α β γ φ ψ (dc.common a) = dc'.common (α a) :=
  (generalizedMap_left dc dc' α β γ φ ψ (dc.leftCylinder.free a)).trans
    (congrArg dc'.left (generalized_free dc'.leftCylinder α β φ dc.leftCylinder a))

lemma generalizedMap_baseLeft (b : B) :
    generalizedMap dc dc' α β γ φ ψ (dc.baseLeft b) = dc'.baseLeft (β b) :=
  (generalizedMap_left dc dc' α β γ φ ψ (dc.leftCylinder.base b)).trans
    (congrArg dc'.left (generalized_base dc'.leftCylinder α β φ dc.leftCylinder b))

lemma generalizedMap_baseRight (c : C) :
    generalizedMap dc dc' α β γ φ ψ (dc.baseRight c) = dc'.baseRight (γ c) :=
  (generalizedMap_right dc dc' α β γ φ ψ (dc.rightCylinder.base c)).trans
    (congrArg dc'.right (generalized_base dc'.rightCylinder α γ ψ dc.rightCylinder c))

end AutomaticCoherence.SplitDoubleCylinderFoundation01
