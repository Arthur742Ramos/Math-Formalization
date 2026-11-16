import IntervalSkeletalDescent
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Homotopy.Basic

/-! SOURCE ONLY / UNCOMPILED.
Actual one-ended mapping cylinders and generalized maps.
No inverse, compatible inverse homotopies, or invariance theorem is assumed. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology

namespace AutomaticCoherence.MappingCylinderFoundation01

abbrev I := unitInterval
abbrev cylinderSpace (A : TopCat.{0}) : TopCat.{0} := TopCat.of (I × A)

def endpoint (A : TopCat.{0}) (t : I) : A ⟶ cylinderSpace A :=
  TopCat.ofHom ⟨fun a => (t, a), continuous_const.prodMk continuous_id⟩

/-- The attached end is 1; the free end is 0. The square is an actual pushout. -/
structure MappingCylinder {A B : TopCat.{0}} (f : A ⟶ B) where
  M : TopCat.{0}
  base : B ⟶ M
  interval : cylinderSpace A ⟶ M
  square : IsPushout f (endpoint A 1) base interval

namespace MappingCylinder

variable {A B : TopCat.{0}} {f : A ⟶ B} (mc : MappingCylinder f)

def free : A ⟶ mc.M := endpoint A 0 ≫ mc.interval

@[simp] lemma interval_zero (a : A) : mc.interval (0, a) = mc.free a := rfl

lemma interval_one (a : A) : mc.interval (1, a) = mc.base (f a) :=
  (ConcreteCategory.congr_hom mc.square.w a).symm

variable {T : TopCat.{0}} (fB : B ⟶ T) (H : C(I × A, T))
  (h1 : ∀ a, H (1, a) = fB (f a))

def desc : mc.M ⟶ T :=
  mc.square.desc fB (TopCat.ofHom H) (by
    apply ConcreteCategory.hom_ext
    intro a
    exact (h1 a).symm)

lemma desc_base (b : B) : mc.desc fB H h1 (mc.base b) = fB b :=
  ConcreteCategory.congr_hom (mc.square.inl_desc _ _ _) b

lemma desc_interval (p : I × A) : mc.desc fB H h1 (mc.interval p) = H p :=
  ConcreteCategory.congr_hom (mc.square.inr_desc _ _ _) p

lemma desc_free (a : A) : mc.desc fB H h1 (mc.free a) = H (0, a) :=
  mc.desc_interval fB H h1 (0, a)

lemma hom_ext {u v : mc.M ⟶ T}
    (hb : ∀ b, u (mc.base b) = v (mc.base b))
    (hj : ∀ p, u (mc.interval p) = v (mc.interval p)) : u = v := by
  apply mc.square.hom_ext
  · exact ConcreteCategory.hom_ext _ _ hb
  · exact ConcreteCategory.hom_ext _ _ hj

variable (HB : C(I × B, T)) (HJ : C(I × cylinderSpace A, T))
  (agree : ∀ t a, HJ (t, (1, a)) = HB (t, f a))

/-- Joint descent. Only the time interval is used as a locally compact space. -/
def timeDesc : C(I × mc.M, T) :=
  IntervalSkeletalDescent01.cylinder mc.square HB HJ (fun t a => (agree t a).symm)

lemma timeDesc_base (t : I) (b : B) :
    mc.timeDesc HB HJ agree (t, mc.base b) = HB (t, b) :=
  IntervalSkeletalDescent01.cylinder_left mc.square HB HJ
    (fun t a => (agree t a).symm) t b

lemma timeDesc_interval (t : I) (p : I × A) :
    mc.timeDesc HB HJ agree (t, mc.interval p) = HJ (t, p) :=
  IntervalSkeletalDescent01.cylinder_right mc.square HB HJ
    (fun t a => (agree t a).symm) t p

lemma timeDesc_free (t : I) (a : A) :
    mc.timeDesc HB HJ agree (t, mc.free a) = HJ (t, (0, a)) :=
  mc.timeDesc_interval HB HJ agree t (0, a)

end MappingCylinder

variable {A B A' B' : TopCat.{0}} {f : A ⟶ B} {f' : A' ⟶ B'}

/-- Supply the actual pushout, without an existence hypothesis. -/
def canonicalMappingCylinder (f : A ⟶ B) : MappingCylinder f where
  M := pushout f (endpoint A 1)
  base := pushout.inl f (endpoint A 1)
  interval := pushout.inr f (endpoint A 1)
  square := IsPushout.of_hasPushout f (endpoint A 1)

variable (mc' : MappingCylinder f') (α : A ⟶ A') (β : B ⟶ B')
  (φ : (α ≫ f').hom.Homotopy (f ≫ β).hom)

/-- Traverse the target cylinder from its free end to its attached end. -/
def firstPath :
    (α ≫ mc'.free).hom.Homotopy (α ≫ f' ≫ mc'.base).hom where
  toContinuousMap := ⟨fun p => mc'.interval (p.1, α p.2),
    mc'.interval.hom.continuous.comp
      (continuous_fst.prodMk (α.hom.continuous.comp continuous_snd))⟩
  map_zero_left a := mc'.interval_zero (α a)
  map_one_left a := mc'.interval_one (α a)

/-- Traverse the supplied square homotopy inside the target base B'. -/
def secondPath :
    (α ≫ f' ≫ mc'.base).hom.Homotopy (f ≫ β ≫ mc'.base).hom where
  toContinuousMap := mc'.base.hom.comp φ.toContinuousMap
  map_zero_left a := congrArg mc'.base (φ.map_zero_left a)
  map_one_left a := congrArg mc'.base (φ.map_one_left a)

/-- The two equal time slots are exactly Mathlib Homotopy.trans. -/
def generalizedPath :
    (α ≫ mc'.free).hom.Homotopy (f ≫ β ≫ mc'.base).hom :=
  (firstPath mc' α).trans (secondPath mc' α β φ)

variable (mc : MappingCylinder f)

/-- The generalized map is an actual pushout descent. -/
def generalized : mc.M ⟶ mc'.M :=
  mc.desc (β ≫ mc'.base) (generalizedPath mc' α β φ).toContinuousMap
    (fun a => (generalizedPath mc' α β φ).map_one_left a)

lemma generalized_base (b : B) :
    generalized mc' α β φ mc (mc.base b) = mc'.base (β b) :=
  mc.desc_base _ _ _ b

lemma generalized_interval (u : I) (a : A) :
    generalized mc' α β φ mc (mc.interval (u, a)) =
      generalizedPath mc' α β φ (u, a) :=
  mc.desc_interval _ _ _ (u, a)

lemma generalized_free (a : A) :
    generalized mc' α β φ mc (mc.free a) = mc'.free (α a) :=
  (mc.desc_free _ _ _ a).trans ((generalizedPath mc' α β φ).map_zero_left a)

lemma generalized_attached (a : A) :
    generalized mc' α β φ mc (mc.interval (1, a)) = mc'.base (β (f a)) :=
  (generalized_interval mc' α β φ mc 1 a).trans
    ((generalizedPath mc' α β φ).map_one_left a)

/-- Exact trans formula. On each half the extend parameter lies in I. -/
lemma generalized_interval_formula (u : I) (a : A) :
    generalized mc' α β φ mc (mc.interval (u, a)) =
      if (u : ℝ) ≤ 1 / 2 then
        (firstPath mc' α).extend (2 * u) a
      else
        (secondPath mc' α β φ).extend (2 * u - 1) a :=
  (generalized_interval mc' α β φ mc u a).trans rfl

end AutomaticCoherence.MappingCylinderFoundation01
