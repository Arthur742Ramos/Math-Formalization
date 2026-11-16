import MappingCylinderFoundation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-! SOURCE ONLY / UNCOMPILED.
Remove the constant collar in the generalized identity square, fixing both
the actual base image and the actual free-end image at every time. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology
namespace AutomaticCoherence.MappingCylinderCollar01
open MappingCylinderFoundation01

def collarParameter (s : I) : I :=
  ⟨Path.Homotopy.transReflReparamAux s,
    Path.Homotopy.transReflReparamAux_mem_I s⟩

lemma continuous_collarParameter : Continuous collarParameter :=
  Path.Homotopy.continuous_transReflReparamAux.subtype_mk _

@[simp] lemma collarParameter_zero : collarParameter 0 = 0 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_zero
@[simp] lemma collarParameter_one : collarParameter 1 = 1 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_one

def collarClock (v s : I) : I := Set.Icc.convexComb (collarParameter s) s v

lemma continuous_collarClock : Continuous (fun p : I × I => collarClock p.1 p.2) :=
  Set.Icc.continuous_convexComb_prod.comp
    ((continuous_collarParameter.comp continuous_snd).prodMk
      (continuous_snd.prodMk continuous_fst))

@[simp] lemma collarClock_zero (s : I) : collarClock 0 s = collarParameter s := by
  simp [collarClock]
@[simp] lemma collarClock_one (s : I) : collarClock 1 s = s := by simp [collarClock]
@[simp] lemma collarClock_left (v : I) : collarClock v 0 = 0 := by simp [collarClock]
@[simp] lemma collarClock_right (v : I) : collarClock v 1 = 1 := by simp [collarClock]

variable {A B : TopCat.{0}} {f : A ⟶ B} (mc : MappingCylinder f)

def constantSquare (f : A ⟶ B) :
    ((𝟙 A) ≫ f).hom.Homotopy (f ≫ (𝟙 B)).hom :=
  (ContinuousMap.Homotopy.refl f.hom).cast rfl rfl

def collaredIdentity : mc.M ⟶ mc.M :=
  generalized mc (𝟙 A) (𝟙 B) (constantSquare f) mc

lemma collaredIdentity_base (b : B) :
    collaredIdentity mc (mc.base b) = mc.base b :=
  generalized_base mc (𝟙 A) (𝟙 B) (constantSquare f) mc b

lemma collaredIdentity_free (x : A) :
    collaredIdentity mc (mc.free x) = mc.free x :=
  generalized_free mc (𝟙 A) (𝟙 B) (constantSquare f) mc x

lemma collaredIdentity_interval (s : I) (x : A) :
    collaredIdentity mc (mc.interval (s,x)) =
      mc.interval (collarParameter s,x) := by
  unfold collaredIdentity
  rw [generalized_interval]
  change ((firstPath mc (𝟙 A)).trans
    (secondPath mc (𝟙 A) (𝟙 B) (constantSquare f))) (s,x) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · apply congrArg (fun t : I => mc.interval (t,x))
    apply Subtype.ext
    change 2 * (s : ℝ) = Path.Homotopy.transReflReparamAux s
    simp only [Path.Homotopy.transReflReparamAux, if_pos hs]
  · change mc.base (f x) = mc.interval (collarParameter s,x)
    have hc : collarParameter s = 1 := by
      apply Subtype.ext
      change Path.Homotopy.transReflReparamAux s = 1
      simp only [Path.Homotopy.transReflReparamAux, if_neg hs]
    rw [hc]
    exact (mc.interval_one x).symm

def cylinderFamily : C(I × (I × A),mc.M) where
  toFun p := mc.interval (collarClock p.1 p.2.1,p.2.2)
  continuous_toFun := mc.interval.hom.continuous.comp
    ((continuous_collarClock.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))

lemma cylinderFamily_left (v : I) (x : A) :
    cylinderFamily mc (v,(0,x)) = mc.free x := by
  change mc.interval (collarClock v 0,x) = _
  rw [collarClock_left]
  exact mc.interval_zero x

lemma cylinderFamily_right (v : I) (x : A) :
    cylinderFamily mc (v,(1,x)) = mc.base (f x) := by
  change mc.interval (collarClock v 1,x) = _
  rw [collarClock_right]
  exact mc.interval_one x

def family : C(I × mc.M,mc.M) :=
  mc.timeDesc ⟨fun p => mc.base p.2, mc.base.hom.continuous.comp continuous_snd⟩
    (cylinderFamily mc) (cylinderFamily_right mc)

lemma family_base (v : I) (b : B) : family mc (v,mc.base b) = mc.base b :=
  mc.timeDesc_base _ _ _ v b

lemma family_interval (v s : I) (x : A) :
    family mc (v,mc.interval (s,x)) = mc.interval (collarClock v s,x) :=
  mc.timeDesc_interval _ _ _ v (s,x)

lemma family_free (v : I) (x : A) : family mc (v,mc.free x) = mc.free x :=
  (mc.timeDesc_free _ _ _ v x).trans (cylinderFamily_left mc v x)

/-- The target is the literal identity continuous map of the actual cylinder. -/
def collarRemoval : (collaredIdentity mc).hom.Homotopy (ContinuousMap.id mc.M) where
  toContinuousMap := family mc
  map_zero_left z := by
    have he : TopCat.ofHom
        (⟨fun y => family mc (0,y), by fun_prop⟩ : C(mc.M,mc.M)) = collaredIdentity mc := by
      apply mc.hom_ext
      · intro b
        exact (family_base mc 0 b).trans (collaredIdentity_base mc b).symm
      · rintro ⟨s,x⟩
        exact (family_interval mc 0 s x).trans
          ((congrArg (fun t : I => mc.interval (t,x)) (collarClock_zero s)).trans
            (collaredIdentity_interval mc s x).symm)
    exact ConcreteCategory.congr_hom he z
  map_one_left z := by
    have he : TopCat.ofHom
        (⟨fun y => family mc (1,y), by fun_prop⟩ : C(mc.M,mc.M)) = 𝟙 mc.M := by
      apply mc.hom_ext
      · intro b
        exact family_base mc 1 b
      · rintro ⟨s,x⟩
        exact (family_interval mc 1 s x).trans
          (congrArg (fun t : I => mc.interval (t,x)) (collarClock_one s))
    exact ConcreteCategory.congr_hom he z

def outerEnds : Set mc.M := Set.range mc.base ∪ Set.range mc.free

def collarRemovalRel : (collaredIdentity mc).hom.HomotopyRel
    (ContinuousMap.id mc.M) (outerEnds mc) where
  toHomotopy := collarRemoval mc
  prop' v z hz := by
    rcases hz with ⟨b,rfl⟩ | ⟨x,rfl⟩
    · exact (family_base mc v b).trans (collaredIdentity_base mc b).symm
    · exact (family_free mc v x).trans (collaredIdentity_free mc x).symm

end AutomaticCoherence.MappingCylinderCollar01
