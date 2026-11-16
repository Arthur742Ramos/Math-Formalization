import TopologicalHEPClosure
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Ring

/-! SOURCE ONLY / UNCOMPILED. Actual double-cylinder collapse from bare HEP.
The two pushouts are data, not inverse or homotopy premises. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology
namespace AutomaticCoherence.DoubleCylinderCollapse01
open TopologicalHEPClosure01
open IntervalSkeletalDescent01 (cylinder cylinder_left cylinder_right)
abbrev I := unitInterval
abbrev cylinderSpace (A : TopCat.{0}) : TopCat.{0} := TopCat.of (I × A)
def endpoint (A : TopCat.{0}) (t : I) : A ⟶ cylinderSpace A :=
  TopCat.ofHom ⟨fun a => (t,a), continuous_const.prodMk continuous_id⟩

structure DoubleCylinder {A B C : TopCat.{0}} (i : A ⟶ B) (j : A ⟶ C) where
  M : TopCat.{0}
  D : TopCat.{0}
  b : B ⟶ M
  c : cylinderSpace A ⟶ M
  m : M ⟶ D
  d : C ⟶ D
  first : IsPushout i (endpoint A 0) b c
  second : IsPushout (endpoint A 1 ≫ c) j m d

namespace DoubleCylinder
variable {A B C : TopCat.{0}} {i : A ⟶ B} {j : A ⟶ C}
variable (dc : DoubleCylinder i j)
abbrev left : B ⟶ dc.D := dc.b ≫ dc.m
abbrev interval : cylinderSpace A ⟶ dc.D := dc.c ≫ dc.m
lemma interval_zero (a : A) : dc.interval (0,a) = dc.left (i a) :=
  (congrArg dc.m (ConcreteCategory.congr_hom dc.first.w a)).symm
lemma interval_one (a : A) : dc.interval (1,a) = dc.d (j a) :=
  ConcreteCategory.congr_hom dc.second.w a

variable {T : TopCat.{0}} (fB : B ⟶ T) (fJ : cylinderSpace A ⟶ T) (fC : C ⟶ T)
  (h0 : ∀ a, fB (i a) = fJ (0,a)) (h1 : ∀ a, fJ (1,a) = fC (j a))
def descFirst : dc.M ⟶ T :=
  dc.first.desc fB fJ (ConcreteCategory.hom_ext _ _ h0)
lemma descFirst_b (b : B) : dc.descFirst fB fJ h0 (dc.b b) = fB b :=
  ConcreteCategory.congr_hom (dc.first.inl_desc _ _ _) b
lemma descFirst_c (p : cylinderSpace A) : dc.descFirst fB fJ h0 (dc.c p) = fJ p :=
  ConcreteCategory.congr_hom (dc.first.inr_desc _ _ _) p

def desc : dc.D ⟶ T := dc.second.desc (dc.descFirst fB fJ h0) fC (by
  apply ConcreteCategory.hom_ext
  intro a
  exact (dc.descFirst_c fB fJ h0 (1,a)).trans (h1 a))
lemma desc_left (b : B) : dc.desc fB fJ fC h0 h1 (dc.left b) = fB b :=
  (ConcreteCategory.congr_hom (dc.second.inl_desc _ _ _) (dc.b b)).trans
    (dc.descFirst_b fB fJ h0 b)
lemma desc_interval (p : cylinderSpace A) : dc.desc fB fJ fC h0 h1 (dc.interval p) = fJ p :=
  (ConcreteCategory.congr_hom (dc.second.inl_desc _ _ _) (dc.c p)).trans
    (dc.descFirst_c fB fJ h0 p)
lemma desc_right (c : C) : dc.desc fB fJ fC h0 h1 (dc.d c) = fC c :=
  ConcreteCategory.congr_hom (dc.second.inr_desc _ _ _) c

lemma hom_ext {f g : dc.D ⟶ T}
    (hb : ∀ b, f (dc.left b) = g (dc.left b))
    (hj : ∀ p, f (dc.interval p) = g (dc.interval p))
    (hc : ∀ c, f (dc.d c) = g (dc.d c)) : f = g := by
  apply dc.second.hom_ext
  · apply dc.first.hom_ext
    · exact ConcreteCategory.hom_ext _ _ hb
    · exact ConcreteCategory.hom_ext _ _ hj
  · exact ConcreteCategory.hom_ext _ _ hc

variable (HB : C(I × B,T)) (HJ : C(I × cylinderSpace A,T)) (HC : C(I × C,T))
  (e0 : ∀ t a, HB (t,i a) = HJ (t,(0,a)))
  (e1 : ∀ t a, HJ (t,(1,a)) = HC (t,j a))
def timeFirst : C(I × dc.M,T) := cylinder dc.first HB HJ e0
def timeDesc : C(I × dc.D,T) :=
  cylinder dc.second (dc.timeFirst HB HJ e0) HC (fun t a =>
    (cylinder_right dc.first HB HJ e0 t (1,a)).trans (e1 t a))
lemma timeDesc_left (t : I) (b : B) :
    dc.timeDesc HB HJ HC e0 e1 (t,dc.left b) = HB (t,b) :=
  (cylinder_left dc.second _ _ _ t (dc.b b)).trans
    (cylinder_left dc.first HB HJ e0 t b)
lemma timeDesc_interval (t : I) (p : cylinderSpace A) :
    dc.timeDesc HB HJ HC e0 e1 (t,dc.interval p) = HJ (t,p) :=
  (cylinder_left dc.second _ _ _ t (dc.c p)).trans
    (cylinder_right dc.first HB HJ e0 t p)
lemma timeDesc_right (t : I) (c : C) :
    dc.timeDesc HB HJ HC e0 e1 (t,dc.d c) = HC (t,c) :=
  cylinder_right dc.second _ _ _ t c
end DoubleCylinder

/-- This interval expression is exactly t + (1-t)u, with bounds intrinsic. -/
def slide (t u : I) : I := unitInterval.symm (unitInterval.symm t * unitInterval.symm u)
lemma slide_coe (t u : I) : (slide t u : ℝ) = t + (1-(t : ℝ))*u := by
  change 1 - (1 - (t : ℝ)) * (1 - (u : ℝ)) = t + (1 - (t : ℝ)) * u
  ring
@[simp] lemma slide_zero_left (u : I) : slide 0 u = u := by simp [slide]
@[simp] lemma slide_one_left (u : I) : slide 1 u = 1 := by simp [slide]
@[simp] lemma slide_zero_right (t : I) : slide t 0 = t := by simp [slide]
@[simp] lemma slide_one_right (t : I) : slide t 1 = 1 := by simp [slide]
lemma continuous_slide : Continuous (fun p : I × I => slide p.1 p.2) := by
  apply (continuous_induced_rng (f := (Subtype.val : I → ℝ))).mpr
  change Continuous (fun p : I × I => 1 - (1 - (p.1 : ℝ)) * (1 - (p.2 : ℝ)))
  exact continuous_const.sub
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_snd)))

variable {A B C P : TopCat.{0}} {i : A ⟶ B} {j : A ⟶ C}
  {L : B ⟶ P} {R : C ⟶ P} (hp : IsPushout i j L R) (dc : DoubleCylinder i j)

def collapse : dc.D ⟶ P := dc.desc L
  (TopCat.ofHom ⟨fun p => L (i p.2), L.hom.continuous.comp
    (i.hom.continuous.comp continuous_snd)⟩) R
  (fun _ => rfl) (fun a => ConcreteCategory.congr_hom hp.w a)
@[simp] lemma collapse_left (b : B) : collapse hp dc (dc.left b) = L b :=
  dc.desc_left _ _ _ _ _ b
@[simp] lemma collapse_interval (u : I) (a : A) :
    collapse hp dc (dc.interval (u,a)) = L (i a) := dc.desc_interval _ _ _ _ _ (u,a)
@[simp] lemma collapse_right (c : C) : collapse hp dc (dc.d c) = R c :=
  dc.desc_right _ _ _ _ _ c

/-- Only bare HasHEP is used to produce the path extension. -/
lemma extension_exists (hi : HasHEP i) :
    ∃ H : C(I × B,dc.D), (∀ b, H (0,b) = dc.left b) ∧
      (∀ t a, H (t,i a) = dc.interval (t,a)) :=
  hi dc.D dc.left.hom dc.interval.hom (fun a => dc.interval_zero a)

def extension (hi : HasHEP i) : C(I × B,dc.D) := Classical.choose (extension_exists dc hi)
lemma extension_zero (hi : HasHEP i) (b : B) : extension dc hi (0,b) = dc.left b :=
  (Classical.choose_spec (extension_exists dc hi)).1 b
lemma extension_boundary (hi : HasHEP i) (t : I) (a : A) :
    extension dc hi (t,i a) = dc.interval (t,a) :=
  (Classical.choose_spec (extension_exists dc hi)).2 t a

def sectionMap (hi : HasHEP i) : P ⟶ dc.D := hp.desc
  (TopCat.ofHom ⟨fun b => extension dc hi (1,b),
    (extension dc hi).continuous.comp (continuous_const.prodMk continuous_id)⟩)
  dc.d (by
    apply ConcreteCategory.hom_ext
    intro a
    exact (extension_boundary dc hi 1 a).trans (dc.interval_one a))
lemma section_left (hi : HasHEP i) (b : B) :
    sectionMap hp dc hi (L b) = extension dc hi (1,b) :=
  ConcreteCategory.congr_hom (hp.inl_desc _ _ _) b
lemma section_right (hi : HasHEP i) (c : C) : sectionMap hp dc hi (R c) = dc.d c :=
  ConcreteCategory.congr_hom (hp.inr_desc _ _ _) c

/-- Homotopy id_P to q s, descended through the original pushout. -/
def targetFamily (hi : HasHEP i) : C(I × P,P) :=
  cylinder hp ((collapse hp dc).hom.comp (extension dc hi))
    ⟨fun p => R p.2, R.hom.continuous.comp continuous_snd⟩ (by
      intro t a
      change collapse hp dc (extension dc hi (t,i a)) = R (j a)
      rw [extension_boundary, collapse_interval]
      exact ConcreteCategory.congr_hom hp.w a)
lemma targetFamily_left (hi : HasHEP i) (t : I) (b : B) :
    targetFamily hp dc hi (t,L b) = collapse hp dc (extension dc hi (t,b)) :=
  cylinder_left hp _ _ _ t b
lemma targetFamily_right (hi : HasHEP i) (t : I) (c : C) :
    targetFamily hp dc hi (t,R c) = R c := cylinder_right hp _ _ _ t c

def targetHomotopy (hi : HasHEP i) : (ContinuousMap.id P).Homotopy
    ((collapse hp dc).hom.comp (sectionMap hp dc hi).hom) where
  toContinuousMap := targetFamily hp dc hi
  map_zero_left p := by
    have e : TopCat.ofHom (⟨fun x => targetFamily hp dc hi (0,x), by fun_prop⟩ : C(P,P)) = 𝟙 P := by
      apply hp.hom_ext
      · apply ConcreteCategory.hom_ext
        intro b
        change targetFamily hp dc hi (0,L b) = L b
        rw [targetFamily_left, extension_zero, collapse_left]
      · apply ConcreteCategory.hom_ext
        intro c
        exact targetFamily_right hp dc hi 0 c
    exact ConcreteCategory.congr_hom e p
  map_one_left p := by
    have e : TopCat.ofHom (⟨fun x => targetFamily hp dc hi (1,x), by fun_prop⟩ : C(P,P)) =
        sectionMap hp dc hi ≫ collapse hp dc := by
      apply hp.hom_ext
      · apply ConcreteCategory.hom_ext
        intro b
        change targetFamily hp dc hi (1,L b) = collapse hp dc (sectionMap hp dc hi (L b))
        rw [targetFamily_left, section_left]
      · apply ConcreteCategory.hom_ext
        intro c
        change targetFamily hp dc hi (1,R c) = collapse hp dc (sectionMap hp dc hi (R c))
        rw [targetFamily_right, section_right, collapse_right]
    exact ConcreteCategory.congr_hom e p

/-- The complete cylinder coordinate is moved by the required affine formula. -/
def sourceFamily (hi : HasHEP i) : C(I × dc.D,dc.D) :=
  dc.timeDesc (extension dc hi)
    ⟨fun p => dc.interval (slide p.1 p.2.1,p.2.2), by
      apply dc.interval.hom.continuous.comp
      exact ((continuous_slide.comp (continuous_fst.prodMk
        (continuous_fst.comp continuous_snd))).prodMk (continuous_snd.comp continuous_snd))⟩
    ⟨fun p => dc.d p.2, dc.d.hom.continuous.comp continuous_snd⟩
    (by intro t a; change extension dc hi (t,i a) = dc.interval (slide t 0,a)
        rw [slide_zero_right, extension_boundary])
    (by intro t a; change dc.interval (slide t 1,a) = dc.d (j a)
        rw [slide_one_right]; exact dc.interval_one a)
lemma sourceFamily_left (hi : HasHEP i) (t : I) (b : B) :
    sourceFamily dc hi (t,dc.left b) = extension dc hi (t,b) := dc.timeDesc_left _ _ _ _ _ t b
lemma sourceFamily_interval (hi : HasHEP i) (t u : I) (a : A) :
    sourceFamily dc hi (t,dc.interval (u,a)) = dc.interval (slide t u,a) :=
  dc.timeDesc_interval _ _ _ _ _ t (u,a)
lemma sourceFamily_right (hi : HasHEP i) (t : I) (c : C) :
    sourceFamily dc hi (t,dc.d c) = dc.d c := dc.timeDesc_right _ _ _ _ _ t c

def sourceHomotopy (hi : HasHEP i) : (ContinuousMap.id dc.D).Homotopy
    ((sectionMap hp dc hi).hom.comp (collapse hp dc).hom) where
  toContinuousMap := sourceFamily dc hi
  map_zero_left z := by
    have e : TopCat.ofHom (⟨fun x => sourceFamily dc hi (0,x), by fun_prop⟩ : C(dc.D,dc.D)) = 𝟙 dc.D := by
      apply dc.hom_ext
      · intro b
        change sourceFamily dc hi (0,dc.left b) = dc.left b
        rw [sourceFamily_left, extension_zero]
      · rintro ⟨u,a⟩
        change sourceFamily dc hi (0,dc.interval (u,a)) = dc.interval (u,a)
        rw [sourceFamily_interval, slide_zero_left]
      · intro c
        exact sourceFamily_right dc hi 0 c
    exact ConcreteCategory.congr_hom e z
  map_one_left z := by
    have e : TopCat.ofHom (⟨fun x => sourceFamily dc hi (1,x), by fun_prop⟩ : C(dc.D,dc.D)) =
        collapse hp dc ≫ sectionMap hp dc hi := by
      apply dc.hom_ext
      · intro b
        change sourceFamily dc hi (1,dc.left b) = sectionMap hp dc hi (collapse hp dc (dc.left b))
        rw [sourceFamily_left, collapse_left, section_left]
      · rintro ⟨u,a⟩
        change sourceFamily dc hi (1,dc.interval (u,a)) =
          sectionMap hp dc hi (collapse hp dc (dc.interval (u,a)))
        rw [sourceFamily_interval, slide_one_left, collapse_interval, section_left,
          extension_boundary]
      · intro c
        change sourceFamily dc hi (1,dc.d c) = sectionMap hp dc hi (collapse hp dc (dc.d c))
        rw [sourceFamily_right, collapse_right, section_right]
    exact ConcreteCategory.congr_hom e z

/-- Genuine collapse equivalence. No supplied inverse or local matching homotopies. -/
def collapseEquivalence (hi : HasHEP i) : dc.D ≃ₕ P where
  toFun := (collapse hp dc).hom
  invFun := (sectionMap hp dc hi).hom
  left_inv := ⟨(sourceHomotopy hp dc hi).symm⟩
  right_inv := ⟨(targetHomotopy hp dc hi).symm⟩
@[simp] lemma collapseEquivalence_toFun (hi : HasHEP i) :
    (collapseEquivalence hp dc hi).toFun = (collapse hp dc).hom := rfl

end AutomaticCoherence.DoubleCylinderCollapse01
