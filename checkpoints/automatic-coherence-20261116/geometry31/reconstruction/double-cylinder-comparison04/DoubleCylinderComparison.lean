import DoubleCylinderCollapse

/-! SOURCE ONLY / UNCOMPILED. Literal maps of actual double cylinders and
ordinary pushouts, and naturality of collapse. No equivalence is assumed. -/
noncomputable section
open CategoryTheory Limits
namespace AutomaticCoherence.DoubleCylinderComparison01
open DoubleCylinderCollapse01

variable {A B C A' B' C' : TopCat.{0}}
  {i : A ⟶ B} {j : A ⟶ C} {i' : A' ⟶ B'} {j' : A' ⟶ C'}

/-- A strictly commuting map of spans, not chosen inverse coherence. -/
structure SpanMap (i : A ⟶ B) (j : A ⟶ C) (i' : A' ⟶ B') (j' : A' ⟶ C') where
  a : A ⟶ A'
  b : B ⟶ B'
  c : C ⟶ C'
  left : i ≫ b = a ≫ i'
  right : j ≫ c = a ≫ j'

variable (f : SpanMap i j i' j')
  (dc : DoubleCylinder i j) (dc' : DoubleCylinder i' j')

def intervalMap : cylinderSpace A ⟶ dc'.D := TopCat.ofHom
  ⟨fun p => dc'.interval (p.1, f.a p.2),
    dc'.interval.hom.continuous.comp
      (continuous_fst.prodMk (f.a.hom.continuous.comp continuous_snd))⟩

lemma intervalMap_zero (a : A) :
    dc'.left (f.b (i a)) = intervalMap f dc' (0,a) := by
  change dc'.left (f.b (i a)) = dc'.interval (0,f.a a)
  have h : f.b (i a) = i' (f.a a) := ConcreteCategory.congr_hom f.left a
  exact (congrArg dc'.left h).trans (dc'.interval_zero (f.a a)).symm

lemma intervalMap_one (a : A) :
    intervalMap f dc' (1,a) = dc'.d (f.c (j a)) := by
  change dc'.interval (1,f.a a) = dc'.d (f.c (j a))
  have h : f.c (j a) = j' (f.a a) := ConcreteCategory.congr_hom f.right a
  exact (dc'.interval_one (f.a a)).trans (congrArg dc'.d h).symm

def doubleMap : dc.D ⟶ dc'.D :=
  dc.desc (f.b ≫ dc'.left) (intervalMap f dc') (f.c ≫ dc'.d)
    (intervalMap_zero f dc') (intervalMap_one f dc')

lemma doubleMap_left (b : B) : doubleMap f dc dc' (dc.left b) = dc'.left (f.b b) :=
  dc.desc_left _ _ _ _ _ b
lemma doubleMap_interval (p : cylinderSpace A) :
    doubleMap f dc dc' (dc.interval p) = dc'.interval (p.1,f.a p.2) :=
  dc.desc_interval _ _ _ _ _ p
lemma doubleMap_right (c : C) : doubleMap f dc dc' (dc.d c) = dc'.d (f.c c) :=
  dc.desc_right _ _ _ _ _ c

variable {P P' : TopCat.{0}} {L : B ⟶ P} {R : C ⟶ P}
  {L' : B' ⟶ P'} {R' : C' ⟶ P'}
  (hp : IsPushout i j L R) (hp' : IsPushout i' j' L' R')

include hp' in
lemma ordinary_compatible : i ≫ f.b ≫ L' = j ≫ f.c ≫ R' := by
  rw [← Category.assoc, f.left, Category.assoc, hp'.w,
    ← Category.assoc, ← f.right, Category.assoc]

def ordinaryMap : P ⟶ P' :=
  hp.desc (f.b ≫ L') (f.c ≫ R') (ordinary_compatible f hp')

lemma ordinaryMap_left (b : B) : ordinaryMap f hp hp' (L b) = L' (f.b b) :=
  ConcreteCategory.congr_hom (hp.inl_desc _ _ _) b
lemma ordinaryMap_right (c : C) : ordinaryMap f hp hp' (R c) = R' (f.c c) :=
  ConcreteCategory.congr_hom (hp.inr_desc _ _ _) c

/-- Exact commuting square for the literal collapse and comparison maps. -/
lemma collapse_naturality :
    doubleMap f dc dc' ≫ collapse hp' dc' = collapse hp dc ≫ ordinaryMap f hp hp' := by
  apply dc.hom_ext
  · intro b
    change collapse hp' dc' (doubleMap f dc dc' (dc.left b)) =
      ordinaryMap f hp hp' (collapse hp dc (dc.left b))
    rw [doubleMap_left, collapse_left, collapse_left, ordinaryMap_left]
  · intro p
    change collapse hp' dc' (doubleMap f dc dc' (dc.interval p)) =
      ordinaryMap f hp hp' (collapse hp dc (dc.interval p))
    rw [doubleMap_interval, collapse_interval, collapse_interval, ordinaryMap_left]
    exact congrArg L' (ConcreteCategory.congr_hom f.left p.2).symm
  · intro c
    change collapse hp' dc' (doubleMap f dc dc' (dc.d c)) =
      ordinaryMap f hp hp' (collapse hp dc (dc.d c))
    rw [doubleMap_right, collapse_right, collapse_right, ordinaryMap_right]

end AutomaticCoherence.DoubleCylinderComparison01
