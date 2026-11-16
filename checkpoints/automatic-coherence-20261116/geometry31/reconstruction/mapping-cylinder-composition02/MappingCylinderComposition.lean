import MappingCylinderFoundation
import HomotopyAssociationFamily

/-! SOURCE ONLY / UNCOMPILED.
Composition of generalized maps is homotopic to the normalized generalized
map, relative to the base and the free end. No square-retraction dependency. -/
noncomputable section
open CategoryTheory Limits ContinuousMap
open scoped Topology
namespace AutomaticCoherence.MappingCylinderComposition01
open MappingCylinderFoundation01
open HomotopyAssociationFamily01 (family family_zero family_one family_left family_right)

section Whiskering
variable {X Y Z : TopCat.{0}} {u v w : X ⟶ Y}

def whiskerRight (k : Y ⟶ Z) (H : u.hom.Homotopy v.hom) :
    (u ≫ k).hom.Homotopy (v ≫ k).hom :=
  ((ContinuousMap.Homotopy.refl k.hom).comp H).cast rfl rfl

def whiskerLeft (a : Z ⟶ X) (H : u.hom.Homotopy v.hom) :
    (a ≫ u).hom.Homotopy (a ≫ v).hom :=
  (H.compContinuousMap a.hom).cast rfl rfl

lemma whiskerRight_trans (k : Y ⟶ Z)
    (H : u.hom.Homotopy v.hom) (K : v.hom.Homotopy w.hom) :
    whiskerRight k (H.trans K) = (whiskerRight k H).trans (whiskerRight k K) := by
  apply ContinuousMap.Homotopy.ext
  rintro ⟨t,x⟩
  change k ((H.trans K) (t,x)) = _
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl
end Whiskering

variable {A₀ B₀ A₁ B₁ A₂ B₂ : TopCat.{0}}
  {f₀ : A₀ ⟶ B₀} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
  (m₀ : MappingCylinder f₀) (m₁ : MappingCylinder f₁) (m₂ : MappingCylinder f₂)
  (a₀ : A₀ ⟶ A₁) (b₀ : B₀ ⟶ B₁)
  (h₀ : (a₀ ≫ f₁).hom.Homotopy (f₀ ≫ b₀).hom)
  (a₁ : A₁ ⟶ A₂) (b₁ : B₁ ⟶ B₂)
  (h₁ : (a₁ ≫ f₂).hom.Homotopy (f₁ ≫ b₁).hom)

local notation "Ω" => ContinuousMap.Homotopy.trans (whiskerLeft a₀ h₁) (whiskerRight b₁ h₀)
local notation "P" => firstPath m₂ (a₀ ≫ a₁)
local notation "Q" => whiskerRight m₂.base (whiskerLeft a₀ h₁)
local notation "R" => whiskerRight m₂.base (whiskerRight b₁ h₀)
local notation "F" => generalized m₁ a₀ b₀ h₀ m₀
local notation "G" => generalized m₂ a₁ b₁ h₁ m₁
local notation "N" => generalized m₂ (a₀ ≫ a₁) (b₀ ≫ b₁) Ω m₀

/-- The target normalized cylinder has the right-associated three pieces. -/
lemma normalized_path :
    generalizedPath m₂ (a₀ ≫ a₁) (b₀ ≫ b₁) Ω = (P).trans ((Q).trans R) := by
  change (P).trans (whiskerRight m₂.base
    ((whiskerLeft a₀ h₁).trans (whiskerRight b₁ h₀))) = _
  rw [whiskerRight_trans]

/-- The image of the first source piece traverses the first two target pieces. -/
lemma composite_first (u : I) (x : A₀) :
    G (firstPath m₁ a₀ (u,x)) = ((P).trans Q) (u,x) := by
  change G (m₁.interval (u,a₀ x)) = _
  rw [generalized_interval]
  change ((firstPath m₂ a₁).trans (secondPath m₂ a₁ b₁ h₁)) (u,a₀ x) =
    ((P).trans Q) (u,x)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

lemma composite_second (u : I) (x : A₀) :
    G (secondPath m₁ a₀ b₀ h₀ (u,x)) = R (u,x) := by
  change G (m₁.base (h₀ (u,x))) = m₂.base (b₁ (h₀ (u,x)))
  exact generalized_base m₂ a₁ b₁ h₁ m₁ (h₀ (u,x))

/-- Literal composite: quarter, quarter, half, without inferred gluing. -/
lemma composite_interval (u : I) (x : A₀) :
    (F ≫ G) (m₀.interval (u,x)) = (((P).trans Q).trans R) (u,x) := by
  change G (F (m₀.interval (u,x))) = _
  rw [generalized_interval]
  change G (((firstPath m₁ a₀).trans (secondPath m₁ a₀ b₀ h₀)) (u,x)) = _
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs with hu
  · exact composite_first m₁ m₂ a₀ a₁ b₁ h₁ _ x
  · exact composite_second m₁ m₂ a₀ b₀ h₀ a₁ b₁ h₁ _ x

lemma composite_base (b : B₀) : (F ≫ G) (m₀.base b) = m₂.base (b₁ (b₀ b)) := by
  change G (F (m₀.base b)) = _
  rw [generalized_base, generalized_base]

lemma composite_free (x : A₀) : (F ≫ G) (m₀.free x) = m₂.free (a₁ (a₀ x)) := by
  change G (F (m₀.free x)) = _
  rw [generalized_free, generalized_free]

/-- The explicit association family is joint in time, cylinder coordinate and x. -/
def comparisonFamily : C(I × m₀.M,m₂.M) :=
  m₀.timeDesc
    ⟨fun p => m₂.base (b₁ (b₀ p.2)), by fun_prop⟩
    (family P Q R) (fun t x => family_right P Q R t x)

lemma comparisonFamily_base (t : I) (b : B₀) :
    comparisonFamily m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ (t,m₀.base b) =
      m₂.base (b₁ (b₀ b)) :=
  m₀.timeDesc_base _ _ _ t b

lemma comparisonFamily_interval (t u : I) (x : A₀) :
    comparisonFamily m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ (t,m₀.interval (u,x)) =
      family P Q R (t,(u,x)) :=
  m₀.timeDesc_interval _ _ _ t (u,x)

lemma comparisonFamily_free (t : I) (x : A₀) :
    comparisonFamily m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ (t,m₀.free x) =
      m₂.free (a₁ (a₀ x)) :=
  (m₀.timeDesc_free _ _ _ t x).trans (family_left P Q R t x)

/-- Actual composition-to-normal-form homotopy, not merely a homotopy-class equation. -/
def compositionHomotopy : (F ≫ G).hom.Homotopy (N).hom where
  toContinuousMap := comparisonFamily m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁
  map_zero_left z := by
    have he : TopCat.ofHom
        (⟨fun y => comparisonFamily m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ (0,y),
          by fun_prop⟩ : C(m₀.M,m₂.M)) = F ≫ G := by
      apply m₀.hom_ext
      · intro b
        exact (comparisonFamily_base m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ 0 b).trans
          (composite_base m₀ m₁ m₂ a₀ b₀ h₀ a₁ b₁ h₁ b).symm
      · rintro ⟨u,x⟩
        exact (comparisonFamily_interval m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ 0 u x).trans
          ((family_zero P Q R u x).trans
            (composite_interval m₀ m₁ m₂ a₀ b₀ h₀ a₁ b₁ h₁ u x).symm)
    exact ConcreteCategory.congr_hom he z
  map_one_left z := by
    have he : TopCat.ofHom
        (⟨fun y => comparisonFamily m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ (1,y),
          by fun_prop⟩ : C(m₀.M,m₂.M)) = N := by
      apply m₀.hom_ext
      · intro b
        exact (comparisonFamily_base m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ 1 b).trans
          (generalized_base m₂ (a₀ ≫ a₁) (b₀ ≫ b₁) Ω m₀ b).symm
      · rintro ⟨u,x⟩
        have hn := normalized_path m₂ a₀ b₀ h₀ a₁ b₁ h₁
        have hn' := ContinuousMap.Homotopy.congr_fun hn (u,x)
        exact (comparisonFamily_interval m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ 1 u x).trans
          ((family_one P Q R u x).trans
            (hn'.symm.trans
              (generalized_interval m₂ (a₀ ≫ a₁) (b₀ ≫ b₁) Ω m₀ u x).symm))
    exact ConcreteCategory.congr_hom he z

/-- The relative subset is the union of the two actual endpoint images. -/
def outerEnds : Set m₀.M := Set.range m₀.base ∪ Set.range m₀.free

def compositionHomotopyRel : (F ≫ G).hom.HomotopyRel (N).hom (outerEnds m₀) where
  toHomotopy := compositionHomotopy m₀ m₁ m₂ a₀ b₀ h₀ a₁ b₁ h₁
  prop' t z hz := by
    rcases hz with ⟨b,rfl⟩ | ⟨x,rfl⟩
    · exact (comparisonFamily_base m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ t b).trans
        (composite_base m₀ m₁ m₂ a₀ b₀ h₀ a₁ b₁ h₁ b).symm
    · exact (comparisonFamily_free m₀ m₂ a₀ b₀ h₀ a₁ b₁ h₁ t x).trans
        (composite_free m₀ m₁ m₂ a₀ b₀ h₀ a₁ b₁ h₁ x).symm

end AutomaticCoherence.MappingCylinderComposition01
