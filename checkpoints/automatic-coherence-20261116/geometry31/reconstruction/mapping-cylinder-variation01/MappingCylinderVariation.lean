import MappingCylinderFoundation

/-! SOURCE ONLY / UNCOMPILED.
Joint families of generalized mapping-cylinder maps with varying endpoint maps.
The comparison square is joint in both interval variables and the source.
No inverse homotopies or all-time compatibility are assumed in applications. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology

namespace AutomaticCoherence.MappingCylinderVariation01
open MappingCylinderFoundation01

/-- A literal time slice, without evaluation on a mapping space. -/
def atTime {X Y : TopCat.{0}} (F : C(I × X, Y)) (v : I) : X ⟶ Y :=
  TopCat.ofHom ⟨fun x => F (v,x), by fun_prop⟩

variable {A B A' B' : TopCat.{0}} {f : A ⟶ B} {f' : A' ⟶ B'}
  (mc : MappingCylinder f) (mc' : MappingCylinder f')
  (a : C(I × A,A')) (b : C(I × B,B'))
  (ξ : C((I × I) × A,B'))
  (left : ∀ v x, ξ ((v,0),x) = f' (a (v,x)))
  (right : ∀ v x, ξ ((v,1),x) = b (v,f x))

def movingFree : C(I × A,mc'.M) :=
  ⟨fun p => mc'.free (a p), by fun_prop⟩

def movingAttached : C(I × A,mc'.M) :=
  ⟨fun p => mc'.base (f' (a p)), by fun_prop⟩

def movingBase : C(I × A,mc'.M) :=
  ⟨fun p => mc'.base (b (p.1,f p.2)), by fun_prop⟩

/-- Here the homotopy coordinate is s and its source is the pair (v,x). -/
def first : (movingFree mc' a).Homotopy (movingAttached mc' a) where
  toContinuousMap := ⟨fun p => mc'.interval (p.1,a p.2), by fun_prop⟩
  map_zero_left p := mc'.interval_zero (a p)
  map_one_left p := mc'.interval_one (a p)

def second : (movingAttached mc' a).Homotopy (movingBase (f := f) mc' b) where
  toContinuousMap := ⟨fun p => mc'.base (ξ ((p.2.1,p.1),p.2.2)), by fun_prop⟩
  map_zero_left p := congrArg mc'.base (left p.1 p.2)
  map_one_left p := congrArg mc'.base (right p.1 p.2)

/-- Concatenation over I × A proves joint continuity; no arbitrary evaluation theorem. -/
def intervalFamily : C(I × cylinderSpace A,mc'.M) :=
  ((first mc' a).trans (second mc' a b ξ left right)).toContinuousMap.comp
    ⟨fun p => (p.2.1,(p.1,p.2.2)), by fun_prop⟩

lemma intervalFamily_left (v : I) (x : A) :
    intervalFamily mc' a b ξ left right (v,(0,x)) = mc'.free (a (v,x)) :=
  ((first mc' a).trans (second mc' a b ξ left right)).map_zero_left (v,x)

lemma intervalFamily_right (v : I) (x : A) :
    intervalFamily mc' a b ξ left right (v,(1,x)) = mc'.base (b (v,f x)) :=
  ((first mc' a).trans (second mc' a b ξ left right)).map_one_left (v,x)

/-- The actual joint pushout descent, with all-time attached-end agreement proved above. -/
def family : C(I × mc.M,mc'.M) :=
  mc.timeDesc ⟨fun p => mc'.base (b p), by fun_prop⟩
    (intervalFamily mc' a b ξ left right)
    (fun v x => intervalFamily_right mc' a b ξ left right v x)

lemma family_base (v : I) (y : B) :
    family mc mc' a b ξ left right (v,mc.base y) = mc'.base (b (v,y)) :=
  mc.timeDesc_base _ _ _ v y

lemma family_interval (v s : I) (x : A) :
    family mc mc' a b ξ left right (v,mc.interval (s,x)) =
      intervalFamily mc' a b ξ left right (v,(s,x)) :=
  mc.timeDesc_interval _ _ _ v (s,x)

lemma family_free (v : I) (x : A) :
    family mc mc' a b ξ left right (v,mc.free x) = mc'.free (a (v,x)) :=
  (mc.timeDesc_free _ _ _ v x).trans
    (intervalFamily_left mc' a b ξ left right v x)

/-- Exact comparison with the existing, unchanged generalized-map formula. -/
lemma intervalFamily_at (v : I) (α : A ⟶ A') (β : B ⟶ B')
    (φ : (α ≫ f').hom.Homotopy (f ≫ β).hom)
    (ha : ∀ x, a (v,x) = α x)
    (hξ : ∀ s x, ξ ((v,s),x) = φ (s,x)) (s : I) (x : A) :
    intervalFamily mc' a b ξ left right (v,(s,x)) =
      generalizedPath mc' α β φ (s,x) := by
  change ((first mc' a).trans (second mc' a b ξ left right)) (s,(v,x)) =
    ((firstPath mc' α).trans (secondPath mc' α β φ)) (s,x)
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · change mc'.interval (_,a (v,x)) = mc'.interval (_,α x)
    rw [ha x]
  · change mc'.base (ξ ((v,_),x)) = mc'.base (φ (_,x))
    rw [hξ]

lemma family_at (v : I) (α : A ⟶ A') (β : B ⟶ B')
    (φ : (α ≫ f').hom.Homotopy (f ≫ β).hom)
    (ha : ∀ x, a (v,x) = α x) (hb : ∀ y, b (v,y) = β y)
    (hξ : ∀ s x, ξ ((v,s),x) = φ (s,x)) :
    atTime (family mc mc' a b ξ left right) v = generalized mc' α β φ mc := by
  apply mc.hom_ext
  · intro y
    change family mc mc' a b ξ left right (v,mc.base y) = _
    rw [family_base, generalized_base, hb y]
  · rintro ⟨s,x⟩
    change family mc mc' a b ξ left right (v,mc.interval (s,x)) = _
    rw [family_interval, generalized_interval]
    exact intervalFamily_at mc' a b ξ left right v α β φ ha hξ s x

def squareAt (v : I) :
    (atTime a v ≫ f').hom.Homotopy (f ≫ atTime b v).hom where
  toContinuousMap := ⟨fun p => ξ ((v,p.1),p.2), by fun_prop⟩
  map_zero_left x := left v x
  map_one_left x := right v x

/-- A complete homotopy whose source and target are the literal endpoint generalized maps. -/
def variation :
    (generalized mc' (atTime a 0) (atTime b 0) (squareAt a b ξ left right 0) mc).hom.Homotopy
    (generalized mc' (atTime a 1) (atTime b 1) (squareAt a b ξ left right 1) mc).hom where
  toContinuousMap := family mc mc' a b ξ left right
  map_zero_left z := ConcreteCategory.congr_hom
    (family_at mc mc' a b ξ left right 0 (atTime a 0) (atTime b 0)
      (squareAt a b ξ left right 0) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl)) z
  map_one_left z := ConcreteCategory.congr_hom
    (family_at mc mc' a b ξ left right 1 (atTime a 1) (atTime b 1)
      (squareAt a b ξ left right 1) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl)) z

lemma variation_base (v : I) (y : B) :
    variation mc mc' a b ξ left right (v,mc.base y) = mc'.base (b (v,y)) :=
  family_base mc mc' a b ξ left right v y

lemma variation_free (v : I) (x : A) :
    variation mc mc' a b ξ left right (v,mc.free x) = mc'.free (a (v,x)) :=
  family_free mc mc' a b ξ left right v x

end AutomaticCoherence.MappingCylinderVariation01
