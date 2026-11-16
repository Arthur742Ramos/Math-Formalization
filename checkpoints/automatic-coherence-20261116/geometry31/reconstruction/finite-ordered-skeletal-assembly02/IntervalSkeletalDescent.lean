import OrderedSkeletalAttach
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Basic

/-! SOURCE ONLY / UNCOMPILED. Interval-cylinder descent through an ACTUAL
pushout. It uses compact-open currying and local compactness of I only at
uncurrying; it does not assume arbitrary products preserve topological colimits. -/
noncomputable section
open CategoryTheory Limits
open scoped Topology
namespace AutomaticCoherence.IntervalSkeletalDescent01

abbrev I := unitInterval

/-- Curry in the SPACE variable: the function-space domain is the interval.
This is deliberately not the other curry direction C(I,C(X,Y)). -/
def curryTime {X T : TopCat.{0}} (H : C(I × X, T)) : X ⟶ TopCat.of C(I,T) :=
  TopCat.ofHom ((H.comp ⟨Prod.swap, continuous_swap⟩).curry)

/-- The only local compactness used is I, not the glued space X. -/
def uncurryTime {X T : TopCat.{0}} (h : X ⟶ TopCat.of C(I,T)) : C(I × X,T) :=
  h.hom.uncurry.comp ⟨Prod.swap, continuous_swap⟩

lemma uncurry_curry {X T : TopCat.{0}} (H : C(I × X,T)) :
    uncurryTime (curryTime H) = H := by ext p; rfl

variable {B X Y P T : TopCat.{0}}
  {f : B ⟶ X} {g : B ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
  (hp : IsPushout f g inl inr)
  (HX : C(I × X,T)) (HY : C(I × Y,T))
  (agree : ∀ (t : I) (b : B), HX (t,f b) = HY (t,g b))

include agree in
lemma curry_agrees : f ≫ curryTime HX = g ≫ curryTime HY := by
  apply ConcreteCategory.hom_ext
  intro b
  apply ContinuousMap.ext
  intro t
  exact agree t b

def cylinder : C(I × P,T) :=
  uncurryTime (hp.desc (curryTime HX) (curryTime HY) (curry_agrees HX HY agree))

lemma cylinder_left (t : I) (x : X) :
    cylinder hp HX HY agree (t,inl x) = HX (t,x) := by
  have h := ConcreteCategory.congr_hom
    (hp.inl_desc (curryTime HX) (curryTime HY) (curry_agrees HX HY agree)) x
  exact congrArg (fun k : C(I,T) ↦ k t) h

lemma cylinder_right (t : I) (y : Y) :
    cylinder hp HX HY agree (t,inr y) = HY (t,y) := by
  have h := ConcreteCategory.congr_hom
    (hp.inr_desc (curryTime HX) (curryTime HY) (curry_agrees HX HY agree)) y
  exact congrArg (fun k : C(I,T) ↦ k t) h

/-- Uniqueness in the actual cylinder. These restrictions determine a JOINTLY
continuous map, not merely a family of separately continuous time slices. -/
lemma cylinder_unique (H : C(I × P,T))
    (hl : ∀ t x, H (t,inl x) = HX (t,x))
    (hr : ∀ t y, H (t,inr y) = HY (t,y)) : H = cylinder hp HX HY agree := by
  have hc : curryTime H = curryTime (cylinder hp HX HY agree) := by
    apply hp.hom_ext
    · apply ConcreteCategory.hom_ext
      intro x
      apply ContinuousMap.ext
      intro t
      exact (hl t x).trans (cylinder_left hp HX HY agree t x).symm
    · apply ConcreteCategory.hom_ext
      intro y
      apply ContinuousMap.ext
      intro t
      exact (hr t y).trans (cylinder_right hp HX HY agree t y).symm
  apply ContinuousMap.ext
  intro p
  exact congrArg (fun k : C(I,T) ↦ k p.1) (ConcreteCategory.congr_hom hc p.2)

/-- Actual matching local homotopies descend. Endpoint equalities follow from
the SAME pushout hom_ext, not a claimed point-cover theorem. -/
def homotopy (a b : C(P,T))
    (H : (a.comp inl.hom).Homotopy (b.comp inl.hom))
    (G : (a.comp inr.hom).Homotopy (b.comp inr.hom))
    (h : ∀ t z, H (t,f z) = G (t,g z)) : a.Homotopy b where
  toContinuousMap := cylinder hp H.toContinuousMap G.toContinuousMap h
  map_zero_left := by
    intro x
    have hz : TopCat.ofHom
        (⟨fun y ↦ cylinder hp H.toContinuousMap G.toContinuousMap h (0,y), by fun_prop⟩ : C(P,T)) =
        TopCat.ofHom a := by
      apply hp.hom_ext
      · apply ConcreteCategory.hom_ext
        intro y
        exact (cylinder_left hp H.toContinuousMap G.toContinuousMap h 0 y).trans (H.map_zero_left y)
      · apply ConcreteCategory.hom_ext
        intro y
        exact (cylinder_right hp H.toContinuousMap G.toContinuousMap h 0 y).trans (G.map_zero_left y)
    exact ConcreteCategory.congr_hom hz x
  map_one_left := by
    intro x
    have hz : TopCat.ofHom
        (⟨fun y ↦ cylinder hp H.toContinuousMap G.toContinuousMap h (1,y), by fun_prop⟩ : C(P,T)) =
        TopCat.ofHom b := by
      apply hp.hom_ext
      · apply ConcreteCategory.hom_ext
        intro y
        exact (cylinder_left hp H.toContinuousMap G.toContinuousMap h 1 y).trans (H.map_one_left y)
      · apply ConcreteCategory.hom_ext
        intro y
        exact (cylinder_right hp H.toContinuousMap G.toContinuousMap h 1 y).trans (G.map_one_left y)
    exact ConcreteCategory.congr_hom hz x

/-- The pushout needed for the actual subdivided skeleton is supplied by the
pinned theorem and TWO genuine left adjoints. No product preservation instance
is postulated, and no arbitrary TopCat object is declared exponentiable. -/
lemma realized_sd_skeletal_pushout {A S : SSet.{0}} (i : A ⟶ S) (d : ℕ) :
    IsPushout
      ((SSet.sd ⋙ SSet.toTop).map (SSet.relativeCellComplexOfMono.t i d))
      ((SSet.sd ⋙ SSet.toTop).map (SSet.relativeCellComplexOfMono.l i d))
      ((SSet.sd ⋙ SSet.toTop).map (SSet.relativeCellComplexOfMono.r i d))
      ((SSet.sd ⋙ SSet.toTop).map (SSet.relativeCellComplexOfMono.b i d)) :=
  (SSet.relativeCellComplexOfMono.isPushout i d).map (SSet.sd ⋙ SSet.toTop)

end AutomaticCoherence.IntervalSkeletalDescent01
