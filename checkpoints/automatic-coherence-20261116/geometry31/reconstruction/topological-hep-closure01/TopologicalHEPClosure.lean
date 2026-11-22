import IntervalSkeletalDescent

/-! SOURCE ONLY / UNCOMPILED. Actual homotopy-extension closure under
composition and pushout. These are closure theorems, not assumed HEP for any
simplicial realization. No arbitrary product-preserves-colimits premise. -/
noncomputable section
open CategoryTheory Limits
open scoped Topology
namespace AutomaticCoherence.TopologicalHEPClosure01
open AutomaticCoherence.IntervalSkeletalDescent01 (cylinder cylinder_left cylinder_right)
abbrev Time := unitInterval

/-- Separate initial and boundary data, with no prescribed terminal interior. -/
def HasHEP {A B : TopCat.{0}} (i : A ⟶ B) : Prop :=
  ∀ (Y : TopCat.{0}) (f : C(B,Y)) (h : C(Time × A,Y)),
    (∀ a : A, h (0,a) = f (i a)) →
    ∃ H : C(Time × B,Y),
      (∀ b : B, H (0,b) = f b) ∧
      (∀ (t : Time) (a : A), H (t,i a) = h (t,a))

lemma hasHEP_id (A : TopCat.{0}) : HasHEP (𝟙 A) := by
  intro Y f h corner
  exact ⟨h, corner, fun _ _ => rfl⟩

/-- Two successive genuine extension operations; no target-space condition. -/
lemma hasHEP_comp {A B C : TopCat.{0}} (i : A ⟶ B) (j : B ⟶ C)
    (hi : HasHEP i) (hj : HasHEP j) : HasHEP (i ≫ j) := by
  intro Y f h corner
  obtain ⟨HB, hB0, hBi⟩ := hi Y (f.comp j.hom) h corner
  obtain ⟨HC, hC0, hCj⟩ := hj Y f HB hB0
  refine ⟨HC, hC0, ?_⟩
  intro t a
  exact (hCj t (i a)).trans (hBi t a)

/-- Isomorphisms have HEP by transporting the supplied boundary homotopy. -/
lemma hasHEP_iso {A B : TopCat.{0}} (e : A ≅ B) : HasHEP e.hom := by
  intro Y f h corner
  let H : C(Time × B,Y) := h.comp
    ⟨fun p => (p.1, e.inv p.2), continuous_fst.prodMk
      (e.inv.hom.continuous.comp continuous_snd)⟩
  refine ⟨H, ?_, ?_⟩
  · intro b
    change h (0,e.inv b) = f b
    exact (corner (e.inv b)).trans
      (congrArg f (ConcreteCategory.congr_hom e.inv_hom_id b))
  · intro t a
    change h (t,e.inv (e.hom a)) = h (t,a)
    exact congrArg (fun x => h (t,x)) (ConcreteCategory.congr_hom e.hom_inv_id a)

/-- A pushout transports HEP along the opposite leg. The actual cylinder
is descended by compact-open currying into C(Time,Y), not by a presumed
preservation theorem for products in arbitrary TopCat. -/
lemma hasHEP_pushout {B X Y P : TopCat.{0}}
    {f : B ⟶ X} {g : B ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (hp : IsPushout f g inl inr) (hg : HasHEP g) : HasHEP inl := by
  intro T F HX corner
  let hB : C(Time × B,T) := HX.comp
    ⟨fun p => (p.1, f p.2), continuous_fst.prodMk
      (f.hom.continuous.comp continuous_snd)⟩
  have hc : ∀ b : B, hB (0,b) = (F.comp inr.hom) (g b) := by
    intro b
    change HX (0,f b) = F (inr (g b))
    exact (corner (f b)).trans (congrArg F (ConcreteCategory.congr_hom hp.w b))
  obtain ⟨HY, hY0, hYg⟩ := hg T (F.comp inr.hom) hB hc
  have agree : ∀ (t : Time) (b : B), HX (t,f b) = HY (t,g b) := by
    intro t b
    exact (hYg t b).symm
  let H := cylinder hp HX HY agree
  have hL : ∀ (t : Time) (x : X), H (t,inl x) = HX (t,x) :=
    cylinder_left hp HX HY agree
  have hR : ∀ (t : Time) (y : Y), H (t,inr y) = HY (t,y) :=
    cylinder_right hp HX HY agree
  refine ⟨H, ?_, hL⟩
  intro p
  have hz : TopCat.ofHom
      (⟨fun q => H (0,q), by fun_prop⟩ : C(P,T)) = TopCat.ofHom F := by
    apply hp.hom_ext
    · apply ConcreteCategory.hom_ext
      intro x
      exact (hL 0 x).trans (corner x)
    · apply ConcreteCategory.hom_ext
      intro y
      exact (hR 0 y).trans (hY0 y)
  exact ConcreteCategory.congr_hom hz p

end AutomaticCoherence.TopologicalHEPClosure01
