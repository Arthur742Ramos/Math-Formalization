import MappingCylinderCollar

/-! SOURCE ONLY / UNCOMPILED. Literal strict mapping-cylinder map and removal
of the constant comparison collar. No inverse or gluing theorem is assumed. -/
noncomputable section
open CategoryTheory ContinuousMap
open scoped Topology
namespace AutomaticCoherence.MappingCylinderStrictMap01
open MappingCylinderFoundation01
open MappingCylinderCollar01

variable {A B A' B' : TopCat.{0}} {f : A ⟶ B} {f' : A' ⟶ B'}
  (mc : MappingCylinder f) (mc' : MappingCylinder f')
  (α : A ⟶ A') (β : B ⟶ B') (h : f ≫ β = α ≫ f')

def intervalMap : C(I × A,mc'.M) :=
  ⟨fun p => mc'.interval (p.1,α p.2), by fun_prop⟩

include h in
lemma attached (a : A) : intervalMap mc' α (1,a) = mc'.base (β (f a)) :=
  (mc'.interval_one (α a)).trans
    (congrArg mc'.base (ConcreteCategory.congr_hom h a)).symm

def strictMap : mc.M ⟶ mc'.M :=
  mc.desc (β ≫ mc'.base) (intervalMap mc' α) (attached mc' α β h)

lemma strictMap_base (b : B) : strictMap mc mc' α β h (mc.base b) = mc'.base (β b) :=
  mc.desc_base _ _ _ b

lemma strictMap_interval (s : I) (a : A) :
    strictMap mc mc' α β h (mc.interval (s,a)) = mc'.interval (s,α a) :=
  mc.desc_interval _ _ _ (s,a)

lemma strictMap_free (a : A) :
    strictMap mc mc' α β h (mc.free a) = mc'.free (α a) :=
  (mc.desc_free _ _ _ a).trans (mc'.interval_zero (α a))

/-- The comparison path is literally constant, with only its final type cast. -/
def constantComparison : (α ≫ f').hom.Homotopy (f ≫ β).hom :=
  (ContinuousMap.Homotopy.refl (α ≫ f').hom).cast rfl
    (congrArg (fun q : A ⟶ B' => q.hom) h.symm)

lemma generalized_interval_collar (s : I) (a : A) :
    generalized mc' α β (constantComparison α β h) mc (mc.interval (s,a)) =
      mc'.interval (collarParameter s,α a) := by
  rw [generalized_interval]
  change ((firstPath mc' α).trans (secondPath mc' α β
    (constantComparison α β h))) (s,a) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with hs
  · apply congrArg (fun t : I => mc'.interval (t,α a))
    apply Subtype.ext
    change 2 * (s : ℝ) = Path.Homotopy.transReflReparamAux s
    simp only [Path.Homotopy.transReflReparamAux, if_pos hs]
  · change mc'.base (f' (α a)) = mc'.interval (collarParameter s,α a)
    have hc : collarParameter s = 1 := by
      apply Subtype.ext
      change Path.Homotopy.transReflReparamAux s = 1
      simp only [Path.Homotopy.transReflReparamAux, if_neg hs]
    rw [hc]
    exact (mc'.interval_one (α a)).symm

/-- The generalized map differs only by the existing source collar. -/
lemma generalized_eq_collared :
    generalized mc' α β (constantComparison α β h) mc =
      collaredIdentity mc ≫ strictMap mc mc' α β h := by
  apply mc.hom_ext
  · intro b
    change generalized mc' α β (constantComparison α β h) mc (mc.base b) =
      strictMap mc mc' α β h (collaredIdentity mc (mc.base b))
    rw [generalized_base, collaredIdentity_base, strictMap_base]
  · rintro ⟨s,a⟩
    change generalized mc' α β (constantComparison α β h) mc (mc.interval (s,a)) =
      strictMap mc mc' α β h (collaredIdentity mc (mc.interval (s,a)))
    rw [generalized_interval_collar, collaredIdentity_interval, strictMap_interval]

/-- Exact generalized-to-strict homotopy, from postcomposing the actual collar removal. -/
def collarRemoval :
    (generalized mc' α β (constantComparison α β h) mc).hom.Homotopy
      (strictMap mc mc' α β h).hom :=
  ((ContinuousMap.Homotopy.refl (strictMap mc mc' α β h).hom).comp
    (MappingCylinderCollar01.collarRemoval mc)).cast
      (congrArg (fun q : mc.M ⟶ mc'.M => q.hom)
        (generalized_eq_collared mc mc' α β h).symm) rfl

lemma collarRemoval_base (t : I) (b : B) :
    collarRemoval mc mc' α β h (t,mc.base b) = mc'.base (β b) := by
  change strictMap mc mc' α β h (MappingCylinderCollar01.family mc (t,mc.base b)) = _
  rw [MappingCylinderCollar01.family_base, strictMap_base]

lemma collarRemoval_free (t : I) (a : A) :
    collarRemoval mc mc' α β h (t,mc.free a) = mc'.free (α a) := by
  change strictMap mc mc' α β h (MappingCylinderCollar01.family mc (t,mc.free a)) = _
  rw [MappingCylinderCollar01.family_free, strictMap_free]

end AutomaticCoherence.MappingCylinderStrictMap01
