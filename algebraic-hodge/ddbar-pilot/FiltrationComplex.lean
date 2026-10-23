module

public import FilteredPages

/-! A filtration by submodules is realized as a functor of actual cochain complexes. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Filtered

variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ}
    (F : Filtration C)

noncomputable def filteredComplex (p : ℤ) : CochainComplex (ModuleCat k) ℤ where
  X n := ModuleCat.of k (F.F p n)
  d n m := ModuleCat.ofHom
    (((C.d n m).hom.domRestrict (F.F p n)).codRestrict (F.F p m)
      fun x => F.preserves p n m x.property)
  shape n m h := by
    ext x
    exact congrArg (fun f => f.hom x.val) (C.shape n m h)
  d_comp_d' n m l _ _ := by
    ext x
    exact congrArg (fun f => f.hom x.val) (C.d_comp_d n m l)

noncomputable def filteredInclusion (p : ℤ) : filteredComplex F p ⟶ C where
  f n := ModuleCat.ofHom (F.F p n).subtype
  comm' _ _ _ := rfl

noncomputable def filteredMap (p p' : ℤ) (h : p' ≤ p) :
    filteredComplex F p ⟶ filteredComplex F p' where
  f n := ModuleCat.ofHom (Submodule.inclusion (F.antitone n h))
  comm' n m _ := by ext x; rfl

/-- The increasing filtration functor `i ↦ F^(-i)`. -/
noncomputable def filtrationFunctor : ℤ ⥤ CochainComplex (ModuleCat k) ℤ where
  obj i := filteredComplex F (-i)
  map {i j} f := filteredMap F (-i) (-j) (neg_le_neg (leOfHom f))
  map_id _ := by ext n x; rfl
  map_comp _ _ := by ext n x; rfl

end AlgebraicHodgePilot.Filtered
