module

public import Representative

/-! A biclosed representative gives an actual cocycle in mathlib totalization. -/

@[expose] public section

open CategoryTheory

namespace AlgebraicHodgePilot

variable {k : Type} [Field k] (K : Bicomplex k)

theorem total_closed_of_biclosed (p q : ℤ) (x : (K.X p).X q)
    (hh : horizontal K p q x = 0) (hv : vertical K p q x = 0) :
    ((total K).d (p + q) (p + q + 1)).hom
      ((K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl).hom x) = 0 := by
  change ((K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl ≫
    (K.total (ComplexShape.up ℤ)).d (p + q) (p + q + 1)).hom) x = 0
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [K.d₁_eq' (ComplexShape.up ℤ) (i₁ := p) (i₁' := p + 1) (by rfl),
    K.d₂_eq' (ComplexShape.up ℤ) p (i₂ := q) (i₂' := q + 1) (by rfl)]
  simp only [horizontal, vertical] at hh hv
  simp [ModuleCat.hom_comp, hh, hv]

/-- The correction theorem is sound in the genuine total complex as well as
in vertical homology. This still asserts no spectral-sequence degeneration. -/
theorem exists_total_closed_representative (p q : ℤ) (hdd : ImageKernel K p q)
    (c : (K.X p).homology q) :
    ∃ z : LinearMap.ker (vertical K p q),
      horizontal K p q z = 0 ∧ verticalClass K p q z = c ∧
      ((total K).d (p + q) (p + q + 1)).hom
        ((K.ιTotal (ComplexShape.up ℤ) p q (p + q) rfl).hom z.val) = 0 := by
  obtain ⟨z, hz, hc⟩ := exists_closed_representative K p q hdd c
  exact ⟨z, hz, hc, total_closed_of_biclosed K p q z.val hz z.property⟩

end AlgebraicHodgePilot
