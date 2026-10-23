module

public import AssociatedSequence

/-! The spectral-sequence recurrence agrees with standard quotient classes on common cycles. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem zeroPageHomologyIso_π (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
    (pageComplex K hdd r hr).homologyπ pq ≫ (zeroPageHomologyIso K hdd r hr pq).hom =
      (pageComplex K hdd r hr).iCycles pq := by
  let h := ShortComplex.LeftHomologyData.ofZeros ((pageComplex K hdd r hr).sc pq)
    (pageDifferential_zero K hdd r hr _ _) (pageDifferential_zero K hdd r hr _ _)
  exact h.homologyπ_comp_homologyIso_hom.trans h.cyclesIso_hom_comp_i

theorem pageIso_quotient (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.cycles (filtered K) r p n) :
    (pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q)).hom
      (Filtered.quotient (filtered K) r p n x) = leadingClassMap K r p q n hn hr x := rfl

theorem page_comparison_common_representative (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r s p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (x : (total K).X n)
    (hx : x ∈ Filtered.cycles (filtered K) r p n)
    (hx' : x ∈ Filtered.cycles (filtered K) s p n) :
    (pageIso K s p q n hn hs (hdd (p - 1) q) (hdd p q)).inv
      ((pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q)).hom
        (Filtered.quotient (filtered K) r p n ⟨x, hx⟩)) =
      Filtered.quotient (filtered K) s p n ⟨x, hx'⟩ := by
  apply (ModuleCat.mono_iff_injective
    (pageIso K s p q n hn hs (hdd (p - 1) q) (hdd p q)).hom).mp inferInstance
  rw [Iso.inv_hom_id_apply]
  change pageClassMap K r p q n hn hr (hdd (p - 1) q)
      (Filtered.quotient (filtered K) r p n ⟨x, hx⟩) =
    pageClassMap K s p q n hn hs (hdd (p - 1) q)
      (Filtered.quotient (filtered K) s p n ⟨x, hx'⟩)
  rw [pageClassMap_quotient, pageClassMap_quotient]
  apply congrArg (verticalClassMap K p q)
  apply Subtype.ext
  rfl

/-- The inverse zero-differential homology comparison really is the homology
class map, by `zeroPageHomologyIso_π`. On every common representative the
recurrence sends its r-class to its (r+1)-class. -/
theorem associatedSequence_transition (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r s : ℤ) (hrs : r + 1 = s) (hr : 1 ≤ r) (p q : ℤ)
    (x : (total K).X (p + q))
    (hx : x ∈ Filtered.cycles (filtered K) r p (p + q))
    (hx' : x ∈ Filtered.cycles (filtered K) s p (p + q)) :
    ((associatedSequence K hdd).iso r s (p, q) hrs hr).hom
      ((zeroPageHomologyIso K hdd r hr (p, q)).inv
        (Filtered.quotient (filtered K) r p (p + q) ⟨x, hx⟩)) =
      Filtered.quotient (filtered K) s p (p + q) ⟨x, hx'⟩ := by
  change (pageIso K s p q (p + q) rfl (by lia -abstractProof) (hdd (p - 1) q) (hdd p q)).inv
    ((pageIso K r p q (p + q) rfl hr (hdd (p - 1) q) (hdd p q)).hom
      ((zeroPageHomologyIso K hdd r hr (p, q)).hom
        ((zeroPageHomologyIso K hdd r hr (p, q)).inv
          (Filtered.quotient (filtered K) r p (p + q) ⟨x, hx⟩)))) = _
  rw [Iso.inv_hom_id_apply]
  exact page_comparison_common_representative K hdd r s p q (p + q) rfl hr (by lia -abstractProof) x hx hx'

end AlgebraicHodgePilot.Column
