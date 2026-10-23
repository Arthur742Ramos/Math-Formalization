module

public import PageIsomorphism

/-! Vanishing of every positive-page differential on the genuine filtered quotients. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem boundary_leading_exact_next (p q n : ℤ) (hn : p + q = n + 1)
    (hdd : ImageKernel K (p - 1) q) (u : (total K).X n)
    (hu : ((total K).d n (n + 1)).hom u ∈ filtration K p (n + 1)) :
    ∃ b : (K.X p).X (q - 1), incomingVertical K p q b =
      (projection K p q (n + 1)).hom (((total K).d n (n + 1)).hom u) := by
  have h := boundary_leading_exact K p q (n + 1) hn hdd
  rw [show n + 1 - 1 = n by lia] at h
  exact h u hu

/-- All actual induced differentials vanish, simultaneously for every `r ≥ 1`.
The pages and their differentials were constructed from total cycles/boundaries
before this hypothesis was used. -/
theorem all_differentials_zero (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p n : ℤ) (hr : 1 ≤ r) :
    Filtered.differential (filtered K) r p n = 0 := by
  apply LinearMap.ext
  intro c
  apply pageClassMap_injective K r (p + r) (n + 1 - (p + r)) (n + 1) (by lia) hr
    (hdd (p + r - 1) (n + 1 - (p + r)))
  simp only [LinearMap.zero_apply, map_zero]
  obtain ⟨x, rfl⟩ := Filtered.quotient_surjective (filtered K) r p n c
  rw [Filtered.differential_quotient, pageClassMap_quotient]
  change verticalClassMap K (p + r) (n + 1 - (p + r))
    (leadingCycleMap K r (p + r) (n + 1 - (p + r)) (n + 1) (by lia) hr
      (Filtered.differentialOnCycles (filtered K) r p n x)) = 0
  apply (verticalClassMap_eq_zero_iff K (p + r) (n + 1 - (p + r)) _).mpr
  obtain ⟨b, hb⟩ := boundary_leading_exact_next K (p + r) (n + 1 - (p + r)) n (by lia)
    (hdd (p + r - 1) (n + 1 - (p + r))) x.val x.property.2
  exact ⟨b, hb⟩

end AlgebraicHodgePilot.Column
