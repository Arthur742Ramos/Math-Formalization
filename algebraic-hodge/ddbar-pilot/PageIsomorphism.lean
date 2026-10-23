module

public import PageComparison

/-! First-page identification without d'd'', and all-page identification under explicit identities. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem pageClassMap_injective (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hdd : ImageKernel K (p - 1) q) :
    Function.Injective (pageClassMap K r p q n hn hr hdd) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := Filtered.quotient_surjective (filtered K) r p n z
  change pageClassMap K r p q n hn hr hdd (Filtered.quotient (filtered K) r p n x) = 0 at hz
  rw [pageClassMap_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (leading_class_zero_mem_denominator K r p q n hn hr x hz)

theorem firstPageClassMap_injective (p q n : ℤ) (hn : p + q = n) :
    Function.Injective (firstPageClassMap K p q n hn) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := Filtered.quotient_surjective (filtered K) 1 p n z
  change firstPageClassMap K p q n hn (Filtered.quotient (filtered K) 1 p n x) = 0 at hz
  rw [firstPageClassMap_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (leading_class_zero_mem_denominator K 1 p q n hn (le_refl 1) x hz)

theorem firstPageClassMap_surjective (p q n : ℤ) (hn : p + q = n) :
    Function.Surjective (firstPageClassMap K p q n hn) := by
  intro c
  obtain ⟨z, hz⟩ := verticalClassMap_surjective K p q c
  let x : Filtered.cycles (filtered K) 1 p n :=
    ⟨(inclusion K p q n hn).hom z.val, pure_vertical_cycle_mem K p q n hn z⟩
  refine ⟨Filtered.quotient (filtered K) 1 p n x, ?_⟩
  rw [firstPageClassMap_quotient]
  change verticalClassMap K p q (leadingCycleMap K 1 p q n hn (le_refl 1) x) = c
  rw [leadingCycleMap_pure]
  exact hz

theorem pageClassMap_surjective (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q) :
    Function.Surjective (pageClassMap K r p q n hn hr hddIn) := by
  intro c
  obtain ⟨z, hz, hc⟩ := exists_closed_representative K p q hddOut c
  let x : Filtered.cycles (filtered K) r p n :=
    ⟨(inclusion K p q n hn).hom z.val, pure_biclosed_mem K r p q n hn z hz⟩
  refine ⟨Filtered.quotient (filtered K) r p n x, ?_⟩
  rw [pageClassMap_quotient]
  change verticalClassMap K p q (leadingCycleMap K r p q n hn hr x) = c
  rw [leadingCycleMap_pure, verticalClassMap_apply]
  exact hc

/-- E1 of the genuine column-filtered quotient is vertical cohomology for every bicomplex. -/
noncomputable def firstPageIso (p q n : ℤ) (hn : p + q = n) :
    ModuleCat.of k (Filtered.Page (filtered K) 1 p n) ≅ (K.X p).homology q :=
  (LinearEquiv.ofBijective (firstPageClassMap K p q n hn)
    ⟨firstPageClassMap_injective K p q n hn, firstPageClassMap_surjective K p q n hn⟩).toModuleIso

/-- All positive pages of the genuine filtered quotient identify with vertical cohomology. -/
noncomputable def pageIso (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q) :
    ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅ (K.X p).homology q :=
  (LinearEquiv.ofBijective (pageClassMap K r p q n hn hr hddIn)
    ⟨pageClassMap_injective K r p q n hn hr hddIn,
      pageClassMap_surjective K r p q n hn hr hddIn hddOut⟩).toModuleIso

end AlgebraicHodgePilot.Column
