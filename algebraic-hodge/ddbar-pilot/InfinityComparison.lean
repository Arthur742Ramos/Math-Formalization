module

public import SequenceTransitions
public import FilteredInfinity

/-! The stable filtered quotient is canonically vertical cohomology under the explicit identities. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

noncomputable def closedLeadingMap (p q n : ℤ) (hn : p + q = n) :
    Filtered.closedCycles (filtered K) p n →ₗ[k] (K.X p).homology q :=
  (leadingClassMap K 1 p q n hn (le_refl 1)).comp
    (Filtered.closedToCycles (filtered K) 1 p n)

theorem closedLeadingMap_zero_of_next (p q n : ℤ) (hn : p + q = n)
    (x : Filtered.closedCycles (filtered K) p n) (hx : x.val ∈ filtration K (p + 1) n) :
    closedLeadingMap K p q n hn x = 0 :=
  leadingClassMap_zero_of_next K 1 p q n hn (le_refl 1)
    (Filtered.closedToCycles (filtered K) 1 p n x) hx

theorem closedLeadingMap_zero_of_boundary (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) (x : Filtered.closedCycles (filtered K) p n)
    (hx : x.val ∈ Filtered.closedBoundaries (filtered K) p n) :
    closedLeadingMap K p q n hn x = 0 := by
  obtain ⟨u, hu⟩ := hx.2
  have huf : ((total K).d (n - 1) n).hom u ∈ filtration K p n := by rw [hu]; exact hx.1
  obtain ⟨b, hb⟩ := boundary_leading_exact K p q n hn hdd u huf
  change verticalClassMap K p q _ = 0
  apply (verticalClassMap_eq_zero_iff K p q _).mpr
  refine ⟨b, ?_⟩
  change incomingVertical K p q b = (projection K p q n).hom x.val
  rw [← hu]
  exact hb

theorem closedLeadingMap_kills_denominator (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) :
    (Filtered.closedDenominator (filtered K) p n).comap
      (Filtered.closedCycles (filtered K) p n).subtype ≤
        LinearMap.ker (closedLeadingMap K p q n hn) := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  have hac : a ∈ Filtered.closedCycles (filtered K) p n :=
    Filtered.closedDenominator_le_closedCycles (filtered K) p n
      ((show Filtered.closedCycles (filtered K) (p + 1) n ≤
        Filtered.closedDenominator (filtered K) p n from le_sup_left) ha)
  have hbc : b ∈ Filtered.closedCycles (filtered K) p n :=
    Filtered.closedDenominator_le_closedCycles (filtered K) p n
      ((show Filtered.closedBoundaries (filtered K) p n ≤
        Filtered.closedDenominator (filtered K) p n from le_sup_right) hb)
  have he : (⟨a, hac⟩ : Filtered.closedCycles (filtered K) p n) + ⟨b, hbc⟩ = x :=
    Subtype.ext hab
  change closedLeadingMap K p q n hn x = 0
  rw [← he, map_add, closedLeadingMap_zero_of_next K p q n hn ⟨a, hac⟩ ha.1,
    closedLeadingMap_zero_of_boundary K p q n hn hdd ⟨b, hbc⟩ hb, add_zero]

theorem closedLeadingMap_zero_mem_denominator (p q n : ℤ) (hn : p + q = n)
    (x : Filtered.closedCycles (filtered K) p n) (hx : closedLeadingMap K p q n hn x = 0) :
    x.val ∈ Filtered.closedDenominator (filtered K) p n := by
  have hz := leading_class_zero_mem_denominator K 1 p q n hn (le_refl 1)
    (Filtered.closedToCycles (filtered K) 1 p n x) hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  have hda : ((total K).d n (n + 1)).hom a = 0 := by
    have h := congrArg (fun t => ((total K).d n (n + 1)).hom t) hab
    rw [map_add, Filtered.boundary_closed (filtered K) (1 - 1) p n hb, add_zero] at h
    change ((total K).d n (n + 1)).hom a = ((total K).d n (n + 1)).hom x.val at h
    rw [x.property.2] at h
    exact h
  have hbb : b ∈ Filtered.closedBoundaries (filtered K) p n := by
    obtain ⟨u, _, hu⟩ := hb.2
    exact ⟨hb.1, u, hu⟩
  exact Submodule.mem_sup.mpr ⟨a, ⟨ha.1, hda⟩, b, hbb, hab⟩

noncomputable def infinityClassMap (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) :
    Filtered.InfinityPage (filtered K) p n →ₗ[k] (K.X p).homology q :=
  ((Filtered.closedDenominator (filtered K) p n).comap
    (Filtered.closedCycles (filtered K) p n).subtype).liftQ
      (closedLeadingMap K p q n hn) (closedLeadingMap_kills_denominator K p q n hn hdd)

@[simp]
theorem infinityClassMap_quotient (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) (x : Filtered.closedCycles (filtered K) p n) :
    infinityClassMap K p q n hn hdd (Filtered.infinityQuotient (filtered K) p n x) =
      closedLeadingMap K p q n hn x := rfl

theorem infinityClassMap_injective (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) :
    Function.Injective (infinityClassMap K p q n hn hdd) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := Filtered.infinityQuotient_surjective (filtered K) p n z
  change infinityClassMap K p q n hn hdd (Filtered.infinityQuotient (filtered K) p n x) = 0 at hz
  rw [infinityClassMap_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr (closedLeadingMap_zero_mem_denominator K p q n hn x hz)

theorem infinityClassMap_surjective (p q n : ℤ) (hn : p + q = n)
    (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q) :
    Function.Surjective (infinityClassMap K p q n hn hddIn) := by
  intro c
  obtain ⟨z, hz, hc⟩ := exists_closed_representative K p q hddOut c
  have hclosed : ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) = 0 := by
    subst n
    exact total_closed_of_biclosed K p q z.val hz z.property
  let x : Filtered.closedCycles (filtered K) p n :=
    ⟨(inclusion K p q n hn).hom z.val,
      inclusion_mem_filtration K p p q n hn (le_refl _) z.val, hclosed⟩
  refine ⟨Filtered.infinityQuotient (filtered K) p n x, ?_⟩
  rw [infinityClassMap_quotient]
  change verticalClassMap K p q
    (leadingCycleMap K 1 p q n hn (le_refl 1) (Filtered.closedToCycles (filtered K) 1 p n x)) = c
  have he : leadingCycleMap K 1 p q n hn (le_refl 1)
      (Filtered.closedToCycles (filtered K) 1 p n x) = z := by
    apply Subtype.ext
    change (projection K p q n).hom ((inclusion K p q n hn).hom z.val) = z.val
    exact congrArg (fun f => f.hom z.val) (inclusion_projection_eq K p q n hn)
  rw [he, verticalClassMap_apply]
  exact hc

noncomputable def infinityIso (p q n : ℤ) (hn : p + q = n)
    (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q) :
    ModuleCat.of k (Filtered.InfinityPage (filtered K) p n) ≅ (K.X p).homology q :=
  (LinearEquiv.ofBijective (infinityClassMap K p q n hn hddIn)
    ⟨infinityClassMap_injective K p q n hn hddIn,
      infinityClassMap_surjective K p q n hn hddIn hddOut⟩).toModuleIso

noncomputable def pageToInfinityIso (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) :
    ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅
      ModuleCat.of k (Filtered.InfinityPage (filtered K) p n) :=
  pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q) ≪≫
    (infinityIso K p q n hn (hdd (p - 1) q) (hdd p q)).symm

theorem infinityIso_quotient (p q n : ℤ) (hn : p + q = n)
    (hddIn : ImageKernel K (p - 1) q) (hddOut : ImageKernel K p q)
    (x : Filtered.closedCycles (filtered K) p n) :
    (infinityIso K p q n hn hddIn hddOut).hom
      (Filtered.infinityQuotient (filtered K) p n x) = closedLeadingMap K p q n hn x := rfl

theorem closedCycles_leading_independent (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.closedCycles (filtered K) p n) :
    leadingCycleMap K r p q n hn hr (Filtered.closedToCycles (filtered K) r p n x) =
      leadingCycleMap K 1 p q n hn (le_refl 1) (Filtered.closedToCycles (filtered K) 1 p n x) := by
  apply Subtype.ext
  rw [leadingCycleMap_val, leadingCycleMap_val, Filtered.closedToCycles_val, Filtered.closedToCycles_val]

theorem pageIso_closed_quotient (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.closedCycles (filtered K) p n) :
    (pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q)).hom
      (Filtered.quotient (filtered K) r p n (Filtered.closedToCycles (filtered K) r p n x)) =
        closedLeadingMap K p q n hn x := by
  rw [pageIso_quotient]
  exact congrArg (verticalClassMap K p q) (closedCycles_leading_independent K r p q n hn hr x)

theorem iso_common_image {X Y Z : ModuleCat k} (e : X ≅ Z) (f : Y ≅ Z)
    (x : X) (y : Y) (h : e.hom x = f.hom y) : (e ≪≫ f.symm).hom x = y := by
  change f.inv (e.hom x) = y
  rw [h, Iso.hom_inv_id_apply]

/-- This comparison carries the class of an actual total cocycle to its stable class. -/
theorem pageToInfinityIso_closed (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.closedCycles (filtered K) p n) :
    (pageToInfinityIso K hdd r p q n hn hr).hom
      (Filtered.quotient (filtered K) r p n
        (Filtered.closedToCycles (filtered K) r p n x)) =
      Filtered.infinityQuotient (filtered K) p n x := by
  have he : (pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q)).hom
      (Filtered.quotient (filtered K) r p n (Filtered.closedToCycles (filtered K) r p n x)) =
    (infinityIso K p q n hn (hdd (p - 1) q) (hdd p q)).hom
      (Filtered.infinityQuotient (filtered K) p n x) := by
    rw [pageIso_closed_quotient, infinityIso_quotient]
  exact iso_common_image (pageIso K r p q n hn hr (hdd (p - 1) q) (hdd p q))
    (infinityIso K p q n hn (hdd (p - 1) q) (hdd p q)) _ _ he

end AlgebraicHodgePilot.Column
