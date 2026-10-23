module

public import CohomologyClass
public import FilteredInfinity

/-!
# The infinity quotient and associated graded of actual total cohomology

The induced filtration consists of actual cohomology classes of cocycles in
each filtered subcomplex. The comparison below is generic: it uses no
boundedness and no image/kernel identity or degeneration assumption.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Filtered

variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)

def closedCycleToCycle (p n : ℤ) :
    closedCycles F p n →ₗ[k] LinearMap.ker (C.d n (n + 1)).hom :=
  (closedCycles F p n).subtype.codRestrict _ fun x => x.property.2

noncomputable def closedClassMap (p n : ℤ) : closedCycles F p n →ₗ[k] C.homology n :=
  (cohomologyClassMap C n).comp (closedCycleToCycle F p n)

/-- The induced filtration on the actual homology object: classes of filtered cocycles. -/
noncomputable def cohomologyFiltration (p n : ℤ) : Submodule k (C.homology n) :=
  LinearMap.range (closedClassMap F p n)

theorem cohomologyFiltration_antitone (n : ℤ) :
    Antitone (fun p => cohomologyFiltration F p n) := by
  intro p p' hpp c hc
  obtain ⟨z, rfl⟩ := hc
  refine ⟨⟨z.val, F.antitone n hpp z.property.1, z.property.2⟩, ?_⟩
  rfl

noncomputable def closedClassToFiltration (p n : ℤ) :
    closedCycles F p n →ₗ[k] cohomologyFiltration F p n :=
  (closedClassMap F p n).codRestrict _ fun x => ⟨x, rfl⟩

/-- The genuine associated graded quotient of the induced cohomology filtration. -/
abbrev GradedCohomology (p n : ℤ) :=
  cohomologyFiltration F p n ⧸
    (cohomologyFiltration F (p + 1) n).comap (cohomologyFiltration F p n).subtype

noncomputable def closedToGraded (p n : ℤ) :
    closedCycles F p n →ₗ[k] GradedCohomology F p n :=
  ((cohomologyFiltration F (p + 1) n).comap
    (cohomologyFiltration F p n).subtype).mkQ.comp (closedClassToFiltration F p n)

theorem closedToGraded_zero_iff (p n : ℤ) (x : closedCycles F p n) :
    closedToGraded F p n x = 0 ↔ x.val ∈ closedDenominator F p n := by
  have hzero : closedToGraded F p n x = 0 ↔
      closedClassMap F p n x ∈ cohomologyFiltration F (p + 1) n :=
    Submodule.Quotient.mk_eq_zero _
  rw [hzero]
  constructor
  · rintro ⟨y, hy⟩
    let xp := closedCycleToCycle F p n x
    let yp := closedCycleToCycle F (p + 1) n y
    have hclass : cohomologyClassMap C n (xp - yp) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hy.symm
    obtain ⟨b, hb⟩ := (cohomologyClassMap_eq_zero_iff C n (xp - yp)).mp hclass
    have hdiff : x.val - y.val ∈ closedBoundaries F p n := by
      refine ⟨(F.F p n).sub_mem x.property.1
        (F.antitone n (show p ≤ p + 1 by lia -abstractProof) y.property.1), b, ?_⟩
      exact hb
    exact Submodule.mem_sup.mpr ⟨y.val, y.property, x.val - y.val, hdiff,
      add_sub_cancel _ _⟩
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    have hbc : b ∈ closedCycles F p n :=
      closedDenominator_le_closedCycles F p n
        ((show closedBoundaries F p n ≤ closedDenominator F p n from le_sup_right) hb)
    have hbb : cohomologyClassMap C n (closedCycleToCycle F p n ⟨b, hbc⟩) = 0 :=
      (cohomologyClassMap_eq_zero_iff C n _).mpr hb.2
    have hac : a ∈ closedCycles F p n :=
      ⟨F.antitone n (show p ≤ p + 1 by lia -abstractProof) ha.1, ha.2⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    have he : (⟨a, hac⟩ : closedCycles F p n) + ⟨b, hbc⟩ = x := Subtype.ext hab
    rw [← he, map_add]
    change closedClassMap F (p + 1) n ⟨a, ha⟩ =
      closedClassMap F p n ⟨a, hac⟩ + cohomologyClassMap C n (closedCycleToCycle F p n ⟨b, hbc⟩)
    rw [hbb, add_zero]
    rfl

/-- Canonical map from the actual infinity quotient to associated graded cohomology. -/
noncomputable def infinityToGraded (p n : ℤ) :
    InfinityPage F p n →ₗ[k] GradedCohomology F p n :=
  ((closedDenominator F p n).comap (closedCycles F p n).subtype).liftQ
    (closedToGraded F p n) fun x hx => (closedToGraded_zero_iff F p n x).mpr hx

@[simp]
theorem infinityToGraded_quotient (p n : ℤ) (x : closedCycles F p n) :
    infinityToGraded F p n (infinityQuotient F p n x) = closedToGraded F p n x := rfl

theorem infinityToGraded_injective (p n : ℤ) :
    Function.Injective (infinityToGraded F p n) := by
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  obtain ⟨x, rfl⟩ := infinityQuotient_surjective F p n z
  change infinityToGraded F p n (infinityQuotient F p n x) = 0 at hz
  rw [infinityToGraded_quotient] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((closedToGraded_zero_iff F p n x).mp hz)

theorem infinityToGraded_surjective (p n : ℤ) :
    Function.Surjective (infinityToGraded F p n) := by
  intro c
  obtain ⟨h, rfl⟩ := ((cohomologyFiltration F (p + 1) n).comap
    (cohomologyFiltration F p n).subtype).mkQ_surjective c
  obtain ⟨x, hx⟩ := h.property
  refine ⟨infinityQuotient F p n x, ?_⟩
  rw [infinityToGraded_quotient]
  change _ = Submodule.mkQ _ h
  apply congrArg (Submodule.mkQ _)
  apply Subtype.ext
  exact hx

/-- The stable quotient is the associated graded of the actual cohomology object. -/
noncomputable def infinityGradedIso (p n : ℤ) :
    ModuleCat.of k (InfinityPage F p n) ≅ ModuleCat.of k (GradedCohomology F p n) :=
  (LinearEquiv.ofBijective (infinityToGraded F p n)
    ⟨infinityToGraded_injective F p n, infinityToGraded_surjective F p n⟩).toModuleIso

@[simp]
theorem infinityGradedIso_quotient (p n : ℤ) (x : closedCycles F p n) :
    (infinityGradedIso F p n).hom (infinityQuotient F p n x) =
      closedToGraded F p n x := rfl

end AlgebraicHodgePilot.Filtered
