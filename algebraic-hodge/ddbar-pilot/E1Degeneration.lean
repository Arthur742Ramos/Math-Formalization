module

public import SequenceTransitions
public import InfinityComparison
public import BoundedFiltration
public import GradedCohomology

/-! E1 degeneration of the genuine column-filtered total complex and bounded convergence. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem exists_closed_page_representative (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (c : Filtered.Page (filtered K) r p n) :
    ∃ x : Filtered.closedCycles (filtered K) p n,
      Filtered.quotient (filtered K) r p n
        (Filtered.closedToCycles (filtered K) r p n x) = c := by
  obtain ⟨x, hx⟩ := Filtered.infinityQuotient_surjective (filtered K) p n
    ((pageToInfinityIso K hdd r p q n hn hr).hom c)
  refine ⟨x, ?_⟩
  apply (ModuleCat.mono_iff_injective (pageToInfinityIso K hdd r p q n hn hr).hom).mp inferInstance
  rw [pageToInfinityIso_closed]
  exact hx

noncomputable def pageToGradedIso (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) :
    ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅
      ModuleCat.of k (Filtered.GradedCohomology (filtered K) p n) :=
  pageToInfinityIso K hdd r p q n hn hr ≪≫ Filtered.infinityGradedIso (filtered K) p n

theorem pageToGradedIso_closed (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.closedCycles (filtered K) p n) :
    (pageToGradedIso K hdd r p q n hn hr).hom
      (Filtered.quotient (filtered K) r p n (Filtered.closedToCycles (filtered K) r p n x)) =
      Filtered.closedToGraded (filtered K) p n x := by
  change (Filtered.infinityGradedIso (filtered K) p n).hom
    ((pageToInfinityIso K hdd r p q n hn hr).hom _) = _
  rw [pageToInfinityIso_closed, Filtered.infinityGradedIso_quotient]

/-- Bounded convergence uses equality of actual page submodules, independently of d′d″. -/
noncomputable def boundedStableGradedIso (L U : ℤ) (hs : HorizontalSupport K L U)
    (r p n : ℤ) (hu : U < p + r) (hl : p - r + 1 ≤ L) :
    ModuleCat.of k (Filtered.Page (filtered K) r p n) ≅
      ModuleCat.of k (Filtered.GradedCohomology (filtered K) p n) :=
  stablePageIso K L U hs r p n hu hl ≪≫ Filtered.infinityGradedIso (filtered K) p n

/-- All higher differentials vanish, and the genuine quotients eventually stabilize.
The first-page identification is `firstPageIso`; convergence is `boundedStableGradedIso`.
The rectangle hypothesis is actual component vanishing, with no degeneration field. -/
theorem bounded_e1_degeneration (hdd : ∀ p q : ℤ, ImageKernel K p q)
    (L U B T : ℤ) (hs : RectangularSupport K L U B T) :
    (∀ r : ℤ, 1 ≤ r → ∀ p n : ℤ, Filtered.differential (filtered K) r p n = 0) ∧
    (∀ p n : ℤ, ∃ R : ℤ, 1 ≤ R ∧ ∀ r : ℤ, R ≤ r →
      Filtered.cycles (filtered K) r p n = Filtered.closedCycles (filtered K) p n ∧
      Filtered.denominator (filtered K) r p n = Filtered.closedDenominator (filtered K) p n) := by
  constructor
  · intro r hr p n
    exact all_differentials_zero K hdd r p n hr
  · intro p n
    exact eventually_stable K L U (rectangularSupport_horizontal K L U B T hs) p n

end AlgebraicHodgePilot.Column
