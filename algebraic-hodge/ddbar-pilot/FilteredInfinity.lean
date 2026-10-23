module

public import FilteredPages

/-! The genuine stable filtered quotient of total cocycles by cocycles one level higher and boundaries. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Filtered

variable {k : Type} [Field k] {C : CochainComplex (ModuleCat k) ℤ} (F : Filtration C)

def closedCycles (p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ LinearMap.ker (C.d n (n + 1)).hom

def closedBoundaries (p n : ℤ) : Submodule k (C.X n) :=
  F.F p n ⊓ LinearMap.range (C.d (n - 1) n).hom

def closedDenominator (p n : ℤ) : Submodule k (C.X n) :=
  closedCycles F (p + 1) n ⊔ closedBoundaries F p n

theorem closedCycles_le_cycles (r p n : ℤ) : closedCycles F p n ≤ cycles F r p n := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  change (C.d n (n + 1)).hom x ∈ F.F (p + r) (n + 1)
  rw [hx.2]
  exact (F.F (p + r) (n + 1)).zero_mem

def closedToCycles (r p n : ℤ) : closedCycles F p n →ₗ[k] cycles F r p n :=
  Submodule.inclusion (closedCycles_le_cycles F r p n)

theorem closedToCycles_val (r p n : ℤ) (x : closedCycles F p n) :
    (closedToCycles F r p n x).val = x.val := rfl

theorem closedDenominator_le_closedCycles (p n : ℤ) :
    closedDenominator F p n ≤ closedCycles F p n := by
  apply sup_le
  · intro x hx
    exact ⟨F.antitone n (show p ≤ p + 1 by lia) hx.1, hx.2⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨u, hu⟩ := hx.2
    change (C.d n (n + 1)).hom x = 0
    rw [← hu]
    exact congrArg (fun f => f.hom u) (C.d_comp_d (n - 1) n (n + 1))

abbrev InfinityPage (p n : ℤ) :=
  closedCycles F p n ⧸ (closedDenominator F p n).comap (closedCycles F p n).subtype

def infinityQuotient (p n : ℤ) : closedCycles F p n →ₗ[k] InfinityPage F p n :=
  ((closedDenominator F p n).comap (closedCycles F p n).subtype).mkQ

theorem infinityQuotient_surjective (p n : ℤ) :
    Function.Surjective (infinityQuotient F p n) := Submodule.mkQ_surjective _

end AlgebraicHodgePilot.Filtered
