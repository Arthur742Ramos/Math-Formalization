module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-! Integration checks only: no degeneration theorem is asserted here. -/
open CategoryTheory

@[expose] public section

namespace AlgebraicHodgePilot

abbrev Bicomplex (k : Type) [Field k] :=
  HomologicalComplex₂ (ModuleCat k) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

noncomputable abbrev total {k : Type} [Field k] (K : Bicomplex k) :
    CochainComplex (ModuleCat k) ℤ := K.total (ComplexShape.up ℤ)

-- The arbitrary starting-page parameter really accepts 1. This does NOT
-- construct the spectral sequence associated to K.
abbrev E1Sequence (k : Type) [Field k] :=
  CohomologicalSpectralSequence (ModuleCat k) 1

-- The existing spectral-object construction is checked at its actual E2 index.
#check Abelian.SpectralObject.spectralSequence
#check HomologicalComplex₂.d_comm
#check HomologicalComplex.d_comp_d
#check ShortComplex.moduleCatHomologyIso

end AlgebraicHodgePilot
