module

public import Integration

/-! Concrete cycle classes in the actual homology object of a cochain complex. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Filtered

variable {k : Type} [Field k] (C : CochainComplex (ModuleCat k) ℤ)

abbrev cohomologySC (n : ℤ) := C.sc' (n - 1) n (n + 1)

noncomputable def cohomologyIso (n : ℤ) : C.homology n ≅ (cohomologySC C n).homology :=
  C.homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)

/-- The canonical class map to actual mathlib cohomology, not a supplied quotient. -/
noncomputable def cohomologyClassMap (n : ℤ) :
    LinearMap.ker (C.d n (n + 1)).hom →ₗ[k] C.homology n :=
  (cohomologyIso C n).inv.hom.comp
    ((cohomologySC C n).moduleCatHomologyIso.inv.hom.comp
      (cohomologySC C n).moduleCatLeftHomologyData.π.hom)

theorem cohomologyClassMap_surjective (n : ℤ) :
    Function.Surjective (cohomologyClassMap C n) := by
  intro c
  let S := cohomologySC C n
  let c' := S.moduleCatHomologyIso.hom ((cohomologyIso C n).hom c)
  obtain ⟨x, hx⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective c'
  let z : LinearMap.ker (C.d n (n + 1)).hom := x
  change S.moduleCatLeftHomologyData.π z = c' at hx
  refine ⟨z, ?_⟩
  change (cohomologyIso C n).inv
    (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = c
  rw [hx]
  simp [c']

theorem cohomologyClassMap_eq_zero_iff (n : ℤ)
    (z : LinearMap.ker (C.d n (n + 1)).hom) :
    cohomologyClassMap C n z = 0 ↔
      ∃ b : C.X (n - 1), (C.d (n - 1) n).hom b = z.val := by
  let S := cohomologySC C n
  constructor
  · intro h
    have hh := congrArg
      (fun c => S.moduleCatHomologyIso.hom ((cohomologyIso C n).hom c)) h
    have hq : S.moduleCatLeftHomologyData.π z = 0 := by
      simp [cohomologyClassMap, S] at hh
      exact hh
    have hm : z ∈ LinearMap.range S.moduleCatToCycles :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hz : S.moduleCatToCycles b = z := Subtype.ext hb
    have hq : S.moduleCatLeftHomologyData.π z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hz⟩
    change (cohomologyIso C n).inv
      (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = 0
    rw [hq]
    simp

end AlgebraicHodgePilot.Filtered
