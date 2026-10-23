module

public import Representative

/-! Linear and exactness properties of the canonical vertical homology class map. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot

variable {k : Type} [Field k] (K : Bicomplex k)

noncomputable def verticalClassMap (p q : ℤ) :
    LinearMap.ker (vertical K p q) →ₗ[k] (K.X p).homology q :=
  (verticalHomologyIso K p q).inv.hom.comp
    ((verticalSC K p q).moduleCatHomologyIso.inv.hom.comp
      (verticalSC K p q).moduleCatLeftHomologyData.π.hom)

theorem verticalClassMap_apply (p q : ℤ) (z : LinearMap.ker (vertical K p q)) :
    verticalClassMap K p q z = verticalClass K p q z := rfl

theorem verticalClassMap_surjective (p q : ℤ) :
    Function.Surjective (verticalClassMap K p q) := by
  intro c
  let S := verticalSC K p q
  let c' := S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)
  obtain ⟨x, hx⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective c'
  let z : LinearMap.ker (vertical K p q) := x
  change S.moduleCatLeftHomologyData.π z = c' at hx
  refine ⟨z, ?_⟩
  change (verticalHomologyIso K p q).inv
    (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = c
  rw [hx]
  simp [c']

theorem verticalClassMap_eq_zero_iff (p q : ℤ) (z : LinearMap.ker (vertical K p q)) :
    verticalClassMap K p q z = 0 ↔
      ∃ b : (K.X p).X (q - 1), incomingVertical K p q b = z.val := by
  let S := verticalSC K p q
  constructor
  · intro h
    have hh := congrArg
      (fun c => S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)) h
    have hq : S.moduleCatLeftHomologyData.π z = 0 := by
      simp [verticalClassMap, S] at hh
      exact hh
    have hm : z ∈ LinearMap.range S.moduleCatToCycles :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hz : S.moduleCatToCycles b = z := Subtype.ext hb
    have hq : S.moduleCatLeftHomologyData.π z = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hz⟩
    change (verticalHomologyIso K p q).inv
      (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = 0
    rw [hq]
    simp

end AlgebraicHodgePilot
