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
    Function.Surjective (verticalClassMap K p q) :=
  fun c =>
    let S := verticalSC K p q
    let c' := S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)
    Exists.elim ((LinearMap.range S.moduleCatToCycles).mkQ_surjective c') fun x hx =>
      let z : LinearMap.ker (vertical K p q) := x
      have hx' : S.moduleCatLeftHomologyData.π z = c' := hx
      ⟨z, show (verticalHomologyIso K p q).inv
          (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = c from
        (congrArg (fun t => (verticalHomologyIso K p q).inv
          (S.moduleCatHomologyIso.inv t)) hx').trans (by simp [c'])⟩

theorem verticalClassMap_eq_zero_iff (p q : ℤ) (z : LinearMap.ker (vertical K p q)) :
    verticalClassMap K p q z = 0 ↔
      ∃ b : (K.X p).X (q - 1), incomingVertical K p q b = z.val :=
  let S := verticalSC K p q
  ⟨fun h =>
    have hq : S.moduleCatLeftHomologyData.π z = 0 := by
      have hh := congrArg (fun c => S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)) h
      simp [verticalClassMap, S] at hh
      exact hh
    Exists.elim ((Submodule.Quotient.mk_eq_zero _).mp hq) fun b hb =>
      ⟨b, congrArg Subtype.val hb⟩,
    fun ⟨b, hb⟩ =>
      have hz : S.moduleCatToCycles b = z := Subtype.ext hb
      have hq : S.moduleCatLeftHomologyData.π z = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨b, hz⟩
      show (verticalHomologyIso K p q).inv
          (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π z)) = 0 from
        (congrArg (fun t => (verticalHomologyIso K p q).inv
          (S.moduleCatHomologyIso.inv t)) hq).trans (by simp)⟩

end AlgebraicHodgePilot
