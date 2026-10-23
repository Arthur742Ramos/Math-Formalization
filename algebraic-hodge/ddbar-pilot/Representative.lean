module

public import Integration

/-!
# A genuine correction witness in a mathlib bicomplex

This is the local representative step, not spectral-sequence degeneration.
The square convention is mathlib's commuting convention. The hypothesis is
one of the explicit image/kernel identities in DGMS (5.15)(b).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicHodgePilot

variable {k : Type} [Field k] (K : Bicomplex k)

abbrev horizontal (p q : ℤ) := ((K.d p (p + 1)).f q).hom
abbrev vertical (p q : ℤ) := ((K.X p).d q (q + 1)).hom
abbrev incomingVertical (p q : ℤ) := ((K.X p).d (q - 1) q).hom

/-- The horizontal-image/vertical-kernel identity at `(p+1,q)`.
The right side is the image of an actual composite of linear maps. -/
def ImageKernel (p q : ℤ) : Prop :=
  LinearMap.range (horizontal K p q) ⊓ LinearMap.ker (vertical K (p + 1) q) =
    LinearMap.range ((horizontal K p q).comp (incomingVertical K p q))

/-- Explicit correction of a vertical cocycle by a vertical boundary. -/
theorem exists_closed_correction (p q : ℤ) (hdd : ImageKernel K p q)
    (x : (K.X p).X q) (hx : vertical K p q x = 0) :
    ∃ b : (K.X p).X (q - 1),
      horizontal K p q (x - incomingVertical K p q b) = 0 ∧
      vertical K p q (x - incomingVertical K p q b) = 0 :=
  have hcomm : vertical K (p + 1) q (horizontal K p q x) =
      horizontal K p (q + 1) (vertical K p q x) :=
    congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom (K.d_comm p (p + 1) q (q + 1)))
  have hmem : horizontal K p q x ∈
      LinearMap.range (horizontal K p q) ⊓ LinearMap.ker (vertical K (p + 1) q) :=
    ⟨⟨x, rfl⟩, hcomm.trans ((congrArg (horizontal K p (q + 1)) hx).trans (map_zero _))⟩
  Exists.elim (show horizontal K p q x ∈
      LinearMap.range ((horizontal K p q).comp (incomingVertical K p q)) from hdd ▸ hmem)
    fun b hb =>
      have hb' : horizontal K p q (incomingVertical K p q b) = horizontal K p q x := hb
      have hvv : vertical K p q (incomingVertical K p q b) = 0 :=
        congrArg (fun f => f b) (congrArg ModuleCat.Hom.hom
          ((K.X p).d_comp_d (q - 1) q (q + 1)))
      ⟨b,
        (map_sub (horizontal K p q) x (incomingVertical K p q b)).trans
          ((congrArg (fun t => horizontal K p q x - t) hb').trans (sub_self _)),
        (map_sub (vertical K p q) x (incomingVertical K p q b)).trans
          ((congrArg₂ (fun a b => a - b) hx hvv).trans (sub_self _))⟩

/-- The genuine three-term piece of the vertical column in degree `q`. -/
abbrev verticalSC (p q : ℤ) := (K.X p).sc' (q - 1) q (q + 1)

/-- The canonical comparison to the column's mathlib homology object. -/
noncomputable def verticalHomologyIso (p q : ℤ) :
    (K.X p).homology q ≅ (verticalSC K p q).homology :=
  (K.X p).homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)

/-- Send a concrete vertical cycle to the column's actual homology object. -/
noncomputable def verticalClass (p q : ℤ)
    (z : LinearMap.ker (vertical K p q)) : (K.X p).homology q :=
  (verticalHomologyIso K p q).inv
    ((verticalSC K p q).moduleCatHomologyIso.inv
      ((verticalSC K p q).moduleCatLeftHomologyData.π z))

/-- Every actual vertical homology class admits a representative killed by
both differentials. No boundedness or finite-dimensionality is needed. -/
theorem exists_closed_representative (p q : ℤ) (hdd : ImageKernel K p q)
    (c : (K.X p).homology q) :
    ∃ z : LinearMap.ker (vertical K p q),
      horizontal K p q z = 0 ∧ verticalClass K p q z = c :=
  let S := verticalSC K p q
  let c' := S.moduleCatHomologyIso.hom ((verticalHomologyIso K p q).hom c)
  Exists.elim ((LinearMap.range S.moduleCatToCycles).mkQ_surjective c') fun x hx =>
    let x₀ : LinearMap.ker (vertical K p q) := x
    have hx' : S.moduleCatLeftHomologyData.π x₀ = c' := hx
    Exists.elim (exists_closed_correction K p q hdd x₀.val x₀.property) fun b ⟨hb, hv⟩ =>
      let y : LinearMap.ker (vertical K p q) := ⟨x₀.val - incomingVertical K p q b, hv⟩
      have hxy : S.moduleCatLeftHomologyData.π y = S.moduleCatLeftHomologyData.π x₀ :=
        (Submodule.Quotient.eq _).2 ⟨-b, Subtype.ext (by
          change incomingVertical K p q (-b) = (x₀.val - incomingVertical K p q b) - x₀.val
          simp [map_neg, sub_sub_cancel_left])⟩
      ⟨y, hb, calc
        verticalClass K p q y =
            (verticalHomologyIso K p q).inv (S.moduleCatHomologyIso.inv
              (S.moduleCatLeftHomologyData.π x₀)) :=
          congrArg (fun t => (verticalHomologyIso K p q).inv (S.moduleCatHomologyIso.inv t)) hxy
        _ = (verticalHomologyIso K p q).inv (S.moduleCatHomologyIso.inv c') :=
          congrArg (fun t => (verticalHomologyIso K p q).inv (S.moduleCatHomologyIso.inv t)) hx'
        _ = c := by simp [c']⟩

end AlgebraicHodgePilot
