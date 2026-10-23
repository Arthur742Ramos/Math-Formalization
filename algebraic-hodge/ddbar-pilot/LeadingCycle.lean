module

public import ColumnComponents
public import VerticalClass

/-! The leading component of a filtered cycle is an actual vertical cycle. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem leading_vertical_closed (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : (total K).X n) (hx : x ∈ Filtered.cycles (filtered K) r p n) :
    vertical K p q ((projection K p q n).hom x) = 0 :=
  have hlo : (projection K (p - 1) (q + 1) n).hom x = 0 :=
    projection_kills_next K (p - 1) (q + 1) n (by
      rw [sub_add_cancel p 1]
      exact hx.1)
  have hhi : (projection K p (q + 1) (n + 1)).hom
      (((total K).d n (n + 1)).hom x) = 0 :=
    projection_kills_next K p (q + 1) (n + 1)
      (filtration_antitone K (n + 1) (show p + 1 ≤ p + r by lia -abstractProof) hx.2)
  have hd : 0 = p.negOnePow • vertical K p q ((projection K p q n).hom x) := by
    have h := d_projection_apply K p (q + 1) n (by lia -abstractProof) x
    rw [show q + 1 - 1 = q by lia -abstractProof, hhi, hlo, map_zero, zero_add] at h
    exact h
  (smul_eq_zero_iff_eq p.negOnePow).mp hd.symm

noncomputable def leadingCycleMap (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) :
    Filtered.cycles (filtered K) r p n →ₗ[k] LinearMap.ker (vertical K p q) :=
  ((projection K p q n).hom.domRestrict (Filtered.cycles (filtered K) r p n)).codRestrict _
    fun x => leading_vertical_closed K r p q n hn hr x.val x.property

noncomputable def leadingClassMap (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r) :
    Filtered.cycles (filtered K) r p n →ₗ[k] (K.X p).homology q :=
  (verticalClassMap K p q).comp (leadingCycleMap K r p q n hn hr)

theorem leadingCycleMap_val (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (z : Filtered.cycles (filtered K) r p n) :
    (leadingCycleMap K r p q n hn hr z).val = (projection K p q n).hom z.val := rfl

theorem leadingClassMap_zero_of_next (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.cycles (filtered K) r p n) (hx : x.val ∈ filtration K (p + 1) n) :
    leadingClassMap K r p q n hn hr x = 0 := by
  have hz : leadingCycleMap K r p q n hn hr x = 0 := by
    apply Subtype.ext
    exact projection_kills_next K p q n hx
  change verticalClassMap K p q (leadingCycleMap K r p q n hn hr x) = 0
  rw [hz, map_zero]

end AlgebraicHodgePilot.Column
