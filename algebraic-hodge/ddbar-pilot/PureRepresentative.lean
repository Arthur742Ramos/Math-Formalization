module

public import LeadingCycle

/-! Pure-column representatives and signed boundary corrections in totalization. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem pure_vertical_cycle_mem (p q n : ℤ) (hn : p + q = n)
    (z : LinearMap.ker (vertical K p q)) :
    (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) 1 p n :=
  have hz : ((K.X p).d q (q + 1)).hom z.val = 0 := z.property
  have hd : ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) =
      (K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) q (n + 1)).hom (((K.d p (p + 1)).f q).hom z.val) := by
    have h := congrArg (fun f => f.hom z.val) (inclusion_d K p q n (n + 1) hn)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      hz, map_zero, smul_zero, add_zero] using h
  ⟨inclusion_mem_filtration K p p q n hn (le_refl p) z.val,
    show ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) ∈
      filtration K (p + 1) (n + 1) from
    hd.symm ▸ inclusionOrZero_mem_filtration K (p + 1) (p + 1) q (n + 1) (le_refl _) _⟩

theorem pure_biclosed_mem (r p q n : ℤ) (hn : p + q = n)
    (z : LinearMap.ker (vertical K p q)) (hz : horizontal K p q z.val = 0) :
    (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) r p n :=
  have hd : ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) = 0 := by
    subst n
    exact total_closed_of_biclosed K p q z.val hz z.property
  ⟨inclusion_mem_filtration K p p q n hn (le_refl p) z.val,
    show ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) ∈
      filtration K (p + r) (n + 1) from
    hd.symm ▸ (filtration K (p + r) (n + 1)).zero_mem⟩

theorem leadingCycleMap_pure (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (z : LinearMap.ker (vertical K p q))
    (hz : (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) r p n) :
    leadingCycleMap K r p q n hn hr ⟨_, hz⟩ = z := by
  apply Subtype.ext
  exact congrArg (fun f => f.hom z.val) (inclusion_projection_eq K p q n hn)

theorem projection_d_pure (p q n : ℤ) (hn : p + q = n)
    (b : (K.X p).X (q - 1)) :
    (projection K p q n).hom
      (((total K).d (n - 1) n).hom
        ((inclusion K p (q - 1) (n - 1) (by lia -abstractProof)).hom b)) =
      p.negOnePow • incomingVertical K p q b :=
  have hi : p + (q - 1) = n - 1 := by lia -abstractProof
  let u := (inclusion K p (q - 1) (n - 1) hi).hom b
  have hu : u ∈ filtration K p (n - 1) :=
    inclusion_mem_filtration K p p (q - 1) (n - 1) hi (le_refl p) b
  have hlo : (projection K (p - 1) q (n - 1)).hom u = 0 :=
    projection_kills_next K (p - 1) q (n - 1) (by
      simpa only [sub_add_cancel p 1] using hu)
  have hp : (projection K p (q - 1) (n - 1)).hom u = b :=
    congrArg (fun f => f.hom b) (inclusion_projection_eq K p (q - 1) (n - 1) hi)
  have hd := d_projection_apply K p q (n - 1) (hn.trans (sub_add_cancel n 1).symm) u
  show (projection K p q n).hom (((total K).d (n - 1) n).hom u) =
    p.negOnePow • incomingVertical K p q b from by
    rw [sub_add_cancel n 1, hlo, hp, map_zero, zero_add] at hd
    exact hd

end AlgebraicHodgePilot.Column
