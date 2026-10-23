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
    (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) 1 p n := by
  refine ⟨inclusion_mem_filtration K p p q n hn (le_refl p) z.val, ?_⟩
  have hd := congrArg (fun f => f.hom z.val) (inclusion_d K p q n (n + 1) hn)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at hd
  change ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) ∈
    filtration K (p + 1) (n + 1)
  rw [hd]
  have hz := z.property
  change ((K.X p).d q (q + 1)).hom z.val = 0 at hz
  rw [hz, map_zero, smul_zero, add_zero]
  exact inclusionOrZero_mem_filtration K (p + 1) (p + 1) q (n + 1) (le_refl _) _

theorem pure_biclosed_mem (r p q n : ℤ) (hn : p + q = n)
    (z : LinearMap.ker (vertical K p q)) (hz : horizontal K p q z.val = 0) :
    (inclusion K p q n hn).hom z.val ∈ Filtered.cycles (filtered K) r p n := by
  refine ⟨inclusion_mem_filtration K p p q n hn (le_refl p) z.val, ?_⟩
  change ((total K).d n (n + 1)).hom ((inclusion K p q n hn).hom z.val) ∈
    filtration K (p + r) (n + 1)
  subst n
  dsimp only [inclusion]
  rw [total_closed_of_biclosed K p q z.val hz z.property]
  exact (filtration K (p + r) (p + q + 1)).zero_mem

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
      p.negOnePow • incomingVertical K p q b := by
  let u := (inclusion K p (q - 1) (n - 1) (by lia -abstractProof)).hom b
  have hu : u ∈ filtration K p (n - 1) :=
    inclusion_mem_filtration K p p (q - 1) (n - 1) (by lia -abstractProof) (le_refl p) b
  have hlo : (projection K (p - 1) q (n - 1)).hom u = 0 := by
    apply projection_kills_next K (p - 1) q (n - 1)
    rw [show p - 1 + 1 = p by lia -abstractProof]
    exact hu
  have hp : (projection K p (q - 1) (n - 1)).hom u = b :=
    congrArg (fun f => f.hom b) (inclusion_projection_eq K p (q - 1) (n - 1) (by lia -abstractProof))
  have hd := d_projection_apply K p q (n - 1) (by lia -abstractProof) u
  rw [show n - 1 + 1 = n by lia -abstractProof, hlo, hp, map_zero, zero_add] at hd
  exact hd

end AlgebraicHodgePilot.Column
