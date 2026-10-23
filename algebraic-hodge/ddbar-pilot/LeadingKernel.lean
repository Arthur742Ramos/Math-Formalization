module

public import PureRepresentative

/-! Exact leading components characterize the kernel of the filtered-page comparison. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem leading_class_zero_mem_denominator (r p q n : ℤ) (hn : p + q = n) (hr : 1 ≤ r)
    (x : Filtered.cycles (filtered K) r p n)
    (hx : leadingClassMap K r p q n hn hr x = 0) :
    x.val ∈ Filtered.denominator (filtered K) r p n := by
  obtain ⟨b, hb⟩ := (verticalClassMap_eq_zero_iff K p q
    (leadingCycleMap K r p q n hn hr x)).mp hx
  change incomingVertical K p q b = (projection K p q n).hom x.val at hb
  let u := (inclusion K p (q - 1) (n - 1) (by lia -abstractProof)).hom (p.negOnePow • b)
  let du := ((total K).d (n - 1) n).hom u
  have hu : u ∈ filtration K p (n - 1) :=
    inclusion_mem_filtration K p p (q - 1) (n - 1) (by lia -abstractProof) (le_refl _) _
  have hdu : du ∈ filtration K p n := differential_preserves_filtration K p (n - 1) n hu
  have hproj : (projection K p q n).hom du = (projection K p q n).hom x.val := by
    have hd := projection_d_pure K p q n hn (p.negOnePow • b)
    change (projection K p q n).hom du = _ at hd
    rw [hd]
    simpa [Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self] using hb
  have hddu : ((total K).d n (n + 1)).hom du = 0 :=
    congrArg (fun f => f.hom u) ((total K).d_comp_d (n - 1) n (n + 1))
  let y := x.val - du
  have hy : y ∈ filtration K (p + 1) n := by
    apply mem_next_of_projection_zero K p q n hn
    · exact (filtration K p n).sub_mem x.property.1 hdu
    · change (projection K p q n).hom (x.val - du) = 0
      rw [map_sub, hproj, sub_self]
  have hyc : y ∈ Filtered.cycles (filtered K) (r - 1) (p + 1) n := by
    refine ⟨hy, ?_⟩
    change ((total K).d n (n + 1)).hom (x.val - du) ∈
      filtration K (p + 1 + (r - 1)) (n + 1)
    rw [map_sub, hddu, sub_zero, show p + 1 + (r - 1) = p + r by lia -abstractProof]
    exact x.property.2
  have hdb : du ∈ Filtered.boundaries (filtered K) (r - 1) p n :=
    ⟨hdu, u, filtration_antitone K (n - 1) (show p - (r - 1) ≤ p by lia -abstractProof) hu, rfl⟩
  exact Submodule.mem_sup.mpr ⟨y, hyc, du, hdb, sub_add_cancel x.val du⟩

end AlgebraicHodgePilot.Column
