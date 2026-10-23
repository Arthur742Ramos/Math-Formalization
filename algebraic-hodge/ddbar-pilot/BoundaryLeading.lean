module

public import ColumnComponents

/-! A total boundary landing in a column filtration has vertically exact leading term. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem boundary_leading_exact_of_primitive_mem (p q n : ℤ) (hn : p + q = n)
    (u : (total K).X (n - 1)) (hu : u ∈ filtration K p (n - 1)) :
    ∃ b : (K.X p).X (q - 1), incomingVertical K p q b =
      (projection K p q n).hom (((total K).d (n - 1) n).hom u) := by
  have hlo : (projection K (p - 1) q (n - 1)).hom u = 0 := by
    apply projection_kills_next K (p - 1) q (n - 1)
    rw [show p - 1 + 1 = p by lia]
    exact hu
  have hd := d_projection_apply K p q (n - 1) (by lia) u
  rw [show n - 1 + 1 = n by lia, hlo, map_zero, zero_add] at hd
  refine ⟨p.negOnePow • (projection K p (q - 1) (n - 1)).hom u, ?_⟩
  simpa using hd.symm

theorem boundary_leading_exact (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) (u : (total K).X (n - 1))
    (hu : ((total K).d (n - 1) n).hom u ∈ filtration K p n) :
    ∃ b : (K.X p).X (q - 1), incomingVertical K p q b =
      (projection K p q n).hom (((total K).d (n - 1) n).hom u) := by
  let a := (projection K (p - 1) q (n - 1)).hom u
  let b := (projection K p (q - 1) (n - 1)).hom u
  let c := (projection K (p - 1 - 1) (q + 1) (n - 1)).hom u
  have hd := d_projection_apply K p q (n - 1) (by lia) u
  rw [show n - 1 + 1 = n by lia] at hd
  change (projection K p q n).hom (((total K).d (n - 1) n).hom u) =
    ((K.d (p - 1) p).f q).hom a + p.negOnePow • incomingVertical K p q b at hd
  have hlo : (projection K (p - 1) (q + 1) n).hom
      (((total K).d (n - 1) n).hom u) = 0 := by
    apply projection_kills_next K (p - 1) (q + 1) n
    rw [show p - 1 + 1 = p by lia]
    exact hu
  have hdlo := d_projection_apply K (p - 1) (q + 1) (n - 1) (by lia) u
  rw [show n - 1 + 1 = n by lia, show q + 1 - 1 = q by lia, hlo] at hdlo
  change 0 = ((K.d (p - 1 - 1) (p - 1)).f (q + 1)).hom c +
    (p - 1).negOnePow • vertical K (p - 1) q a at hdlo
  have hhzero : ((K.d (p - 1) p).f (q + 1)).hom
      (((K.d (p - 1 - 1) (p - 1)).f (q + 1)).hom c) = 0 :=
    congrArg (fun f => f.hom c) (K.d_f_comp_d_f (p - 1 - 1) (p - 1) p (q + 1))
  have hcomm : vertical K p q (((K.d (p - 1) p).f q).hom a) =
      ((K.d (p - 1) p).f (q + 1)).hom (vertical K (p - 1) q a) :=
    congrArg (fun f => f.hom a) (K.d_comm (p - 1) p q (q + 1))
  have hv : vertical K p q (((K.d (p - 1) p).f q).hom a) = 0 := by
    have he := congrArg (fun t => ((K.d (p - 1) p).f (q + 1)).hom t) hdlo
    simp only [Units.smul_def, map_zero, map_add, map_zsmul] at he
    rw [hhzero, zero_add, ← hcomm] at he
    have hs := congrArg (fun t => ((p - 1).negOnePow : ℤ) • t) he.symm
    simpa [smul_smul, ← Units.val_mul, Int.units_mul_self] using hs
  dsimp only [ImageKernel, horizontal] at hdd
  rw [show p - 1 + 1 = p by lia] at hdd
  have hm : ((K.d (p - 1) p).f q).hom a ∈
      LinearMap.range ((K.d (p - 1) p).f q).hom ⊓ LinearMap.ker (vertical K p q) :=
    ⟨⟨a, rfl⟩, hv⟩
  rw [hdd] at hm
  obtain ⟨w, hw⟩ := hm
  have hc : incomingVertical K p q (((K.d (p - 1) p).f (q - 1)).hom w) =
      ((K.d (p - 1) p).f q).hom (incomingVertical K (p - 1) q w) :=
    congrArg (fun f => f.hom w) (K.d_comm (p - 1) p (q - 1) q)
  refine ⟨((K.d (p - 1) p).f (q - 1)).hom w + p.negOnePow • b, ?_⟩
  change ((K.d (p - 1) p).f q).hom (incomingVertical K (p - 1) q w) =
    ((K.d (p - 1) p).f q).hom a at hw
  rw [map_add, hc, hw, hd]
  simp

end AlgebraicHodgePilot.Column
