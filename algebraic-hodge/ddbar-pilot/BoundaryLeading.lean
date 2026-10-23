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
      (projection K p q n).hom (((total K).d (n - 1) n).hom u) :=
  have hN : n - 1 + 1 = n := sub_add_cancel n 1
  have hlo : (projection K (p - 1) q (n - 1)).hom u = 0 :=
    projection_kills_next K (p - 1) q (n - 1) (by rw [sub_add_cancel p 1]; exact hu)
  have hd := d_projection_apply K p q (n - 1) (hn.trans hN.symm) u
  ⟨p.negOnePow • (projection K p (q - 1) (n - 1)).hom u, by
    rw [hN, hlo, map_zero, zero_add] at hd
    simpa using hd.symm⟩

theorem boundary_leading_exact (p q n : ℤ) (hn : p + q = n)
    (hdd : ImageKernel K (p - 1) q) (u : (total K).X (n - 1))
    (hu : ((total K).d (n - 1) n).hom u ∈ filtration K p n) :
    ∃ b : (K.X p).X (q - 1), incomingVertical K p q b =
      (projection K p q n).hom (((total K).d (n - 1) n).hom u) :=
  let a := (projection K (p - 1) q (n - 1)).hom u
  let b := (projection K p (q - 1) (n - 1)).hom u
  let c := (projection K (p - 1 - 1) (q + 1) (n - 1)).hom u
  have hd : (projection K p q n).hom (((total K).d (n - 1) n).hom u) =
      ((K.d (p - 1) p).f q).hom a + p.negOnePow • incomingVertical K p q b := by
    have h := d_projection_apply K p q (n - 1) (hn.trans (sub_add_cancel n 1).symm) u
    rw [sub_add_cancel n 1] at h
    exact h
  have hlo : (projection K (p - 1) (q + 1) n).hom
      (((total K).d (n - 1) n).hom u) = 0 :=
    projection_kills_next K (p - 1) (q + 1) n (by
      simpa only [show p - 1 + 1 = p by lia -abstractProof] using hu)
  have hdlo : 0 = ((K.d (p - 1 - 1) (p - 1)).f (q + 1)).hom c +
      (p - 1).negOnePow • vertical K (p - 1) q a := by
    have h := d_projection_apply K (p - 1) (q + 1) (n - 1) (by lia -abstractProof) u
    rw [sub_add_cancel n 1, show q + 1 - 1 = q by lia -abstractProof, hlo] at h
    exact h
  have hhzero : ((K.d (p - 1) p).f (q + 1)).hom
      (((K.d (p - 1 - 1) (p - 1)).f (q + 1)).hom c) = 0 :=
    congrArg (fun f => f.hom c) (K.d_f_comp_d_f (p - 1 - 1) (p - 1) p (q + 1))
  have hcomm : vertical K p q (((K.d (p - 1) p).f q).hom a) =
      ((K.d (p - 1) p).f (q + 1)).hom (vertical K (p - 1) q a) :=
    congrArg (fun f => f.hom a) (K.d_comm (p - 1) p q (q + 1))
  have hv : vertical K p q (((K.d (p - 1) p).f q).hom a) = 0 :=
    (smul_eq_zero_iff_eq (p - 1).negOnePow).mp (by
      have he := congrArg (fun t => ((K.d (p - 1) p).f (q + 1)).hom t) hdlo
      simpa only [Units.smul_def, map_zero, map_add, map_zsmul,
        hhzero, zero_add, ← hcomm] using he.symm)
  Exists.elim (show horizontal K (p - 1) q a ∈
      LinearMap.range ((horizontal K (p - 1) q).comp (incomingVertical K (p - 1) q)) from
    hdd ▸ ⟨⟨a, rfl⟩, Eq.mpr (congrArg (fun j =>
      vertical K j q (((K.d (p - 1) j).f q).hom a) = 0) (sub_add_cancel p 1)) hv⟩) fun w hw =>
    have hw' : ((K.d (p - 1) p).f q).hom (incomingVertical K (p - 1) q w) =
        ((K.d (p - 1) p).f q).hom a :=
      Eq.mp (congrArg (fun j => ((K.d (p - 1) j).f q).hom (incomingVertical K (p - 1) q w) =
        ((K.d (p - 1) j).f q).hom a) (sub_add_cancel p 1)) hw
    have hc : incomingVertical K p q (((K.d (p - 1) p).f (q - 1)).hom w) =
        ((K.d (p - 1) p).f q).hom (incomingVertical K (p - 1) q w) :=
      congrArg (fun f => f.hom w) (K.d_comm (p - 1) p (q - 1) q)
    ⟨((K.d (p - 1) p).f (q - 1)).hom w + p.negOnePow • b,
      (map_add (incomingVertical K p q) _ _).trans
        ((congrArg₂ (fun s t => s + t) (hc.trans hw')
          (show incomingVertical K p q (p.negOnePow • b) = p.negOnePow • incomingVertical K p q b from
            map_zsmul (incomingVertical K p q) (p.negOnePow : ℤ) b)).trans hd.symm)⟩

end AlgebraicHodgePilot.Column
