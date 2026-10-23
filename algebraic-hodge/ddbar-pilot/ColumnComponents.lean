module

public import ColumnFiltration

/-! Component formulas for the actual total differential. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicHodgePilot.Column

variable {k : Type} [Field k] (K : Bicomplex k)

theorem inclusionOrZero_projection_ne (a b p q n : ℤ) (h : ¬ (a = p ∧ b = q)) :
    K.ιTotalOrZero (ComplexShape.up ℤ) a b n ≫ projection K p q n = 0 := by
  by_cases hab : a + b = n
  · rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) a b n hab]
    exact inclusion_projection_ne K a b p q n hab h
  · rw [K.ιTotalOrZero_eq_zero (ComplexShape.up ℤ) a b n hab, zero_comp]

theorem inclusionOrZero_projection_eq (p q n : ℤ) (h : p + q = n) :
    K.ιTotalOrZero (ComplexShape.up ℤ) p q n ≫ projection K p q n = 𝟙 _ := by
  rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) p q n h]
  exact inclusion_projection_eq K p q n h

theorem inclusion_d (a b n m : ℤ) (hab : a + b = n) :
    inclusion K a b n hab ≫ (total K).d n m =
      (K.d a (a + 1)).f b ≫ K.ιTotalOrZero (ComplexShape.up ℤ) (a + 1) b m +
      a.negOnePow • ((K.X a).d b (b + 1) ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) a (b + 1) m) := by
  dsimp only [inclusion, AlgebraicHodgePilot.total]
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    K.d₁_eq' (ComplexShape.up ℤ) (i₁ := a) (i₁' := a + 1) (by rfl),
    K.d₂_eq' (ComplexShape.up ℤ) a (i₂ := b) (i₂' := b + 1) (by rfl)]
  simp [ComplexShape.ε₁, ComplexShape.ε₂]

theorem d_projection (p q n : ℤ) (hn : p + q = n + 1) :
    (total K).d n (n + 1) ≫ projection K p q (n + 1) =
      projection K (p - 1) q n ≫ (K.d (p - 1) p).f q +
      p.negOnePow • (projection K p (q - 1) n ≫ (K.X p).d (q - 1) q) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  change a + b = n at hab
  change inclusion K a b n hab ≫ _ = inclusion K a b n hab ≫ _
  rw [← Category.assoc, inclusion_d, Preadditive.add_comp,
    Linear.units_smul_comp]
  simp only [Preadditive.comp_add, Linear.comp_units_smul, Category.assoc]
  by_cases ha : a = p - 1
  · have hb : b = q := by lia
    subst a b
    rw [show p - 1 + 1 = p by lia]
    rw [inclusionOrZero_projection_eq K p q (n + 1) hn,
      inclusionOrZero_projection_ne K (p - 1) (q + 1) p q (n + 1) (by intro h; lia),
      inclusion_projection_eq_assoc K (p - 1) q n hab,
      inclusion_projection_ne_assoc K (p - 1) q p (q - 1) n hab (by intro h; lia)]
    simp
  · by_cases ha' : a = p
    · have hb : b = q - 1 := by lia
      subst a b
      rw [show q - 1 + 1 = q by lia]
      rw [inclusionOrZero_projection_ne K (p + 1) (q - 1) p q (n + 1) (by intro h; lia),
        inclusionOrZero_projection_eq K p q (n + 1) hn,
        inclusion_projection_ne_assoc K p (q - 1) (p - 1) q n hab (by intro h; lia),
        inclusion_projection_eq_assoc K p (q - 1) n hab]
      simp
    · rw [inclusionOrZero_projection_ne K (a + 1) b p q (n + 1) (by intro h; lia),
        inclusionOrZero_projection_ne K a (b + 1) p q (n + 1) (by intro h; lia),
        inclusion_projection_ne_assoc K a b (p - 1) q n hab (by intro h; exact ha h.1),
        inclusion_projection_ne_assoc K a b p (q - 1) n hab (by intro h; exact ha' h.1)]
      simp

theorem d_projection_apply (p q n : ℤ) (hn : p + q = n + 1)
    (x : (total K).X n) :
    (projection K p q (n + 1)).hom (((total K).d n (n + 1)).hom x) =
      ((K.d (p - 1) p).f q).hom ((projection K (p - 1) q n).hom x) +
      p.negOnePow • ((K.X p).d (q - 1) q).hom ((projection K p (q - 1) n).hom x) := by
  exact congrArg (fun f => f.hom x) (d_projection K p q n hn)

end AlgebraicHodgePilot.Column
