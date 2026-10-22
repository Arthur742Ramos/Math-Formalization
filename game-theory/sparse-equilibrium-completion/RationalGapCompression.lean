/- AI-assisted formalization under the repository Apache-2.0 license.
Constructive solver preparation: real compression at the actual rational grid.
No computational complexity claim. -/
module
public import RationalGapRealDecision
public import MomentCompression
public import AllMassWitness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

noncomputable def rationalSparseFeatures {k m : ℕ} {I : Type}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (i : Fin m) :
    (Fin k ⊕ (Fin (rationalGridSize M r η) ⊕ I)) → ℝ :=
  Sum.elim (fun a => ((-D i a : ℚ) : ℝ))
    (Sum.elim (fun l => ((max (rationalScore D p i-ρ-
      (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ))
      (fun a => (R.coefficient a i : ℝ)))

/-- Real compression preserves every actual finite-grid inequality and every
supplied linear physical constraint. The support bound uses the actual rational
node count, and includes the number of additional rows. -/
theorem rational_gap_real_compression {k m : ℕ} {I : Type} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (x : Fin m → ℝ)
    (hx : ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies x)
    (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ)) :
    ∃ y : Fin m → ℝ,
      ((rationalGapSystem K D p M r ρ η).append R).RealSatisfies y ∧
      (∀ i, 0 ≤ y i) ∧ (∑ i, y i)=(r : ℝ) ∧
      (∀ i, x i=0 → y i=0) ∧
      (Finset.univ.filter fun i => y i ≠ 0).card ≤
        min m (k+rationalGridSize M r η+Fintype.card I+1) := by
  classical
  have hr : (0 : ℝ) ≤ (r : ℝ) := by
    rw [←hm]
    exact Finset.sum_nonneg fun i _ => hq i
  by_cases hz : (r : ℝ)=0
  · have hzero : x=fun _ => 0 := nonnegative_mass_zero x hq (by simpa only [hz] using hm)
    refine ⟨x,hx,hq,hm,fun _ hi => hi,?_⟩
    simp [hzero]
  · obtain ⟨y,hy,hym,hys,hyc,hyf⟩ := finite_feature_compression
      (Fin k ⊕ (Fin (rationalGridSize M r η) ⊕ I)) x
      (rationalSparseFeatures D p M r ρ η R) (r : ℝ) hq hm
      (lt_of_le_of_ne hr (Ne.symm hz))
    have hparts := (rational_linear_real_append_iff _ _ x).mp hx
    refine ⟨y,(rational_linear_real_append_iff _ _ y).mpr ⟨?_,?_⟩,
      hy,hym,hys,Nat.le_min.mpr ⟨?_,?_⟩⟩
    · intro row
      rcases row with i | row
      · change (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*y j) ≤ ((0 : ℚ) : ℝ)
        have he : (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*y j)= -y i := by
          calc
            _ = ∑ j, if j=i then -y j else 0 := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : j=i <;> simp [hj]
            _ = _ := by simp
        rw [he,Rat.cast_zero]
        exact neg_nonpos.mpr (hy i)
      · rcases row with a | row
        · by_cases ha : a.val=0
          · change (∑ j, ((if a.val=0 then (1 : ℚ) else -1 : ℚ) : ℝ)*y j) ≤
              ((if a.val=0 then r else -r : ℚ) : ℝ)
            simpa only [ha,ite_true,Rat.cast_one,one_mul] using le_of_eq hym
          · change (∑ j, ((if a.val=0 then (1 : ℚ) else -1 : ℚ) : ℝ)*y j) ≤
              ((if a.val=0 then r else -r : ℚ) : ℝ)
            simpa only [ha,ite_false,Rat.cast_neg,Rat.cast_one,neg_one_mul,
              Finset.sum_neg_distrib] using neg_le_neg (le_of_eq hym.symm)
        · rcases row with i | row
          · have hh := hparts.1 (.inr (.inr (.inl i)))
            simpa only [RationalLinearSystem.RealSatisfies,rationalGapSystem,
              rationalGapCoefficient,Sum.elim_inr,Sum.elim_inl,Rat.cast_zero,
              zero_mul,Finset.sum_const_zero] using hh
          · rcases row with a | l
            · have he := hyf (.inl a)
              change (∑ i, y i*((-D i a : ℚ) : ℝ))=∑ i, x i*((-D i a : ℚ) : ℝ) at he
              have hh := hparts.1 (.inr (.inr (.inr (.inl a))))
              change (∑ i, ((-D i a : ℚ) : ℝ)*y i) ≤ _
              change (∑ i, ((-D i a : ℚ) : ℝ)*x i) ≤ _ at hh
              calc
                _ = ∑ i, y i*((-D i a : ℚ) : ℝ) :=
                  Finset.sum_congr rfl fun _ _ => mul_comm _ _
                _ = _ := he
                _ ≤ _ := by simpa only [mul_comm] using hh
            · have he := hyf (.inr (.inl l))
              change (∑ i, y i*((max (rationalScore D p i-ρ-
                (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ))=
                ∑ i, x i*((max (rationalScore D p i-ρ-
                  (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ) at he
              have hh := hparts.1 (.inr (.inr (.inr (.inr l))))
              change (∑ i, ((max (rationalScore D p i-ρ-
                (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ)*y i) ≤ _
              change (∑ i, ((max (rationalScore D p i-ρ-
                (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ)*x i) ≤ _ at hh
              calc
                _ = ∑ i, y i*((max (rationalScore D p i-ρ-
                    (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ) :=
                  Finset.sum_congr rfl fun _ _ => mul_comm _ _
                _ = _ := he
                _ ≤ _ := by simpa only [mul_comm] using hh
    · intro a
      have he := hyf (.inr (.inr a))
      change (∑ i, y i*(R.coefficient a i : ℝ))=∑ i, x i*(R.coefficient a i : ℝ) at he
      change (∑ i, (R.coefficient a i : ℝ)*y i) ≤ _
      calc
        _ = ∑ i, y i*(R.coefficient a i : ℝ) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = _ := he
        _ ≤ _ := by simpa only [mul_comm] using hparts.2 a
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_assoc] using hyc

end SparseCompletion
