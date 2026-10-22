/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalGap
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

abbrev RationalGapRow (k m H : ℕ) := Fin m ⊕ (Fin 2 ⊕ (Fin m ⊕ (Fin k ⊕ Fin H)))

def rationalGapCoefficient {k m : ℕ}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalGapRow k m (rationalGridSize M r η) → Fin m → ℚ :=
  Sum.elim (fun j i => if i=j then -1 else 0)
    (Sum.elim (fun a _ => if a=0 then 1 else -1)
      (Sum.elim (fun _ _ => 0)
        (Sum.elim (fun h i => -D i h) (fun l i =>
          max (rationalScore D p i-ρ-(M*r-rationalGridNode M r η (l.val+1))) 0))))

def rationalGapRightSide {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalGapRow k m (rationalGridSize M r η) → ℚ :=
  Sum.elim (fun _ => 0)
    (Sum.elim (fun a => if a=0 then r else -r)
      (Sum.elim (fun i => ρ+M*r-rationalScore D p i)
        (Sum.elim (fun h => ρ-∑ a, K h a*p a)
          (fun l => rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))))))

theorem rational_gap_encoding_rows (k m H : ℕ) :
    Fintype.card (RationalGapRow k m H)=(2 : ℕ)*m+2+k+H := by
  simp only [RationalGapRow,Fintype.card_sum,Fintype.card_fin]
  omega


theorem rational_gap_conditions_iff_linear {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    RationalGapConditions K D p q M r ρ η ↔
      ∀ a, (∑ i, rationalGapCoefficient D p M r ρ η a i*q i) ≤
        rationalGapRightSide K D p M r ρ η a := by
  constructor
  · rintro ⟨hq,hm,hg,ha,hc⟩ a
    rcases a with i | a
    · simp only [rationalGapCoefficient,Sum.elim_inl,ite_mul,neg_one_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,ite_true,rationalGapRightSide]
      linarith [hq i]
    · rcases a with a | a
      · by_cases hz : a=0
        · simpa [rationalGapCoefficient,rationalGapRightSide,hz] using le_of_eq hm
        · simpa [rationalGapCoefficient,rationalGapRightSide,hz] using neg_le_neg (le_of_eq hm.symm)
      · rcases a with i | a
        · simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
            zero_mul,Finset.sum_const_zero]
          linarith [hg i]
        · rcases a with a | l
          · have hh := ha a
            unfold rationalAnchorResponse at hh
            simpa only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
              neg_mul,Finset.sum_neg_distrib] using (by linarith :
                -(∑ i, D i a*q i) ≤ ρ-∑ b, K a b*p b)
          · have hh := hc l
            unfold rationalCall at hh
            simpa only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,mul_comm] using hh
  · intro h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i
      have hh := h (.inl i)
      simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inl,ite_mul,
        neg_one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
      linarith
    · have h1 := h (.inr (.inl 0))
      have h2 := h (.inr (.inl 1))
      simp [rationalGapCoefficient,rationalGapRightSide] at h1 h2
      linarith
    · intro i
      have hh := h (.inr (.inr (.inl i)))
      simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
        zero_mul,Finset.sum_const_zero] at hh
      linarith
    · intro a
      have hh := h (.inr (.inr (.inr (.inl a))))
      simp only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,Sum.elim_inl,
        neg_mul,Finset.sum_neg_distrib] at hh
      unfold rationalAnchorResponse
      linarith
    · intro l
      have hh := h (.inr (.inr (.inr (.inr l))))
      simpa only [rationalGapCoefficient,rationalGapRightSide,Sum.elim_inr,rationalCall,mul_comm] using hh


theorem rational_gap_linear_acceptance_iff {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    checkRationalGap K D p q M r ρ η=true ↔
      ∀ a, (∑ i, rationalGapCoefficient D p M r ρ η a i*q i) ≤
        rationalGapRightSide K D p M r ρ η a :=
  (rational_gap_check_iff K D p q M r ρ η).trans
    (rational_gap_conditions_iff_linear K D p q M r ρ η)

theorem rational_gap_nontrivial_rows (k H : ℕ) : Fintype.card (Fin k ⊕ Fin H)=k+H := by
  simp only [Fintype.card_sum,Fintype.card_fin]

end SparseCompletion
