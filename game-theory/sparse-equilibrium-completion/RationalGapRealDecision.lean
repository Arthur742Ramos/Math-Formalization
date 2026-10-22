/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Exact rational elimination links real game feasibility to the supplied linear program. -/
module
public import RationalGapDecision
public import RationalLinearTransfer
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_linear_real_append_iff {I J : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (T : RationalLinearSystem J n) (x : Fin n → ℝ) :
    (S.append T).RealSatisfies x ↔ S.RealSatisfies x ∧ T.RealSatisfies x := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i),fun j => h (.inr j)⟩
  · rintro ⟨hS,hT⟩ a
    rcases a with i | j
    · exact hS i
    · exact hT j

theorem exact_game_rational_gap_system_real {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (x : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (M r ρ η : ℚ)
    (hM : 0 < M) (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
      (blockWeights (fun h => (p h : ℝ)) x) a ≤ (ρ : ℝ)) :
    (rationalGapSystem K D p M r ρ η).RealSatisfies x := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hh := (block_response_bounds_iff _ _ B _ x (ρ : ℝ)).mp hrows
  have hc := (weighted_completion_iff x (score (fun i h => (D i h : ℝ)) (fun h => (p h : ℝ)))
    (M : ℝ) (r : ℝ) (ρ : ℝ) (le_of_lt hMR) hq hm).mp ⟨B,hB,hb,hh.2⟩
  have hcall := cuts_imply_call_bound x
    (fun i => score (fun i h => (D i h : ℝ)) (fun h => (p h : ℝ)) i-(ρ : ℝ))
    (M : ℝ) (r : ℝ) hMR hc.2
  intro a
  rcases a with i | a
  · change (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*x j) ≤ ((0 : ℚ) : ℝ)
    have he : (∑ j, ((if j=i then (-1 : ℚ) else 0 : ℚ) : ℝ)*x j)= -x i := by
      calc
        _ = ∑ j, if j=i then -x j else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j=i <;> simp [hj]
        _ = _ := by simp
    rw [he,Rat.cast_zero]
    exact neg_nonpos.mpr (hq i)
  · rcases a with a | a
    · by_cases hz : a=0
      · subst a
        change (∑ j, ((1 : ℚ) : ℝ)*x j) ≤ (r : ℝ)
        simpa using le_of_eq hm
      · change (∑ j, ((if a=0 then (1 : ℚ) else -1 : ℚ) : ℝ)*x j) ≤
          ((if a=0 then r else -r : ℚ) : ℝ)
        simpa [hz] using neg_le_neg (le_of_eq hm.symm)
    · rcases a with i | a
      · change (∑ j, ((0 : ℚ) : ℝ)*x j) ≤ ((ρ+M*r-rationalScore D p i : ℚ) : ℝ)
        simp only [Rat.cast_zero,zero_mul,Finset.sum_const_zero]
        push_cast
        rw [rational_score_real]
        linarith [hc.1 i]
      · rcases a with a | l
        · change (∑ i, ((-D i a : ℚ) : ℝ)*x i) ≤ ((ρ-∑ b, K a b*p b : ℚ) : ℝ)
          push_cast
          simp_rw [neg_mul,Finset.sum_neg_distrib]
          have ha := hh.1 a
          unfold anchorResponse at ha
          linarith
        · change (∑ i, ((max (rationalScore D p i-ρ-
            (M*r-rationalGridNode M r η (l.val+1))) 0 : ℚ) : ℝ)*x i) ≤
            (rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1)) : ℝ)
          have ht := hcall ((M*r-rationalGridNode M r η (l.val+1) : ℚ) : ℝ)
          rw [←rational_envelope_real M r (M*r-rationalGridNode M r η (l.val+1))] at ht
          simpa only [call,Rat.cast_max,Rat.cast_sub,Rat.cast_zero,rational_score_real,mul_comm] using ht


theorem exact_game_rational_gap_solve {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (x : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (hR : R.RealSatisfies x)
    (hM : 0 < M) (hq : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=(r : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
      (blockWeights (fun h => (p h : ℝ)) x) a ≤ (ρ : ℝ)) :
    ∃ q, rationalGapSolve K D p M r ρ η R=some q := by
  apply rational_lp_real_complete m ((rationalGapSystem K D p M r ρ η).append R)
  exact ⟨x,(rational_linear_real_append_iff _ R x).mpr
    ⟨exact_game_rational_gap_system_real K D p x B M r ρ η hM hq hm hB hb hrows,hR⟩⟩

theorem rational_gap_solve_none_excludes_real_completion {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (hM : 0 < M)
    (hn : rationalGapSolve K D p M r ρ η R=none) :
    ¬∃ (x : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
      R.RealSatisfies x ∧ (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=(r : ℝ) ∧ IsSkew B ∧
      (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) x) a ≤ (ρ : ℝ) := by
  rintro ⟨x,B,hR,hq,hm,hB,hb,hrows⟩
  obtain ⟨q,hsol⟩ := exact_game_rational_gap_solve K D p x B M r ρ η R hR hM hq hm hB hb hrows
  rw [hn] at hsol
  cases hsol

end SparseCompletion
