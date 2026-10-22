/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalSparseGapAlgorithm
public import GapSparse
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_sparse_gap_algorithm_full_game {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (R : RationalLinearSystem I m)
    (B : Fin m → Fin m → ℚ) (h : rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B)) :
    (∀ a, 0 ≤ blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    IsSkew (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
        (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  have hs := rational_sparse_gap_algorithm_sound K D p M r ρ η R q B h
  have hc := hs.2.1
  have hB := (residual_rat_real_iff q (rationalScore D p) M (ρ+η) B).mp hs.2.2.1
  have hrows : ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
    apply (block_response_bounds_iff _ _ _ _ _ _).mpr
    constructor
    · intro a
      have hh : (rationalAnchorResponse K D p q a : ℝ) ≤ (ρ : ℝ) := by
        exact_mod_cast hc.2.2.2.1 a
      rw [rational_anchor_response_real] at hh
      have hηR : (0 : ℝ)<(η : ℝ) := by exact_mod_cast hη
      linarith
    · intro i
      have hi := hB.2.2 i
      simpa only [response,←rational_score_real,Rat.cast_add] using hi
  have hKR : IsSkew (fun h a => (K h a : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    exact_mod_cast hK a b
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  refine ⟨blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a)
    (fun i => by exact_mod_cast hc.1 i),?_,blockMatrix_skew _ _ _ hKR hB.1,
    blockMatrix_bounds _ _ _ _ hKbR hDbR hB.2.1,
    hrows⟩
  rw [blockWeights_mass]
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast hc.2.1
  rw [hm]
  exact_mod_cast hnorm

theorem rational_sparse_gap_algorithm_full_support {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalSparseGapAlgorithm K D p M r ρ η R=some (q,B)) :
    (Finset.univ.filter fun a => blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a ≠ 0).card ≤
      min (k+m) ((2 : ℕ)*k+rationalGridSize M r η+Fintype.card I+1) := by
  classical
  have hc := (rational_sparse_gap_algorithm_sound K D p M r ρ η R q B h).2.2.2
  have hcR : (Finset.univ.filter fun i => (q i : ℝ) ≠ 0).card ≤
      min m (k+rationalGridSize M r η+Fintype.card I+1) := by
    have he : (Finset.univ.filter fun i => (q i : ℝ) ≠ 0)=
        Finset.univ.filter (fun i => q i ≠ 0) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Rat.cast_ne_zero]
    rw [he]
    exact hc
  rw [block_support_card]
  have hpa : (Finset.univ.filter fun a => (p a : ℝ) ≠ 0).card ≤ k :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  have h1 := le_trans hcR (min_le_left _ _)
  have h2 := le_trans hcR (min_le_right _ _)
  exact Nat.le_min.mpr ⟨by omega,by omega⟩

end SparseCompletion
