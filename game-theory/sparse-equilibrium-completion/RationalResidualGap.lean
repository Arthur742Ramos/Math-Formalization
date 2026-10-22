/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Actual rational residual reconstruction for an accepted rational gap point;
no polynomial complexity claim. -/
module
public import RationalResidualSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def reconstructRationalGap {k m : ℕ} (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (q : Fin m → ℚ) (M ρ η : ℚ) : Option (Fin m → Fin m → ℚ) :=
  rationalResidualCompletion q (rationalScore D p) M (ρ+η)

theorem rational_gap_reconstruction_complete {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hcheck : checkRationalGap K D p q M r ρ η=true) :
    ∃ B, reconstructRationalGap D p q M ρ η=some B := by
  obtain ⟨B,hsk,hb,hr⟩ := rational_gap_completed_witness K D p q M r ρ η hM hη hcheck
  apply rational_residual_completion_complete q (rationalScore D p) M (ρ+η)
  refine ⟨B,hsk,hb,?_⟩
  intro i
  have hi := hr (.inr i)
  rw [block_response_residual] at hi
  simpa only [response,←rational_score_real,Rat.cast_add] using hi

theorem rational_gap_reconstruction_residual_sound {k m : ℕ}
    (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M ρ η : ℚ) (B : Fin m → Fin m → ℚ)
    (h : reconstructRationalGap D p q M ρ η=some B) :
    ResidualRatConditions q (rationalScore D p) M (ρ+η) B :=
  rational_residual_completion_rat_sound q (rationalScore D p) M (ρ+η) B h

theorem rational_gap_reconstruction_full_rows {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hη : 0 < η) (hcheck : checkRationalGap K D p q M r ρ η=true)
    (B : Fin m → Fin m → ℚ) (h : reconstructRationalGap D p q M ρ η=some B) :
    ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  have hc := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  have hB := rational_residual_completion_real_sound q (rationalScore D p) M (ρ+η) B h
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

theorem rational_gap_reconstruction_normalized_full_game {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hcheck : checkRationalGap K D p q M r ρ η=true)
    (B : Fin m → Fin m → ℚ) (h : reconstructRationalGap D p q M ρ η=some B) :
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
  have hc := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  have hB := rational_residual_completion_real_sound q (rationalScore D p) M (ρ+η) B h
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
    rational_gap_reconstruction_full_rows K D p q M r ρ η hη hcheck B h⟩
  rw [blockWeights_mass]
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast hc.2.1
  rw [hm]
  exact_mod_cast hnorm

end SparseCompletion
