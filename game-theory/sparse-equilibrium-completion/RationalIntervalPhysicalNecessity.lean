/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalRepertoire
public import IntervalGap
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem real_interval_completion_physical_point {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ)) :
    ∃ A, RationalIntervalRealPoint loK hiK lo hi (fun i a => q i*D i a) K p q M r ρ η A := by
  have hMR : (0 : ℝ)<(M : ℝ) := by exact_mod_cast hM
  have hh := (block_response_bounds_iff K D B (fun a => (p a : ℝ)) q (ρ : ℝ)).mp hrows
  have hc := (weighted_completion_iff q (score D (fun a => (p a : ℝ))) M r ρ
    (le_of_lt hMR) hq hr).mp ⟨B,hB,hb,hh.2⟩
  let V := fun i a => q i*D i a
  let A := fun (l : Fin (rationalGridSize M r η)) i =>
    max ((∑ a, V i a*(p a : ℝ))-
      ((ρ+(M*r-rationalGridNode M r η (l.val+1)) : ℚ) : ℝ)*q i) 0
  have hprod : ∀ i a, q i*D i a=V i a := fun _ _ => rfl
  have hH : ∀ i, q i*score D (fun a => (p a : ℝ)) i=∑ a, V i a*(p a : ℝ) := by
    intro i
    unfold score
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by dsimp only [V]; ring
  have hpoint : RationalIntervalRealPoint loK hiK lo hi V K p q M r ρ η A := by
    refine ⟨hq,hr,?_,hK,hKb,?_,?_,?_,?_⟩
    · intro i a
      exact ⟨mul_le_mul_of_nonneg_right (hD i a).1 (hq i) |>.trans_eq (mul_comm _ _),
        (mul_comm (q i) (D i a)).le.trans (mul_le_mul_of_nonneg_right (hD i a).2 (hq i))⟩
    · intro a
      rw [←anchor_response_of_perspective K D V (fun a => (p a : ℝ)) q hprod a]
      exact hh.1 a
    · intro i
      have hs := score_lower_from_intervals (fun i a => (lo i a : ℝ)) D (fun a => (p a : ℝ))
        (fun a => by exact_mod_cast hp a) (fun i a => (hD i a).1) i
      have ht := le_trans hs (hc.1 i)
      simpa only [←rational_score_real,Rat.cast_add,Rat.cast_mul] using ht
    · intro i
      rw [←hH i]
      have ht := mul_le_mul_of_nonneg_right (hc.1 i) (hq i)
      simpa only [mul_comm (q i),Rat.cast_add,Rat.cast_mul] using ht
    · intro l
      refine ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,?_⟩
      have ht := cuts_imply_call_bound q (fun i => score D (fun a => (p a : ℝ)) i-(ρ : ℝ))
        M r hMR hc.2 ((M*r-rationalGridNode M r η (l.val+1) : ℚ) : ℝ)
      rw [perspective_call_identity q _ _ _ _ hq hH] at ht
      simpa only [perspectiveCall,A,rational_envelope_real,Rat.cast_add] using ht
  exact ⟨A,hpoint⟩

end
end SparseCompletion
