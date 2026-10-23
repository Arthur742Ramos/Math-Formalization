/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.WeakCoverWitness
public import ProtectedSources.IntervalLossMaximum

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_weak_cover_maximum {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η+(residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M)*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  exact normalized_weak_cover_witness k d K D F B p q M r ρ η
    (residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M) hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp lo hi
    (residual_loss_bound_nonnegative _ _ M) hlu hlo hhi hrev
    (fun i j hij => residual_loss_le_bound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M i j hij) hI

theorem normalized_exact_weak_cover_maximum {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η+(residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M)*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  exact normalized_exact_weak_cover_witness k d K D F B p q M r η
    (residualLossBound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M) hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp lo hi
    (residual_loss_bound_nonnegative _ _ M) hlu hlo hhi hrev
    (fun i j hij => residual_loss_le_bound (fun i j => lo (.inr i) (.inr j)) (fun i j => hi (.inr i) (.inr j)) M i j hij) hI

end
end SparseCompletion
