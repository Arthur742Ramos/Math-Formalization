/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalCertificate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
namespace RationalCertificate
noncomputable section

/-- Acceptance produces this actual explicit completion, not merely an
    existential response vector or assumed feasibility certificate. -/
theorem accepted_full_game {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ)
    (hc : c.check K D M σ=true) :
    (∀ a, 0 ≤ blockWeights (fun h => (c.anchors h : ℝ)) c.realQ a) ∧
    (∑ a, blockWeights (fun h => (c.anchors h : ℝ)) c.realQ a)=1 ∧
    IsSkew (blockMatrix (fun h h' => (K h h' : ℝ)) (fun i h => (D i h : ℝ)) (c.realB M)) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h h' => (K h h' : ℝ))
      (fun i h => (D i h : ℝ)) (c.realB M) a b ∧
      blockMatrix (fun h h' => (K h h' : ℝ)) (fun i h => (D i h : ℝ)) (c.realB M) a b ≤ (M : ℝ)) ∧
    (∀ a, response (blockMatrix (fun h h' => (K h h' : ℝ)) (fun i h => (D i h : ℝ)) (c.realB M))
      (blockWeights (fun h => (c.anchors h : ℝ)) c.realQ) a ≤ (σ : ℝ)) := by
  obtain ⟨hM,hp,hq,hm,hK,hKb,hD,hB,hBb,hrows⟩ := c.check_iff K D M σ |>.mp hc
  have hpR : ∀ h, 0 ≤ (c.anchors h : ℝ) := by intro h; exact_mod_cast hp h
  have hqR : ∀ i, 0 ≤ c.realQ i := by
    intro i
    change 0 ≤ (c.q i : ℝ)
    exact_mod_cast hq i
  have hKR : IsSkew (fun h h' => (K h h' : ℝ)) := by
    intro h h'
    change (K h h' : ℝ) = -(K h' h : ℝ)
    exact_mod_cast hK h h'
  have hBR : IsSkew (c.realB M) := by
    apply compactCompletion_skew
    intro i hi j hj
    exact_mod_cast hB i hi j hj
  have hKbR : ∀ h h', -(M : ℝ) ≤ (K h h' : ℝ) ∧ (K h h' : ℝ) ≤ (M : ℝ) := by
    intro h h'; exact_mod_cast hKb h h'
  have hDR : ∀ i h, -(M : ℝ) ≤ (D i h : ℝ) ∧ (D i h : ℝ) ≤ (M : ℝ) := by
    intro i h; exact_mod_cast hD i h
  have hBbR : ∀ i j, -(M : ℝ) ≤ c.realB M i j ∧ c.realB M i j ≤ (M : ℝ) := by
    apply compactCompletion_bounds
    · exact_mod_cast hM
    · intro i hi j hj; exact_mod_cast hBb i hi j hj
  refine ⟨blockWeights_nonneg _ _ hpR hqR,?_,blockMatrix_skew _ _ _ hKR hBR,
    blockMatrix_bounds _ _ _ _ hKbR hDR hBbR,(c.rows_iff K D M σ).mpr hrows⟩
  rw [blockWeights_mass]
  simp only [realQ]
  exact_mod_cast hm

/-- With probability and bounded-skew data validated, acceptance is equivalent
    to all rows of the explicit omitted-row real completion passing. -/
theorem check_iff_full_rows {k m : ℕ} (c : RationalCertificate k m)
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (M σ : ℚ)
    (hg : 0 ≤ M ∧ (∀ h, 0 ≤ c.anchors h) ∧ (∀ i, 0 ≤ c.q i) ∧
      (∑ h, c.anchors h)+(∑ i, c.q i)=1 ∧
      (∀ h h', K h h' = -K h' h) ∧
      (∀ h h', -M ≤ K h h' ∧ K h h' ≤ M) ∧
      (∀ i h, -M ≤ D i h ∧ D i h ≤ M) ∧
      (∀ i ∈ c.support, ∀ j ∈ c.support, c.b i j = -c.b j i) ∧
      (∀ i ∈ c.support, ∀ j ∈ c.support, -M ≤ c.b i j ∧ c.b i j ≤ M)) :
    c.check K D M σ=true ↔
      ∀ a, response (blockMatrix (fun h h' => (K h h' : ℝ))
        (fun i h => (D i h : ℝ)) (c.realB M))
        (blockWeights (fun h => (c.anchors h : ℝ)) c.realQ) a ≤ (σ : ℝ) := by
  rw [c.check_iff,c.rows_iff]
  obtain ⟨hM,hp,hq,hm,hK,hKb,hD,hB,hBb⟩ := hg
  exact ⟨fun h => h.2.2.2.2.2.2.2.2.2,
    fun hr => ⟨hM,hp,hq,hm,hK,hKb,hD,hB,hBb,hr⟩⟩
end
end RationalCertificate
end SparseCompletion
