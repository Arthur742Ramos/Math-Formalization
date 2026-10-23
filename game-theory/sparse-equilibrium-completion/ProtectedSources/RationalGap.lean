/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalGrid
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalScore {α ι : Type*} [Fintype α] (D : ι → α → ℚ) (p : α → ℚ) (i : ι) : ℚ :=
  ∑ h, D i h*p h

def rationalAnchorResponse {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℚ) (D : ι → α → ℚ) (p : α → ℚ) (q : ι → ℚ) (h : α) : ℚ :=
  (∑ a, K h a*p a)-∑ i, D i h*q i

def RationalGapConditions {k m : ℕ} (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i, rationalScore D p i ≤ ρ+M*r) ∧
  (∀ h, rationalAnchorResponse K D p q h ≤ ρ) ∧
  ∀ l : Fin (rationalGridSize M r η),
    rationalCall q (fun i => rationalScore D p i-ρ) (M*r-rationalGridNode M r η (l.val+1)) ≤
      rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))

instance rationalGapConditionsDecidable {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    Decidable (RationalGapConditions K D p q M r ρ η) := by
  unfold RationalGapConditions
  infer_instance

def checkRationalGap {k m : ℕ} (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) : Bool :=
  decide (RationalGapConditions K D p q M r ρ η)

theorem rational_gap_check_iff {k m : ℕ} (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    checkRationalGap K D p q M r ρ η=true ↔ RationalGapConditions K D p q M r ρ η := by
  simp only [checkRationalGap,decide_eq_true_eq]

theorem rational_score_real {α ι : Type*} [Fintype α] (D : ι → α → ℚ) (p : α → ℚ) (i : ι) :
    (rationalScore D p i : ℝ)=score (fun i h => (D i h : ℝ)) (fun h => (p h : ℝ)) i := by
  unfold rationalScore score
  push_cast
  rfl

theorem rational_anchor_response_real {α ι : Type*} [Fintype α] [Fintype ι]
    (K : α → α → ℚ) (D : ι → α → ℚ) (p : α → ℚ) (q : ι → ℚ) (h : α) :
    (rationalAnchorResponse K D p q h : ℝ)=
      anchorResponse (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ))
        (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) h := by
  unfold rationalAnchorResponse anchorResponse
  push_cast
  rfl


theorem rational_gap_completed_witness {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hcheck : checkRationalGap K D p q M r ρ η=true) :
    ∃ B : Fin m → Fin m → ℝ, IsSkew B ∧
      (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  have h := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  have hr : 0 ≤ r := by rw [←h.2.1]; exact Finset.sum_nonneg fun i _ => h.1 i
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hqr : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast h.1 i
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast h.2.1
  have hg : ∀ i, score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i ≤
      (ρ : ℝ)+(M : ℝ)*(r : ℝ) := by
    intro i
    have hh : (rationalScore D p i : ℝ) ≤ ((ρ+M*r : ℚ) : ℝ) := by exact_mod_cast h.2.2.1 i
    simpa only [rational_score_real,Rat.cast_add,Rat.cast_mul] using hh
  have hc := rational_finite_grid_implication q (fun i => rationalScore D p i-ρ) M r η hM hr hη h.1
    (fun i _ => by linarith [h.2.2.1 i]) (by
      intro l hl hL
      let u : Fin (rationalGridSize M r η) := ⟨l-1,by omega⟩
      have he : u.val+1=l := by dsimp only [u]; omega
      simpa only [he] using h.2.2.2.2 u)
  have hcuts := call_bound_implies_cuts (fun i => (q i : ℝ))
    (fun i => ((rationalScore D p i-ρ : ℚ) : ℝ)-(η : ℝ)) (M : ℝ) (r : ℝ) hMR hqr hm hc
  have he : (fun i => ((rationalScore D p i-ρ : ℚ) : ℝ)-(η : ℝ))=
      (fun i => score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ)) i-((ρ : ℝ)+(η : ℝ))) := by
    funext i
    rw [Rat.cast_sub,rational_score_real]
    ring
  rw [he] at hcuts
  obtain ⟨B,hB,hb,hrows⟩ := (weighted_completion_iff (fun i => (q i : ℝ))
    (score (fun i a => (D i a : ℝ)) (fun a => (p a : ℝ))) (M : ℝ) (r : ℝ)
    ((ρ : ℝ)+(η : ℝ)) (le_of_lt hMR) hqr hm).mpr
      ⟨fun i => by
        have hh : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
        linarith [hg i],hcuts⟩
  refine ⟨B,hB,hb,?_⟩
  apply (block_response_bounds_iff _ _ B _ _ _).mpr
  refine ⟨?_,hrows⟩
  intro a
  have hh : (rationalAnchorResponse K D p q a : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast h.2.2.2.1 a
  rw [rational_anchor_response_real] at hh
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  linarith


theorem rational_gap_normalized_full_game {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (hM : 0 < M) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hK : ∀ a b, K a b= -K b a)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (hcheck : checkRationalGap K D p q M r ρ η=true) :
    ∃ B : Fin m → Fin m → ℝ,
      (∀ a, 0 ≤ blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a) ∧
      (∑ a, blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
      IsSkew (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B) ∧
      (∀ a b, -(M : ℝ) ≤ blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B a b ∧
        blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B a b ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  have h := (rational_gap_check_iff K D p q M r ρ η).mp hcheck
  obtain ⟨B,hB,hb,hrows⟩ := rational_gap_completed_witness K D p q M r ρ η hM hη hcheck
  have hKR : IsSkew (fun h a => (K h a : ℝ)) := by
    intro a b
    change (K a b : ℝ)= -(K b a : ℝ)
    rw [hK a b,Rat.cast_neg]
  have hKbR : ∀ a b, -(M : ℝ) ≤ (K a b : ℝ) ∧ (K a b : ℝ) ≤ (M : ℝ) := by
    intro a b
    exact_mod_cast hKb a b
  have hDbR : ∀ i a, -(M : ℝ) ≤ (D i a : ℝ) ∧ (D i a : ℝ) ≤ (M : ℝ) := by
    intro i a
    exact_mod_cast hDb i a
  refine ⟨B,blockWeights_nonneg _ _ (fun a => by exact_mod_cast hp a)
    (fun i => by exact_mod_cast h.1 i),?_,blockMatrix_skew _ _ B hKR hB,
    blockMatrix_bounds _ _ B (M : ℝ) hKbR hDbR hb,hrows⟩
  rw [blockWeights_mass]
  have hm : (∑ i, (q i : ℝ))=(r : ℝ) := by exact_mod_cast h.2.1
  rw [hm]
  exact_mod_cast hnorm

end SparseCompletion
