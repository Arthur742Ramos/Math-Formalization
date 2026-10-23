/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalEncoding
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalPoint {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) ∧
  (∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
  (∀ a, (∑ b, K a b*p b)-(∑ i, V i a) ≤ ρ) ∧
  (∀ i, rationalScore lo p i ≤ ρ+M*r) ∧
  (∀ i, rationalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : Fin (rationalGridSize M r η),
    (∀ i, 0 ≤ A l i) ∧
    (∀ i, rationalMomentScore p V i-
      (ρ+(M*r-rationalGridNode M r η (l.val+1)))*q i ≤ A l i) ∧
    (∑ i, A l i) ≤ rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))

instance rationalIntervalPointDecidable {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℚ) :
    Decidable (RationalIntervalPoint loK hiK lo hi V K p q M r ρ η A) := by
  unfold RationalIntervalPoint
  infer_instance

theorem rational_interval_point_gap {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ)
    (A : Fin (rationalGridSize M r η) → Fin m → ℚ)
    (h : RationalIntervalPoint loK hiK lo hi V K p q M r ρ η A) :
    (∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η := by
  rcases h with ⟨hq,hm,hV,hK,hKb,ha,hlo,hcap,hA⟩
  refine ⟨hK,hKb,hq,hm,hV,ha,hlo,hcap,?_⟩
  intro l
  exact le_trans (Finset.sum_le_sum fun i _ => max_le ((hA l).2.1 i) ((hA l).1 i)) (hA l).2.2

theorem rational_interval_point_epigraph_iff {k m : ℕ} (loK hiK : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (K : Fin k → Fin k → ℚ)
    (p : Fin k → ℚ) (q : Fin m → ℚ) (M r ρ η : ℚ) :
    ((∀ a b, K a b= -K b a) ∧ (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
      RationalIntervalGapConditions K lo hi V p q M r ρ η) ↔
    ∃ A, RationalIntervalPoint loK hiK lo hi V K p q M r ρ η A := by
  constructor
  · rintro ⟨hK,hKb,hq,hm,hV,ha,hlo,hcap,hcall⟩
    let A := fun (l : Fin (rationalGridSize M r η)) i =>
      max (rationalMomentScore p V i-(ρ+(M*r-rationalGridNode M r η (l.val+1)))*q i) 0
    refine ⟨A,hq,hm,hV,hK,hKb,ha,hlo,hcap,?_⟩
    intro l
    exact ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,hcall l⟩
  · rintro ⟨A,h⟩
    exact rational_interval_point_gap loK hiK lo hi V K p q M r ρ η A h

end SparseCompletion
