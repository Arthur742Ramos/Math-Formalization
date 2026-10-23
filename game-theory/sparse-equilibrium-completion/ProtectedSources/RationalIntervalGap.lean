/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalRecovery
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalGapConditions {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i a, lo i a*q i ≤ V i a ∧ V i a ≤ hi i a*q i) ∧
  (∀ a, (∑ b, K a b*p b)-(∑ i, V i a) ≤ ρ) ∧
  (∀ i, rationalScore lo p i ≤ ρ+M*r) ∧
  (∀ i, rationalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : Fin (rationalGridSize M r η),
    rationalPerspectiveCall q (rationalMomentScore p V) ρ
      (M*r-rationalGridNode M r η (l.val+1)) ≤
      rationalEnvelope M r (M*r-rationalGridNode M r η (l.val+1))

instance rationalIntervalGapConditionsDecidable {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) : Decidable (RationalIntervalGapConditions K lo hi V p q M r ρ η) := by
  unfold RationalIntervalGapConditions
  infer_instance

theorem rational_interval_gap_recovered {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    (∀ i a, lo i a ≤ rationalIntervalRecover lo V q i a ∧
      rationalIntervalRecover lo V q i a ≤ hi i a) ∧
    RationalGapConditions K (rationalIntervalRecover lo V q) p q M r ρ η := by
  rcases h with ⟨hq,hm,hV,ha,hlo,hcap,hcall⟩
  have hprod := rational_interval_recovered_product lo hi V q hV
  have hH := rational_recovered_score_moment lo V p q hprod
  refine ⟨rational_interval_recovered_bounds lo hi V q hq hlu hV,hq,hm,?_,?_,?_⟩
  · intro i
    by_cases hz : q i=0
    · simpa only [rationalScore,rationalIntervalRecover,hz,ite_true] using hlo i
    · have hp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hc := hcap i
      rw [←hH i] at hc
      nlinarith
  · intro a
    unfold rationalAnchorResponse
    have he : (∑ i, rationalIntervalRecover lo V q i a*q i)=∑ i, V i a := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm,hprod i a]
    rw [he]
    exact ha a
  · intro l
    rw [rational_perspective_call_identity q _ _ ρ _ hq hH]
    exact hcall l

theorem rational_interval_gap_rational_completion {k m : ℕ} (K : Fin k → Fin k → ℚ)
    (lo hi V : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (q : Fin m → ℚ)
    (M r ρ η : ℚ) (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : RationalIntervalGapConditions K lo hi V p q M r ρ η) :
    ∃ B, reconstructRationalGap (rationalIntervalRecover lo V q) p q M ρ η=some B := by
  have hg := (rational_interval_gap_recovered K lo hi V p q M r ρ η hlu h).2
  exact rational_gap_reconstruction_complete K _ p q M r ρ η hM hη
    ((rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hg)

end SparseCompletion
