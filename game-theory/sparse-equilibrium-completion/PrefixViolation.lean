/- AI-assisted formalization under the repository Apache-2.0 license.
Quantitative prefix domination from the source conic-section proof. -/
module
public import ScorePrefixes

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem call_positive_filter_identity {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (z : ℝ) :
    call q v z =
      (∑ i ∈ Finset.univ.filter (fun i => 0 < v i-z), q i*v i)-
        z*mass (Finset.univ.filter (fun i => 0 < v i-z)) q := by
  classical
  have he : call q v z =
      ∑ i ∈ Finset.univ.filter (fun i => 0 < v i-z), q i*(v i-z) := by
    unfold call
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < v i-z
    · rw [ite_eq_left hi, max_eq_left (le_of_lt hi)]
    · rw [ite_eq_right hi, max_eq_right (le_of_not_gt hi), mul_zero]
  rw [he]
  simp only [mass, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_comm]

/-- Every subset's numerical cut violation is dominated by a score prefix,
even when the subset already violates the constraints. -/
theorem score_prefix_violation_dominates {m : ℕ}
    (q v : Fin m → ℝ) (M r : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hv : Antitone v) (S : Finset (Fin m)) :
    ∃ l : ℕ, l ≤ m ∧
      (∑ i ∈ S, q i*v i)-M*mass S q*(r-mass S q) ≤
      (∑ i ∈ scorePrefix m l, q i*v i)-
        M*mass (scorePrefix m l) q*(r-mass (scorePrefix m l) q) := by
  classical
  let Q := mass S q
  let z := M*r-2*M*Q
  obtain ⟨l, hl, he⟩ := threshold_is_score_prefix v hv z
  refine ⟨l, hl, ?_⟩
  have hsub : (∑ i ∈ S, q i*v i)-z*Q ≤ call q v z := by
    calc
      _ = ∑ i ∈ S, q i*(v i-z) := by
        simp only [Q, mass, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ ≤ ∑ i ∈ S, q i*max (v i-z) 0 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hq i)
      _ ≤ call q v z := Finset.sum_le_univ_sum_of_nonneg fun i =>
        mul_nonneg (hq i) (le_max_right _ _)
  rw [call_positive_filter_identity, he] at hsub
  have hs := mul_nonneg hM (sq_nonneg (mass (scorePrefix m l) q-Q))
  dsimp only [z, Q] at hsub hs
  nlinarith

/-- Prefixes certify any upper bound on the maximum cut violation, not only
feasibility at zero. No normalization or positivity of total mass is needed. -/
theorem cut_violation_bound_iff_prefix_bound {m : ℕ}
    (q v : Fin m → ℝ) (M r δ : ℝ) (hM : 0 ≤ M)
    (hq : ∀ i, 0 ≤ q i) (hv : Antitone v) :
    (∀ S : Finset (Fin m),
      (∑ i ∈ S, q i*v i)-M*mass S q*(r-mass S q) ≤ δ) ↔
    ∀ l : ℕ, l ≤ m →
      (∑ i ∈ scorePrefix m l, q i*v i)-
        M*mass (scorePrefix m l) q*(r-mass (scorePrefix m l) q) ≤ δ := by
  constructor
  · intro h l _
    exact h _
  · intro h S
    obtain ⟨l, hl, hd⟩ := score_prefix_violation_dominates q v M r hM hq hv S
    exact le_trans hd (h l hl)

end
end SparseCompletion
