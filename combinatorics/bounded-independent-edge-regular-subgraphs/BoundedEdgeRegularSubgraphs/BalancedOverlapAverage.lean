module

public import BoundedEdgeRegularSubgraphs.IntersectionSampling
public import BoundedEdgeRegularSubgraphs.OverlapTiltAverage
import Mathlib.Tactic

/-!
# Averaging the restricted energies in the balanced second moment
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The averaged small-overlap factor in Theorem 4.1. The coefficients
of the two candidate energies are handled symmetrically before weighting
the uniform intersections. -/
theorem sum_balanced_overlap_exp_le {α : Type*} [DecidableEq α]
    (s : Finset α) (k j : ℕ) (hk : 0 < k) (hj : j ≤ k) (F : Finset (Finset α))
    (hF : F ⊆ s.powersetCard k) (θ : Finset α → α → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hEnergy : ∀ S ∈ F, (∑ i ∈ S, θ S i ^ 2) ≤ A)
    (hSmall : ∀ S ∈ F, ∀ i ∈ S, (j : ℝ) * θ S i ^ 2 ≤ 1) :
    (∑ S ∈ F, ∑ T ∈ F, if (S ∩ T).card = j then
      Real.exp ((j : ℝ) / 4 * ((∑ i ∈ S ∩ T, θ S i ^ 2) + (∑ i ∈ S ∩ T, θ T i ^ 2))) else 0) ≤
      (F.card : ℝ) * ((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ) *
        Real.exp (A * (j : ℝ) ^ 2 / k) := by
  classical
  let W (S T : Finset α) := ∑ i ∈ S ∩ T, θ S i ^ 2
  let f (S T : Finset α) := if (S ∩ T).card = j then Real.exp ((j : ℝ) / 2 * W S T) else 0
  have hpair (S T : Finset α) :
      (if (S ∩ T).card = j then
        Real.exp ((j : ℝ) / 4 * (W S T + W T S)) else 0) ≤ (f S T + f T S) / 2 := by
    have he : (T ∩ S).card = (S ∩ T).card := by rw [Finset.inter_comm T S]
    by_cases h : (S ∩ T).card = j
    · have h' : (T ∩ S).card = j := he.trans h
      dsimp only [f]
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left h']
      let a := (j : ℝ) / 4 * W S T
      let b := (j : ℝ) / 4 * W T S
      have h₁ : (j : ℝ) / 4 * (W S T + W T S) = a + b := by dsimp only [a, b]; ring
      have h₂ : (j : ℝ) / 2 * W S T = a + a := by dsimp only [a]; ring
      have h₃ : (j : ℝ) / 2 * W T S = b + b := by dsimp only [b]; ring
      rw [h₁, h₂, h₃, Real.exp_add, Real.exp_add, Real.exp_add]
      nlinarith only [sq_nonneg (Real.exp a - Real.exp b)]
    · have h' : ¬ (T ∩ S).card = j := fun h' ↦ h (he.symm.trans h')
      simp only [f, ite_eq_right h, ite_eq_right h', add_zero, zero_div, le_refl]
  have hbasic : (∑ S ∈ F, ∑ T ∈ F, if (S ∩ T).card = j then
      Real.exp ((j : ℝ) / 4 * (W S T + W T S)) else 0) ≤ ∑ S ∈ F, ∑ T ∈ F, f S T := by
    have h := Finset.sum_le_sum (s := F) (fun S _ ↦
      Finset.sum_le_sum (s := F) (fun T _ ↦ hpair S T))
    refine h.trans_eq ?_
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
    rw [show (∑ S ∈ F, ∑ T ∈ F, f T S) = ∑ S ∈ F, ∑ T ∈ F, f S T by rw [Finset.sum_comm]]
    ring
  simp_rw [show ∀ S T : Finset α, (∑ i ∈ S ∩ T, θ T i ^ 2) = W T S by
    intro S T; dsimp only [W]; rw [Finset.inter_comm S T]]
  refine hbasic.trans ?_
  have hbound (S : Finset α) (hS : S ∈ F) : (∑ T ∈ F, f S T) ≤
      ((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ) *
        Real.exp (A * (j : ℝ) ^ 2 / k) := by
    obtain ⟨hSs, hSk⟩ := Finset.mem_powersetCard.mp (hF hS)
    calc
      _ ≤ ∑ T ∈ s.powersetCard k, f S T := Finset.sum_le_sum_of_subset_of_nonneg hF
        (fun T _ _ ↦ by unfold f; split_ifs <;> positivity)
      _ = ((s.card - k).choose (k - j) : ℝ) *
          ∑ J ∈ S.powersetCard j, Real.exp ((j : ℝ) / 2 * ∑ i ∈ J, θ S i ^ 2) := by
        dsimp only [f, W]
        rw [← Finset.sum_filter]
        have he := sum_sample_intersection_of_card s S hSs hj
          (fun J ↦ Real.exp ((j : ℝ) / 2 * ∑ i ∈ J, θ S i ^ 2))
        simpa only [nsmul_eq_mul, Finset.card_sdiff_of_subset hSs, hSk] using he
      _ ≤ _ := by
        have hS₀ := Finset.card_pos.mp (show 0 < S.card by rwa [hSk])
        have h := sum_restricted_tilt_exp_le S (θ S) hA (c := 1 / 2) (by norm_num)
          j hS₀ (hEnergy S hS) (fun i hi ↦ by linarith only [hSmall S hS i hi])
        simp_rw [show (1 / 2 : ℝ) * (j : ℝ) = (j : ℝ) / 2 by ring,
          hSk, show 2 * (1 / 2 : ℝ) * A = A by ring] at h
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hbound).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end BoundedEdgeRegularSubgraphs
