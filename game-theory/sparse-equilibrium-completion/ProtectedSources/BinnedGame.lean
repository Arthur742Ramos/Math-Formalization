/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.BinnedMoments

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem binned_game_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) :
    let m := ∑ b, L b
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧
      d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ))*∑ b, (L b : ℝ)^(3 : ℕ) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  let qstar := uniformTarget m (1/4)
  let q := binnedWeights L hL (1/4)
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let d := βstar-scoreMoment q w
  have hq : ∀ j, 0 ≤ q j := binned_nonneg L hL (1/4) (by norm_num)
  have hmass : ∑ j, q j=1/4 := binned_mass L hL (1/4) hm
  have hmean : scoreMoment q t=0 := binned_uniform_score_mean L hL hm (1/4)
  have hloss := binned_exposing_loss L hL hm (1/4) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hloss
  change 0 ≤ d ∧ d ≤ (1/16 : ℝ)/(12*(m : ℝ)^3)*∑ b, (L b : ℝ)^3 at hloss
  have hw : ∀ j, 0 ≤ w j := fun j =>
    (exposingWeight_bounds hm qstar (fun _ => div_nonneg (by norm_num) (Nat.cast_nonneg _)) (1/4)
      (uniformTarget_mass _ hm (1/4)) j).1
  have hβ : 0 ≤ scoreMoment q w := Finset.sum_nonneg fun j _ => mul_nonneg (hq j) (hw j)
  obtain ⟨B,hB,hb,hrows⟩ := binned_uniform_residual_completion L hL hm (1/4) (by norm_num)
  refine ⟨q,B,d,hq,hmass,hB,hb,binned_support L hL (1/4),hloss.1,?_,hloss.2,?_,?_,?_⟩
  · dsimp only [d]
    linarith
  · rw [block_response_anchor]
    have ha := (two_anchor_responses t w q (3/4) βstar (by norm_num)).1
    change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 0=d
    rw [ha,hmean]
    dsimp only [d]
    ring
  · rw [block_response_anchor]
    have ha := (two_anchor_responses t w q (3/4) βstar (by norm_num)).2
    change anchorResponse (twoCore (2*βstar/(3/4))) (twoCross t w (3/4)) (twoShares (3/4)) q 1= -d
    rw [ha,hmean]
    dsimp only [d]
    ring
  · intro j
    rw [block_response_residual]
    have hs : score (rigidityCross qstar) (twoShares (3/4))=t :=
      two_score t w (3/4) (by norm_num)
    rw [hs]
    exact hrows j

end
end SparseCompletion
