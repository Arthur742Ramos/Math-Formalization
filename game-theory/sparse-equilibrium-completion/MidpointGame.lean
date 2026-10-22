/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import BinnedExact
public import BinnedGame

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem binned_game_completion_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) :
    let m := ∑ b, L b
    let qstar := uniformTarget m (1/(4 : ℕ))
    let q := binnedWeights L hL (1/(4 : ℕ))
    let d := scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ)))-
      scoreMoment q (exposingWeight qstar (1/(4 : ℕ)))
    ∃ B : Fin m → Fin m → ℝ, IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  let qstar := uniformTarget m (1/4)
  let q := binnedWeights L hL (1/4)
  let t := targetScore qstar (1/4)
  let w := exposingWeight qstar (1/4)
  let βstar := scoreMoment qstar w
  let d := βstar-scoreMoment q w
  have hmean : scoreMoment q t=0 := binned_uniform_score_mean L hL hm (1/4)
  obtain ⟨B,hB,hb,hrows⟩ := binned_uniform_residual_completion L hL hm (1/4) (by norm_num)
  refine ⟨B,hB,hb,?_,?_,?_⟩
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
    have hs : score (rigidityCross qstar) (twoShares (3/4))=t := two_score t w (3/4) (by norm_num)
    rw [hs]
    exact hrows j

theorem binned_odd_game_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hodd : ∀ b, L b%(2 : ℕ)≠0) :
    let m := ∑ b, L b
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      UniformWitness m d true (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q=h ∧
      response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d ∧
      d=(1/(4 : ℕ) : ℝ)^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ))*∑ b, binParityTerm (L b) := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  let qstar := uniformTarget m (1/4)
  let q := binnedWeights L hL (1/4)
  let d := scoreMoment qstar (exposingWeight qstar (1/4))-
    scoreMoment q (exposingWeight qstar (1/4))
  have hq : ∀ j, 0 ≤ q j := binned_nonneg L hL (1/4) (by norm_num)
  have hmass : ∑ j, q j=1/4 := binned_mass L hL (1/4) hm
  have hd : 0 ≤ d := (binned_exposing_loss L hL hm (1/4) (by norm_num)).1
  obtain ⟨B,hB,hb,h0,h1,hrows⟩ := binned_game_completion_exact L hL hm
  refine ⟨q,B,d,?_,binned_odd_support_exact L hL hm hodd (1/4) (by norm_num),h0,?_⟩
  · unfold UniformWitness
    norm_num only [Nat.cast_ofNat]
    refine ⟨hq,fun _ => by norm_num [twoShares],(by simp),?_,hB,hb,?_⟩
    · rw [hmass,Fin.sum_univ_two]
      norm_num [twoShares]
    · intro v
      cases v with
      | inl a =>
        fin_cases a
        · exact le_of_eq h0
        · exact le_of_eq_of_le h1 (by linarith)
      | inr j => exact le_trans (hrows j) hd
  · have he := binned_exposing_loss_exact L hL hm (1/4)
    norm_num only [Nat.cast_ofNat] at he
    exact he

theorem odd_midpoint_error_identity (h s : ℕ) (hh : 0 < h) (hs : 0 < s) (r : ℝ) :
    (r^(2 : ℕ)/((12 : ℕ)*((h*s : ℕ) : ℝ)^(3 : ℕ)))*(h : ℝ)*(s : ℝ)*((s : ℝ)^(2 : ℕ)-1)=
      r^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)^(2 : ℕ)-1/((h*s : ℕ) : ℝ)^(2 : ℕ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  push_cast
  field_simp

theorem uniform_odd_midpoint_witness (h s : ℕ) (hh : 0 < h) (hs : 0 < s) (hodd : s%(2 : ℕ)≠0) :
    ∃ (q : Fin (h*s) → ℝ) (B : Fin (h*s) → Fin (h*s) → ℝ),
      UniformWitness (h*s) ((1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)^(2 : ℕ)-1/((h*s : ℕ) : ℝ)^(2 : ℕ))) true
        (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q=h ∧
      response (blockMatrix (rigidityCore (uniformTarget (h*s) (1/(4 : ℕ))))
        (rigidityCross (uniformTarget (h*s) (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=
          (1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)^(2 : ℕ)-1/((h*s : ℕ) : ℝ)^(2 : ℕ)) := by
  have hsum : (∑ _ : Fin h, s)=h*s := by simp
  have hm : 0 < ∑ _ : Fin h, s := by rw [hsum]; exact Nat.mul_pos hh hs
  obtain ⟨q,B,d,hw,hcard,hrow,hd⟩ := binned_odd_game_witness (fun _ : Fin h => s) (fun _ => hs) hm (fun _ => hodd)
  have hparity : binParityTerm s=(s : ℝ)*((s : ℝ)^2-1) := by
    simp only [binParityTerm,ite_eq_right hodd]
  have herr : d=(1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2) := by
    rw [hd,hsum]
    simp only [hparity,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    convert odd_midpoint_error_identity h s hh hs (1/4) using 1
    ring
  rw [herr] at hw hrow
  have result : ∃ (q : Fin (∑ _ : Fin h, s) → ℝ)
      (B : Fin (∑ _ : Fin h, s) → Fin (∑ _ : Fin h, s) → ℝ),
      UniformWitness (∑ _ : Fin h, s) ((1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2))
        true (twoShares (3/4)) q B ∧ supportSize q=h ∧
      response (blockMatrix (rigidityCore (uniformTarget (∑ _ : Fin h, s) (1/4)))
        (rigidityCross (uniformTarget (∑ _ : Fin h, s) (1/4))) B)
        (blockWeights (twoShares (3/4)) q) (.inl 0)=
          (1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2) := ⟨q,B,hw,hcard,hrow⟩
  exact (congrArg (fun m : ℕ => ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ),
    UniformWitness m ((1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2))
      true (twoShares (3/4)) q B ∧ supportSize q=h ∧
    response (blockMatrix (rigidityCore (uniformTarget m (1/4)))
      (rigidityCross (uniformTarget m (1/4))) B)
      (blockWeights (twoShares (3/4)) q) (.inl 0)=
        (1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)^2-1/((h*s : ℕ) : ℝ)^2)) hsum).mp result

end
end SparseCompletion
