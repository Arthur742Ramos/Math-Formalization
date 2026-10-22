/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import BalancedGame
public import SupportMinimum

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_error_finite_identity (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (r : ℝ) :
    (r^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ)))*(m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ) =
      r^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  field_simp

theorem binned_finite_correction {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hh : 0 < h) (r : ℝ) (hr : 0 ≤ r)
    (hcube : (∑ b : Fin h, (L b : ℝ)^(3 : ℕ)) ≤
      (∑ b, L b : ℝ)*(((∑ b, L b : ℕ) : ℝ)/(h : ℝ)+1)^(2 : ℕ)) :
    let m := ∑ b, L b
    let qstar := uniformTarget m r
    scoreMoment qstar (exposingWeight qstar r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight qstar r) ≤
        r^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hc : 0 ≤ r^2/(12*((∑ b, L b : ℕ) : ℝ)^3) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcube hc
  have hloss := (binned_exposing_loss L hL hm r hr).2
  have hid := bin_error_finite_identity _ h hm hh r
  norm_num only [Nat.cast_ofNat] at hid
  refine le_trans hloss (le_trans ?_ (le_of_eq hid))
  norm_num only [Nat.cast_ofNat] at *
  simpa only [Nat.cast_sum,mul_assoc] using hbound


theorem binned_finite_game_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hh : 0 < h)
    (hcube : (∑ b : Fin h, (L b : ℝ)^(3 : ℕ)) ≤
      (∑ b, L b : ℝ)*(((∑ b, L b : ℕ) : ℝ)/(h : ℝ)+1)^(2 : ℕ)) :
    let m := ∑ b, L b
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      UniformWitness m d true (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) ∧
      response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d := by
  norm_num only [Nat.cast_ofNat] at *
  obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,_,hloss,h0,h1,hrows⟩ := binned_game_witness L hL hm
  refine ⟨q,B,d,?_,hcard,hd,?_,h0⟩
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
  · have hc : 0 ≤ (1/(4 : ℕ) : ℝ)^2/(12*((∑ b, L b : ℕ) : ℝ)^3) := by positivity
    have hbound := mul_le_mul_of_nonneg_left hcube hc
    have hid := bin_error_finite_identity _ h hm hh (1/4)
    norm_num only [Nat.cast_ofNat] at hid
    refine le_trans hloss (le_trans ?_ (le_of_eq hid))
    norm_num only [Nat.cast_ofNat] at *
    simpa only [Nat.cast_sum,mul_assoc] using hbound

theorem balanced_finite_game_witness (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m) :
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      UniformWitness m d true (twoShares ((3 : ℕ)/(4 : ℕ))) q B ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/(12 : ℕ)*(1/(h : ℝ)+1/(m : ℝ))^(2 : ℕ) ∧
      response (blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
        (rigidityCross (uniformTarget m (1/(4 : ℕ)))) B)
        (blockWeights (twoShares ((3 : ℕ)/(4 : ℕ))) q) (.inl 0)=d := by
  have hw := binned_finite_game_witness (balancedLength m h)
    (balancedLength_positive m h hh hhm) (by rw [balancedLength_mass m h hh]; exact hm) hh
  have hcube : (∑ b : Fin h, (balancedLength m h b : ℝ)^3) ≤
      (∑ b, balancedLength m h b : ℝ)*(((∑ b, balancedLength m h b : ℕ) : ℝ)/(h : ℝ)+1)^2 := by
    simpa only [←Nat.cast_sum,balancedLength_mass m h hh] using balancedLength_cube_sum m h hh
  have result := hw hcube
  exact (congrArg (fun n : ℕ => ∃ (q : Fin n → ℝ) (B : Fin n → Fin n → ℝ) (d : ℝ),
    UniformWitness n d true (twoShares (3/4)) q B ∧ supportSize q ≤ min n (2*h) ∧
      0 ≤ d ∧ d ≤ (1/(4 : ℕ) : ℝ)^2/12*(1/(h : ℝ)+1/(n : ℝ))^2 ∧
      response (blockMatrix (rigidityCore (uniformTarget n (1/4)))
        (rigidityCross (uniformTarget n (1/4))) B)
        (blockWeights (twoShares (3/4)) q) (.inl 0)=d) (balancedLength_mass m h hh)).mp result

end
end SparseCompletion
