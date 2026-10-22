/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import BinnedGame

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_error_scale (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m) (r : ℝ) :
    (r^(2 : ℕ)/((12 : ℕ)*(m : ℝ)^(3 : ℕ)))*(m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ) ≤ r^(2 : ℕ)/((3 : ℕ)*(h : ℝ)^(2 : ℕ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hdim : (h : ℝ) ≤ m := by exact_mod_cast hhm
  have hsq : ((m : ℝ)+(h : ℝ))^2 ≤ 4*(m : ℝ)^2 := by nlinarith
  have heq : (r^2/(12*(m : ℝ)^3))*(m : ℝ)*((m : ℝ)/(h : ℝ)+1)^2 =
      (r^2/(12*(m : ℝ)^2*(h : ℝ)^2))*((m : ℝ)+(h : ℝ))^2 := by
    field_simp
  rw [heq]
  calc
    _ ≤ (r^2/(12*(m : ℝ)^2*(h : ℝ)^2))*(4*(m : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by field_simp; ring

theorem partition_game_witness (m h : ℕ) (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hsum : ∑ b, L b=m) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m)
    (hcube : (∑ b : Fin h, (L b : ℝ)^(3 : ℕ)) ≤ (m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ)) :
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧
      d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((3 : ℕ)*(h : ℝ)^(2 : ℕ)) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  subst m
  obtain ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,hloss,h0,h1,hrows⟩ := binned_game_witness L hL hm
  refine ⟨q,B,d,hq,hmass,hB,hb,hcard,hd,hβ,?_,h0,h1,hrows⟩
  norm_num only [Nat.cast_ofNat] at hloss
  have hc : 0 ≤ (1/16 : ℝ)/(12*((∑ b, L b : ℕ) : ℝ)^3) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcube hc
  exact le_trans hloss (le_trans hbound (by
    have hh := bin_error_scale _ h hm hh hhm (1/4)
    norm_num only [Nat.cast_ofNat] at hh
    simpa only [mul_assoc] using hh))

theorem balanced_game_witness (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (hhm : h ≤ m) :
    let qstar := uniformTarget m (1/(4 : ℕ))
    ∃ (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) (d : ℝ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j=1/(4 : ℕ)) ∧ IsSkew B ∧
      (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧ supportSize q ≤ min m ((2 : ℕ)*h) ∧
      0 ≤ d ∧ d ≤ scoreMoment qstar (exposingWeight qstar (1/(4 : ℕ))) ∧
      d ≤ (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((3 : ℕ)*(h : ℝ)^(2 : ℕ)) ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 0)=d ∧
      response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inl 1)= -d ∧
      ∀ j, response (blockMatrix (rigidityCore qstar) (rigidityCross qstar) B)
        (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) q) (.inr j) ≤ 0 := by
  norm_num only [Nat.cast_ofNat] at *
  have hc := partition_game_witness m h (balancedLength m h) (balancedLength_positive m h hh hhm)
    (balancedLength_mass m h hh) hm hh hhm (balancedLength_cube_sum m h hh)
  norm_num only [Nat.cast_ofNat] at hc
  exact hc

end
end SparseCompletion
