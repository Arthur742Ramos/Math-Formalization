/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.BinnedCompletion
public import ProtectedSources.BalancedBins

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem binned_quadratic_loss {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r : ℝ) (hr : 0 ≤ r) (a d : ℝ) :
    let qstar := uniformTarget (∑ b, L b) r
    let q := binnedWeights L hL r
    let f := fun j : Fin (∑ b, L b) => (a+d*j.val)^(2 : ℕ)
    0 ≤ scoreMoment qstar f-scoreMoment q f ∧
    scoreMoment qstar f-scoreMoment q f ≤
      (r/((∑ b, L b : ℕ) : ℝ))*d^(2 : ℕ)/(12 : ℕ)*∑ b, (L b : ℝ)^(3 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  let Δ := fun b : Fin h =>
    (∑ i : Fin (L b), (a+d*(binIndex L b i).val)^2)-
      ∑ i : Fin (L b), binCompressedWeights (L b) (hL b) i*(a+d*(binIndex L b i).val)^2
  have hb : ∀ b, 0 ≤ Δ b ∧ Δ b ≤ d^2*(L b : ℝ)^3/12 := by
    intro b
    have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val=(a+d*binStart L b)+d*i.val := by
      intro i
      rw [binIndex_val]
      push_cast
      ring
    dsimp only [Δ]
    simp only [hform]
    have hh := bin_compressed_quadratic_loss (L b) (hL b) (a+d*binStart L b) d
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have he : scoreMoment (uniformTarget (∑ b, L b) r) (fun j => (a+d*j.val)^2)-
      scoreMoment (binnedWeights L hL r) (fun j => (a+d*j.val)^2) =
      (r/((∑ b, L b : ℕ) : ℝ))*∑ b, Δ b := by
    unfold scoreMoment
    rw [binned_moment]
    simp only [uniformTarget,←Finset.mul_sum]
    rw [sum_bin_partition L,←mul_sub,←Finset.sum_sub_distrib]
  rw [he]
  have hc : 0 ≤ r/((∑ b, L b : ℕ) : ℝ) := by positivity
  constructor
  · exact mul_nonneg hc (Finset.sum_nonneg fun b _ => (hb b).1)
  · have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin h))) (fun b _ => (hb b).2)
    have heq : (∑ b : Fin h, d^2*(L b : ℝ)^3/12)=d^2/12*∑ b, (L b : ℝ)^3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [heq] at hs
    have hh := mul_le_mul_of_nonneg_left hs hc
    nlinarith

theorem binned_exposing_loss {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 ≤ r) :
    let qstar := uniformTarget (∑ b, L b) r
    let q := binnedWeights L hL r
    let w := exposingWeight qstar r
    0 ≤ scoreMoment qstar w-scoreMoment q w ∧
    scoreMoment qstar w-scoreMoment q w ≤
      r^(2 : ℕ)/((12 : ℕ)*((∑ b, L b : ℕ) : ℝ)^(3 : ℕ))*∑ b, (L b : ℝ)^(3 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  let m := ∑ b, L b
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let f := fun j : Fin m => (((m : ℝ)-1)/(m : ℝ)+(-1/(m : ℝ))*j.val)^2
  have hw : exposingWeight (uniformTarget m r) r=(fun j => r*f j) := by
    funext j
    rw [uniform_exposing_weight]
    dsimp only [f]
    congr 1
    congr 1
    ring
  have he : scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r)=
      r*(scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f) := by
    rw [hw]
    simp only [scoreMoment,mul_left_comm _ r,←Finset.mul_sum]
    ring
  change 0 ≤ scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r) ∧ _
  rw [he]
  have hq := binned_quadratic_loss L hL r hr (((m : ℝ)-1)/(m : ℝ)) (-1/(m : ℝ))
  norm_num only [Nat.cast_ofNat] at hq
  change 0 ≤ scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f ∧ _ at hq
  constructor
  · exact mul_nonneg hr hq.1
  · have hh := mul_le_mul_of_nonneg_left hq.2 hr
    convert hh using 1
    dsimp only [m]
    field_simp

end
end SparseCompletion
