/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import BinnedWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem uniform_score_affine (m : ℕ) (r : ℝ) :
    targetScore (uniformTarget m r) r =
      (fun j => r*(1-1/(m : ℝ))+(-((2 : ℕ) : ℝ)*r/(m : ℝ))*j.val) := by
  norm_num only [Nat.cast_ofNat] at *
  funext j
  rw [uniform_target_score]
  ring

theorem uniform_target_cuts (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    Cuts 1 r (uniformTarget m r) (targetScore (uniformTarget m r) r) := by
  have hq : ∀ j, 0 ≤ uniformTarget m r j := fun _ => div_nonneg hr (Nat.cast_nonneg _)
  have hmass := uniformTarget_mass m hm r
  have hh := completion_cuts_necessary (uniformTarget m r) (targetScore (uniformTarget m r) r)
    (orderedBlock 1) 1 r 0 hq hmass (orderedBlock_skew 1)
    (fun i j => (orderedBlock_bounds 1 (by norm_num) i j).1)
    (fun j => by rw [orderedBlock_response _ r hmass]; linarith)
  simpa only [sub_zero] using hh

theorem binned_uniform_cuts {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 ≤ r) :
    Cuts 1 r (binnedWeights L hL r) (targetScore (uniformTarget (∑ b, L b) r) r) := by
  apply call_bound_implies_cuts _ _ 1 r (by norm_num) (binned_nonneg L hL r hr)
    (binned_mass L hL r hm)
  intro z _
  have hc := binned_call_contraction L hL r hr (r*(1-1/((∑ b, L b : ℕ) : ℝ)))
    (-2*r/((∑ b, L b : ℕ) : ℝ)) z
  have hform := uniform_score_affine (∑ b, L b) r
  norm_num only [Nat.cast_ofNat] at hform
  rw [← hform] at hc
  exact le_trans hc (cuts_imply_call_bound _ _ 1 r (by norm_num)
    (uniform_target_cuts _ hm r hr) z)

theorem binned_uniform_score_mean {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) :
    scoreMoment (binnedWeights L hL r) (targetScore (uniformTarget (∑ b, L b) r) r)=0 := by
  have hh := binned_affine_moment L hL r (r*(1-1/((∑ b, L b : ℕ) : ℝ)))
    (-2*r/((∑ b, L b : ℕ) : ℝ))
  have hform := uniform_score_affine (∑ b, L b) r
  norm_num only [Nat.cast_ofNat] at hform
  rw [← hform] at hh
  change (∑ j, binnedWeights L hL r j*targetScore (uniformTarget (∑ b, L b) r) r j)=0
  rw [hform,hh]
  have ht := target_score_moment_zero (uniformTarget (∑ b, L b) r) r
    (uniformTarget_mass _ hm r)
  simpa only [scoreMoment,uniformTarget,←Finset.mul_sum] using ht

theorem binned_uniform_residual_completion {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 ≤ r) :
    ∃ B : Fin (∑ b, L b) → Fin (∑ b, L b) → ℝ,
      IsSkew B ∧ (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
      ∀ i, targetScore (uniformTarget (∑ b, L b) r) r i+
        response B (binnedWeights L hL r) i ≤ 0 := by
  apply completion_of_cuts_and_guards _ _ 1 r 0 (by norm_num)
    (binned_nonneg L hL r hr) (binned_mass L hL r hm)
  · simpa only [sub_zero] using binned_uniform_cuts L hL hm r hr
  · intro j
    simpa only [zero_add,one_mul] using
      (targetScore_bounds (uniformTarget (∑ b, L b) r)
        (fun _ => div_nonneg hr (Nat.cast_nonneg _)) r (uniformTarget_mass _ hm r) j).2

end
end SparseCompletion
