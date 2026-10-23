/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.MidpointExact

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def binParityTerm (L : ℕ) : ℝ :=
  (L : ℝ)*((L : ℝ)^2-(if L%2=0 then ((4 : ℕ) : ℝ) else 1))

theorem binned_quadratic_loss_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r a d : ℝ) :
    scoreMoment (uniformTarget (∑ b, L b) r) (fun j => (a+d*j.val)^(2 : ℕ))-
      scoreMoment (binnedWeights L hL r) (fun j => (a+d*j.val)^(2 : ℕ)) =
      (r/((∑ b, L b : ℕ) : ℝ))*d^(2 : ℕ)/(12 : ℕ)*∑ b, binParityTerm (L b) := by
  norm_num only [Nat.cast_ofNat] at *
  let Δ := fun b : Fin h =>
    (∑ i : Fin (L b), (a+d*(binIndex L b i).val)^2)-
      ∑ i : Fin (L b), binCompressedWeights (L b) (hL b) i*(a+d*(binIndex L b i).val)^2
  have hb : ∀ b, Δ b=d^2/12*binParityTerm (L b) := by
    intro b
    have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val=(a+d*binStart L b)+d*i.val := by
      intro i
      rw [binIndex_val]
      push_cast
      ring
    dsimp only [Δ]
    simp only [hform]
    rw [bin_quadratic_parity_identity]
    unfold binParityTerm
    split_ifs <;> norm_num only [Nat.cast_ofNat] <;> ring
  have he : scoreMoment (uniformTarget (∑ b, L b) r) (fun j => (a+d*j.val)^2)-
      scoreMoment (binnedWeights L hL r) (fun j => (a+d*j.val)^2) =
      (r/((∑ b, L b : ℕ) : ℝ))*∑ b, Δ b := by
    unfold scoreMoment
    rw [binned_moment]
    simp only [uniformTarget,←Finset.mul_sum]
    rw [sum_bin_partition L,←mul_sub,←Finset.sum_sub_distrib]
  rw [he]
  simp only [hb,←Finset.mul_sum]
  ring

theorem binned_exposing_loss_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) :
    let qstar := uniformTarget (∑ b, L b) r
    let q := binnedWeights L hL r
    let w := exposingWeight qstar r
    scoreMoment qstar w-scoreMoment q w =
      r^(2 : ℕ)/((12 : ℕ)*((∑ b, L b : ℕ) : ℝ)^(3 : ℕ))*∑ b, binParityTerm (L b) := by
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
  change scoreMoment (uniformTarget m r) (exposingWeight (uniformTarget m r) r)-
      scoreMoment (binnedWeights L hL r) (exposingWeight (uniformTarget m r) r)=_
  rw [he]
  have hq := binned_quadratic_loss_exact L hL r (((m : ℝ)-1)/(m : ℝ)) (-1/(m : ℝ))
  change scoreMoment (uniformTarget m r) f-scoreMoment (binnedWeights L hL r) f=_ at hq
  norm_num only [Nat.cast_ofNat] at hq
  rw [hq]
  dsimp only [m]
  field_simp

theorem binned_odd_support {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hodd : ∀ b, L b%(2 : ℕ)≠0) (r : ℝ) : supportSize (binnedWeights L hL r) ≤ h := by
  classical
  let s := Finset.univ.image (fun b : Fin h => binIndex L b (binLower (L b) (hL b)))
  have hs : ∀ k : Fin h × Fin 2, binnedLabel L hL k ∈ s := by
    intro k
    apply Finset.mem_image.mpr
    refine ⟨k.1,Finset.mem_univ _,?_⟩
    simp only [binnedLabel,binCompressedLabel,←bin_middle_odd_same (L k.1) (hL k.1) (hodd k.1),ite_self]
  have hsup : residualSupport (binnedWeights L hL r) ⊆ s := by
    intro i hi
    by_contra he
    have hz : binnedWeights L hL r i=0 := by
      unfold binnedWeights
      exact pushWeights_zero_outside _ _ s hs i he
    exact (Finset.mem_filter.mp hi).2 hz
  exact le_trans (Finset.card_le_card hsup)
    (le_trans (Finset.card_image_le) (by simp))


theorem binned_middle_positive {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 < r) (b : Fin h) :
    0 < binnedWeights L hL r (binIndex L b (binLower (L b) (hL b))) := by
  have hmR : (0 : ℝ) < (∑ b, L b : ℕ) := Nat.cast_pos.mpr hm
  have hLb : (0 : ℝ) < L b := Nat.cast_pos.mpr (hL b)
  have hnonneg : ∀ k : Fin h × Fin 2,
      0 ≤ (if binnedLabel L hL k=binIndex L b (binLower (L b) (hL b)) then
        (r/((∑ b, L b : ℕ) : ℝ))*(L k.1 : ℝ)/(2 : ℕ) else 0) := by
    intro k
    split_ifs <;> positivity
  have hsingle := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin h × Fin 2))) => hnonneg k)
    (Finset.mem_univ (b,(0 : Fin 2)))
  have hlab : binnedLabel L hL (b,(0 : Fin 2))=binIndex L b (binLower (L b) (hL b)) := by
    simp only [binnedLabel,binCompressedLabel,Fin.val_zero,ite_true]
  simp only [hlab,ite_true] at hsingle
  change 0 < ∑ k : Fin h × Fin 2, if binnedLabel L hL k=binIndex L b (binLower (L b) (hL b)) then
    (r/((∑ b, L b : ℕ) : ℝ))*(L k.1 : ℝ)/(2 : ℕ) else 0
  exact lt_of_lt_of_le (by positivity) hsingle

theorem binned_middle_injective {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) :
    Function.Injective (fun b => binIndex L b (binLower (L b) (hL b))) := by
  intro b c he
  change finSigmaFinEquiv ⟨b,binLower (L b) (hL b)⟩=
    finSigmaFinEquiv ⟨c,binLower (L c) (hL c)⟩ at he
  exact congrArg Sigma.fst (finSigmaFinEquiv.injective he)

theorem binned_support_lower {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (r : ℝ) (hr : 0 < r) : h ≤ supportSize (binnedWeights L hL r) := by
  classical
  let s := Finset.univ.image (fun b : Fin h => binIndex L b (binLower (L b) (hL b)))
  have hs : s ⊆ residualSupport (binnedWeights L hL r) := by
    intro i hi
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hi
    subst i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ne_of_gt (binned_middle_positive L hL hm r hr b)⟩
  have hcard : s.card=h := by
    dsimp only [s]
    rw [Finset.card_image_of_injective _ (binned_middle_injective L hL)]
    simp
  calc
    h = s.card := hcard.symm
    _ ≤ supportSize (binnedWeights L hL r) := Finset.card_le_card hs

theorem binned_odd_support_exact {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (hm : 0 < ∑ b, L b) (hodd : ∀ b, L b%(2 : ℕ)≠0) (r : ℝ) (hr : 0 < r) :
    supportSize (binnedWeights L hL r)=h := by
  exact le_antisymm (binned_odd_support L hL hodd r) (binned_support_lower L hL hm r hr)

end
end SparseCompletion
