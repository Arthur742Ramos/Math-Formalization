/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.BinCompression

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def binIndex {h : ℕ} (L : Fin h → ℕ) (b : Fin h) (i : Fin (L b)) : Fin (∑ b, L b) :=
  finSigmaFinEquiv ⟨b,i⟩

def binStart {h : ℕ} (L : Fin h → ℕ) (b : Fin h) : ℕ :=
  ∑ i : Fin b.val, L (Fin.castLE b.isLt.le i)

theorem binIndex_val {h : ℕ} (L : Fin h → ℕ) (b : Fin h) (i : Fin (L b)) :
    (binIndex L b i).val=binStart L b+i.val := finSigmaFinEquiv_apply ⟨b,i⟩

theorem sum_bin_partition {h : ℕ} (L : Fin h → ℕ) (f : Fin (∑ b, L b) → ℝ) :
    (∑ j, f j)=∑ b, ∑ i : Fin (L b), f (binIndex L b i) := by
  simpa only [Fintype.sum_sigma,binIndex] using (Equiv.sum_comp finSigmaFinEquiv f).symm

def binnedLabel {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (b : Fin h × Fin 2) :
    Fin (∑ b, L b) := binIndex L b.1 (binCompressedLabel (L b.1) (hL b.1) b.2)

def binnedWeights {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ) :
    Fin (∑ b, L b) → ℝ :=
  pushWeights (binnedLabel L hL) (fun b => (r/((∑ b, L b : ℕ) : ℝ))*(L b.1 : ℝ)/(2 : ℕ))

theorem binned_nonneg {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ) (hr : 0 ≤ r) :
    ∀ j, 0 ≤ binnedWeights L hL r j := by
  exact pushWeights_nonneg _ _ (fun _ => by positivity)

theorem binned_support {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ) :
    supportSize (binnedWeights L hL r) ≤ min (∑ b, L b) ((2 : ℕ)*h) := by
  classical
  have hdim := supportSize_le_dimension (binnedWeights L hL r)
  have hc : supportSize (binnedWeights L hL r) ≤ 2*h := by
    unfold supportSize residualSupport binnedWeights
    exact le_trans (pushWeights_support_card _ _) (by simp [mul_comm])
  omega

theorem binned_moment {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ)
    (f : Fin (∑ b, L b) → ℝ) :
    (∑ j, binnedWeights L hL r j*f j)=
      (r/((∑ b, L b : ℕ) : ℝ))*∑ b, ∑ i : Fin (L b),
        binCompressedWeights (L b) (hL b) i*f (binIndex L b i) := by
  rw [binnedWeights,pushWeights_moment,Finset.mul_sum]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro b _
  rw [bin_compressed_moment]
  simp only [binnedLabel,binCompressedLabel,Fin.val_zero,Fin.val_one,ite_true,one_ne_zero,ite_false,Nat.cast_ofNat]
  ring

theorem binned_mass {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℝ)
    (hm : 0 < ∑ b, L b) : (∑ j, binnedWeights L hL r j)=r := by
  have hh := binned_moment L hL r (fun _ => 1)
  simp only [mul_one,bin_compressed_mass,←Nat.cast_sum] at hh
  have hne : ((∑ b, L b : ℕ) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  rw [hh]
  field_simp

theorem binned_affine_moment {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r a d : ℝ) :
    (∑ j, binnedWeights L hL r j*(a+d*j.val))=
      (r/((∑ b, L b : ℕ) : ℝ))*∑ j : Fin (∑ b, L b), (a+d*j.val) := by
  rw [binned_moment,sum_bin_partition L]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val = (a+d*binStart L b)+d*i.val := by
    intro i
    rw [binIndex_val]
    push_cast
    ring
  simp only [hform]
  exact bin_compressed_affine_moment (L b) (hL b) _ _

theorem binned_call_contraction {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r : ℝ) (hr : 0 ≤ r) (a d z : ℝ) :
    call (binnedWeights L hL r) (fun j => a+d*j.val) z ≤
      call (uniformTarget (∑ b, L b) r) (fun j => a+d*j.val) z := by
  unfold call
  rw [binned_moment]
  have hright : (∑ j : Fin (∑ b, L b), uniformTarget (∑ b, L b) r j*max (a+d*j.val-z) 0) =
      (r/((∑ b, L b : ℕ) : ℝ))*∑ j : Fin (∑ b, L b), max (a+d*j.val-z) 0 := by
    simp only [uniformTarget,Finset.mul_sum]
  rw [hright,sum_bin_partition L]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro b _
  have hform : ∀ i : Fin (L b), a+d*(binIndex L b i).val-z = (a+d*binStart L b)+d*i.val-z := by
    intro i
    rw [binIndex_val]
    push_cast
    ring
  simp only [hform]
  exact bin_compressed_calls (L b) (hL b) _ _ _

end
end SparseCompletion
