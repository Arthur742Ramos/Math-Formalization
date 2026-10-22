/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import CoreLower

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Moving a symmetric pair inward decreases every call payoff. -/
theorem inner_pair_call_le (a u v b z : ℝ) (hau : a ≤ u) (huv : u ≤ v)
    (hvb : v ≤ b) (hsum : a+b=u+v) :
    max (u-z) 0+max (v-z) 0 ≤ max (a-z) 0+max (b-z) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

/-- The two central original labels, coalescing when the bin has odd size. -/
def binLower (L : ℕ) (hL : 0 < L) : Fin L := ⟨(L-1)/2,lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hL (Nat.zero_lt_succ 0))⟩
def binUpper (L : ℕ) (hL : 0 < L) : Fin L := ⟨L/2,Nat.div_lt_self hL (Nat.lt_succ_self 1)⟩

theorem bin_middle_sum (L : ℕ) (hL : 0 < L) :
    (binLower L hL).val+(binUpper L hL).val=L-1 := by
  simp only [binLower,binUpper]
  omega

theorem bin_middle_order (L : ℕ) (hL : 0 < L) : binLower L hL ≤ binUpper L hL := by
  simp only [Fin.le_def,binLower,binUpper]
  omega

theorem bin_middle_outer (L : ℕ) (hL : 0 < L) (i : Fin L) :
    min i.val (L-1-i.val) ≤ (binLower L hL).val ∧
      (binUpper L hL).val ≤ max i.val (L-1-i.val) := by
  simp only [binLower,binUpper]
  omega

theorem bin_pair_call_le (L : ℕ) (hL : 0 < L) (a d z : ℝ) (hd : 0 ≤ d) (i : Fin L) :
    max (a+d*(binLower L hL).val-z) 0+max (a+d*(binUpper L hL).val-z) 0 ≤
      max (a+d*i.val-z) 0+max (a+d*(L-1-i.val : ℕ)-z) 0 := by
  have houter := bin_middle_outer L hL i
  have hmiddle := bin_middle_order L hL
  have hsum := bin_middle_sum L hL
  have hi : i.val ≤ L-1 := by omega
  by_cases hii : i.val ≤ L-1-i.val
  · have hlo : i.val ≤ (binLower L hL).val := by simpa only [min_eq_left hii] using houter.1
    have hhi : (binUpper L hL).val ≤ L-1-i.val := by simpa only [max_eq_right hii] using houter.2
    apply inner_pair_call_le
    · have hh : (i.val : ℝ) ≤ (binLower L hL).val := by exact_mod_cast hlo
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binLower L hL).val : ℝ) ≤ (binUpper L hL).val := by exact_mod_cast hmiddle
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binUpper L hL).val : ℝ) ≤ (L-1-i.val : ℕ) := by exact_mod_cast hhi
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : (i.val : ℝ)+(L-1-i.val : ℕ) =
          (binLower L hL).val+(binUpper L hL).val := by
        exact_mod_cast (show i.val+(L-1-i.val)= (binLower L hL).val+(binUpper L hL).val by omega)
      nlinarith
  · have hii' : L-1-i.val ≤ i.val := by omega
    have hlo : L-1-i.val ≤ (binLower L hL).val := by simpa only [min_eq_right hii'] using houter.1
    have hhi : (binUpper L hL).val ≤ i.val := by simpa only [max_eq_left hii'] using houter.2
    rw [add_comm (max (a+d*(i.val : ℝ)-z) 0)]
    apply inner_pair_call_le
    · have hh : ((L-1-i.val : ℕ) : ℝ) ≤ (binLower L hL).val := by exact_mod_cast hlo
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binLower L hL).val : ℝ) ≤ (binUpper L hL).val := by exact_mod_cast hmiddle
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : ((binUpper L hL).val : ℝ) ≤ i.val := by exact_mod_cast hhi
      nlinarith [mul_nonneg hd (sub_nonneg.mpr hh)]
    · have hh : (i.val : ℝ)+(L-1-i.val : ℕ) =
          (binLower L hL).val+(binUpper L hL).val := by
        exact_mod_cast (show i.val+(L-1-i.val)= (binLower L hL).val+(binUpper L hL).val by omega)
      nlinarith


theorem bin_call_compression_nonneg (L : ℕ) (hL : 0 < L) (a d z : ℝ) (hd : 0 ≤ d) :
    (L : ℝ)*(max (a+d*(binLower L hL).val-z) 0+
      max (a+d*(binUpper L hL).val-z) 0) ≤
      (2 : ℕ)*∑ i : Fin L, max (a+d*i.val-z) 0 := by
  norm_num only [Nat.cast_ofNat] at *
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L)))
    (fun i _ => bin_pair_call_le L hL a d z hd i)
  have hrev : (∑ i : Fin L, max (a+d*(L-1-i.val : ℕ)-z) 0) =
      ∑ i : Fin L, max (a+d*i.val-z) 0 := by
    simpa only [Fin.revPerm_apply,Fin.val_rev,Nat.sub_sub,Nat.add_comm] using
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin L)) (fun i => max (a+d*i.val-z) 0))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_add_distrib,hrev] at hs
  linarith

theorem negative_call_identity (x : ℝ) : max (-x) 0=max x 0-x := by
  simp only [max_def]
  split_ifs <;> linarith

theorem bin_call_compression (L : ℕ) (hL : 0 < L) (a d z : ℝ) :
    (L : ℝ)*(max (a+d*(binLower L hL).val-z) 0+
      max (a+d*(binUpper L hL).val-z) 0) ≤
      (2 : ℕ)*∑ i : Fin L, max (a+d*i.val-z) 0 := by
  norm_num only [Nat.cast_ofNat] at *
  by_cases hd : 0 ≤ d
  · exact bin_call_compression_nonneg L hL a d z hd
  · have hh := bin_call_compression_nonneg L hL (-a) (-d) (-z) (by linarith)
    have heq : ∀ i : Fin L, max (-a+-d*i.val- -z) 0 = max (a+d*i.val-z) 0-(a+d*i.val-z) := by
      intro i
      convert negative_call_identity (a+d*i.val-z) using 1
      congr 1
      ring
    simp only [heq] at hh
    have hsum : (∑ i : Fin L, (a+d*i.val-z)) =
        (L : ℝ)*((a+d*(binLower L hL).val-z)+(a+d*(binUpper L hL).val-z))/2 := by
      have hidx : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
        rw [Fin.sum_univ_eq_sum_range]
        exact first_index_moment L
      have hmid := bin_middle_sum L hL
      have hmidR : ((binLower L hL).val : ℝ)+(binUpper L hL).val=(L : ℝ)-1 := by
        have hcast : ((L-1 : ℕ) : ℝ)=(L : ℝ)-1 := by
          have hh : ((L-1 : ℕ) : ℝ)+1=(L : ℝ) := by exact_mod_cast (show (L-1)+1=L by omega)
          linarith
        rw [←hcast]
        exact_mod_cast hmid
      simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,hidx]
      nlinarith [congrArg (fun x : ℝ => (L : ℝ)*d*x) hmidR]
    rw [Finset.sum_sub_distrib,hsum] at hh
    nlinarith


theorem bin_middle_sum_real (L : ℕ) (hL : 0 < L) :
    ((binLower L hL).val : ℝ)+(binUpper L hL).val=(L : ℝ)-1 := by
  have hh : ((L-1 : ℕ) : ℝ)+1=(L : ℝ) := by exact_mod_cast (show (L-1)+1=L by omega)
  have hs : ((binLower L hL).val : ℝ)+(binUpper L hL).val=((L-1 : ℕ) : ℝ) :=
    by exact_mod_cast bin_middle_sum L hL
  linarith

theorem bin_affine_mean (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i : Fin L, (a+d*i.val)) =
      (L : ℝ)*((a+d*(binLower L hL).val)+(a+d*(binUpper L hL).val))/(2 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hidx : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact first_index_moment L
  have hm := bin_middle_sum_real L hL
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,←Finset.mul_sum,hidx]
  nlinarith [congrArg (fun x : ℝ => (L : ℝ)*d*x) hm]

theorem bin_quadratic_loss_identity (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (L : ℝ)/(2 : ℕ)*((a+d*(binLower L hL).val)^(2 : ℕ)+(a+d*(binUpper L hL).val)^(2 : ℕ)) =
      d^(2 : ℕ)*(L : ℝ)/(12 : ℕ)*((L : ℝ)^(2 : ℕ)-1-((3 : ℕ) : ℝ)*((binLower L hL).val-(binUpper L hL).val : ℝ)^(2 : ℕ)) := by
  norm_num only [Nat.cast_ofNat] at *
  have hidx : (∑ i : Fin L, (i.val : ℝ)) = (L : ℝ)*((L : ℝ)-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact first_index_moment L
  have hsq : (∑ i : Fin L, (i.val : ℝ)^2) =
      (L : ℝ)*(((L : ℝ)-1)/2)^2+(L : ℝ)*((L : ℝ)^2-1)/12 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)^2)]
    simpa only [zero_add,one_mul,zero_sub,neg_sq,one_pow,mul_one,sub_zero] using
      constant_run_error_identity L 0 1 0
  have hm := bin_middle_sum_real L hL
  have hv : ((binUpper L hL).val : ℝ)=(L : ℝ)-1-(binLower L hL).val := by linarith
  have he : (∑ i : Fin L, (a+d*i.val)^2) =
      (L : ℝ)*a^2+2*a*d*(∑ i : Fin L, (i.val : ℝ))+d^2*(∑ i : Fin L, (i.val : ℝ)^2) := by
    simp only [add_sq,mul_pow,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
    ring
  rw [he,hidx,hsq,hv]
  ring

theorem bin_middle_gap_bound (L : ℕ) (hL : 0 < L) :
    ((binLower L hL).val-(binUpper L hL).val : ℝ)^(2 : ℕ) ≤ 1 := by
  have hh : (binLower L hL).val ≤ (binUpper L hL).val ∧
      (binUpper L hL).val ≤ (binLower L hL).val+1 := by
    simp only [binLower,binUpper]
    omega
  have h1 : ((binLower L hL).val : ℝ) ≤ (binUpper L hL).val := by exact_mod_cast hh.1
  have h2 : ((binUpper L hL).val : ℝ) ≤ (binLower L hL).val+1 := by exact_mod_cast hh.2
  nlinarith

theorem bin_quadratic_loss_bounds (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    0 ≤ (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (L : ℝ)/(2 : ℕ)*((a+d*(binLower L hL).val)^(2 : ℕ)+(a+d*(binUpper L hL).val)^(2 : ℕ)) ∧
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (L : ℝ)/(2 : ℕ)*((a+d*(binLower L hL).val)^(2 : ℕ)+(a+d*(binUpper L hL).val)^(2 : ℕ)) ≤
      d^(2 : ℕ)*(L : ℝ)^(3 : ℕ)/(12 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  have hid := bin_quadratic_loss_identity L hL a d
  norm_num only [Nat.cast_ofNat] at hid
  rw [hid]
  have hL0 : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hcoef : 0 ≤ d^2*(L : ℝ)/12 := by positivity
  have hgap := bin_middle_gap_bound L hL
  constructor
  · apply mul_nonneg hcoef
    by_cases he : L=1
    · subst L
      norm_num [binLower,binUpper]
    · have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
      nlinarith
  · have hsq : 0 ≤ ((binLower L hL).val-(binUpper L hL).val : ℝ)^2 := sq_nonneg _
    have hp := mul_nonneg hcoef (show 0 ≤ 1+3*((binLower L hL).val-(binUpper L hL).val : ℝ)^2 by positivity)
    nlinarith


/-- Coalescing labels retain a single middle action in an odd bin. -/
def binCompressedLabel (L : ℕ) (hL : 0 < L) (b : Fin 2) : Fin L :=
  if b.val=0 then binLower L hL else binUpper L hL

def binCompressedWeights (L : ℕ) (hL : 0 < L) : Fin L → ℝ :=
  pushWeights (binCompressedLabel L hL) (fun _ => (L : ℝ)/(2 : ℕ))

theorem bin_compressed_nonneg (L : ℕ) (hL : 0 < L) :
    ∀ i, 0 ≤ binCompressedWeights L hL i := by
  exact pushWeights_nonneg _ _ (fun _ => by positivity)

theorem bin_compressed_mass (L : ℕ) (hL : 0 < L) :
    (∑ i, binCompressedWeights L hL i)=(L : ℝ) := by
  rw [binCompressedWeights,pushWeights_mass,Fin.sum_univ_two]
  norm_num

theorem bin_compressed_support (L : ℕ) (hL : 0 < L) :
    (Finset.univ.filter fun i => binCompressedWeights L hL i ≠ 0).card ≤ min L (2 : ℕ) := by
  classical
  apply le_min
  · exact le_trans (Finset.card_filter_le _ _) (by simp)
  · exact le_trans (pushWeights_support_card _ _) (by simp)

theorem bin_compressed_moment (L : ℕ) (hL : 0 < L) (f : Fin L → ℝ) :
    (∑ i, binCompressedWeights L hL i*f i)=
      (L : ℝ)/(2 : ℕ)*(f (binLower L hL)+f (binUpper L hL)) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [binCompressedWeights,pushWeights_moment,Fin.sum_univ_two]
  simp only [binCompressedLabel,Fin.val_zero,Fin.val_one,ite_true,one_ne_zero,ite_false,Nat.cast_ofNat]
  ring

theorem bin_compressed_affine_moment (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i, binCompressedWeights L hL i*(a+d*i.val))=∑ i : Fin L, (a+d*i.val) := by
  rw [bin_compressed_moment,bin_affine_mean L hL a d]
  ring

theorem bin_compressed_calls (L : ℕ) (hL : 0 < L) (a d z : ℝ) :
    (∑ i, binCompressedWeights L hL i*max (a+d*i.val-z) 0) ≤
      ∑ i : Fin L, max (a+d*i.val-z) 0 := by
  rw [bin_compressed_moment]
  have hh := bin_call_compression L hL a d z
  norm_num only [Nat.cast_ofNat] at *
  linarith

theorem bin_compressed_quadratic_loss (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    0 ≤ (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (∑ i, binCompressedWeights L hL i*(a+d*i.val)^(2 : ℕ)) ∧
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (∑ i, binCompressedWeights L hL i*(a+d*i.val)^(2 : ℕ)) ≤ d^(2 : ℕ)*(L : ℝ)^(3 : ℕ)/(12 : ℕ) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [bin_compressed_moment]
  exact bin_quadratic_loss_bounds L hL a d

end
end SparseCompletion
