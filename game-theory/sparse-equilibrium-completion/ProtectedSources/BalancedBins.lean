/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.BinnedWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def balancedLength (m h : ℕ) (b : Fin h) : ℕ :=
  m/h+if b.val<m%h then 1 else 0

theorem balancedLength_positive (m h : ℕ) (hh : 0 < h) (hhm : h ≤ m) :
    ∀ b, 0 < balancedLength m h b := by
  have hq : 0 < m/h := Nat.div_pos hhm hh
  intro b
  unfold balancedLength
  split_ifs <;> omega

theorem balancedLength_mass (m h : ℕ) (hh : 0 < h) : ∑ b, balancedLength m h b=m := by
  classical
  have hr : m%h<h := Nat.mod_lt m hh
  have hf : (Finset.univ.filter fun b : Fin h => b.val<m%h) = Finset.Iio ⟨m%h,hr⟩ := by
    ext b
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio,Fin.lt_def]
  have hrem : (∑ b : Fin h, if b.val<m%h then (1 : ℕ) else 0)=m%h := by
    rw [←Finset.sum_filter,hf]
    simp only [Finset.sum_const,smul_eq_mul,mul_one,Fin.card_Iio]
  simp only [balancedLength,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,hrem]
  have hdiv := Nat.mod_add_div m h
  omega

theorem balancedLength_bound (m h : ℕ) (hh : 0 < h) (b : Fin h) :
    (balancedLength m h b : ℝ) ≤ (m : ℝ)/(h : ℝ)+1 := by
  have hhR : (0 : ℝ) < h := Nat.cast_pos.mpr hh
  have hq : ((m/h : ℕ) : ℝ) ≤ (m : ℝ)/(h : ℝ) := by
    apply (le_div_iff₀ hhR).mpr
    exact_mod_cast Nat.div_mul_le_self m h
  have hb : balancedLength m h b ≤ m/h+1 := by
    unfold balancedLength
    split_ifs <;> omega
  have hbR : (balancedLength m h b : ℝ) ≤ ((m/h : ℕ) : ℝ)+1 := by exact_mod_cast hb
  linarith

theorem balancedLength_cube_sum (m h : ℕ) (hh : 0 < h) :
    (∑ b : Fin h, (balancedLength m h b : ℝ)^(3 : ℕ)) ≤
      (m : ℝ)*((m : ℝ)/(h : ℝ)+1)^(2 : ℕ) := by
  have hc : ∀ b : Fin h, (balancedLength m h b : ℝ)^3 ≤
      ((m : ℝ)/(h : ℝ)+1)^2*(balancedLength m h b : ℝ) := by
    intro b
    have hb := balancedLength_bound m h hh b
    have hn : (0 : ℝ) ≤ balancedLength m h b := Nat.cast_nonneg _
    have hh0 : (0 : ℝ) ≤ (m : ℝ)/(h : ℝ)+1 := by positivity
    have hs : (balancedLength m h b : ℝ)^2 ≤ ((m : ℝ)/(h : ℝ)+1)^2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hs hn
    nlinarith
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin h))) (fun b _ => hc b)
  rw [←Finset.mul_sum,←Nat.cast_sum,balancedLength_mass m h hh] at hs
  nlinarith

end
end SparseCompletion
