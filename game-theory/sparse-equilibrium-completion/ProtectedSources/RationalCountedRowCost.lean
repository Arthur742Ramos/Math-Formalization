/- AI-assisted formalization under the repository Apache-2.0 license.
Intrinsic ledger bounds count rational arithmetic and rational order tests;
index/Boolean bookkeeping, table loading and bit costs are separate. -/
module
public import ProtectedSources.RationalCountedTableRows
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_counted_omitted_zero_cost {m s : ℕ} (c : RationalTableCertificate 0 m s)
    (D : Vector (Vector ℚ 0) m) (threshold : ℚ) :
    (rationalCountedTableOmitted c D threshold).2 ≤ 1 := by
  simp only [rationalCountedTableOmitted,ite_true]
  split_ifs <;> norm_num

theorem rational_counted_omitted_positive_cost {k m s : ℕ} (c : RationalTableCertificate k m s)
    (D : Vector (Vector ℚ k) m) (threshold : ℚ) (hk : k ≠ 0) :
    (rationalCountedTableOmitted c D threshold).2 ≤ m*(((2 : ℕ))*k+1) := by
  simp only [rationalCountedTableOmitted,hk,ite_false,rational_counted_all_calls]
  calc
    _ ≤ ∑ _ : Fin m,(((2 : ℕ))*k+1) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp only [rational_counted_fin_dot_calls] <;> omega
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem rational_counted_rows_exact_ledger {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableRows c K D M σ).2=
      ((2 : ℕ))*s+((2 : ℕ))+k*(((2 : ℕ))*k+((2 : ℕ))*s+((2 : ℕ)))+
        s*(((2 : ℕ))*k+((2 : ℕ))*s+((2 : ℕ)))+
        (rationalCountedTableOmitted c D (σ+M*(∑ j,c.weights.get j))).2 := by
  simp only [rationalCountedTableRows,rational_counted_fin_dot_calls,
    rational_counted_all_calls,rational_counted_fin_dot_value,mul_one,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem rational_counted_rows_quadratic_bound {k m s : ℕ}
    (c : RationalTableCertificate k m s) (K : Vector (Vector ℚ k) k)
    (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableRows c K D M σ).2 ≤
      ((16 : ℕ))*(1+(k+m)*k+s*s) := by
  rw [rational_counted_rows_exact_ledger]
  by_cases hk : k=0
  · subst k
    have ho := rational_counted_omitted_zero_cost c D (σ+M*(∑ j,c.weights.get j))
    have hs := Nat.le_mul_self s
    nlinarith
  · have ho := rational_counted_omitted_positive_cost c D (σ+M*(∑ j,c.weights.get j)) hk
    have hsm : s ≤ m := by
      have hh := Finset.card_le_card (Finset.subset_univ (rationalTableSupport c))
      simpa only [rational_table_support_card,Finset.card_univ,Fintype.card_fin] using hh
    have hk1 : 1 ≤ k := by omega
    have hsk := Nat.mul_le_mul_right k hsm
    have hmk := Nat.mul_le_mul_left m hk1
    have hkk := Nat.le_mul_self k
    have hss := Nat.le_mul_self s
    nlinarith

end SparseCompletion
