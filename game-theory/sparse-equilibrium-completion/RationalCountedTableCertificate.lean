/- AI-assisted formalization under the repository Apache-2.0 license.
Finite-table checker with intrinsic unit arithmetic/comparison ledger.
Table loading, index operations and bit costs are not charged by this ledger. -/
module
public import RationalTableConditions
public import RationalCountedRowCost
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCountedTableCertificate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) : Bool × ℕ :=
  let lower := -M
  let pmass := rationalCountedFinDot c.anchors.get (fun _ => 1)
  let qmass := rationalCountedFinDot c.weights.get (fun _ => 1)
  let tests := rationalCountedConjunction [
    (decide (0 ≤ M),1),
    rationalCountedAll (fun h : Fin k => (decide (0 ≤ c.anchors.get h),1)),
    rationalCountedAll (fun j : Fin s => (decide (0 ≤ c.weights.get j),1)),
    (decide (pmass.1+qmass.1=1),pmass.2+qmass.2+((2 : ℕ))),
    rationalCountedAll (fun h : Fin k => rationalCountedAll (fun h' : Fin k =>
      (decide ((K.get h).get h' = -(K.get h').get h ∧
        lower ≤ (K.get h).get h' ∧ (K.get h).get h' ≤ M),((4 : ℕ))))),
    rationalCountedAll (fun i : Fin m => rationalCountedAll (fun h : Fin k =>
      (decide (lower ≤ (D.get i).get h ∧ (D.get i).get h ≤ M),((2 : ℕ))))),
    rationalCountedAll (fun i : Fin s => rationalCountedAll (fun j : Fin s =>
      (decide ((c.residual.get i).get j = -(c.residual.get j).get i ∧
        lower ≤ (c.residual.get i).get j ∧ (c.residual.get i).get j ≤ M),((4 : ℕ))))),
    rationalCountedTableRows c K D M σ]
  (tests.1,tests.2+1)

theorem rational_counted_table_certificate_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableCertificate c K D M σ).1=true ↔ rationalTableConditions c K D M σ := by
  simp only [rationalCountedTableCertificate,rational_counted_conjunction_value,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,rational_counted_all_value,
    rational_counted_fin_dot_value,decide_eq_true_eq,mul_one,rational_counted_table_rows_value]
  unfold rationalTableConditions
  constructor
  · rintro ⟨hM,hp,hq,hn,hK,hD,hB,hr⟩
    exact ⟨hM,hp,hq,hn,(fun a b => (hK a b).1),(fun a b => (hK a b).2),hD,
      (fun i j => (hB i j).1),(fun i j => (hB i j).2),hr⟩
  · rintro ⟨hM,hp,hq,hn,hKs,hKb,hD,hBs,hBb,hr⟩
    exact ⟨hM,hp,hq,hn,(fun a b => ⟨hKs a b,hKb a b⟩),hD,
      (fun i j => ⟨hBs i j,hBb i j⟩),hr⟩

theorem rational_counted_table_certificate_ledger {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableCertificate c K D M σ).2=
      ((3 : ℕ))*k+((3 : ℕ))*s+((4 : ℕ))+((4 : ℕ))*k*k+((2 : ℕ))*m*k+
        ((4 : ℕ))*s*s+(rationalCountedTableRows c K D M σ).2 := by
  simp only [rationalCountedTableCertificate,rational_counted_conjunction_calls,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,rational_counted_all_calls,
    rational_counted_fin_dot_calls,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id]
  ring

theorem rational_counted_table_certificate_quadratic_bound {k m s : ℕ}
    (c : RationalTableCertificate k m s) (K : Vector (Vector ℚ k) k)
    (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalCountedTableCertificate c K D M σ).2 ≤
      ((64 : ℕ))*(1+(k+m)*k+s*s) := by
  rw [rational_counted_table_certificate_ledger]
  have hr := rational_counted_rows_quadratic_bound c K D M σ
  have hk := Nat.le_mul_self k
  have hs := Nat.le_mul_self s
  nlinarith

end SparseCompletion
