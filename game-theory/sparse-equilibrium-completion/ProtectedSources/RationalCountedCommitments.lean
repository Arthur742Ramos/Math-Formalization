/- AI-assisted formalization under the repository Apache-2.0 license.
Actual prescribed-anchor and coordinatewise-floor checks; arbitrary R costs separate. -/
module
public import ProtectedSources.RationalCountedCertificateSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCountedFixedCertificate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ)
    (p : Vector ℚ k) : Bool × ℕ :=
  let base := rationalCountedTableCertificate c K D M σ
  let extra := rationalCountedAll fun h : Fin k => (decide (c.anchors.get h=p.get h),1)
  (base.1 && extra.1,base.2+extra.2)

def rationalCountedFloorCertificate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ)
    (floors : Vector ℚ k) : Bool × ℕ :=
  let base := rationalCountedTableCertificate c K D M σ
  let extra := rationalCountedAll fun h : Fin k => (decide (floors.get h ≤ c.anchors.get h),1)
  (base.1 && extra.1,base.2+extra.2)

theorem rational_counted_fixed_certificate_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (p : Vector ℚ k) :
    (rationalCountedFixedCertificate c K D M σ p).1=true ↔
      rationalTableConditions c K D M σ ∧ ∀ h,c.anchors.get h=p.get h := by
  simp only [rationalCountedFixedCertificate,Bool.and_eq_true,rational_counted_all_value,
    rational_counted_table_certificate_value,decide_eq_true_eq]

theorem rational_counted_floor_certificate_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (floors : Vector ℚ k) :
    (rationalCountedFloorCertificate c K D M σ floors).1=true ↔
      rationalTableConditions c K D M σ ∧ ∀ h,floors.get h ≤ c.anchors.get h := by
  simp only [rationalCountedFloorCertificate,Bool.and_eq_true,rational_counted_all_value,
    rational_counted_table_certificate_value,decide_eq_true_eq]

theorem rational_counted_fixed_certificate_calls {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (p : Vector ℚ k) :
    (rationalCountedFixedCertificate c K D M σ p).2=
      (rationalCountedTableCertificate c K D M σ).2+k := by
  simp only [rationalCountedFixedCertificate,rational_counted_all_calls,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one]

theorem rational_counted_floor_certificate_calls {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (floors : Vector ℚ k) :
    (rationalCountedFloorCertificate c K D M σ floors).2=
      (rationalCountedTableCertificate c K D M σ).2+k := by
  simp only [rationalCountedFloorCertificate,rational_counted_all_calls,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,mul_one]

theorem rational_counted_fixed_certificate_bound {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (p : Vector ℚ k) :
    (rationalCountedFixedCertificate c K D M σ p).2 ≤ ((128 : ℕ))*(1+(k+m)*k+s*s) := by
  rw [rational_counted_fixed_certificate_calls]
  have hb := rational_counted_table_certificate_quadratic_bound c K D M σ
  have hk := Nat.le_mul_self k
  nlinarith

theorem rational_counted_floor_certificate_bound {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (floors : Vector ℚ k) :
    (rationalCountedFloorCertificate c K D M σ floors).2 ≤ ((128 : ℕ))*(1+(k+m)*k+s*s) := by
  rw [rational_counted_floor_certificate_calls]
  have hb := rational_counted_table_certificate_quadratic_bound c K D M σ
  have hk := Nat.le_mul_self k
  nlinarith

end SparseCompletion
