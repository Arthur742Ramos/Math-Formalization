/- AI-assisted formalization under the repository Apache-2.0 license.
Valid normalized certificates absorb the additive ledger constant.
These remain unit-rational source counts, not bit or machine time. -/
module
public import RationalCountedIntervalObservations
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_table_valid_dimensions {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ)
    (hc : rationalTableConditions c K D M σ) : 0 < k+s := by
  have hn := hc.2.2.2.1
  by_contra hh
  have hk : k=0 := by omega
  have hs : s=0 := by omega
  subst k
  subst s
  simp only [Finset.univ_eq_empty,Finset.sum_empty,zero_add] at hn
  norm_num at hn

theorem rational_table_valid_size {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ)
    (hc : rationalTableConditions c K D M σ) : 1 ≤ (k+m)*k+s*s := by
  have hd := rational_table_valid_dimensions c K D M σ hc
  by_cases hk : k=0
  · subst k
    have hs : 1 ≤ s := by omega
    have hsq := Nat.le_mul_self s
    nlinarith
  · have hk1 : 1 ≤ k := by omega
    have hsq := Nat.le_mul_self k
    nlinarith

theorem rational_counted_certificate_valid_rate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ)
    (hc : (rationalCountedTableCertificate c K D M σ).1=true) :
    (rationalCountedTableCertificate c K D M σ).2 ≤ ((128 : ℕ))*((k+m)*k+s*s) := by
  have hsize := rational_table_valid_size c K D M σ
    ((rational_counted_table_certificate_value c K D M σ).mp hc)
  have hb := rational_counted_table_certificate_quadratic_bound c K D M σ
  nlinarith

theorem rational_counted_fixed_valid_rate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (p : Vector ℚ k)
    (hc : (rationalCountedFixedCertificate c K D M σ p).1=true) :
    (rationalCountedFixedCertificate c K D M σ p).2 ≤ ((256 : ℕ))*((k+m)*k+s*s) := by
  have hsize := rational_table_valid_size c K D M σ
    ((rational_counted_fixed_certificate_value c K D M σ p).mp hc).1
  have hb := rational_counted_fixed_certificate_bound c K D M σ p
  nlinarith

theorem rational_counted_floor_valid_rate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) (floors : Vector ℚ k)
    (hc : (rationalCountedFloorCertificate c K D M σ floors).1=true) :
    (rationalCountedFloorCertificate c K D M σ floors).2 ≤ ((256 : ℕ))*((k+m)*k+s*s) := by
  have hsize := rational_table_valid_size c K D M σ
    ((rational_counted_floor_certificate_value c K D M σ floors).mp hc).1
  have hb := rational_counted_floor_certificate_bound c K D M σ floors
  nlinarith

theorem rational_counted_interval_fixed_valid_rate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (p : Vector ℚ k)
    (hc : (rationalCountedIntervalFixedCertificate c K loK hiK D loD hiD M σ p).1=true) :
    (rationalCountedIntervalFixedCertificate c K loK hiK D loD hiD M σ p).2 ≤
      ((512 : ℕ))*((k+m)*k+s*s) := by
  have hsize := rational_table_valid_size c K D M σ
    ((rational_counted_interval_fixed_value c K loK hiK D loD hiD M σ p).mp hc).1.1
  have hb := rational_counted_interval_fixed_bound c K loK hiK D loD hiD M σ p
  nlinarith

theorem rational_counted_interval_floor_valid_rate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (floors : Vector ℚ k)
    (hc : (rationalCountedIntervalFloorCertificate c K loK hiK D loD hiD M σ floors).1=true) :
    (rationalCountedIntervalFloorCertificate c K loK hiK D loD hiD M σ floors).2 ≤
      ((512 : ℕ))*((k+m)*k+s*s) := by
  have hsize := rational_table_valid_size c K D M σ
    ((rational_counted_interval_floor_value c K loK hiK D loD hiD M σ floors).mp hc).1.1
  have hb := rational_counted_interval_floor_bound c K loK hiK D loD hiD M σ floors
  nlinarith

end SparseCompletion
