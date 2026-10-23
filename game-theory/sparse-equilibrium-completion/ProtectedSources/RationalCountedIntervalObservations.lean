/- AI-assisted formalization under the repository Apache-2.0 license.
Chosen D,K are checked against every supplied endpoint; arbitrary R is separate. -/
module
public import ProtectedSources.RationalCountedCommitments
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalCountedObservationCheck {k m : ℕ}
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m) : Bool × ℕ :=
  let core := rationalCountedAll fun h : Fin k => rationalCountedAll fun h' : Fin k =>
    (decide ((loK.get h).get h' ≤ (K.get h).get h' ∧
      (K.get h).get h' ≤ (hiK.get h).get h'),((2 : ℕ)))
  let cross := rationalCountedAll fun i : Fin m => rationalCountedAll fun h : Fin k =>
    (decide ((loD.get i).get h ≤ (D.get i).get h ∧
      (D.get i).get h ≤ (hiD.get i).get h),((2 : ℕ)))
  (core.1 && cross.1,core.2+cross.2)

theorem rational_counted_observation_value {k m : ℕ}
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m) :
    (rationalCountedObservationCheck K loK hiK D loD hiD).1=true ↔
      (∀ h h',(loK.get h).get h' ≤ (K.get h).get h' ∧ (K.get h).get h' ≤ (hiK.get h).get h') ∧
      (∀ i h,(loD.get i).get h ≤ (D.get i).get h ∧ (D.get i).get h ≤ (hiD.get i).get h) := by
  simp only [rationalCountedObservationCheck,Bool.and_eq_true,rational_counted_all_value,decide_eq_true_eq]

theorem rational_counted_observation_calls {k m : ℕ}
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m) :
    (rationalCountedObservationCheck K loK hiK D loD hiD).2=((2 : ℕ))*(k+m)*k := by
  simp only [rationalCountedObservationCheck,rational_counted_all_calls,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

def rationalCountedIntervalFixedCertificate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (p : Vector ℚ k) : Bool × ℕ :=
  let base := rationalCountedFixedCertificate c K D M σ p
  let observation := rationalCountedObservationCheck K loK hiK D loD hiD
  (base.1 && observation.1,base.2+observation.2)

def rationalCountedIntervalFloorCertificate {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (floors : Vector ℚ k) : Bool × ℕ :=
  let base := rationalCountedFloorCertificate c K D M σ floors
  let observation := rationalCountedObservationCheck K loK hiK D loD hiD
  (base.1 && observation.1,base.2+observation.2)

theorem rational_counted_interval_fixed_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (p : Vector ℚ k) :
    (rationalCountedIntervalFixedCertificate c K loK hiK D loD hiD M σ p).1=true ↔
      (rationalTableConditions c K D M σ ∧ ∀ h,c.anchors.get h=p.get h) ∧
      (∀ h h',(loK.get h).get h' ≤ (K.get h).get h' ∧ (K.get h).get h' ≤ (hiK.get h).get h') ∧
      (∀ i h,(loD.get i).get h ≤ (D.get i).get h ∧ (D.get i).get h ≤ (hiD.get i).get h) := by
  simp only [rationalCountedIntervalFixedCertificate,Bool.and_eq_true,
    rational_counted_fixed_certificate_value,rational_counted_observation_value]

theorem rational_counted_interval_floor_value {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (floors : Vector ℚ k) :
    (rationalCountedIntervalFloorCertificate c K loK hiK D loD hiD M σ floors).1=true ↔
      (rationalTableConditions c K D M σ ∧ ∀ h,floors.get h ≤ c.anchors.get h) ∧
      (∀ h h',(loK.get h).get h' ≤ (K.get h).get h' ∧ (K.get h).get h' ≤ (hiK.get h).get h') ∧
      (∀ i h,(loD.get i).get h ≤ (D.get i).get h ∧ (D.get i).get h ≤ (hiD.get i).get h) := by
  simp only [rationalCountedIntervalFloorCertificate,Bool.and_eq_true,
    rational_counted_floor_certificate_value,rational_counted_observation_value]

theorem rational_counted_interval_fixed_calls {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (p : Vector ℚ k) :
    (rationalCountedIntervalFixedCertificate c K loK hiK D loD hiD M σ p).2=
      (rationalCountedTableCertificate c K D M σ).2+k+((2 : ℕ))*(k+m)*k := by
  simp only [rationalCountedIntervalFixedCertificate,rational_counted_fixed_certificate_calls,
    rational_counted_observation_calls]

theorem rational_counted_interval_floor_calls {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (floors : Vector ℚ k) :
    (rationalCountedIntervalFloorCertificate c K loK hiK D loD hiD M σ floors).2=
      (rationalCountedTableCertificate c K D M σ).2+k+((2 : ℕ))*(k+m)*k := by
  simp only [rationalCountedIntervalFloorCertificate,rational_counted_floor_certificate_calls,
    rational_counted_observation_calls]

theorem rational_counted_interval_fixed_bound {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (p : Vector ℚ k) :
    (rationalCountedIntervalFixedCertificate c K loK hiK D loD hiD M σ p).2 ≤
      ((256 : ℕ))*(1+(k+m)*k+s*s) := by
  rw [rational_counted_interval_fixed_calls]
  have hb := rational_counted_table_certificate_quadratic_bound c K D M σ
  have hk := Nat.le_mul_self k
  nlinarith

theorem rational_counted_interval_floor_bound {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K loK hiK : Vector (Vector ℚ k) k) (D loD hiD : Vector (Vector ℚ k) m)
    (M σ : ℚ) (floors : Vector ℚ k) :
    (rationalCountedIntervalFloorCertificate c K loK hiK D loD hiD M σ floors).2 ≤
      ((256 : ℕ))*(1+(k+m)*k+s*s) := by
  rw [rational_counted_interval_floor_calls]
  have hb := rational_counted_table_certificate_quadratic_bound c K D M σ
  have hk := Nat.le_mul_self k
  nlinarith

end SparseCompletion
