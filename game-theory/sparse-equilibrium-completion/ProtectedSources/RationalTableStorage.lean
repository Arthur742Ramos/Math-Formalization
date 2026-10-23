/- AI-assisted formalization under the repository Apache-2.0 license.
Counts rational scalar slots; label indices and encoding bits are separate. -/
module
public import ProtectedSources.RationalTableCertificate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalTableScalarSlots {k m s : ℕ} (c : RationalTableCertificate k m s) : ℕ :=
  c.anchors.toArray.size+c.weights.toArray.size+
    ∑ i : Fin s,(c.residual.get i).toArray.size

theorem rational_table_scalar_slots {k m s : ℕ} (c : RationalTableCertificate k m s) :
    rationalTableScalarSlots c=k+s+s*s := by
  simp [rationalTableScalarSlots,Vector.size_toArray]

theorem rational_table_scalar_slots_bound {k m s : ℕ} (c : RationalTableCertificate k m s) :
    rationalTableScalarSlots c ≤ k+((2 : ℕ))*s*s := by
  rw [rational_table_scalar_slots]
  have hs := Nat.le_mul_self s
  nlinarith

def rationalObservationScalarSlots {k m : ℕ}
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) : ℕ :=
  (∑ h : Fin k,(K.get h).toArray.size)+(∑ i : Fin m,(D.get i).toArray.size)

theorem rational_observation_scalar_slots {k m : ℕ}
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) :
    rationalObservationScalarSlots K D=(k+m)*k := by
  simp [rationalObservationScalarSlots,Vector.size_toArray]
  ring

end SparseCompletion
