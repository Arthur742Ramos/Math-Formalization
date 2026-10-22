/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalCountedTableRows
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalTableConditions {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) : Prop :=
  0 ≤ M ∧ (∀ h,0 ≤ c.anchors.get h) ∧ (∀ j,0 ≤ c.weights.get j) ∧
  (∑ h,c.anchors.get h)+(∑ j,c.weights.get j)=1 ∧
  (∀ h h',(K.get h).get h' = -(K.get h').get h) ∧
  (∀ h h',-M ≤ (K.get h).get h' ∧ (K.get h).get h' ≤ M) ∧
  (∀ i h,-M ≤ (D.get i).get h ∧ (D.get i).get h ≤ M) ∧
  (∀ i j,(c.residual.get i).get j = -(c.residual.get j).get i) ∧
  (∀ i j,-M ≤ (c.residual.get i).get j ∧ (c.residual.get i).get j ≤ M) ∧
  rationalTableRows c K D M σ

theorem rational_table_support_forall {k m s : ℕ} (c : RationalTableCertificate k m s)
    (P : Fin m → Prop) : (∀ i ∈ rationalTableSupport c,P i) ↔ ∀ j,P (c.labels.get j) := by
  constructor
  · intro h j
    exact h _ ((rational_table_support_mem c _).mpr ⟨j,rfl⟩)
  · intro h i hi
    obtain ⟨j,rfl⟩ := (rational_table_support_mem c i).mp hi
    exact h j

theorem rational_table_q_nonnegative {k m s : ℕ} (c : RationalTableCertificate k m s) :
    (∀ i,0 ≤ (rationalTableAsCertificate c).q i) ↔ ∀ j,0 ≤ c.weights.get j := by
  constructor
  · intro h j
    simpa only [rational_table_q_label] using h (c.labels.get j)
  · intro h i
    by_cases hi : i ∈ rationalTableSupport c
    · obtain ⟨j,rfl⟩ := (rational_table_support_mem c i).mp hi
      simpa only [rational_table_q_label] using h j
    · rw [rational_table_q_off c i hi]

theorem rational_table_conditions_iff {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalTableAsCertificate c).Conditions (fun h h' => (K.get h).get h')
      (fun i h => (D.get i).get h) M σ ↔ rationalTableConditions c K D M σ := by
  change (0 ≤ M ∧ (∀ h,0 ≤ c.anchors.get h) ∧
    (∀ i,0 ≤ (rationalTableAsCertificate c).q i) ∧
    (∑ h,c.anchors.get h)+(∑ i,(rationalTableAsCertificate c).q i)=1 ∧
    (∀ h h',(K.get h).get h' = -(K.get h').get h) ∧
    (∀ h h',-M ≤ (K.get h).get h' ∧ (K.get h).get h' ≤ M) ∧
    (∀ i h,-M ≤ (D.get i).get h ∧ (D.get i).get h ≤ M) ∧
    (∀ i ∈ rationalTableSupport c,∀ j ∈ rationalTableSupport c,
      (rationalTableAsCertificate c).b i j = -(rationalTableAsCertificate c).b j i) ∧
    (∀ i ∈ rationalTableSupport c,∀ j ∈ rationalTableSupport c,
      -M ≤ (rationalTableAsCertificate c).b i j ∧ (rationalTableAsCertificate c).b i j ≤ M) ∧
    (rationalTableAsCertificate c).Rows (fun h h' => (K.get h).get h')
      (fun i h => (D.get i).get h) M σ) ↔ _
  simp_rw [rational_table_q_nonnegative,rational_table_mass_sum,
    rational_table_support_forall,rational_table_b_labels,rational_table_rows_iff]
  rfl

end SparseCompletion
