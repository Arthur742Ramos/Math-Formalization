/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalTableCertificate
public import ProtectedSources.RationalCountedDot
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_table_weighted_sum {k m s : ℕ} (c : RationalTableCertificate k m s)
    (f : Fin m → ℚ) :
    (∑ i,f i*(rationalTableAsCertificate c).q i)=∑ j,f (c.labels.get j)*c.weights.get j := by
  have hreduce : (∑ i ∈ rationalTableSupport c,f i*(rationalTableAsCertificate c).q i)=
      ∑ i,f i*(rationalTableAsCertificate c).q i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    rw [rational_table_q_off c i hi,mul_zero]
  rw [←hreduce,rationalTableSupport,Finset.sum_image c.labelsInjective.injOn]
  apply Finset.sum_congr rfl
  intro j _
  rw [rational_table_q_label]

theorem rational_table_mass_sum {k m s : ℕ} (c : RationalTableCertificate k m s) :
    (∑ i,(rationalTableAsCertificate c).q i)=∑ j,c.weights.get j := by
  simpa only [one_mul] using rational_table_weighted_sum c (fun _ => 1)

theorem rational_table_b_labels {k m s : ℕ} (c : RationalTableCertificate k m s)
    (i j : Fin s) :
    (rationalTableAsCertificate c).b (c.labels.get i) (c.labels.get j)=
      (c.residual.get i).get j := by
  have hi := (rational_table_support_mem c _).mpr ⟨i,rfl⟩
  have hj := (rational_table_support_mem c _).mpr ⟨j,rfl⟩
  simp only [RationalCertificate.b,rationalTableAsCertificate,hi,hj,dite_eq_left,
    rational_table_label_index]

theorem rational_table_supported_sum {k m s : ℕ} (c : RationalTableCertificate k m s)
    (i : Fin s) :
    (∑ j ∈ (rationalTableAsCertificate c).support,
      (rationalTableAsCertificate c).b (c.labels.get i) j*(rationalTableAsCertificate c).q j)=
    ∑ j,(c.residual.get i).get j*c.weights.get j := by
  change (∑ j ∈ rationalTableSupport c,
      (rationalTableAsCertificate c).b (c.labels.get i) j*(rationalTableAsCertificate c).q j)=_
  rw [rationalTableSupport,Finset.sum_image c.labelsInjective.injOn]
  apply Finset.sum_congr rfl
  intro j _
  rw [rational_table_q_label,rational_table_b_labels]

end SparseCompletion
