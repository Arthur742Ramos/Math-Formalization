/- AI-assisted formalization under the repository Apache-2.0 license.
Table-backed compact certificate; scalar lookup is explicit Vector access. -/
module
public import RationalCertificate
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

structure RationalTableCertificate (k m s : ℕ) where
  labels : Vector (Fin m) s
  anchors : Vector ℚ k
  weights : Vector ℚ s
  residual : Vector (Vector ℚ s) s
  labelsInjective : Function.Injective labels.get

def rationalTableSupport {k m s : ℕ} (c : RationalTableCertificate k m s) : Finset (Fin m) :=
  Finset.univ.image c.labels.get

theorem rational_table_support_mem {k m s : ℕ} (c : RationalTableCertificate k m s)
    (i : Fin m) : i ∈ rationalTableSupport c ↔ ∃ j,c.labels.get j=i := by
  simp only [rationalTableSupport,Finset.mem_image,Finset.mem_univ,true_and]

theorem rational_table_support_card {k m s : ℕ} (c : RationalTableCertificate k m s) :
    (rationalTableSupport c).card=s := by
  rw [rationalTableSupport,Finset.card_image_of_injective _ c.labelsInjective,Finset.card_univ,Fintype.card_fin]

noncomputable def rationalTableIndex {k m s : ℕ} (c : RationalTableCertificate k m s)
    (i : rationalTableSupport c) : Fin s :=
  Classical.choose ((rational_table_support_mem c i).mp i.property)

theorem rational_table_index_label {k m s : ℕ} (c : RationalTableCertificate k m s)
    (i : rationalTableSupport c) : c.labels.get (rationalTableIndex c i)=i :=
  Classical.choose_spec ((rational_table_support_mem c i).mp i.property)

theorem rational_table_label_index {k m s : ℕ} (c : RationalTableCertificate k m s)
    (j : Fin s) (h : c.labels.get j ∈ rationalTableSupport c) :
    rationalTableIndex c ⟨c.labels.get j,h⟩=j := by
  apply c.labelsInjective
  exact rational_table_index_label c _

noncomputable def rationalTableAsCertificate {k m s : ℕ} (c : RationalTableCertificate k m s) :
    RationalCertificate k m where
  support := rationalTableSupport c
  anchors := c.anchors.get
  weights := fun i => c.weights.get (rationalTableIndex c i)
  residual := fun i j => (c.residual.get (rationalTableIndex c i)).get (rationalTableIndex c j)

theorem rational_table_q_label {k m s : ℕ} (c : RationalTableCertificate k m s) (j : Fin s) :
    (rationalTableAsCertificate c).q (c.labels.get j)=c.weights.get j := by
  have h : c.labels.get j ∈ rationalTableSupport c := (rational_table_support_mem c _).mpr ⟨j,rfl⟩
  simp only [RationalCertificate.q,rationalTableAsCertificate,h,dite_eq_left,rational_table_label_index]

theorem rational_table_q_off {k m s : ℕ} (c : RationalTableCertificate k m s)
    (i : Fin m) (h : i ∉ rationalTableSupport c) : (rationalTableAsCertificate c).q i=0 := by
  simp [RationalCertificate.q,rationalTableAsCertificate,h]

end SparseCompletion
