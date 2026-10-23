/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalTableSums
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalTableRows {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) : Prop :=
  (∀ h,(∑ h',(K.get h).get h'*c.anchors.get h')-
      ∑ j,(D.get (c.labels.get j)).get h*c.weights.get j ≤ σ) ∧
  (∀ i,(∑ h,(D.get (c.labels.get i)).get h*c.anchors.get h)+
      ∑ j,(c.residual.get i).get j*c.weights.get j ≤ σ) ∧
  (∀ i,(∀ j,c.labels.get j ≠ i) →
      (∑ h,(D.get i).get h*c.anchors.get h)-M*(∑ j,c.weights.get j) ≤ σ)

theorem rational_table_rows_iff {k m s : ℕ} (c : RationalTableCertificate k m s)
    (K : Vector (Vector ℚ k) k) (D : Vector (Vector ℚ k) m) (M σ : ℚ) :
    (rationalTableAsCertificate c).Rows (fun h h' => (K.get h).get h')
      (fun i h => (D.get i).get h) M σ ↔ rationalTableRows c K D M σ := by
  constructor
  · rintro ⟨ha,hr,ho⟩
    refine ⟨?_,?_,?_⟩
    · intro h
      have hh := ha h
      change (∑ h',(K.get h).get h'*c.anchors.get h')-
        (∑ i,(D.get i).get h*(rationalTableAsCertificate c).q i) ≤ σ at hh
      rwa [rational_table_weighted_sum] at hh
    · intro i
      have hh := hr (c.labels.get i) ((rational_table_support_mem c _).mpr ⟨i,rfl⟩)
      change (∑ h,(D.get (c.labels.get i)).get h*c.anchors.get h)+_ ≤ σ at hh
      rwa [rational_table_supported_sum] at hh
    · intro i hi
      have hoff : i ∉ rationalTableSupport c := by
        rw [rational_table_support_mem]
        rintro ⟨j,hj⟩
        exact hi j hj
      have hh := ho i hoff
      change (∑ h,(D.get i).get h*c.anchors.get h)-M*_ ≤ σ at hh
      rwa [rational_table_mass_sum] at hh
  · rintro ⟨ha,hr,ho⟩
    refine ⟨?_,?_,?_⟩
    · intro h
      change (∑ h',(K.get h).get h'*c.anchors.get h')-
        (∑ i,(D.get i).get h*(rationalTableAsCertificate c).q i) ≤ σ
      rw [rational_table_weighted_sum]
      exact ha h
    · intro i hi
      obtain ⟨j,rfl⟩ := (rational_table_support_mem c i).mp hi
      change (∑ h,(D.get (c.labels.get j)).get h*c.anchors.get h)+_ ≤ σ
      rw [rational_table_supported_sum]
      exact hr j
    · intro i hi
      change (∑ h,(D.get i).get h*c.anchors.get h)-M*_ ≤ σ
      rw [rational_table_mass_sum]
      apply ho i
      intro j hj
      exact hi ((rational_table_support_mem c i).mpr ⟨j,hj⟩)

end SparseCompletion
