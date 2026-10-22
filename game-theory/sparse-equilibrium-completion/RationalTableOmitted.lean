/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalTableRows
@[expose] public section
namespace SparseCompletion

theorem rational_table_omitted_exists {k m s : ℕ} (c : RationalTableCertificate k m s) :
    (∃ i : Fin m,∀ j : Fin s,c.labels.get j ≠ i) ↔ s < m := by
  have hcard := rational_table_support_card c
  constructor
  · rintro ⟨i,hi⟩
    have hnot : i ∉ rationalTableSupport c := by
      rw [rational_table_support_mem]
      rintro ⟨j,hj⟩
      exact hi j hj
    have hlt : rationalTableSupport c ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _,?_⟩
      intro he
      exact hnot (he ▸ Finset.mem_univ i)
    have hc := Finset.card_lt_card hlt
    simpa only [hcard,Finset.card_univ,Fintype.card_fin] using hc
  · intro hlt
    by_contra hn
    push Not at hn
    have he : rationalTableSupport c=Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      exact (rational_table_support_mem c i).mpr (hn i)
    have hc := congrArg Finset.card he
    simp only [hcard,Finset.card_univ,Fintype.card_fin] at hc
    omega

end SparseCompletion
