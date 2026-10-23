/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalConvexity

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem repertoire_interval_completion_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 < M) (hp : ∀ h, 0 ≤ p h)
    (hpmass : (∑ h, p h)+r=1)
    (hclo : ∀ h h', -M ≤ coreLo h h') (hchi : ∀ h h', coreHi h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) (R : Set (ι → ℝ)) :
    (∃ (q : ι → ℝ) (K : α → α → ℝ),
      q ∈ R ∧ (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧ IsSkew K ∧
      (∀ h h', coreLo h h' ≤ K h h' ∧ K h h' ≤ coreHi h h') ∧
      ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
        (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
        (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
        IsSkew (blockMatrix K D B) ∧
        (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
        ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ε) ↔
    ∃ z, intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z ∧ z.1 ∈ R := by
  constructor
  · rintro ⟨q,K,hR,hq,hr,hK,hC,hgame⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    obtain ⟨V,hV,hA,hg,hcuts⟩ :=
      (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
        hK hKb hlo hhi hlu).mp hgame
    exact ⟨(q,V,K),⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩,hR⟩
  · rintro ⟨⟨q,V,K⟩,⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩,hR⟩
    have hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M := fun h h' =>
      ⟨le_trans (hclo h h') (hC h h').1,le_trans (hC h h').2 (hchi h h')⟩
    refine ⟨q,K,hR,hq,hr,hK,hC,?_⟩
    exact (normalized_interval_perspective_iff K lo hi p q M r ε hM hp hq hr hpmass
      hK hKb hlo hhi hlu).mpr ⟨V,hV,hA,hg,hcuts⟩

end
end SparseCompletion
