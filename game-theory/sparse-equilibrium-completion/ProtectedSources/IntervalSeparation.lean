/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.ThresholdSeparation
public import ProtectedSources.IntervalRepertoire

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem perspective_moment_zero {ι α : Type*} [Fintype α]
    (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (hb : ∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) :
    ∀ i, q i=0 → intervalMomentScore p V i=0 := by
  intro i hiq
  unfold intervalMomentScore
  apply Finset.sum_eq_zero
  intro h _
  rw [perspective_zero (lo i h) (hi i h) (V i h) (q i) hiq (hb i h).1 (hb i h).2,mul_zero]

def intervalThresholdSystem {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ)
    (z : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) : Prop :=
  (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i)=r ∧
  (∀ i h, lo i h*z.1 i ≤ z.2.1 i h ∧ z.2.1 i h ≤ hi i h*z.1 i) ∧
  (∀ h, (∑ a, z.2.2 h a*p a)-(∑ i, z.2.1 i h) ≤ ε) ∧
  IsSkew z.2.2 ∧ (∀ h h', coreLo h h' ≤ z.2.2 h h' ∧ z.2.2 h h' ≤ coreHi h h') ∧
  (∀ i, score lo p i ≤ ε+M*r) ∧ ∀ i : ι, z.1 i ≠ 0 →
    M*(mass (weightedUpperSet z.1 (effectiveScore z.1 (intervalMomentScore p z.2.1)) i) z.1)^2-
      M*r*mass (weightedUpperSet z.1 (effectiveScore z.1 (intervalMomentScore p z.2.1)) i) z.1+
      (∑ j ∈ weightedUpperSet z.1 (effectiveScore z.1 (intervalMomentScore p z.2.1)) i,
        (intervalMomentScore p z.2.1 j-ε*z.1 j)) ≤ 0

theorem interval_system_iff_threshold_system {ι α : Type*} [Fintype ι] [Fintype α]
    (lo hi : ι → α → ℝ) (coreLo coreHi : α → α → ℝ)
    (p : α → ℝ) (M r ε : ℝ) (hM : 0 < M)
    (z : (ι → ℝ) × (ι → α → ℝ) × (α → α → ℝ)) :
    intervalPerspectiveSystem lo hi coreLo coreHi p M r ε z ↔
      intervalThresholdSystem lo hi coreLo coreHi p M r ε z := by
  constructor
  · rintro ⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩
    exact ⟨hq,hr,hV,hA,hK,hC,hg,
      (perspective_cuts_iff_candidate_thresholds z.1 (intervalMomentScore p z.2.1) M r ε hM hq hr
        (perspective_moment_zero lo hi z.2.1 p z.1 hV)).mp hcuts⟩
  · rintro ⟨hq,hr,hV,hA,hK,hC,hg,hcuts⟩
    exact ⟨hq,hr,hV,hA,hK,hC,hg,
      (perspective_cuts_iff_candidate_thresholds z.1 (intervalMomentScore p z.2.1) M r ε hM hq hr
        (perspective_moment_zero lo hi z.2.1 p z.1 hV)).mpr hcuts⟩

end
end SparseCompletion
