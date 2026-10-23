/- AI-assisted formalization under the repository Apache-2.0 license.
The actual sharp clone family on consecutive finite anchor labels. -/
module
public import ProtectedSources.AnchorRelabel
public import ProtectedSources.ScaledJointSupportTheorem
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem clone_anchor_count (n : ℕ) : Fintype.card (CloneAnchors n)=n+2 := by
  simp [CloneAnchors]

def cloneFinEquiv (n : ℕ) : Fin (n+2) ≃ CloneAnchors n :=
  (Fintype.equivFinOfCardEq (α := CloneAnchors n) (clone_anchor_count n)).symm

def finiteScaledCloneInstance (n m : ℕ) (hm : 0 < m) (M : ℝ) (hM : 0 ≤ M) :
    ScaledExactAnchorInstance M (n+2) m where
  K := anchorPullCore (cloneFinEquiv n)
    (fun a b => M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b)
  D := anchorPullCross (cloneFinEquiv n)
    (fun i a => M*clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))) i a)
  B := fun i j => M*orderedBlock 1 i j
  p := fun h => cloneShares n (cloneFinEquiv n h)
  q := uniformTarget m (1/((4 : ℕ) : ℝ))
  r := 1/((4 : ℕ) : ℝ)
  residual_nonnegative := by norm_num
  anchors_nonnegative := fun h => le_of_lt (clone_shares_positive n _)
  residual_weights_nonnegative := fun i =>
    le_of_lt (uniformTarget_positive m (1/((4 : ℕ) : ℝ)) (by norm_num) i)
  normalized := by
    have hd := (scaled_cloned_dense n m hm M 0 hM (le_refl 0) false).2.2.2.1
    rw [Equiv.sum_comp (cloneFinEquiv n) (cloneShares n)]
    rw [uniformTarget_mass m hm (1/((4 : ℕ) : ℝ))] at hd
    exact hd
  residual_mass := uniformTarget_mass m hm (1/((4 : ℕ) : ℝ))
  core_skew := by
    intro a b
    exact (scaled_cloned_observations_bounded n m hm M hM).1 _ _
  residual_skew := by
    intro i j
    change M*orderedBlock 1 i j = -(M*orderedBlock 1 j i)
    rw [orderedBlock_skew 1 i j,mul_neg]
  core_bounds := fun a b => (scaled_cloned_observations_bounded n m hm M hM).2.1 _ _
  cross_bounds := fun i a => (scaled_cloned_observations_bounded n m hm M hM).2.2 _ _
  residual_bounds := (scaled_cloned_dense n m hm M 0 hM (le_refl 0) false).2.2.2.2.2.1
  exact_responses := by
    intro a
    rw [response_anchor_pull]
    exact (scaled_cloned_dense n m hm M 0 hM (le_refl 0) false).2.2.2.2.2.2 _

end
end SparseCompletion
