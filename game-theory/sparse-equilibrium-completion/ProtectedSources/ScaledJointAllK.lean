/- AI-assisted formalization under the repository Apache-2.0 license.
General-scale joint order for every number of anchors at least two. -/
module
public import ProtectedSources.ScaledJointSupportTheorem
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem joint_anchor_support_scaled_order_general (k m : ℕ) (hk : (2 : ℕ) ≤ k)
    (hm : 0 < m) (M η : ℝ) (hM : 0 < M) (hη : 0 < η) (hηM : η ≤ M) :
    (∀ I : ScaledExactAnchorInstance M k m,
      ∃ q' B', ScaledJointUpperWitness I η q' B') ∧
    (∀ fixed : Bool,
      (∃ p q B, ScaledClonedUniformWitness (k-2) m M 0 fixed p q B) ∧
      ∀ p q B, ScaledClonedUniformWitness (k-2) m M η fixed p q B →
        Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
          min (k+(m : ℝ)) (k+Real.sqrt (M/η)) ≤
          ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ)) := by
  have he : k-2+2=k := Nat.sub_add_cancel hk
  generalize hn : k-2=n at *
  subst k
  exact joint_anchor_support_scaled_order n m hm M η hM hη hηM

end
end SparseCompletion
