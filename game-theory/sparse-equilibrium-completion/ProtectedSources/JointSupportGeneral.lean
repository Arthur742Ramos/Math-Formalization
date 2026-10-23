/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.JointSupportTheorem

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem joint_anchor_support_order_general (k m : ℕ) (hk : (2 : ℕ) ≤ k) (hm : 0 < m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (∀ I : ExactAnchorInstance k m,
      ∃ q' B', JointUpperWitness I η q' B') ∧
    (∀ fixed : Bool,
      (∃ p q B, ClonedUniformWitness (k-2) m 0 fixed p q B) ∧
      ∀ p q B, ClonedUniformWitness (k-2) m η fixed p q B →
        Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) * min (k+(m : ℝ))
          (k+1/Real.sqrt η) ≤
          ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ)) ∧
    (IsSkew (clonedCore (n := k-2) (rigidityCore (uniformTarget m (1/(4 : ℕ))))) ∧
      (∀ h h', -1 ≤ clonedCore (n := k-2) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ∧
        clonedCore (n := k-2) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ≤ 1) ∧
      (∀ i h, -1 ≤ clonedCross (n := k-2) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ∧
        clonedCross (n := k-2) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ≤ 1)) := by
  have he : k-2+2=k := Nat.sub_add_cancel hk
  generalize hn : k-2=n at *
  subst k
  exact joint_anchor_support_order n m hm η hη hη1

end
end SparseCompletion
