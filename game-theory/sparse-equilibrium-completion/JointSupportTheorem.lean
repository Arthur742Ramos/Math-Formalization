/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import JointSupportLower
public import JointSupportUpper
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- An actual bounded normalized exact game, with supplied anchor allocation. -/
structure ExactAnchorInstance (k m : ℕ) where
  K : Fin k → Fin k → ℝ
  D : Fin m → Fin k → ℝ
  B : Fin m → Fin m → ℝ
  p : Fin k → ℝ
  q : Fin m → ℝ
  r : ℝ
  residual_nonnegative : 0 ≤ r
  anchors_nonnegative : ∀ h, 0 ≤ p h
  residual_weights_nonnegative : ∀ i, 0 ≤ q i
  normalized : (∑ h, p h)+r=1
  residual_mass : ∑ i, q i=r
  core_skew : IsSkew K
  residual_skew : IsSkew B
  core_bounds : ∀ h h', -1 ≤ K h h' ∧ K h h' ≤ 1
  cross_bounds : ∀ i h, -1 ≤ D i h ∧ D i h ≤ 1
  residual_bounds : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1
  exact_responses : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0

/-- The supplied allocation p is held fixed literally, so any originally satisfied
    coordinatewise anchor floors remain satisfied as well. -/
def JointUpperWitness {k m : ℕ} (I : ExactAnchorInstance k m) (η : ℝ)
    (q' : Fin m → ℝ) (B' : Fin m → Fin m → ℝ) : Prop :=
  (∀ a, 0 ≤ blockWeights I.p q' a) ∧ (∑ a, blockWeights I.p q' a)=1 ∧
  (∀ i, I.q i=0 → q' i=0) ∧
  (∀ h, (∑ i, q' i*I.D i h)=∑ i, I.q i*I.D i h) ∧
  IsSkew (blockMatrix I.K I.D B') ∧
  (∀ a b, -1 ≤ blockMatrix I.K I.D B' a b ∧ blockMatrix I.K I.D B' a b ≤ 1) ∧
  (∀ a, response (blockMatrix I.K I.D B') (blockWeights I.p q') a ≤ η) ∧
  ((Finset.univ.filter fun a => blockWeights I.p q' a ≠ 0).card : ℝ) ≤
    (2 : ℕ)*min ((k : ℝ)+m) ((k : ℝ)+1/Real.sqrt η)

/-- Quantified sharp joint order: every actual exact instance has the universal
    upper witness, while the actual bounded clone family is exactly feasible and
    forces the lower bound in both commitment classes. No worst-case operator or
    supremum is asserted or assumed. Here the number of anchors is k=n+2. -/
theorem joint_anchor_support_order (n m : ℕ) (hm : 0 < m)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (∀ I : ExactAnchorInstance (n+2) m,
      ∃ q' B', JointUpperWitness I η q' B') ∧
    (∀ fixed : Bool,
      (∃ p q B, ClonedUniformWitness n m 0 fixed p q B) ∧
      ∀ p q B, ClonedUniformWitness n m η fixed p q B →
        Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) * min ((n+2 : ℕ)+(m : ℝ))
          ((n+2 : ℕ)+1/Real.sqrt η) ≤
          ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ)) ∧
    (IsSkew (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ))))) ∧
      (∀ h h', -1 ≤ clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ∧
        clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ≤ 1) ∧
      (∀ i h, -1 ≤ clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ∧
        clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ≤ 1)) := by
  refine ⟨?_,?_,cloned_uniform_observations_bounded n m hm⟩
  · intro I
    simpa only [JointUpperWitness,Fintype.card_fin] using normalized_joint_support_upper
      (n+2) I.K I.D I.B I.p I.q I.r η I.residual_nonnegative hη hη1
      I.anchors_nonnegative I.residual_weights_nonnegative I.normalized I.residual_mass
      I.core_skew I.residual_skew I.core_bounds I.cross_bounds I.residual_bounds I.exact_responses
  · intro fixed
    refine ⟨⟨cloneShares n,uniformTarget m (1/(4 : ℕ)),orderedBlock 1,
      cloned_uniform_dense n m hm 0 (le_refl 0) fixed⟩,?_⟩
    intro p q B hw
    exact cloned_uniform_total_support_lower hm η hη fixed p q B hw

end
end SparseCompletion
