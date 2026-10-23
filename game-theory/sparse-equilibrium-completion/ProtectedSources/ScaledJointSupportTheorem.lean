/- AI-assisted formalization under the repository Apache-2.0 license.
General payoff-scale quantified joint support order. -/
module
public import ProtectedSources.ScaledJointLower
public import ProtectedSources.ScaledJointUpper
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- An actual bounded normalized exact game, with supplied anchor allocation. -/
structure ScaledExactAnchorInstance (M : ℝ) (k m : ℕ) where
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
  core_bounds : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M
  cross_bounds : ∀ i h, -M ≤ D i h ∧ D i h ≤ M
  residual_bounds : ∀ i j, -M ≤ B i j ∧ B i j ≤ M
  exact_responses : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0

/-- The supplied allocation p is held fixed literally, so any originally satisfied
    coordinatewise anchor floors remain satisfied as well. -/
def ScaledJointUpperWitness {k m : ℕ} {M : ℝ} (I : ScaledExactAnchorInstance M k m) (η : ℝ)
    (q' : Fin m → ℝ) (B' : Fin m → Fin m → ℝ) : Prop :=
  (∀ a, 0 ≤ blockWeights I.p q' a) ∧ (∑ a, blockWeights I.p q' a)=1 ∧
  (∀ i, I.q i=0 → q' i=0) ∧
  (∀ h, (∑ i, q' i*I.D i h)=∑ i, I.q i*I.D i h) ∧
  IsSkew (blockMatrix I.K I.D B') ∧
  (∀ a b, -M ≤ blockMatrix I.K I.D B' a b ∧ blockMatrix I.K I.D B' a b ≤ M) ∧
  (∀ a, response (blockMatrix I.K I.D B') (blockWeights I.p q') a ≤ η) ∧
  ((Finset.univ.filter fun a => blockWeights I.p q' a ≠ 0).card : ℝ) ≤
    (2 : ℕ)*min ((k : ℝ)+m) ((k : ℝ)+Real.sqrt (M/η))


/-- Actual universal upper witnesses and actual lower families, at arbitrary
positive payoff scale. No worst-case/supremum operator is assumed. -/
theorem joint_anchor_support_scaled_order (n m : ℕ) (hm : 0 < m)
    (M η : ℝ) (hM : 0 < M) (hη : 0 < η) (hηM : η ≤ M) :
    (∀ I : ScaledExactAnchorInstance M (n+2) m,
      ∃ q' B', ScaledJointUpperWitness I η q' B') ∧
    (∀ fixed : Bool,
      (∃ p q B, ScaledClonedUniformWitness n m M 0 fixed p q B) ∧
      ∀ p q B, ScaledClonedUniformWitness n m M η fixed p q B →
        Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
          min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) ≤
          ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ)) := by
  constructor
  · intro I
    simpa only [ScaledJointUpperWitness,Fintype.card_fin] using normalized_scaled_joint_support_upper
      (n+2) I.K I.D I.B I.p I.q M I.r η hM I.residual_nonnegative hη hηM
      I.anchors_nonnegative I.residual_weights_nonnegative I.normalized I.residual_mass
      I.core_skew I.residual_skew I.core_bounds I.cross_bounds I.residual_bounds I.exact_responses
  · intro fixed
    refine ⟨⟨cloneShares n,uniformTarget m (1/((4 : ℕ) : ℝ)),
      (fun i j => M*orderedBlock 1 i j),
      scaled_cloned_dense n m hm M 0 (le_of_lt hM) (le_refl 0) fixed⟩,?_⟩
    intro p q B hw
    exact scaled_cloned_total_support_lower hm M η hM hη fixed p q B hw

end
end SparseCompletion
