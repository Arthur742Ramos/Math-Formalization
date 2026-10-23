/- AI-assisted formalization under the repository Apache-2.0 license.
The attained support objective depends on observations and commitments only;
original exact witnesses certify feasibility without changing that objective. -/
module
public import ProtectedSources.SupportProblemMinimum
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem supportProblemMinimum_observation_invariant {M : ℝ} {k m : ℕ} {fixed : Bool}
    (P Q : AnchoredSupportProblem M k m fixed) (ε : ℝ) (hε : 0 ≤ ε)
    (hK : P.original.K=Q.original.K) (hD : P.original.D=Q.original.D)
    (hf : P.floors=Q.floors) : supportProblemMinimum P ε hε=supportProblemMinimum Q ε hε := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨p,q,B,hw,hc⟩ := supportProblemMinimum_attained Q ε hε
    have hp : PhysicalAnchoredWitness P.original.K P.original.D P.floors M ε fixed p q B := by
      simpa only [hK,hD,hf] using hw
    have hl := physicalMinimumSupport_le P.original.K P.original.D P.floors M ε fixed
      (support_problem_exists P ε hε) p q B hp
    exact le_trans hl (le_of_eq hc)
  · obtain ⟨p,q,B,hw,hc⟩ := supportProblemMinimum_attained P ε hε
    have hq : PhysicalAnchoredWitness Q.original.K Q.original.D Q.floors M ε fixed p q B := by
      simpa only [hK,hD,hf] using hw
    have hl := physicalMinimumSupport_le Q.original.K Q.original.D Q.floors M ε fixed
      (support_problem_exists Q ε hε) p q B hq
    exact le_trans hl (le_of_eq hc)

theorem anchored_support_problem_representation (k m : ℕ) (M : ℝ)
    (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (floors : Fin k → ℝ) (fixed : Bool)
    (hp : ∀ h,0 ≤ p h) (hq : ∀ i,0 ≤ q i) (hf : ∀ h,0 ≤ floors h)
    (hfloor : ∀ h,floors h ≤ p h) (hfix : fixed=true → p=floors)
    (hm : (∑ h,p h)+(∑ i,q i)=1) (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h',-M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h,-M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j,-M ≤ B i j ∧ B i j ≤ M)
    (hr : ∀ a,response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ P : AnchoredSupportProblem M k m fixed,
      P.original.K=K ∧ P.original.D=D ∧ P.floors=floors := by
  let I : ScaledExactAnchorInstance M k m := {
    K := K, D := D, B := B, p := p, q := q, r := ∑ i,q i,
    residual_nonnegative := Finset.sum_nonneg fun i _ => hq i,
    anchors_nonnegative := hp, residual_weights_nonnegative := hq,
    normalized := hm, residual_mass := rfl,
    core_skew := hK, residual_skew := hB, core_bounds := hKb,
    cross_bounds := hDb, residual_bounds := hBb, exact_responses := hr }
  exact ⟨⟨I,floors,hf,hfloor,hfix⟩,rfl,rfl,rfl⟩

end
end SparseCompletion
