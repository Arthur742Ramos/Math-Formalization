/- AI-assisted formalization under the repository Apache-2.0 license.
Attained minima with arbitrary prescribed feasible anchor floors or fixed shares.
Original exact game data earns nonemptiness; no optimum witness is assumed. -/
module
public import ProtectedSources.PhysicalSupportMinimum
public import ProtectedSources.ScaledJointSupportTheorem
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

structure AnchoredSupportProblem (M : ℝ) (k m : ℕ) (fixed : Bool) where
  original : ScaledExactAnchorInstance M k m
  floors : Fin k → ℝ
  floors_nonnegative : ∀ h, 0 ≤ floors h
  floors_original : ∀ h, floors h ≤ original.p h
  fixed_original : fixed=true → original.p=floors

theorem support_problem_exists {M : ℝ} {k m : ℕ} {fixed : Bool}
    (P : AnchoredSupportProblem M k m fixed) (ε : ℝ) (hε : 0 ≤ ε) :
    physicalAnchoredSupportExists P.original.K P.original.D P.floors M ε fixed := by
  refine ⟨_,P.original.p,P.original.q,P.original.B,?_,rfl⟩
  refine ⟨blockWeights_nonneg _ _ P.original.anchors_nonnegative P.original.residual_weights_nonnegative,
    ?_,P.floors_original,P.fixed_original,
    blockMatrix_skew _ _ _ P.original.core_skew P.original.residual_skew,
    blockMatrix_bounds _ _ _ M P.original.core_bounds P.original.cross_bounds P.original.residual_bounds,
    fun a => le_trans (P.original.exact_responses a) hε⟩
  rw [blockWeights_mass,P.original.residual_mass]
  exact P.original.normalized

def supportProblemMinimum {M : ℝ} {k m : ℕ} {fixed : Bool}
    (P : AnchoredSupportProblem M k m fixed) (ε : ℝ) (hε : 0 ≤ ε) : ℕ :=
  physicalMinimumSupport P.original.K P.original.D P.floors M ε fixed
    (support_problem_exists P ε hε)

theorem supportProblemMinimum_attained {M : ℝ} {k m : ℕ} {fixed : Bool}
    (P : AnchoredSupportProblem M k m fixed) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ p q B, PhysicalAnchoredWitness P.original.K P.original.D P.floors M ε fixed p q B ∧
      (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card=supportProblemMinimum P ε hε :=
  physicalMinimumSupport_attained _ _ _ M ε fixed _

theorem supportProblemMinimum_finite {M : ℝ} {k m : ℕ} {fixed : Bool}
    (P : AnchoredSupportProblem M k m fixed) (ε : ℝ) (hε : 0 ≤ ε) :
    supportProblemMinimum P ε hε ≤ k+m :=
  physicalMinimumSupport_finite_bound _ _ _ M ε fixed _

theorem supportProblemMinimum_upper {M : ℝ} {k m : ℕ} {fixed : Bool}
    (P : AnchoredSupportProblem M k m fixed) (η : ℝ) (hM : 0 < M)
    (hη : 0 < η) (hηM : η ≤ M) :
    (supportProblemMinimum P η (le_of_lt hη) : ℝ) ≤
      ((2 : ℕ) : ℝ)*min ((k : ℝ)+m) ((k : ℝ)+Real.sqrt (M/η)) := by
  classical
  let I := P.original
  obtain ⟨q,B,hn,hm,_,_,hsk,hb,hr,hc⟩ := normalized_scaled_joint_support_upper
    k I.K I.D I.B I.p I.q M I.r η hM I.residual_nonnegative hη hηM
    I.anchors_nonnegative I.residual_weights_nonnegative I.normalized I.residual_mass
    I.core_skew I.residual_skew I.core_bounds I.cross_bounds I.residual_bounds I.exact_responses
  have hw : PhysicalAnchoredWitness I.K I.D P.floors M η fixed I.p q B :=
    ⟨hn,hm,P.floors_original,P.fixed_original,hsk,hb,hr⟩
  have hl := physicalMinimumSupport_le I.K I.D P.floors M η fixed
    (support_problem_exists P η (le_of_lt hη)) I.p q B hw
  have hreal : (supportProblemMinimum P η (le_of_lt hη) : ℝ) ≤
      ((Finset.univ.filter fun a => blockWeights I.p q a ≠ 0).card : ℝ) := by
    exact_mod_cast hl
  exact le_trans hreal (by simpa only [Fintype.card_fin] using hc)

end
end SparseCompletion
