/- AI-assisted formalization under the repository Apache-2.0 license.
Actual attained support minima for every bounded exact-feasible anchored input. -/
module
public import PhysicalSupportMinimum
public import ScaledJointSupportTheorem
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem exact_instance_support_exists {k m : ℕ} {M : ℝ}
    (I : ScaledExactAnchorInstance M k m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    physicalAnchoredSupportExists I.K I.D I.p M ε fixed := by
  apply physical_anchored_support_exists I.K I.D I.p I.p I.q I.B M ε fixed
  apply physical_anchored_original I.K I.D I.p I.q I.B M ε fixed hε
  · exact blockWeights_nonneg I.p I.q I.anchors_nonnegative I.residual_weights_nonnegative
  · rw [blockWeights_mass,I.residual_mass]
    exact I.normalized
  · exact blockMatrix_skew I.K I.D I.B I.core_skew I.residual_skew
  · exact blockMatrix_bounds I.K I.D I.B M I.core_bounds I.cross_bounds I.residual_bounds
  · exact I.exact_responses

def exactInstanceMinimumSupport {k m : ℕ} {M : ℝ}
    (I : ScaledExactAnchorInstance M k m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) : ℕ :=
  physicalMinimumSupport I.K I.D I.p M ε fixed (exact_instance_support_exists I ε hε fixed)

theorem exactInstanceMinimumSupport_attained {k m : ℕ} {M : ℝ}
    (I : ScaledExactAnchorInstance M k m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ∃ p q B, PhysicalAnchoredWitness I.K I.D I.p M ε fixed p q B ∧
      (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card=
        exactInstanceMinimumSupport I ε hε fixed :=
  physicalMinimumSupport_attained I.K I.D I.p M ε fixed _

theorem exactInstanceMinimumSupport_finite {k m : ℕ} {M : ℝ}
    (I : ScaledExactAnchorInstance M k m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    exactInstanceMinimumSupport I ε hε fixed ≤ k+m :=
  physicalMinimumSupport_finite_bound I.K I.D I.p M ε fixed _

theorem exactInstanceMinimumSupport_upper {k m : ℕ} {M : ℝ}
    (I : ScaledExactAnchorInstance M k m) (η : ℝ) (hM : 0 < M)
    (hη : 0 < η) (hηM : η ≤ M) (fixed : Bool) :
    (exactInstanceMinimumSupport I η (le_of_lt hη) fixed : ℝ) ≤
      ((2 : ℕ) : ℝ)*min ((k : ℝ)+m) ((k : ℝ)+Real.sqrt (M/η)) := by
  classical
  obtain ⟨q,B,hn,hm,_,_,hsk,hb,hr,hc⟩ := normalized_scaled_joint_support_upper
    k I.K I.D I.B I.p I.q M I.r η hM I.residual_nonnegative hη hηM
    I.anchors_nonnegative I.residual_weights_nonnegative I.normalized I.residual_mass
    I.core_skew I.residual_skew I.core_bounds I.cross_bounds I.residual_bounds I.exact_responses
  have hw : PhysicalAnchoredWitness I.K I.D I.p M η fixed I.p q B :=
    ⟨hn,hm,fun _ => le_refl _,fun _ => rfl,hsk,hb,hr⟩
  have hl := physicalMinimumSupport_le I.K I.D I.p M η fixed
    (exact_instance_support_exists I η (le_of_lt hη) fixed) I.p q B hw
  have hreal : (exactInstanceMinimumSupport I η (le_of_lt hη) fixed : ℝ) ≤
      ((Finset.univ.filter fun a => blockWeights I.p q a ≠ 0).card : ℝ) := by
    exact_mod_cast hl
  exact le_trans hreal (by simpa only [Fintype.card_fin] using hc)

end
end SparseCompletion
