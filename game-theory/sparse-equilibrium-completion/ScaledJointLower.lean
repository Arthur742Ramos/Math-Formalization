/- AI-assisted formalization under the repository Apache-2.0 license.
General-M scaling of the actual mandatory-clone support obstruction. -/
module
public import PayoffScaling
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def ScaledClonedUniformWitness (n m : ℕ) (M ε : ℝ) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, cloneShares n h ≤ p h) ∧
  (fixed=true → p=cloneShares n) ∧
  (∑ h, p h)+(∑ j, q j)=1 ∧ IsSkew B ∧
  (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
  ∀ v, response
    (blockMatrix
      (fun a b => M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b)
      (fun i a => M*clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))) i a) B)
    (blockWeights p q) v ≤ ε

theorem scaled_cloned_witness_unit {n m : ℕ} (M ε : ℝ) (hM : 0 < M) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (h : ScaledClonedUniformWitness n m M ε fixed p q B) :
    ClonedUniformWitness n m (ε/M) fixed p q (fun i j => B i j/M) := by
  rcases h with ⟨hq,hp,hfix,hm,hsk,hb,hr⟩
  refine ⟨hq,hp,hfix,hm,?_,?_,?_⟩
  · intro i j
    change B i j/M = -(B j i/M)
    rw [hsk i j, neg_div]
  · intro i j
    constructor
    · exact (le_div_iff₀ hM).mpr (by simpa only [neg_one_mul] using (hb i j).1)
    · exact (div_le_iff₀ hM).mpr (by simpa only [one_mul] using (hb i j).2)
  · intro v
    have he : blockMatrix
        (fun a b => M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b)
        (fun i a => M*clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))) i a) B =
        fun a b => M*blockMatrix
          (clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))))
          (clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))))
          (fun i j => B i j/M) a b := by
      funext a b
      cases a <;> cases b <;> simp only [blockMatrix, mul_neg, mul_div_cancel₀ _ (ne_of_gt hM)]
    have hv := hr v
    rw [he,response_payoff_scale] at hv
    apply (le_div_iff₀ hM).mpr
    nlinarith

theorem scaled_cloned_total_support_lower {n m : ℕ} (hm : 0 < m)
    (M η : ℝ) (hM : 0 < M) (hη : 0 < η) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (h : ScaledClonedUniformWitness n m M η fixed p q B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) *
      min ((n+2 : ℕ)+(m : ℝ)) ((n+2 : ℕ)+Real.sqrt (M/η)) ≤
      ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ) := by
  have hw := scaled_cloned_witness_unit M η hM fixed p q B h
  have hl := cloned_uniform_total_support_lower hm (η/M) (div_pos hη hM) fixed p q
    (fun i j => B i j/M) hw
  simpa only [inverse_sqrt_tolerance_scale] using hl


theorem scaled_cloned_dense (n m : ℕ) (hm : 0 < m) (M ε : ℝ)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (fixed : Bool) :
    ScaledClonedUniformWitness n m M ε fixed (cloneShares n)
      (uniformTarget m (1/((4 : ℕ) : ℝ))) (fun i j => M*orderedBlock 1 i j) := by
  obtain ⟨hq,hp,hfix,hn,hsk,hb,hr⟩ := cloned_uniform_dense n m hm 0 (le_refl 0) fixed
  refine ⟨hq,hp,hfix,hn,?_,?_,?_⟩
  · intro i j
    change M*orderedBlock 1 i j = -(M*orderedBlock 1 j i)
    rw [hsk i j, mul_neg]
  · intro i j
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hb i j).1 hM
      simpa only [mul_neg, mul_one] using hh
    · have hh := mul_le_mul_of_nonneg_left (hb i j).2 hM
      simpa only [mul_one] using hh
  · intro v
    rw [block_payoff_scale, response_payoff_scale]
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hM (hr v)) hε

theorem scaled_cloned_observations_bounded (n m : ℕ) (hm : 0 < m)
    (M : ℝ) (hM : 0 ≤ M) :
    IsSkew (fun a b => M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b) ∧
    (∀ a b, -M ≤ M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b ∧
      M*clonedCore (n := n) (rigidityCore (uniformTarget m (1/((4 : ℕ) : ℝ)))) a b ≤ M) ∧
    (∀ i a, -M ≤ M*clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))) i a ∧
      M*clonedCross (n := n) (rigidityCross (uniformTarget m (1/((4 : ℕ) : ℝ)))) i a ≤ M) := by
  obtain ⟨hsk,hK,hD⟩ := cloned_uniform_observations_bounded n m hm
  refine ⟨?_,?_,?_⟩
  · intro a b
    change M*_ = -(M*_)
    rw [hsk a b, mul_neg]
  · intro a b
    constructor
    · simpa only [mul_neg,mul_one] using mul_le_mul_of_nonneg_left (hK a b).1 hM
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hK a b).2 hM
  · intro i a
    constructor
    · simpa only [mul_neg,mul_one] using mul_le_mul_of_nonneg_left (hD i a).1 hM
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hD i a).2 hM

end
end SparseCompletion
