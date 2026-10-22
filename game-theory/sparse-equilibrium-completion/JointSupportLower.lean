/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import JointSupportFoundation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def ClonedUniformWitness (n m : ℕ) (ε : ℝ) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ (∀ h, cloneShares n h ≤ p h) ∧
  (fixed=true → p=cloneShares n) ∧
  (∑ h, p h)+(∑ j, q j)=1 ∧ IsSkew B ∧
  (∀ i j, -1 ≤ B i j ∧ B i j ≤ 1) ∧
  ∀ v, response (blockMatrix (clonedCore (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
    (clonedCross (rigidityCross (uniformTarget m (1/(4 : ℕ))))) B) (blockWeights p q) v ≤ ε

theorem cloned_witness_aggregates {n m : ℕ} (ε : ℝ) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (h : ClonedUniformWitness n m ε fixed p q B) :
    UniformWitness m ε fixed (aggregateClones p) q B := by
  rcases h with ⟨hq,hp,hfix,hm,hB,hb,hr⟩
  refine ⟨hq,?_,?_,?_,hB,hb,?_⟩
  · simpa only [Nat.cast_ofNat] using aggregate_clone_lower p hp
  · intro hf
    rw [hfix hf,aggregate_clone_shares]
  · rw [aggregate_clones_mass]
    exact hm
  · exact (cloned_response_bounds_iff _ _ _ _ _ _).mp hr

theorem cloned_uniform_dense (n m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) (fixed : Bool) :
    ClonedUniformWitness n m ε fixed (cloneShares n) (uniformTarget m (1/(4 : ℕ))) (orderedBlock 1) := by
  have h := uniform_witness_dense m hm ε hε fixed
  rcases h with ⟨hq,ha,hfix,hn,hB,hb,hr⟩
  refine ⟨hq,fun _ => le_refl _,fun _ => rfl,?_,hB,hb,?_⟩
  · rw [←aggregate_clones_mass,aggregate_clone_shares]
    exact hn
  · apply (cloned_response_bounds_iff _ _ _ _ _ _).mpr
    rw [aggregate_clone_shares]
    exact hr

theorem cloned_uniform_observations_bounded (n m : ℕ) (hm : 0 < m) :
    IsSkew (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ))))) ∧
    (∀ h h', -1 ≤ clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ∧
      clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))) h h' ≤ 1) ∧
    (∀ i h, -1 ≤ clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ∧
      clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ)))) i h ≤ 1) := by
  have hb := two_anchor_observed_bounds hm (uniformTarget m (1/(4 : ℕ)))
    (fun j => le_of_lt (uniformTarget_positive m (1/(4 : ℕ)) (by norm_num) j))
    (uniformTarget_mass m hm (1/(4 : ℕ)))
  norm_num only [Nat.cast_ofNat] at hb
  refine ⟨cloned_core_skew _ (twoCore_skew _),?_,?_⟩
  · intro h h'
    simpa only [clonedCore,rigidityCore,Nat.cast_ofNat] using hb.1 (cloneClass h) (cloneClass h')
  · intro i h
    simpa only [clonedCross,rigidityCross,Nat.cast_ofNat] using hb.2 i (cloneClass h)

theorem cloned_uniform_dense_full_game (n m : ℕ) (hm : 0 < m) :
    (∀ v, 0 ≤ blockWeights (cloneShares n) (uniformTarget m (1/(4 : ℕ))) v) ∧
    (∑ v, blockWeights (cloneShares n) (uniformTarget m (1/(4 : ℕ))) v)=1 ∧
    IsSkew (blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1)) ∧
    (∀ v w, -1 ≤ blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1) v w ∧
      blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1) v w ≤ 1) ∧
    ∀ v, response (blockMatrix (clonedCore (n := n) (rigidityCore (uniformTarget m (1/(4 : ℕ)))))
      (clonedCross (n := n) (rigidityCross (uniformTarget m (1/(4 : ℕ))))) (orderedBlock 1))
      (blockWeights (cloneShares n) (uniformTarget m (1/(4 : ℕ)))) v ≤ 0 := by
  have hw := cloned_uniform_dense n m hm 0 (le_refl 0) true
  have hb := cloned_uniform_observations_bounded n m hm
  refine ⟨blockWeights_nonneg _ _ (fun h => le_of_lt (clone_shares_positive n h)) hw.1,?_,
    blockMatrix_skew _ _ _ hb.1 hw.2.2.2.2.1,
    blockMatrix_bounds _ _ _ 1 hb.2.1 hb.2.2 hw.2.2.2.2.2.1,hw.2.2.2.2.2.2⟩
  rw [blockWeights_mass]
  exact hw.2.2.2.1

theorem joint_support_scalar_lower (k m H Q c : ℝ) (hk : 2 ≤ k)
    (hH : 0 ≤ H) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hbase : c*min (m+2) Q ≤ H+2) :
    c/(2 : ℕ)*min (k+m) (k+Q) ≤ k+H := by
  have hsmall : c*min m Q ≤ k+H := by
    have hm : min m Q ≤ min (m+2) Q := min_le_min (by linarith) (le_refl _)
    have := mul_le_mul_of_nonneg_left hm hc
    linarith
  have hident : min (k+m) (k+Q) = k+min m Q := by rw [min_add_add_left]
  rw [hident]
  have hk0 : 0 ≤ k := by linarith
  have hck := mul_le_mul_of_nonneg_right hc1 hk0
  nlinarith

theorem cloned_uniform_total_support_lower {n m : ℕ} (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) (fixed : Bool)
    (p : CloneAnchors n → ℝ) (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (h : ClonedUniformWitness n m ε fixed p q B) :
    Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))/(2 : ℕ) * min ((n+2 : ℕ)+ (m : ℝ))
      ((n+2 : ℕ)+1/Real.sqrt ε) ≤
      ((Finset.univ.filter fun v => blockWeights p q v ≠ 0).card : ℝ) := by
  classical
  have ha := cloned_witness_aggregates ε fixed p q B h
  have hlow := uniform_total_support_lower hm q (aggregateClones p)
    ha.1 ha.2.1 ha.2.2.2.1 B ha.2.2.2.2.1 (fun i j => (ha.2.2.2.2.2.1 i j).1)
    ε hε ha.2.2.2.2.2.2
  rw [clone_support_card p q h.2.1]
  push_cast
  have hc0 := Real.sqrt_nonneg (((3 : ℕ) : ℝ)/(1216 : ℕ) : ℝ)
  have hc1 : Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ) : ℝ) ≤ 1 := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ ((3 : ℕ) : ℝ)/(1216 : ℕ) by norm_num)
    nlinarith
  have hb := joint_support_scalar_lower ((n : ℝ)+2) m (supportSize q) (1/Real.sqrt ε)
    (Real.sqrt (((3 : ℕ) : ℝ)/(1216 : ℕ))) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by positivity) hc0 hc1 hlow
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hb

end
end SparseCompletion
