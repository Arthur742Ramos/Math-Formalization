/- AI-assisted formalization under the repository Apache-2.0 license.
Universal joint-support upper bound at arbitrary positive payoff scale. -/
module
public import PayoffScaling
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bounded_mass_grid_bound (M r η : ℝ) (hM : 0 < M) (hr : r ≤ 1)
    (hη : 0 < η) (hηM : η ≤ M) :
    (gridSize M r η : ℝ) ≤ ((2 : ℕ) : ℝ)*Real.sqrt (M/η) := by
  have hQ : 1 ≤ Real.sqrt (M/η) := by
    have hd : (1 : ℝ) ≤ M/η := (le_div_iff₀ hη).mpr (by simpa only [one_mul] using hηM)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hd
  have hroot : Real.sqrt (M*r/η) ≤ Real.sqrt (M/η) := by
    apply Real.sqrt_le_sqrt
    exact (div_le_div_iff_of_pos_right hη).mpr (mul_le_of_le_one_right (le_of_lt hM) hr)
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (M*r/η))
  change (gridSize M r η : ℝ) < Real.sqrt (M*r/η)+1 at hc
  norm_num only [Nat.cast_ofNat]
  linarith

theorem normalized_scaled_joint_support_upper {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η) (hηM : η ≤ M)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r=1) (hqmass : ∑ i, q i=r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (∀ h, (∑ i, q' i*D i h)=∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) ∧
      ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤
        (2 : ℕ)*min ((k : ℝ)+Fintype.card ι) ((k : ℝ)+Real.sqrt (M/η)) := by
  norm_num only [Nat.cast_ofNat] at *
  classical
  obtain ⟨q',B',hn,hm,_ha,hs,_hc,ht,hmo,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_all_mass k K D B p q M r η hM hr hη
      hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,hs,hmo,hsk,hb,hrows,?_⟩
  have hr1 : r ≤ 1 := by
    have hsp := Finset.sum_nonneg (fun h (_ : h ∈ Finset.univ) => hp h)
    linarith
  have hgrid := bounded_mass_grid_bound M r η hM hr1 hη hηM
  norm_num only [Nat.cast_ofNat] at hgrid
  have hdim := le_trans ht (min_le_left _ _)
  have hgridnat := le_trans ht (min_le_right _ _)
  have hdimR : ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤ k+Fintype.card ι := by exact_mod_cast hdim
  have hgridR : ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤ (2 : ℕ)*(k : ℝ)+(gridSize M r η : ℝ) := by exact_mod_cast hgridnat
  exact joint_support_scalar_upper k (Fintype.card ι) _ (Real.sqrt (M/η))
    (by positivity) (by positivity) hdimR (by
      norm_num only [Nat.cast_ofNat] at hgridR ⊢
      linarith)

end
end SparseCompletion
