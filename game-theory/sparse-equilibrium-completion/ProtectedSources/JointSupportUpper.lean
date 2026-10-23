/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.JointSupportFoundation
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem unit_mass_grid_bound (r η : ℝ) (hr : r ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1) :
    (gridSize 1 r η : ℝ) ≤ (2 : ℕ)*(1/Real.sqrt η) := by
  norm_num only [Nat.cast_ofNat] at *
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hs1 : Real.sqrt η ≤ 1 := by simpa using Real.sqrt_le_sqrt hη1
  have hQ : 1 ≤ 1/Real.sqrt η := (le_div_iff₀ hs).mpr (by simpa using hs1)
  have hroot : Real.sqrt (1*r/η) ≤ 1/Real.sqrt η := by
    calc
      _ ≤ Real.sqrt (1/η) := Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right hη).mpr (by simpa using hr))
      _ = _ := by rw [Real.sqrt_div (by norm_num),Real.sqrt_one]
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (1*r/η))
  change (gridSize 1 r η : ℝ) < Real.sqrt (1*r/η)+1 at hc
  linarith

theorem joint_support_scalar_upper (k m T Q : ℝ) (hm : 0 ≤ m) (hk : 0 ≤ k)
    (h1 : T ≤ k+m) (h2 : T ≤ (2 : ℕ)*k+(2 : ℕ)*Q) :
    T ≤ (2 : ℕ)*min (k+m) (k+Q) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact le_min (by linarith) (by linarith)

theorem normalized_joint_support_upper {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (r η : ℝ)
    (hr : 0 ≤ r) (hη : 0 < η) (hη1 : η ≤ 1)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r=1) (hqmass : ∑ i, q i=r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -1 ≤ K h h' ∧ K h h' ≤ 1)
    (hDb : ∀ i h, -1 ≤ D i h ∧ D i h ≤ 1)
    (hBb : ∀ i j, -1 ≤ B i j ∧ B i j ≤ 1)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (∀ h, (∑ i, q' i*D i h)=∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -1 ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ 1) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) ∧
      ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤
        (2 : ℕ)*min ((k : ℝ)+Fintype.card ι) ((k : ℝ)+1/Real.sqrt η) := by
  norm_num only [Nat.cast_ofNat] at *
  classical
  obtain ⟨q',B',hn,hm,_ha,hs,_hc,ht,hmo,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_all_mass k K D B p q 1 r η (by norm_num) hr hη
      hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,hs,hmo,hsk,hb,hrows,?_⟩
  have hr1 : r ≤ 1 := by
    have hsp := Finset.sum_nonneg (fun h (_ : h ∈ Finset.univ) => hp h)
    linarith
  have hgrid := unit_mass_grid_bound r η hr1 hη hη1
  norm_num only [Nat.cast_ofNat] at hgrid
  have hdim := le_trans ht (min_le_left _ _)
  have hgridnat := le_trans ht (min_le_right _ _)
  have hdimR : ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤ k+Fintype.card ι := by exact_mod_cast hdim
  have hgridR : ((Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card : ℝ) ≤ (2 : ℕ)*(k : ℝ)+(gridSize 1 r η : ℝ) := by exact_mod_cast hgridnat
  exact joint_support_scalar_upper k (Fintype.card ι) _ (1/Real.sqrt η)
    (by positivity) (by positivity) hdimR (by
      norm_num only [Nat.cast_ofNat] at hgridR ⊢
      linarith)

end
end SparseCompletion
