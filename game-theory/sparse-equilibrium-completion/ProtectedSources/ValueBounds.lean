/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.FixedValue

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem exploitability_nonnegative {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (hA : IsSkew A)
    (hx : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) : 0 ≤ exploitability A x := by
  have hz : (∑ i, x i*response A x i)=0 := by
    simpa only [response,Finset.mul_sum,mul_assoc] using skew_weighted_sum Finset.univ x A hA
  calc
    0 = ∑ i, x i*response A x i := hz.symm
    _ ≤ ∑ i, x i*exploitability A x := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (response_le_exploitability A x i) (hx i)
    _ = _ := by rw [←Finset.sum_mul,hm,one_mul]

theorem exploitability_bounded_above {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x : ν → ℝ) (M : ℝ)
    (hA : ∀ i j, A i j ≤ M) (hx : ∀ i, 0 ≤ x i) (hm : ∑ i, x i=1) :
    exploitability A x ≤ M := by
  apply (exploitability_le_iff A x M).mpr
  intro i
  unfold response
  calc
    (∑ j, A i j*x j) ≤ ∑ j, M*x j := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hA i j) (hx j)
    _ = M := by rw [←Finset.mul_sum,hm,mul_one]

theorem fixed_game_value_bounds {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r : ℝ) (R : Set (ι → ℝ)) (hM : 0 ≤ M) (hR : IsCompact R) (hne : R.Nonempty)
    (hp : ∀ h, 0 ≤ p h) (hpm : (∑ h, p h)+r=1)
    (hprob : ∀ q ∈ R, (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M) :
    0 ≤ fixedGameValue K D p M R ∧ fixedGameValue K D p M R ≤ M ∧
      fixedAnchorFeasible R K D p M r (fixedGameValue K D p M R) := by
  obtain ⟨B,hB,q,hq,he⟩ := fixed_game_value_attained K D p M R hM hR hne
  have hsk := blockMatrix_skew K D B hK hB.1
  have hb := blockMatrix_bounds K D B M hKb hDb hB.2
  have hn := blockWeights_nonneg p q hp (hprob q hq).1
  have hm : (∑ a, blockWeights p q a)=1 := by rw [blockWeights_mass,(hprob q hq).2,hpm]
  have h0 := exploitability_nonnegative _ _ hsk hn hm
  have hu := exploitability_bounded_above _ _ M (fun i j => (hb i j).2) hn hm
  rw [he] at h0 hu
  refine ⟨h0,hu,q,hq,(hprob q hq).1,(hprob q hq).2,B,hB.1,hB.2,?_⟩
  intro a
  rw [←he]
  exact response_le_exploitability _ _ a

end
end SparseCompletion
