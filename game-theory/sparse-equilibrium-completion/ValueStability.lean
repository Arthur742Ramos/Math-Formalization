/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import OptimisticValue

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_matrices_projection {ν : Type*}
    (lo hi lo' hi' A : ν → ν → ℝ) (M : ℝ)
    (hI' : ValidIntervalSystem lo' hi' M) (hA : A ∈ intervalMatrices lo hi M) :
    projectedResidual lo' hi' A ∈ intervalMatrices lo' hi' M := by
  have hlu := fun i j he => (hI'.2 i j he).2.1
  have hlo := fun i j he => (hI'.2 i j he).1
  have hhi := fun i j he => (hI'.2 i j he).2.2.1
  have hrev := fun i j he => (hI'.2 i j he).2.2.2
  exact ⟨⟨projected_residual_skew lo' hi' A hA.1.1 hlu hrev,
    projected_residual_bounds lo' hi' A M hI'.1 hlu hlo hhi⟩,
    projected_residual_interval lo' hi' A hlu⟩

theorem optimistic_value_projection_bound {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : X.Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    optimisticValue lo' hi' M X ≤ optimisticValue lo hi M X+δ := by
  obtain ⟨A,hA,x,hx,he⟩ := optimistic_value_attained lo hi M X hI hX hne
  let A' := projectedResidual lo' hi' A
  have hA' : A' ∈ intervalMatrices lo' hi' M := interval_matrices_projection lo hi lo' hi' A M hI' hA
  have hdist := interval_system_projection_distance lo hi lo' hi' A δ hδ hA.1.1 hA.2
    (fun i j hij => (hI'.2 i j hij).2.1) hd
  have hp := exploitability_perturbation A A' x δ 1 (hprob x hx).1 (hprob x hx).2 hdist
  have hv := optimistic_value_le_witness lo' hi' M X hX A' x hA' hx
  have hb := (abs_le.mp hp).1
  rw [he] at hb
  nlinarith

theorem optimistic_value_interval_stability {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi lo' hi' : ν → ν → ℝ) (M δ : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hI' : ValidIntervalSystem lo' hi' M)
    (hδ : 0 ≤ δ) (hX : IsCompact X) (hne : X.Nonempty)
    (hprob : ∀ x ∈ X, (∀ i, 0 ≤ x i) ∧ (∑ i, x i)=1)
    (hd : ∀ i j, i ≠ j → |lo i j-lo' i j| ≤ δ ∧ |hi i j-hi' i j| ≤ δ) :
    |optimisticValue lo hi M X-optimisticValue lo' hi' M X| ≤ δ := by
  have h1 := optimistic_value_projection_bound lo hi lo' hi' M δ X hI hI' hδ hX hne hprob hd
  have hd' : ∀ i j, i ≠ j → |lo' i j-lo i j| ≤ δ ∧ |hi' i j-hi i j| ≤ δ := by
    intro i j hij
    constructor
    · rw [abs_sub_comm]; exact (hd i j hij).1
    · rw [abs_sub_comm]; exact (hd i j hij).2
  have h2 := optimistic_value_projection_bound lo' hi' lo hi M δ X hI' hI hδ hX hne hprob hd'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end SparseCompletion
