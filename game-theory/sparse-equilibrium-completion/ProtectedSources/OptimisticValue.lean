/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalStability

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def ValidIntervalSystem {ν : Type*} (lo hi : ν → ν → ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ i j, i ≠ j → -M ≤ lo i j ∧ lo i j ≤ hi i j ∧ hi i j ≤ M ∧
    lo i j= -hi j i ∧ hi i j= -lo j i

def intervalMatrices {ν : Type*} (lo hi : ν → ν → ℝ) (M : ℝ) : Set (ν → ν → ℝ) :=
  skewBox M ∩ {A | offDiagonalIntervals lo hi A}

theorem interval_matrices_compact {ν : Type*} [Fintype ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) : IsCompact (intervalMatrices lo hi M) := by
  apply (skewBox_compact M).inter_right
  have he : {A : ν → ν → ℝ | offDiagonalIntervals lo hi A}=
      ⋂ i, ⋂ j, ⋂ (_h : i ≠ j), {A | lo i j ≤ A i j ∧ A i j ≤ hi i j} := by
    ext A
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,offDiagonalIntervals]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  change IsClosed ({A : ν → ν → ℝ | lo i j ≤ A i j} ∩ {A | A i j ≤ hi i j})
  exact (isClosed_le continuous_const
    (show Continuous (fun A : ν → ν → ℝ => A i j) by fun_prop)).inter
    (isClosed_le (show Continuous (fun A : ν → ν → ℝ => A i j) by fun_prop) continuous_const)

theorem interval_matrices_nonempty {ν : Type*}
    (lo hi : ν → ν → ℝ) (M : ℝ) (h : ValidIntervalSystem lo hi M) :
    (intervalMatrices lo hi M).Nonempty := by
  let A := projectedResidual lo hi (fun _ _ => 0)
  have hzero : IsSkew (fun _ _ : ν => (0 : ℝ)) := by intro _ _; exact neg_zero.symm
  have hlu := fun i j he => (h.2 i j he).2.1
  have hlo := fun i j he => (h.2 i j he).1
  have hhi := fun i j he => (h.2 i j he).2.2.1
  have hrev := fun i j he => (h.2 i j he).2.2.2
  exact ⟨A,⟨projected_residual_skew lo hi _ hzero hlu hrev,
    projected_residual_bounds lo hi _ M h.1 hlu hlo hhi⟩,
    projected_residual_interval lo hi _ hlu⟩

def optimisticValue {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ)) : ℝ :=
  sInf ((fun z : (ν → ν → ℝ) × (ν → ℝ) => exploitability z.1 z.2) ''
    (intervalMatrices lo hi M ×ˢ X))

theorem optimistic_value_attained {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ))
    (hI : ValidIntervalSystem lo hi M) (hX : IsCompact X) (hne : X.Nonempty) :
    ∃ A ∈ intervalMatrices lo hi M, ∃ x ∈ X, exploitability A x=optimisticValue lo hi M X := by
  have hc := ((interval_matrices_compact lo hi M).prod hX).image exploitability_continuous
  have hn := ((interval_matrices_nonempty lo hi M hI).prod hne).image
    (fun z : (ν → ν → ℝ) × (ν → ℝ) => exploitability z.1 z.2)
  obtain ⟨⟨A,x⟩,⟨hA,hx⟩,he⟩ := hc.sInf_mem hn
  exact ⟨A,hA,x,hx,he⟩

theorem optimistic_value_le_witness {ν : Type*} [Fintype ν] [Nonempty ν]
    (lo hi : ν → ν → ℝ) (M : ℝ) (X : Set (ν → ℝ)) (hX : IsCompact X)
    (A : ν → ν → ℝ) (x : ν → ℝ) (hA : A ∈ intervalMatrices lo hi M) (hx : x ∈ X) :
    optimisticValue lo hi M X ≤ exploitability A x := by
  apply csInf_le (((interval_matrices_compact lo hi M).prod hX).image exploitability_continuous).bddBelow
  exact ⟨(A,x),⟨hA,hx⟩,rfl⟩

end
end SparseCompletion
